#![feature(rustc_private)]
#[macro_use]
mod common;

#[cfg(feature = "sst-json")]
mod sst_json_tests {
    use super::common::*;
    use serde_json::Value;
    use tempfile::TempDir;

    fn write_source(tempdir: &TempDir, file_name: &str, body: &str) -> std::path::PathBuf {
        let path = tempdir.path().join(file_name);
        let code = format!("{FEATURE_PRELUDE}\n{USE_PRELUDE}\nverus! {{ {body} }}\n");
        std::fs::write(&path, code).expect("write source file");
        path
    }

    fn read_json(path: &std::path::Path) -> Value {
        let contents = std::fs::read_to_string(path).expect("read SST JSON");
        serde_json::from_str(&contents).expect("parse SST JSON")
    }

    fn collect_call_type_args<'a>(value: &'a Value, function_name: &str, out: &mut Vec<&'a Value>) {
        if let Some(call) = value.get("Call").and_then(Value::as_array) {
            if call.first().is_some_and(|fun| fun.to_string().contains(function_name)) {
                out.push(&call[1]);
            }
        }
        match value {
            Value::Array(values) => {
                for value in values {
                    collect_call_type_args(value, function_name, out);
                }
            }
            Value::Object(fields) => {
                for value in fields.values() {
                    collect_call_type_args(value, function_name, out);
                }
            }
            _ => {}
        }
    }

    fn collect_binary_ops<'a>(value: &'a Value, out: &mut Vec<&'a Value>) {
        if let Some(binary) = value.get("Binary").and_then(Value::as_array) {
            out.push(&binary[0]);
        }
        match value {
            Value::Array(values) => {
                for value in values {
                    collect_binary_ops(value, out);
                }
            }
            Value::Object(fields) => {
                for value in fields.values() {
                    collect_binary_ops(value, out);
                }
            }
            _ => {}
        }
    }

    #[test]
    fn export_writes_versioned_envelope_deterministically() {
        let tempdir = TempDir::new().expect("temp dir");
        let source = write_source(&tempdir, "test.rs", "fn exported() {}");

        let output = run_verus_raw(
            &[
                "--crate-type=lib",
                "--export-sst-json",
                tempdir.path().to_str().unwrap(),
                source.to_str().unwrap(),
            ],
            tempdir.path(),
        );
        assert!(
            output.status.success(),
            "verus failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );

        let json = read_json(&tempdir.path().join("test.json"));
        assert_eq!(json["format"], "verus-sst");
        assert_eq!(json["format_version"], 1);
        assert_eq!(json["krate"], "test");
        assert!(!json["decls"].as_array().expect("declaration array").is_empty());
        let mut top_level_keys =
            json.as_object().expect("SST JSON envelope").keys().cloned().collect::<Vec<_>>();
        top_level_keys.sort();
        assert_eq!(top_level_keys, ["decls", "format", "format_version", "krate"]);
        let function = json["decls"]
            .as_array()
            .unwrap()
            .iter()
            .find(|decl| decl["DeclType"] == "ExecFn")
            .expect("exported function");
        assert!(function["x"].get("attrs").is_none());
        assert!(function["x"].get("safe_api_check").is_none());

        let first_export =
            std::fs::read(tempdir.path().join("test.json")).expect("read first SST JSON export");
        let second_output = run_verus_raw(
            &[
                "--crate-type=lib",
                "--export-sst-json",
                tempdir.path().to_str().unwrap(),
                source.to_str().unwrap(),
            ],
            tempdir.path(),
        );
        assert!(
            second_output.status.success(),
            "second verus run failed:\n{}",
            String::from_utf8_lossy(&second_output.stderr)
        );
        let second_export =
            std::fs::read(tempdir.path().join("test.json")).expect("read second SST JSON export");
        assert_eq!(first_export, second_export, "SST JSON export is not deterministic");
    }

    #[test]
    fn export_is_independent_of_source_directory() {
        let first_dir = TempDir::new().expect("first temp dir");
        let second_dir = TempDir::new().expect("second temp dir");
        let body = "proof fn exported() { assert(false); }";
        let first_source = write_source(&first_dir, "same.rs", body);
        let second_source = write_source(&second_dir, "same.rs", body);

        for (dir, source) in [(&first_dir, &first_source), (&second_dir, &second_source)] {
            let output = run_verus_raw(
                &[
                    "--crate-type=lib",
                    "--export-sst-json",
                    dir.path().to_str().unwrap(),
                    source.to_str().unwrap(),
                ],
                dir.path(),
            );
            assert!(
                !output.status.success(),
                "invalid assertion unexpectedly verified:\n{}",
                String::from_utf8_lossy(&output.stderr)
            );
        }

        let first = std::fs::read(first_dir.path().join("same.json")).unwrap();
        let second = std::fs::read(second_dir.path().join("same.json")).unwrap();
        assert_eq!(first, second, "SST JSON contains source-directory-dependent data");
    }

    #[test]
    fn export_projects_pure_sst_binary_operators() {
        let tempdir = TempDir::new().expect("temp dir");
        let source = write_source(
            &tempdir,
            "binary_ops.rs",
            r#"
                pub open spec fn add(x: int, y: int) -> int { x + y }

                proof fn check(x: int, y: int) {
                    assert(add(x, y) == x + y);
                }
            "#,
        );

        let output = run_verus_raw(
            &[
                "--crate-type=lib",
                "--export-sst-json",
                tempdir.path().to_str().unwrap(),
                source.to_str().unwrap(),
            ],
            tempdir.path(),
        );
        assert!(
            output.status.success(),
            "verus failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );

        let json = read_json(&tempdir.path().join("binary%5Fops.json"));
        let mut ops = Vec::new();
        collect_binary_ops(&json, &mut ops);
        assert!(ops.iter().any(|op| **op == serde_json::json!("Eq")));
        assert!(ops.iter().any(|op| **op == serde_json::json!({ "Arith": "Add" })));
    }

    #[test]
    fn export_precedes_verification_failure() {
        let tempdir = TempDir::new().expect("temp dir");
        let source = write_source(&tempdir, "failing.rs", "proof fn exported() { assert(false); }");

        let output = run_verus_raw(
            &[
                "--crate-type=lib",
                "--export-sst-json",
                tempdir.path().to_str().unwrap(),
                source.to_str().unwrap(),
            ],
            tempdir.path(),
        );
        assert!(
            !output.status.success(),
            "invalid assertion unexpectedly verified:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );

        let json = read_json(&tempdir.path().join("failing.json"));
        assert!(json["decls"].as_array().expect("declaration array").iter().any(
            |decl| decl["DeclType"] == "ProofFn" && decl.to_string().contains("\"Bool\":false")
        ));
    }

    #[test]
    fn export_reports_file_creation_errors() {
        let tempdir = TempDir::new().expect("temp dir");
        let source = write_source(&tempdir, "test.rs", "fn exported() {}");
        std::fs::create_dir(tempdir.path().join("test.json"))
            .expect("create conflicting output directory");

        let output = run_verus_raw(
            &[
                "--crate-type=lib",
                "--export-sst-json",
                tempdir.path().to_str().unwrap(),
                source.to_str().unwrap(),
            ],
            tempdir.path(),
        );
        assert!(!output.status.success(), "export unexpectedly succeeded");
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("failed to create SST JSON file"),
            "unexpected diagnostic:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    #[test]
    fn export_excludes_unreachable_mutual_functions() {
        let tempdir = TempDir::new().expect("temp dir");
        let source = write_source(
            &tempdir,
            "mutual.rs",
            r#"
                mod exported {
                    use super::*;

                    pub open spec fn even(n: u64) -> bool
                        decreases n,
                    {
                        n == 0 || odd(n)
                    }

                    pub open spec fn odd(n: u64) -> bool
                        decreases n,
                    {
                        n != 0 && even(n)
                    }
                }

                mod hidden {
                    use super::*;

                    pub open spec fn first(n: u64) -> bool
                        decreases n,
                    {
                        n == 0 || second(n)
                    }

                    pub open spec fn second(n: u64) -> bool
                        decreases n,
                    {
                        n != 0 && first(n)
                    }
                }
            "#,
        );

        let output = run_verus_raw(
            &[
                "--crate-type=lib",
                "--verify-module",
                "exported",
                "--export-sst-json",
                tempdir.path().to_str().unwrap(),
                source.to_str().unwrap(),
            ],
            tempdir.path(),
        );
        assert!(!output.status.success(), "non-decreasing mutual recursion unexpectedly verified");

        let json = read_json(&tempdir.path().join("mutual_exported.json"));
        let serialized = json.to_string();
        assert!(serialized.contains("\"segments\":[\"exported\""));
        assert!(!serialized.contains("\"segments\":[\"hidden\""));
    }

    #[test]
    fn export_includes_resolved_trait_method_dependencies() {
        let tempdir = TempDir::new().expect("temp dir");
        let source = write_source(
            &tempdir,
            "resolved.rs",
            r#"
                mod definitions {
                    use super::*;

                    pub struct S;

                    pub trait T {
                        spec fn holds(&self) -> bool;
                    }

                    impl T for S {
                        open spec fn holds(&self) -> bool { true }
                    }
                }

                mod exported {
                    use super::definitions::*;

                    proof fn check(s: S) {
                        assert(s.holds());
                    }
                }
            "#,
        );

        let output = run_verus_raw(
            &[
                "--crate-type=lib",
                "--verify-module",
                "exported",
                "--export-sst-json",
                tempdir.path().to_str().unwrap(),
                source.to_str().unwrap(),
            ],
            tempdir.path(),
        );
        assert!(
            output.status.success(),
            "verus failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );

        let json = read_json(&tempdir.path().join("resolved_exported.json"));
        assert!(
            json["decls"].as_array().expect("declaration array").iter().any(|decl| {
                decl["DeclType"] == "SpecFn"
                    && decl["x"]["kind"].get("TraitMethodImpl").is_some()
                    && decl.to_string().contains("holds")
            }),
            "resolved trait-method implementation was not exported"
        );
    }

    #[test]
    fn export_includes_dependencies_from_spec_recommends() {
        let tempdir = TempDir::new().expect("temp dir");
        let source = write_source(
            &tempdir,
            "declaration_dependencies.rs",
            r#"
                mod definitions {
                    pub open spec fn recommended() -> bool { true }
                }

                mod exported {
                    use super::definitions;

                    pub open spec fn checked() -> bool
                        recommends definitions::recommended(),
                    {
                        true
                    }
                }
            "#,
        );

        let output = run_verus_raw(
            &[
                "--crate-type=lib",
                "--verify-module",
                "exported",
                "--export-sst-json",
                tempdir.path().to_str().unwrap(),
                source.to_str().unwrap(),
            ],
            tempdir.path(),
        );
        assert!(
            output.status.success(),
            "verus failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );

        let json = read_json(&tempdir.path().join("declaration%5Fdependencies_exported.json"));
        let declarations = json["decls"].as_array().expect("declaration array");
        let has_function = |name: &str| {
            declarations.iter().any(|decl| {
                matches!(decl["DeclType"].as_str(), Some("SpecFn" | "ProofFn" | "ExecFn"))
                    && decl["x"]["name"].to_string().contains(name)
            })
        };
        assert!(has_function("recommended"), "recommends dependency was not exported");
    }

    #[test]
    fn export_generic_function_once_for_multiple_instantiations() {
        let tempdir = TempDir::new().expect("temp dir");
        let source = write_source(
            &tempdir,
            "polymorphic.rs",
            r#"
                pub open spec fn identity<A>(a: A) -> A { a }

                proof fn check() {
                    assert(identity::<u64>(1) == 1);
                    assert(identity::<bool>(true));
                }
            "#,
        );

        let output = run_verus_raw(
            &[
                "--crate-type=lib",
                "--export-sst-json",
                tempdir.path().to_str().unwrap(),
                source.to_str().unwrap(),
            ],
            tempdir.path(),
        );
        assert!(
            output.status.success(),
            "verus failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );

        let json = read_json(&tempdir.path().join("polymorphic.json"));
        let identity_decls = json["decls"]
            .as_array()
            .expect("declaration array")
            .iter()
            .filter(|decl| decl["DeclType"] == "SpecFn" && decl.to_string().contains("identity"))
            .count();
        assert_eq!(identity_decls, 1);
        let mut call_type_args = Vec::new();
        collect_call_type_args(&json, "identity", &mut call_type_args);
        assert_eq!(call_type_args.len(), 2);
        assert!(call_type_args.iter().any(|args| **args == serde_json::json!(["Bool"])));
        assert!(
            call_type_args.iter().any(|args| **args == serde_json::json!([{ "Int": { "U": 64 } }]))
        );
    }

    #[test]
    fn export_writes_datatype_only_modules() {
        let tempdir = TempDir::new().expect("temp dir");
        let source = write_source(
            &tempdir,
            "datatype_only.rs",
            "struct One; enum Only { A } struct Middle { one: One } struct Root { middle: Middle }",
        );

        let output = run_verus_raw(
            &[
                "--crate-type=lib",
                "--export-sst-json",
                tempdir.path().to_str().unwrap(),
                source.to_str().unwrap(),
            ],
            tempdir.path(),
        );
        assert!(
            output.status.success(),
            "verus failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );

        let json = read_json(&tempdir.path().join("datatype%5Fonly.json"));
        let declarations = json["decls"].as_array().expect("declaration array");
        let one = declarations
            .iter()
            .find(|decl| decl["DeclType"] == "Datatype" && decl.to_string().contains("One"))
            .expect("struct declaration");
        let only = declarations
            .iter()
            .find(|decl| decl["DeclType"] == "Datatype" && decl.to_string().contains("Only"))
            .expect("enum declaration");
        assert_eq!(one["x"]["dt_type"], "Struct");
        assert_eq!(only["x"]["dt_type"], "Enum");
        let names = declarations
            .iter()
            .filter(|decl| decl["DeclType"] == "Datatype")
            .map(|decl| decl["x"]["name"].to_string())
            .collect::<Vec<_>>();
        let position = |needle: &str| {
            names.iter().position(|name| name.contains(needle)).expect("datatype declaration")
        };
        assert!(position("One") < position("Middle"));
        assert!(position("Middle") < position("Root"));
    }

    #[test]
    fn export_uses_distinct_files_for_spinoff_buckets() {
        let tempdir = TempDir::new().expect("temp dir");
        let source = write_source(
            &tempdir,
            "spinoff.rs",
            r#"
                #[verifier::spinoff_prover]
                proof fn spun() { assert(true); }

                proof fn normal() { assert(true); }
            "#,
        );

        let output = run_verus_raw(
            &[
                "--crate-type=lib",
                "--num-threads",
                "2",
                "--export-sst-json",
                tempdir.path().to_str().unwrap(),
                source.to_str().unwrap(),
            ],
            tempdir.path(),
        );
        assert!(
            output.status.success(),
            "verus failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );

        let module = read_json(&tempdir.path().join("spinoff.json")).to_string();
        let spun =
            read_json(&tempdir.path().join("spinoff__function__spinoff_spun.json")).to_string();
        assert!(module.contains("normal"));
        assert!(spun.contains("spun"));
        assert!(!spun.contains("normal"));
    }

    #[test]
    fn export_file_names_encode_module_boundaries() {
        let tempdir = TempDir::new().expect("temp dir");
        let source = write_source(
            &tempdir,
            "collision.rs",
            r#"
                mod a_b {
                    pub mod c {
                        proof fn left() {}
                    }
                }
                mod a {
                    pub mod b_c {
                        proof fn right() {}
                    }
                }
            "#,
        );

        let output = run_verus_raw(
            &[
                "--crate-type=lib",
                "--export-sst-json",
                tempdir.path().to_str().unwrap(),
                source.to_str().unwrap(),
            ],
            tempdir.path(),
        );
        assert!(
            output.status.success(),
            "verus failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );

        let left_path = tempdir.path().join("collision_a%5Fb_c.json");
        let right_path = tempdir.path().join("collision_a_b%5Fc.json");
        assert!(left_path.is_file());
        assert!(right_path.is_file());
        assert_eq!(read_json(&left_path)["krate"], "collision");
        assert_eq!(read_json(&right_path)["krate"], "collision");
    }
}

#[cfg(not(feature = "sst-json"))]
#[test]
fn export_flag_requires_sst_json_feature() {
    use common::*;

    let tempdir = tempfile::TempDir::new().expect("temp dir");
    let source = tempdir.path().join("test.rs");
    let code = format!("{FEATURE_PRELUDE}\n{USE_PRELUDE}\nverus! {{ enum Only {{ A }} }}\n");
    std::fs::write(&source, code).expect("write source file");

    let output = run_verus_raw(
        &[
            "--crate-type=lib",
            "--export-sst-json",
            tempdir.path().to_str().unwrap(),
            source.to_str().unwrap(),
        ],
        tempdir.path(),
    );
    assert!(!output.status.success(), "export unexpectedly succeeded");
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("SST JSON export requires building Verus with `--features sst-json`"),
        "unexpected diagnostic:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}
