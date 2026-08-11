use std::collections::{HashMap, HashSet};
#[cfg(feature = "sst-json")]
use std::fmt::Write as _;
#[cfg(feature = "sst-json")]
use vir::ast::CrateId;
use vir::{
    ast::{Fun, Krate, Path},
    ast_util::fun_as_friendly_rust_name,
};

// A "bucket" is a group of functions that are processed together
// with the same pruning context.
//
// In general, a bucket can be an arbitrary subset of a module (we need visibility
// to be coherent for a single bucket, so a bucket cannot be cross-module).
//
// More precisely, we determine the buckets based off the spinoff_prover attribute
// (see get_buckets).

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub enum BucketId {
    /// Bucket for everything in the given module (except for any functions that
    /// get their own bucket)
    Module(Path),
    /// Bucket contains a single function (the Path is for the owning module)
    Fun(Path, Fun),
}

#[derive(Clone, Debug)]
pub struct Bucket {
    pub funs: HashSet<Fun>,
}

impl BucketId {
    pub fn to_log_string(&self) -> String {
        match self {
            BucketId::Module(m) => {
                if m.segments.len() == 0 {
                    "root".to_string()
                } else {
                    m.segments.iter().map(|s| s.to_string()).collect::<Vec<_>>().join("__")
                }
            }
            BucketId::Fun(_, f) => {
                f.path.segments.iter().map(|s| s.to_string()).collect::<Vec<_>>().join("__")
            }
        }
    }

    pub fn friendly_name(&self) -> String {
        let module = self.module();
        let mstring = if module.segments.len() == 0 {
            "root module".to_string()
        } else {
            "module ".to_string()
                + &module.segments.iter().map(|s| s.to_string()).collect::<Vec<_>>().join("::")
        };
        match self {
            BucketId::Module(_) => mstring,
            BucketId::Fun(_, f) => {
                format!("{}, function {}", mstring, fun_as_friendly_rust_name(f),)
            }
        }
    }

    /// Get the module for this bucket.
    pub fn module(&self) -> &Path {
        match self {
            BucketId::Module(module) => module,
            BucketId::Fun(module, _) => module,
        }
    }

    /// Get the exact function in this bucket, if it is a singleton bucket.
    pub fn function(&self) -> Option<&Fun> {
        match self {
            BucketId::Module(_) => None,
            BucketId::Fun(_, f) => Some(f),
        }
    }

    /// Return an injective, filesystem-safe stem for this current-crate verification bucket.
    #[cfg(feature = "sst-json")]
    pub fn sst_json_file_stem(&self) -> String {
        let module_stem = path_to_encoded_file_stem(self.module());
        match self {
            BucketId::Module(_) => module_stem,
            BucketId::Fun(_, fun) => {
                format!("{module_stem}__function__{}", path_to_encoded_file_stem(&fun.path))
            }
        }
    }
}

#[cfg(feature = "sst-json")]
fn path_to_encoded_file_stem(path: &Path) -> String {
    fn encode_component(component: &str) -> String {
        let mut encoded = String::new();
        for byte in component.bytes() {
            if byte.is_ascii_alphanumeric() || byte == b'-' {
                encoded.push(byte as char);
            } else {
                write!(&mut encoded, "%{byte:02X}").expect("writing to String cannot fail");
            }
        }
        encoded
    }

    let krate = match &path.krate {
        CrateId::Internal => None,
        CrateId::Core => Some("core"),
        CrateId::Alloc => Some("alloc"),
        CrateId::Vstd => Some("vstd"),
        CrateId::Id(name, _) => Some(name.as_str()),
    };
    let stem = krate
        .into_iter()
        .chain(path.segments.iter().map(|segment| segment.as_ref().as_str()))
        .map(encode_component)
        .collect::<Vec<_>>()
        .join("_");
    if stem.is_empty() { "root".to_string() } else { stem }
}

impl Bucket {
    pub fn contains(&self, fun: &Fun) -> bool {
        self.funs.contains(fun)
    }
}

/// Arrange the given modules into buckets.
/// Typically, this means 1 bucket per module;
/// However, any functions marked 'spinoff_prover' get their own bucket.
pub fn get_buckets(
    krate: &Krate,
    modules_to_verify: &Vec<vir::ast::Module>,
    include_empty_module_buckets: bool,
) -> Vec<(BucketId, Bucket)> {
    let mut map: HashMap<BucketId, Vec<Fun>> = HashMap::new();
    if include_empty_module_buckets {
        for module in modules_to_verify {
            map.entry(BucketId::Module(module.x.path.clone())).or_default();
        }
    }
    let module_set: HashSet<&Path> = modules_to_verify.iter().map(|m| &m.x.path).collect();
    for func in &krate.functions {
        if let Some(owning_module) = &func.x.owning_module {
            if module_set.contains(owning_module) {
                let bucket_id = if func.x.attrs.spinoff_prover {
                    BucketId::Fun(owning_module.clone(), func.x.name.clone())
                } else {
                    BucketId::Module(owning_module.clone())
                };

                if !map.contains_key(&bucket_id) {
                    map.insert(bucket_id.clone(), vec![]);
                }
                map.get_mut(&bucket_id).unwrap().push(func.x.name.clone());
            }
        }
    }

    // Sorting this way puts all the modules first, and individual spinoffs last
    let mut buckets: Vec<_> = map.into_iter().collect();
    buckets.sort_by_key(|kv| kv.0.clone());

    buckets
        .into_iter()
        .map(|(bucket_id, vec)| (bucket_id, Bucket { funs: vec.into_iter().collect() }))
        .collect()
}
