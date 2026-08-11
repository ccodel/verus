//! Versioned, translation-oriented JSON projection of VIR-SST.
//!
//! This module deliberately serializes an explicit recursive subset rather
//! than deriving `Serialize` for SST internals. That keeps the wire format
//! independent of source spans, diagnostics, and unrelated verifier metadata.

use crate::ast::{
    CrateId, Datatype, DatatypeX, Dt, DtType, Fun, Mode, NullaryOpr, Path, Typ, TypX, Typs,
    VarBinder, VarBinders, Variant, VirErr,
};
use crate::ast_util::types_equal;
use crate::context::Ctx;
use crate::messages::error_bare;
use crate::recursion::Node;
use crate::scc::Graph;
use crate::sst::{
    ArithOp as SstArithOp, BinaryOp as SstBinaryOp, Bnd, BndX, CallFun, CallTarget, Dest, Exp,
    ExpX, Exps, FuncCheckSst, FunctionSst, InternalFun, KrateSst, LocalDeclKind, LoopInv, LoopInvs,
    Par, ParPurpose, Pars, Stm, StmX, Stms,
};

use std::collections::HashSet;

// For printing and file I/O
use std::io::Write;
use std::path::{Path as FsPath, PathBuf};

const SST_JSON_FORMAT: &str = "verus-sst";
/// Increment this when a breaking change is made to the serialized representation.
const SST_JSON_FORMAT_VERSION: u32 = 1;

////////////////////////////////////////////////////////////////////////////////

/// Tracks the functions, datatypes, and type instantiations reachable from the
/// current module's serialized SST declarations.
struct ExportCtx<'a> {
    ctx: &'a Ctx,
    // TypX has no Eq implementation, so structural deduplication uses `types_equal`.
    typs: Vec<Typ>,
    dts: HashSet<Dt>,
    missing_dts: HashSet<Dt>,
    fns: HashSet<Fun>,
}

////////////////////////////////////////////////////////////////////////////////

fn visit_datatype(export_ctx: &mut ExportCtx, datatype: &Datatype) {
    let DatatypeX { variants, .. } = &datatype.x;
    for variant in variants.iter() {
        let Variant { fields, .. } = variant;
        for field in fields.iter() {
            let typ = &field.a.0;
            visit_typ(export_ctx, typ);
        }
    }
}

// Keep serialization scoped to the current module or its submodules
fn in_module_or_submodule(
    owning_module: &Option<Path>,
    path: Option<&Path>,
    module: &Path,
) -> bool {
    if let Some(owning_module) = owning_module {
        owning_module.matches_prefix(module)
    } else if let Some(path) = path {
        path.matches_prefix(module)
    } else {
        false
    }
}

fn visit_dt(export_ctx: &mut ExportCtx, dt: &Dt) {
    // Tuple structure is represented directly by `TypX::Datatype`; no tuple
    // declaration is emitted, and the caller separately visits its type arguments.
    if matches!(dt, Dt::Tuple(_)) {
        return;
    }
    if export_ctx.dts.contains(dt) || export_ctx.missing_dts.contains(dt) {
        return;
    }
    let Some(datatype) = export_ctx.ctx.datatype_map.get(dt) else {
        export_ctx.missing_dts.insert(dt.clone());
        return;
    };
    export_ctx.dts.insert(dt.clone());
    visit_datatype(export_ctx, datatype);
}

fn visit_typ(export_ctx: &mut ExportCtx, typ: &Typ) {
    // `TypX` cannot implement `Eq`/`PartialEq` (see the note in vir/src/ast.rs),
    // so duplicate visits are suppressed with a linear scan over a list of
    // already-seen types rather than a `HashSet`.
    for typ2 in export_ctx.typs.iter() {
        if types_equal(typ, typ2) {
            return;
        }
    }
    export_ctx.typs.push(typ.clone());

    match &**typ {
        TypX::SpecFn(typs, typ) => {
            visit_typs(export_ctx, typs);
            visit_typ(export_ctx, typ);
        }
        TypX::AnonymousClosure(typs, typ, _, _) => {
            visit_typs(export_ctx, typs);
            visit_typ(export_ctx, typ);
        }
        TypX::FnDef(fun, typs, resolved) => {
            visit_fun(export_ctx, fun);
            visit_typs(export_ctx, typs);
            if let Some(resolved) = resolved {
                visit_fun(export_ctx, resolved);
            }
        }
        TypX::Datatype(dt, typs, _) => {
            visit_dt(export_ctx, dt);
            visit_typs(export_ctx, typs);
        }
        TypX::Dyn(_, typs, _) | TypX::Primitive(_, typs) => {
            visit_typs(export_ctx, typs);
        }
        TypX::Opaque { args, .. } => {
            visit_typs(export_ctx, args);
        }
        TypX::Decorate(_, decoration_arg, typ) => {
            if let Some(decoration_arg) = decoration_arg {
                visit_typ(export_ctx, &decoration_arg.allocator_typ);
            }
            visit_typ(export_ctx, typ);
        }
        TypX::Boxed(typ) | TypX::PointeeMetadata(typ) | TypX::MutRef(typ) => {
            visit_typ(export_ctx, typ);
        }
        TypX::Projection { trait_typ_args, .. } => {
            visit_typs(export_ctx, trait_typ_args);
        }
        _ => {}
    }
}

fn visit_typs(export_ctx: &mut ExportCtx, typs: &Typs) {
    for typ in typs.iter() {
        visit_typ(export_ctx, &typ);
    }
}

fn visit_varbinder_typ(export_ctx: &mut ExportCtx, binder: &VarBinder<Typ>) {
    visit_typ(export_ctx, &binder.a);
}

fn visit_varbinder_exp(export_ctx: &mut ExportCtx, binder: &VarBinder<Exp>) {
    visit_exp(export_ctx, &binder.a);
}

fn visit_varbinders_typ(export_ctx: &mut ExportCtx, binders: &VarBinders<Typ>) {
    for binder in binders.iter() {
        visit_varbinder_typ(export_ctx, binder);
    }
}

fn visit_varbinders_exp(export_ctx: &mut ExportCtx, binders: &VarBinders<Exp>) {
    for binder in binders.iter() {
        visit_varbinder_exp(export_ctx, binder);
    }
}

fn visit_bnd(export_ctx: &mut ExportCtx, bnd: &Bnd) {
    match &bnd.x {
        BndX::Let(binders) => {
            visit_varbinders_exp(export_ctx, binders);
        }
        BndX::Quant(_, typ_binders, trigs, _) => {
            visit_varbinders_typ(export_ctx, typ_binders);
            visit_trigs(export_ctx, trigs);
        }
        BndX::Lambda(typ_binders, trigs) => {
            visit_varbinders_typ(export_ctx, typ_binders);
            visit_trigs(export_ctx, trigs);
        }
        BndX::Choose(typ_binders, trigs, exp) => {
            visit_varbinders_typ(export_ctx, typ_binders);
            visit_trigs(export_ctx, trigs);
            visit_exp(export_ctx, exp)
        }
    }
}

fn visit_trigs(export_ctx: &mut ExportCtx, trigs: &crate::sst::Trigs) {
    for trig in trigs.iter() {
        visit_exps(export_ctx, trig);
    }
}

fn visit_loop_inv(export_ctx: &mut ExportCtx, inv: &LoopInv) {
    visit_exp(export_ctx, &inv.inv);
}

fn visit_loop_invs(export_ctx: &mut ExportCtx, invs: &LoopInvs) {
    for inv in invs.iter() {
        visit_loop_inv(export_ctx, inv);
    }
}

fn visit_fun(export_ctx: &mut ExportCtx, fun: &Fun) {
    if export_ctx.fns.contains(fun) {
        return;
    }

    // A generic function declaration is exported once; each call expression retains
    // its own concrete type arguments.
    if let Some(sst) = export_ctx.ctx.func_sst_map.get(fun) {
        visit_func_sst(export_ctx, sst);
    }
}

fn visit_call_fun(export_ctx: &mut ExportCtx, call_fun: &CallFun) {
    match call_fun {
        CallFun::Fun(fun, resolved) => {
            visit_fun(export_ctx, fun);
            if let Some((resolved_fun, resolved_typs)) = resolved {
                visit_fun(export_ctx, resolved_fun);
                visit_typs(export_ctx, resolved_typs);
            }
        }
        CallFun::Recursive(fun) => {
            visit_fun(export_ctx, fun);
        }
        _ => {}
    }
}

fn visit_nullary_opr(export_ctx: &mut ExportCtx, op: &NullaryOpr) {
    match op {
        // Trait declarations are outside this projection, but their type arguments
        // can make datatype declarations reachable.
        NullaryOpr::ConstGeneric(typ) => {
            visit_typ(export_ctx, typ);
        }
        NullaryOpr::TraitBound(_, typs) => {
            visit_typs(export_ctx, typs);
        }
        NullaryOpr::TypEqualityBound(_, typs, _, typ) => {
            visit_typs(export_ctx, typs);
            visit_typ(export_ctx, typ);
        }
        NullaryOpr::ConstTypBound(typ1, typ2) => {
            visit_typ(export_ctx, typ1);
            visit_typ(export_ctx, typ2);
        }
    }
}

fn visit_exp(export_ctx: &mut ExportCtx, exp: &Exp) {
    // To ensure we don't miss any types, we visit the type of *every* expression
    // However, we keep around a list of unique types, so while these calls are
    // redundant, we don't end up doing too much extra work
    visit_typ(export_ctx, &exp.typ);

    match &exp.x {
        // Skip ExpX::Const     (no new context to visit)
        // Skip ExpX::Var       (no new context to visit)
        ExpX::StaticVar(fun) => {
            visit_fun(export_ctx, fun);
        }
        // Skip ExpX::VarLoc    (no new context to visit)
        // Skip ExpX::VarAt     (no new context to visit)
        ExpX::Loc(exp) => {
            visit_exp(export_ctx, exp);
        }
        // Skip ExpX::Old       (no new context to visit)
        ExpX::Call(call_fun, typs, exps) => {
            visit_call_fun(export_ctx, call_fun);
            visit_typs(export_ctx, typs);
            visit_exps(export_ctx, exps);
        }
        ExpX::CallLambda(exp, exps) => {
            visit_exp(export_ctx, exp);
            visit_exps(export_ctx, exps);
        }
        ExpX::Ctor(dt, _, binders) => {
            visit_dt(export_ctx, dt);
            for binder in binders.iter() {
                visit_exp(export_ctx, &binder.a);
            }
        }
        ExpX::NullaryOpr(op) => {
            visit_nullary_opr(export_ctx, op);
        }
        ExpX::Unary(_, exp) => {
            visit_exp(export_ctx, exp);
        }
        ExpX::UnaryOpr(op, exp) => {
            // Variant tests and field projections name a datatype in the
            // operator payload; register it so a type referenced only in
            // specs (e.g. vstd's `MemContents` via `mem_contents(...) is
            // Init`) still ships its declaration.
            match op {
                crate::ast::UnaryOpr::Box(typ)
                | crate::ast::UnaryOpr::Unbox(typ)
                | crate::ast::UnaryOpr::HasType(typ)
                | crate::ast::UnaryOpr::HasResolved(typ)
                | crate::ast::UnaryOpr::ToDyn(typ) => visit_typ(export_ctx, typ),
                crate::ast::UnaryOpr::IsVariant { datatype, .. } => visit_dt(export_ctx, datatype),
                crate::ast::UnaryOpr::Field(field_opr) => visit_dt(export_ctx, &field_opr.datatype),
                _ => {}
            }
            visit_exp(export_ctx, exp);
        }
        ExpX::Binary(_, exp1, exp2) => {
            visit_exp(export_ctx, exp1);
            visit_exp(export_ctx, exp2);
        }
        ExpX::BinaryOpr(op, exp1, exp2) => {
            match op {
                crate::ast::BinaryOpr::ExtEq(_, typ) => visit_typ(export_ctx, typ),
            }
            visit_exp(export_ctx, exp1);
            visit_exp(export_ctx, exp2);
        }
        ExpX::If(exp1, exp2, exp3) => {
            visit_exp(export_ctx, exp1);
            visit_exp(export_ctx, exp2);
            visit_exp(export_ctx, exp3);
        }
        ExpX::WithTriggers(trigs, exp) => {
            visit_trigs(export_ctx, trigs);
            visit_exp(export_ctx, exp);
        }
        ExpX::Bind(bnd, exp) => {
            visit_bnd(export_ctx, bnd);
            visit_exp(export_ctx, exp);
        }
        ExpX::ExecFnByName(fun) => {
            visit_fun(export_ctx, fun);
        }
        ExpX::ArrayLiteral(exps) => {
            visit_exps(export_ctx, exps);
        }
        _ => {}
    }
}

fn visit_exps(export_ctx: &mut ExportCtx, exps: &Exps) {
    for exp in exps.iter() {
        visit_exp(export_ctx, exp);
    }
}

fn visit_dest(export_ctx: &mut ExportCtx, dest: &Dest) {
    visit_exp(export_ctx, &dest.dest);
}

fn visit_stm(export_ctx: &mut ExportCtx, stm: &Stm) {
    match &stm.x {
        StmX::Call { fun, resolved_method, typ_args, args, dest, body, .. } => {
            if let CallTarget::Fun(f) = fun {
                visit_fun(export_ctx, f);
            }
            if let Some((resolved_fun, resolved_typs)) = resolved_method {
                visit_fun(export_ctx, resolved_fun);
                visit_typs(export_ctx, resolved_typs);
            }
            visit_typs(export_ctx, typ_args);
            visit_exps(export_ctx, args);
            if let Some(dest) = dest {
                visit_dest(export_ctx, dest);
            }
            if let Some(body) = body {
                visit_stm(export_ctx, body);
            }
        }
        StmX::Assert(_, _, exp) => {
            visit_exp(export_ctx, exp);
        }
        StmX::AssertBitVector { requires, ensures } => {
            visit_exps(export_ctx, requires);
            visit_exps(export_ctx, ensures);
        }
        StmX::AssertQuery { body, .. } => {
            visit_stm(export_ctx, body);
        }
        StmX::AssertCompute(_, exp, _) => {
            visit_exp(export_ctx, exp);
        }
        StmX::Assume(exp) => {
            visit_exp(export_ctx, exp);
        }
        StmX::Assign { lhs, rhs } => {
            visit_dest(export_ctx, lhs);
            visit_exp(export_ctx, rhs);
        }
        StmX::Fuel(fun, _) => {
            visit_fun(export_ctx, fun);
        }
        StmX::DeadEnd(stm) => {
            visit_stm(export_ctx, stm);
        }
        StmX::Return { ret_exp, .. } => {
            ret_exp.as_ref().map(|r| visit_exp(export_ctx, r));
        }
        StmX::If(exp, stm1, stm2) => {
            visit_exp(export_ctx, exp);
            visit_stm(export_ctx, stm1);
            if let Some(stm2) = stm2 {
                visit_stm(export_ctx, stm2);
            }
        }
        StmX::Loop { cond, body, invs, decrease, .. } => {
            if let Some((stm, exp)) = cond {
                visit_stm(export_ctx, stm);
                visit_exp(export_ctx, exp);
            }
            visit_stm(export_ctx, body);
            visit_loop_invs(export_ctx, invs);
            visit_exps(export_ctx, decrease);
        }
        StmX::OpenInvariant(stm) => {
            visit_stm(export_ctx, stm);
        }
        StmX::ClosureInner { body, .. } => {
            visit_stm(export_ctx, body);
        }
        StmX::Block(stms) => {
            visit_stms(export_ctx, stms);
        }
        _ => {}
    }
}

fn visit_stms(export_ctx: &mut ExportCtx, stms: &Stms) {
    for stm in stms.iter() {
        visit_stm(export_ctx, stm);
    }
}

fn visit_par(export_ctx: &mut ExportCtx, par: &Par) {
    let typ = &par.x.typ;
    visit_typ(export_ctx, typ);
}

fn visit_pars(export_ctx: &mut ExportCtx, pars: &Pars) {
    for par in pars.iter() {
        visit_par(export_ctx, par);
    }
}

fn visit_func_check(export_ctx: &mut ExportCtx, check: &FuncCheckSst) {
    visit_exps(export_ctx, &check.reqs);
    visit_exps(export_ctx, &check.post_condition.ens_exps);
    visit_stm(export_ctx, &check.body);
    for local in check.local_decls.iter() {
        visit_typ(export_ctx, &local.typ);
    }
    visit_stms(export_ctx, &check.local_decls_decreases_init);
}

fn visit_func_sst<'a>(export_ctx: &mut ExportCtx<'a>, sst: &'a FunctionSst) {
    let sst = &sst.x;
    let f = &sst.name;

    // Skip functions that have already been reached through another declaration.
    if export_ctx.fns.contains(f) {
        return;
    }

    export_ctx.fns.insert(f.clone());
    visit_pars(export_ctx, &sst.pars);
    visit_par(export_ctx, &sst.ret);
    visit_pars(export_ctx, &sst.decl.ens_pars);
    visit_exps(export_ctx, &sst.decl.reqs);
    visit_exps(export_ctx, &sst.decl.enss.0);
    visit_exps(export_ctx, &sst.decl.enss.1);

    match sst.mode {
        Mode::Spec => {
            if let Some(spec_axioms) = &sst.axioms.spec_axioms {
                if let Some(termination_check) = &spec_axioms.termination_check {
                    visit_func_check(export_ctx, termination_check);
                }
                visit_exp(export_ctx, &spec_axioms.body_exp);
            }
        }
        Mode::Proof | Mode::Exec => {
            if let Some(proof) = &sst.exec_proof_check {
                visit_func_check(export_ctx, proof);
            }
        }
    }
}

////////////////////////////////////////////////////////////////////////////////

fn collect_dt_deps_for_typ(deps: &mut HashSet<Dt>, typ: &Typ) {
    match &**typ {
        TypX::SpecFn(typs, typ) => {
            collect_dt_deps_for_typs(deps, typs);
            collect_dt_deps_for_typ(deps, typ);
        }
        TypX::AnonymousClosure(typs, typ, _, _) => {
            collect_dt_deps_for_typs(deps, typs);
            collect_dt_deps_for_typ(deps, typ);
        }
        TypX::FnDef(_, typs, _) => {
            // Only the type arguments affect datatype declaration ordering.
            collect_dt_deps_for_typs(deps, typs);
        }
        TypX::Datatype(dt, typs, _) => {
            if !matches!(dt, Dt::Tuple(_)) {
                deps.insert(dt.clone());
            }
            collect_dt_deps_for_typs(deps, typs);
        }
        TypX::Dyn(_, typs, _) | TypX::Primitive(_, typs) => {
            collect_dt_deps_for_typs(deps, typs);
        }
        TypX::Opaque { args, .. } => {
            collect_dt_deps_for_typs(deps, args);
        }
        TypX::Decorate(_, decoration_arg, typ) => {
            if let Some(decoration_arg) = decoration_arg {
                collect_dt_deps_for_typ(deps, &decoration_arg.allocator_typ);
            }
            collect_dt_deps_for_typ(deps, typ);
        }
        TypX::Boxed(typ) | TypX::PointeeMetadata(typ) | TypX::MutRef(typ) => {
            collect_dt_deps_for_typ(deps, typ);
        }
        TypX::Projection { trait_typ_args, .. } => {
            collect_dt_deps_for_typs(deps, trait_typ_args);
        }
        _ => {}
    }
}

fn collect_dt_deps_for_typs(deps: &mut HashSet<Dt>, typs: &Typs) {
    for typ in typs.iter() {
        collect_dt_deps_for_typ(deps, typ);
    }
}

fn compute_dt_deps(export_ctx: &ExportCtx, graph: &mut Graph<Dt>, dt: &Dt) -> Result<(), VirErr> {
    let datatype = registered_datatype(export_ctx.ctx, dt)?;
    let mut deps = HashSet::new();
    let DatatypeX { variants, .. } = &datatype.x;
    for variant in variants.iter() {
        let Variant { fields, .. } = variant;
        for field in fields.iter() {
            collect_dt_deps_for_typ(&mut deps, &field.a.0);
        }
    }
    deps.remove(dt);
    let mut deps = deps.into_iter().collect::<Vec<_>>();
    deps.sort();
    for dep in deps {
        graph.add_edge(dt.clone(), dep);
    }
    Ok(())
}

fn compute_all_dt_deps(export_ctx: &ExportCtx, graph: &mut Graph<Dt>) -> Result<(), VirErr> {
    for dt in export_ctx.dts.iter() {
        compute_dt_deps(export_ctx, graph, dt)?;
    }
    Ok(())
}

type JsonResult = Result<serde_json::Value, VirErr>;

fn json_value<T: serde::Serialize>(field_name: &str, value: &T) -> JsonResult {
    serde_json::to_value(value).map_err(|err| {
        error_bare(format!("failed to serialize SST JSON field `{field_name}`: {err}"))
    })
}

fn json_values<T>(values: &[T], f: impl Fn(&T) -> JsonResult) -> JsonResult {
    values.iter().map(f).collect::<Result<Vec<_>, _>>().map(serde_json::Value::Array)
}

fn json_exps(exps: &Exps) -> JsonResult {
    json_values(exps, json_exp)
}

fn json_stms(stms: &Stms) -> JsonResult {
    json_values(stms, json_stm)
}

fn json_trigs(trigs: &crate::sst::Trigs) -> JsonResult {
    json_values(trigs, json_exps)
}

fn json_exp_binders(binders: &VarBinders<Exp>) -> JsonResult {
    json_values(binders, |binder| {
        Ok(serde_json::json!({
            "name": json_value("expression binder name", &binder.name)?,
            "a": json_exp(&binder.a)?,
        }))
    })
}

fn json_bnd(bnd: &Bnd) -> JsonResult {
    let x = match &bnd.x {
        BndX::Let(binders) => serde_json::json!({ "Let": json_exp_binders(binders)? }),
        BndX::Quant(quant, binders, trigs, _) => serde_json::json!({
            "Quant": [
                json_value("quantifier", quant)?,
                json_value("quantifier binders", binders)?,
                json_trigs(trigs)?,
                serde_json::Value::Null,
            ]
        }),
        BndX::Lambda(binders, trigs) => serde_json::json!({
            "Lambda": [json_value("lambda binders", binders)?, json_trigs(trigs)?]
        }),
        BndX::Choose(binders, trigs, exp) => serde_json::json!({
            "Choose": [
                json_value("choose binders", binders)?,
                json_trigs(trigs)?,
                json_exp(exp)?,
            ]
        }),
    };
    Ok(serde_json::json!({ "x": x }))
}

fn json_internal_fun(fun: &InternalFun) -> JsonResult {
    Ok(match fun {
        InternalFun::ClosureReq => serde_json::json!("ClosureReq"),
        InternalFun::ClosureEns => serde_json::json!("ClosureEns"),
        InternalFun::DefaultEns => serde_json::json!("DefaultEns"),
        InternalFun::CheckDecreaseHeight => serde_json::json!("CheckDecreaseHeight"),
        InternalFun::OpenInvariantMask(fun, index) => serde_json::json!({
            "OpenInvariantMask": [json_value("internal function", fun)?, index]
        }),
    })
}

fn json_call_fun(fun: &CallFun) -> JsonResult {
    Ok(match fun {
        CallFun::Fun(fun, resolved) => serde_json::json!({
            "Fun": [json_value("function", fun)?, json_value("resolved function", resolved)?]
        }),
        CallFun::Recursive(fun) => {
            serde_json::json!({ "Recursive": json_value("recursive function", fun)? })
        }
        CallFun::InternalFun(fun) => {
            serde_json::json!({ "InternalFun": json_internal_fun(fun)? })
        }
    })
}

fn json_arith_op(op: &SstArithOp) -> &'static str {
    match op {
        SstArithOp::Add => "Add",
        SstArithOp::Sub => "Sub",
        SstArithOp::Mul => "Mul",
        SstArithOp::EuclideanDiv => "EuclideanDiv",
        SstArithOp::EuclideanMod => "EuclideanMod",
    }
}

fn json_binary_op(op: &SstBinaryOp) -> JsonResult {
    Ok(match op {
        SstBinaryOp::And => serde_json::json!("And"),
        SstBinaryOp::Or => serde_json::json!("Or"),
        SstBinaryOp::Xor => serde_json::json!("Xor"),
        SstBinaryOp::Implies => serde_json::json!("Implies"),
        SstBinaryOp::HeightCompare { strictly_lt, recursive_function_field } => {
            serde_json::json!({
                "HeightCompare": {
                    "strictly_lt": strictly_lt,
                    "recursive_function_field": recursive_function_field,
                }
            })
        }
        SstBinaryOp::Eq => serde_json::json!("Eq"),
        SstBinaryOp::Ne => serde_json::json!("Ne"),
        SstBinaryOp::Inequality(op) => {
            serde_json::json!({ "Inequality": json_value("inequality operator", op)? })
        }
        SstBinaryOp::Arith(op) => serde_json::json!({ "Arith": json_arith_op(op) }),
        SstBinaryOp::RealArith(op) => {
            serde_json::json!({ "RealArith": json_value("real arithmetic operator", op)? })
        }
        SstBinaryOp::Bitwise(op) => {
            serde_json::json!({ "Bitwise": json_value("bitwise operator", op)? })
        }
        SstBinaryOp::IeeeFloat(op) => {
            serde_json::json!({ "IeeeFloat": json_value("IEEE float operator", op)? })
        }
        SstBinaryOp::StrGetChar => serde_json::json!("StrGetChar"),
        SstBinaryOp::Index(kind) => {
            serde_json::json!({ "Index": json_value("array kind", kind)? })
        }
    })
}

fn json_exp(exp: &Exp) -> JsonResult {
    let x = match &exp.x {
        ExpX::Const(value) => serde_json::json!({ "Const": json_value("constant", value)? }),
        ExpX::Var(var) => serde_json::json!({ "Var": json_value("variable", var)? }),
        ExpX::StaticVar(fun) => {
            serde_json::json!({ "StaticVar": json_value("static variable", fun)? })
        }
        ExpX::VarLoc(var) => serde_json::json!({ "VarLoc": json_value("variable", var)? }),
        ExpX::VarAt(var, at) => serde_json::json!({
            "VarAt": [json_value("variable", var)?, json_value("variable snapshot", at)?]
        }),
        ExpX::Loc(inner) => serde_json::json!({ "Loc": json_exp(inner)? }),
        ExpX::Old(_, _) => {
            return Err(error_bare("SST JSON does not support internal `Old` expressions"));
        }
        ExpX::Call(fun, typs, args) => serde_json::json!({
            "Call": [json_call_fun(fun)?, json_value("call type arguments", typs)?, json_exps(args)?]
        }),
        ExpX::CallLambda(fun, args) => {
            serde_json::json!({ "CallLambda": [json_exp(fun)?, json_exps(args)?] })
        }
        ExpX::Ctor(dt, variant, fields) => serde_json::json!({
            "Ctor": [
                json_value("constructor datatype", dt)?,
                variant,
                json_values(fields, |field| Ok(serde_json::json!({
                    "name": field.name,
                    "a": json_exp(&field.a)?,
                })))?,
            ]
        }),
        ExpX::NullaryOpr(op) => {
            serde_json::json!({ "NullaryOpr": json_value("nullary operator", op)? })
        }
        ExpX::Unary(op, inner) => serde_json::json!({
            "Unary": [json_value("unary operator", op)?, json_exp(inner)?]
        }),
        ExpX::UnaryOpr(op, inner) => serde_json::json!({
            "UnaryOpr": [json_value("unary operator", op)?, json_exp(inner)?]
        }),
        ExpX::Binary(op, lhs, rhs) => serde_json::json!({
            "Binary": [json_binary_op(op)?, json_exp(lhs)?, json_exp(rhs)?]
        }),
        ExpX::BinaryOpr(op, lhs, rhs) => serde_json::json!({
            "BinaryOpr": [json_value("binary operator", op)?, json_exp(lhs)?, json_exp(rhs)?]
        }),
        ExpX::If(cond, then_exp, else_exp) => serde_json::json!({
            "If": [json_exp(cond)?, json_exp(then_exp)?, json_exp(else_exp)?]
        }),
        ExpX::WithTriggers(trigs, inner) => {
            serde_json::json!({ "WithTriggers": [json_trigs(trigs)?, json_exp(inner)?] })
        }
        ExpX::Bind(bnd, body) => {
            serde_json::json!({ "Bind": [json_bnd(bnd)?, json_exp(body)?] })
        }
        ExpX::ExecFnByName(fun) => {
            serde_json::json!({ "ExecFnByName": json_value("exec function", fun)? })
        }
        ExpX::ArrayLiteral(values) => {
            serde_json::json!({ "ArrayLiteral": json_exps(values)? })
        }
        ExpX::Interp(_) => {
            return Err(error_bare("SST JSON does not support interpreter expressions"));
        }
        ExpX::FuelConst(_) => {
            return Err(error_bare("SST JSON does not support internal fuel constants"));
        }
    };
    Ok(serde_json::json!({
        "typ": json_value("expression type", &exp.typ)?,
        "x": x,
    }))
}

fn json_dest(dest: &Dest) -> JsonResult {
    Ok(serde_json::json!({ "dest": json_exp(&dest.dest)?, "is_init": dest.is_init }))
}

fn json_loop_inv(inv: &LoopInv) -> JsonResult {
    Ok(serde_json::json!({
        "at_entry": inv.at_entry,
        "at_exit": inv.at_exit,
        "inv": json_exp(&inv.inv)?,
    }))
}

fn json_call_target(target: &CallTarget) -> JsonResult {
    Ok(match target {
        CallTarget::Fun(fun) => serde_json::json!({ "Fun": json_value("function", fun)? }),
        CallTarget::AssumeExternal => serde_json::json!("AssumeExternal"),
    })
}

fn json_stm(stm: &Stm) -> JsonResult {
    let x = match &stm.x {
        StmX::Call { fun, resolved_method, typ_args, args, dest, body, .. } => serde_json::json!({
            "Call": {
                "fun": json_call_target(fun)?,
                "resolved_method": json_value("resolved method", resolved_method)?,
                "typ_args": json_value("call type arguments", typ_args)?,
                "args": json_exps(args)?,
                "dest": match dest { Some(dest) => json_dest(dest)?, None => serde_json::Value::Null },
                "body": match body { Some(body) => json_stm(body)?, None => serde_json::Value::Null },
            }
        }),
        StmX::Assert(_, _, exp) => {
            serde_json::json!({ "Assert": [serde_json::Value::Null, serde_json::Value::Null, json_exp(exp)?] })
        }
        StmX::AssertBitVector { requires, ensures } => serde_json::json!({
            "AssertBitVector": { "requires": json_exps(requires)?, "ensures": json_exps(ensures)? }
        }),
        StmX::AssertQuery { mode, body, .. } => serde_json::json!({
            "AssertQuery": { "mode": json_value("assert-query mode", mode)?, "body": json_stm(body)? }
        }),
        StmX::AssertCompute(_, exp, _) => {
            serde_json::json!({ "AssertCompute": json_exp(exp)? })
        }
        StmX::Assume(exp) => serde_json::json!({ "Assume": json_exp(exp)? }),
        StmX::Assign { lhs, rhs } => serde_json::json!({
            "Assign": { "lhs": json_dest(lhs)?, "rhs": json_exp(rhs)? }
        }),
        StmX::Fuel(fun, amount) => {
            serde_json::json!({ "Fuel": [json_value("fuel function", fun)?, amount] })
        }
        StmX::RevealString(value) => serde_json::json!({ "RevealString": value }),
        StmX::RevealByteString(value) => serde_json::json!({ "RevealByteString": value }),
        StmX::DeadEnd(body) => serde_json::json!({ "DeadEnd": json_stm(body)? }),
        StmX::Return { ret_exp, .. } => serde_json::json!({
            "Return": match ret_exp {
                Some(exp) => serde_json::json!({ "ret_exp": json_exp(exp)? }),
                None => serde_json::json!({}),
            }
        }),
        StmX::BreakOrContinue { label, is_break } => serde_json::json!({
            "BreakOrContinue": { "label": label, "is_break": is_break }
        }),
        StmX::If(cond, then_stm, else_stm) => serde_json::json!({
            "If": [
                json_exp(cond)?,
                json_stm(then_stm)?,
                match else_stm { Some(stm) => json_stm(stm)?, None => serde_json::Value::Null },
            ]
        }),
        StmX::Loop { is_for_loop, label, cond, body, invs, decrease, au_branch_bool, .. } => {
            if au_branch_bool.is_some() {
                return Err(error_bare(
                    "SST JSON does not support logical-atomicity loops".to_string(),
                ));
            }
            serde_json::json!({
                "Loop": {
                    "is_for_loop": is_for_loop,
                    "label": label,
                    "cond": match cond {
                        Some((stm, exp)) => serde_json::json!([json_stm(stm)?, json_exp(exp)?]),
                        None => serde_json::Value::Null,
                    },
                    "body": json_stm(body)?,
                    "invs": json_values(invs, json_loop_inv)?,
                    "decrease": json_exps(decrease)?,
                }
            })
        }
        StmX::OpenInvariant(body) => serde_json::json!({ "OpenInvariant": json_stm(body)? }),
        StmX::ClosureInner { body, .. } => {
            serde_json::json!({ "ClosureInner": { "body": json_stm(body)? } })
        }
        StmX::Air(value) => serde_json::json!({ "Air": value }),
        StmX::Block(stms) => serde_json::json!({ "Block": json_stms(stms)? }),
    };
    Ok(serde_json::json!({ "x": x }))
}

/// Serialize the current module's SST declarations to a versioned JSON file.
pub fn serialize_crate_to_json(
    ctx: &Ctx,
    krate: &KrateSst,
    output_dir: &FsPath,
    output_file_stem: &str,
) -> Result<PathBuf, VirErr> {
    let mut export_ctx = ExportCtx {
        ctx,
        typs: Vec::new(),
        dts: HashSet::new(),
        missing_dts: HashSet::new(),
        fns: HashSet::new(),
    };

    let module = ctx.module_path();
    for sst in krate.functions.iter() {
        let fun_path = &sst.x.name.path;
        if in_module_or_submodule(&sst.x.owning_module, Some(fun_path), &module) {
            visit_func_sst(&mut export_ctx, sst);
        }
    }
    for datatype in krate.datatypes.iter() {
        let name_path = match &datatype.x.name {
            Dt::Path(path) => Some(path),
            Dt::Tuple(..) => None,
        };
        if in_module_or_submodule(&datatype.x.owning_module, name_path, &module) {
            visit_dt(&mut export_ctx, &datatype.x.name);
        }
    }

    if !export_ctx.missing_dts.is_empty() {
        let mut missing = export_ctx.missing_dts.iter().cloned().collect::<Vec<_>>();
        missing.sort();
        let names = missing.iter().map(|dt| format!("{dt:?}")).collect::<Vec<_>>().join(", ");
        return Err(error_bare(format!(
            "SST JSON export: missing declarations for referenced datatypes: {names}"
        )));
    }

    // Declarations are stored in the top-level envelope's `decls` array.
    let mut decls: Vec<serde_json::Value> = Vec::new();

    // Take the values in the `dts` and sort them topologically
    let mut datatype_graph = Graph::new();
    let mut datatypes: Vec<Dt> = export_ctx.dts.iter().cloned().collect();
    datatypes.sort();
    for dt in datatypes {
        datatype_graph.add_node(dt);
    }

    compute_all_dt_deps(&export_ctx, &mut datatype_graph)?;
    datatype_graph.compute_sccs();

    // Loop through the datatype connected components and serialize them as they come
    let representatives = datatype_graph.sort_sccs();
    for rep in representatives.iter() {
        let scc = datatype_graph.get_scc_nodes(rep);
        if let [dt] = scc.as_slice() {
            // If the SCC has only one node, we serialize it as a single datatype
            decls.push(serialize_dt(ctx, dt)?);
        } else if scc.len() > 1 {
            // If the SCC has more than one node, we serialize it as a mutual block
            let mut dts: Vec<serde_json::Value> = Vec::new();
            for dt in scc.iter() {
                dts.push(serialize_dt(ctx, dt)?);
            }
            decls.push(serialize_mut_block(dts));
        }
    }

    // Loop through the function connected components, serializing in dependency order.
    for representative in ctx.global.func_call_sccs.iter() {
        let nodes = ctx.global.func_call_graph.get_scc_nodes(representative);
        let reachable_funs = nodes
            .iter()
            .filter_map(|node| match node {
                Node::Fun(fun) if export_ctx.fns.contains(fun) => Some(fun),
                _ => None,
            })
            .collect::<Vec<_>>();
        match reachable_funs.as_slice() {
            [] => {}
            [fun] => decls.push(serialize_fn(ctx, fun)?),
            funs => {
                let funs =
                    funs.iter().map(|fun| serialize_fn(ctx, fun)).collect::<Result<Vec<_>, _>>()?;
                decls.push(serialize_mut_block(funs));
            }
        }
    }

    let krate_name = crate_id_to_name(&ctx.global.crate_name)?;
    let path = output_dir.join(format!("{output_file_stem}.json"));

    let json = serde_json::json! {
        {
            "format": SST_JSON_FORMAT,
            "format_version": SST_JSON_FORMAT_VERSION,
            "krate": krate_name,
            "decls": decls,
        }
    };

    let mut bytes = serde_json::to_vec(&json).map_err(|err| {
        error_bare(format!("failed to serialize SST JSON file `{}`: {err}", path.display()))
    })?;
    bytes.push(b'\n');

    let mut file = std::fs::File::create(&path).map_err(|err| {
        error_bare(format!("failed to create SST JSON file `{}`: {err}", path.display()))
    })?;
    file.write_all(&bytes).map_err(|err| {
        error_bare(format!("failed to write SST JSON file `{}`: {err}", path.display()))
    })?;

    Ok(path)
}

// Each declaration is tagged with `DeclType`; its serialized SST value is in `x`.

const DECL_TYPE: &str = "DeclType";
const DECL_VAL: &str = "x";
const DATATYPE_DECL: &str = "Datatype";
const SPEC_FUN_DECL: &str = "SpecFn";
const PROOF_FUN_DECL: &str = "ProofFn";
const EXEC_FUN_DECL: &str = "ExecFn";

fn json_dt_type(dt_type: &DtType) -> &'static str {
    match dt_type {
        DtType::Struct => "Struct",
        DtType::Enum => "Enum",
        DtType::Union => "Union",
        DtType::Tuple => "Tuple",
        DtType::Closure => "Closure",
        DtType::External => "External",
    }
}

fn crate_id_to_name(krate: &CrateId) -> Result<String, VirErr> {
    match krate {
        // The current crate ID comes from `mk_crate_id(LOCAL_CRATE)`, which is never `Internal`.
        CrateId::Internal => Err(error_bare(
            "SST JSON export: current crate has no external crate identity".to_string(),
        )),
        CrateId::Core => Ok("core".to_string()),
        CrateId::Alloc => Ok("alloc".to_string()),
        CrateId::Vstd => Ok("vstd".to_string()),
        CrateId::Id(name, _) => Ok(name.to_string()),
    }
}

fn registered_datatype<'a>(ctx: &'a Ctx, dt: &Dt) -> Result<&'a Datatype, VirErr> {
    ctx.datatype_map
        .get(dt)
        .ok_or_else(|| error_bare(format!("SST JSON export: unknown datatype `{dt:?}`")))
}

fn serialize_dt(ctx: &Ctx, dt: &Dt) -> JsonResult {
    let datatype = &registered_datatype(ctx, dt)?.x;
    let variants = json_values(&datatype.variants, |variant| {
        Ok(serde_json::json!({
            "name": variant.name,
            "fields": json_values(&variant.fields, |field| {
                Ok(serde_json::json!({
                    "name": field.name,
                    "typ": json_value("datatype field type", &field.a.0)?,
                }))
            })?,
        }))
    })?;
    let typ_params = datatype
        .typ_params
        .iter()
        .map(|(name, _)| serde_json::Value::String(name.to_string()))
        .collect::<Vec<_>>();
    Ok(serde_json::json! {
        {
            DECL_TYPE: DATATYPE_DECL,
            DECL_VAL: {
                "name": json_value("datatype name", &datatype.name)?,
                "dt_type": json_dt_type(&datatype.dt_type),
                "typ_params": typ_params,
                "variants": variants,
            },
        }
    })
}

fn json_par_purpose(purpose: ParPurpose) -> &'static str {
    match purpose {
        ParPurpose::MutPre => "MutPre",
        ParPurpose::MutPost => "MutPost",
        ParPurpose::Regular => "Regular",
    }
}

fn json_par(par: &Par) -> JsonResult {
    Ok(serde_json::json!({
        "x": {
            "name": json_value("parameter name", &par.x.name)?,
            "typ": json_value("parameter type", &par.x.typ)?,
            "purpose": json_par_purpose(par.x.purpose),
        }
    }))
}

fn json_pars(pars: &Pars) -> JsonResult {
    json_values(pars, json_par)
}

fn json_local_decl_kind(kind: LocalDeclKind) -> serde_json::Value {
    match kind {
        LocalDeclKind::Param { mutable } => serde_json::json!({ "Param": { "mutable": mutable } }),
        LocalDeclKind::Return => serde_json::json!("Return"),
        LocalDeclKind::StmtLet { mutable } => {
            serde_json::json!({ "StmtLet": { "mutable": mutable } })
        }
        LocalDeclKind::TempViaAssign => serde_json::json!("TempViaAssign"),
        LocalDeclKind::Decreases => serde_json::json!("Decreases"),
        LocalDeclKind::StmCallArg { native } => {
            serde_json::json!({ "StmCallArg": { "native": native } })
        }
        LocalDeclKind::Assert => serde_json::json!("Assert"),
        LocalDeclKind::AssertByVar { native } => {
            serde_json::json!({ "AssertByVar": { "native": native } })
        }
        LocalDeclKind::LetBinder => serde_json::json!("LetBinder"),
        LocalDeclKind::QuantBinder => serde_json::json!("QuantBinder"),
        LocalDeclKind::ChooseBinder => serde_json::json!("ChooseBinder"),
        LocalDeclKind::ClosureBinder => serde_json::json!("ClosureBinder"),
        LocalDeclKind::ExecClosureId => serde_json::json!("ExecClosureId"),
        LocalDeclKind::ExecClosureParam { mutable } => {
            serde_json::json!({ "ExecClosureParam": { "mutable": mutable } })
        }
        LocalDeclKind::ExecClosureRet => serde_json::json!("ExecClosureRet"),
        LocalDeclKind::Nondeterministic => serde_json::json!("Nondeterministic"),
        LocalDeclKind::OpenInvariantInnerTemp => serde_json::json!("OpenInvariantInnerTemp"),
        LocalDeclKind::BorrowMut => serde_json::json!("BorrowMut"),
    }
}

fn json_func_check(check: &FuncCheckSst) -> JsonResult {
    Ok(serde_json::json!({
        "reqs": json_exps(&check.reqs)?,
        "post_condition": {
            "ens_exps": json_exps(&check.post_condition.ens_exps)?,
        },
        "body": json_stm(&check.body)?,
        "local_decls": json_values(&check.local_decls, |local| {
            Ok(serde_json::json!({
                "ident": json_value("local name", &local.ident)?,
                "typ": json_value("local type", &local.typ)?,
                "kind": json_local_decl_kind(local.kind),
            }))
        })?,
        "local_decls_decreases_init": json_stms(&check.local_decls_decreases_init)?,
    }))
}

fn serialize_fn(ctx: &Ctx, fun: &Fun) -> JsonResult {
    let sst = ctx.func_sst_map.get(fun).ok_or_else(|| {
        error_bare(format!("SST JSON export: missing SST declaration for function `{fun:?}`"))
    })?;
    let sst = &sst.x;

    let fun_type = match sst.mode {
        Mode::Spec => SPEC_FUN_DECL,
        Mode::Proof => PROOF_FUN_DECL,
        Mode::Exec => EXEC_FUN_DECL,
    };

    let spec_axioms = match &sst.axioms.spec_axioms {
        None => serde_json::Value::Null,
        Some(axioms) => serde_json::json!({
            "body_exp": json_exp(&axioms.body_exp)?,
            "termination_check": match &axioms.termination_check {
                Some(check) => json_func_check(check)?,
                None => serde_json::Value::Null,
            },
        }),
    };
    let exec_proof_check = match &sst.exec_proof_check {
        Some(check) => json_func_check(check)?,
        None => serde_json::Value::Null,
    };

    Ok(serde_json::json! {
        {
            DECL_TYPE: fun_type,
            DECL_VAL: {
                "name": json_value("function name", &sst.name)?,
                "kind": json_value("function kind", &sst.kind)?,
                "opaqueness": json_value("function opaqueness", &sst.opaqueness)?,
                "typ_params": json_value("function type parameters", &sst.typ_params)?,
                "pars": json_pars(&sst.pars)?,
                "ret": json_par(&sst.ret)?,
                "has": { "is_recursive": sst.has.is_recursive },
                "decl": {
                    "ens_pars": json_pars(&sst.decl.ens_pars)?,
                    "reqs": json_exps(&sst.decl.reqs)?,
                    "enss": [json_exps(&sst.decl.enss.0)?, json_exps(&sst.decl.enss.1)?],
                },
                "axioms": { "spec_axioms": spec_axioms },
                "exec_proof_check": exec_proof_check,
            },
        }
    })
}

fn serialize_mut_block(funs: Vec<serde_json::Value>) -> serde_json::Value {
    serde_json::json! {
        {
            DECL_TYPE: "Mutual",
            DECL_VAL: funs,
        }
    }
}
