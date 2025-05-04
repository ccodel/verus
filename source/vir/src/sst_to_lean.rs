use crate::context::Ctx;
use crate::ast::{
    Typ, TypX, Typs, Datatype, DatatypeX, Dt, Fun, LeanMode, NullaryOpr, PathX, Mode, Variant, VarBinder, VarBinders,
};
use crate::ast_util::types_equal;
use crate::sst::{
    Bnd, BndX, Dest, Exp, Exps, ExpX, LoopInv, LoopInvs, Par, Pars, Stm, Stms, StmX, CallFun, KrateSst, FunctionSst,
};
use crate::scc::Graph;
use crate::recursion::Node;

use std::collections::{HashMap, HashSet};

// For the global variable LEAN_SERIALIZING_THREADS
use lazy_static::lazy_static;
use std::sync::{Arc, RwLock};
use std::thread::ThreadId;

// For printing and file I/O
use std::io::Write;

////////////////////////////////////////////////////////////////////////////////

/// A Lean context.
/// 
/// Contains a `Ctx`, and `HashSet`s of already-processed
/// functions (both spec and proof) and datatypes.
/// These hash sets ensure that we don't visit the same objects twice,
/// while also logging which objects are needed in the Lean serialization.
struct LeanCtx<'a> {
    ctx: &'a Ctx,
    current_fun: Option<Fun>,
    found_by_lean: bool,
    total_by_lean: u32,
    // Mark down which definitions we've seen already
    typs: Vec<Typ>, // CC: Replace with manual hash set/map later?
    dts: HashSet<Dt>,
    fns: HashSet<Fun>,
    asserts_to_serialize: Vec<(&'a Exp, Fun)>,
}

fn start_by_lean(lctx: &mut LeanCtx) {
    lctx.found_by_lean = true;
    lctx.total_by_lean += 1;
}

fn stop_by_lean(lctx: &mut LeanCtx) {
    lctx.found_by_lean = false;
}

fn is_by_lean_active(lctx: &LeanCtx) -> bool {
    lctx.found_by_lean
}

// TODO: Don't clone, work with lifetimes to say that `LeanCtx` and `Exp` come from the same place
fn add_by_lean_assertion<'lctx>(lctx: &mut LeanCtx<'lctx>, exp: &'lctx Exp) {
    lctx.asserts_to_serialize.push((exp, lctx.current_fun.clone().unwrap()));
}

/*
    Global hash set storing the thread IDs of threads doing Lean serialization.
    Added to by `this_thread_start_skipping_nonlean_fields()`,
    and removed from by `this_thread_stop_skipping_nonlean_fields()`.

    In general, we use the default `serde_json::to_value` serialization
    for our Lean serialization. However, the `Span`, `Spanned`, and `SpannedTyped`
    objects include a `RawSpan` object that contains important disambiguation
    data for Verus, but which Lean isn't (currently) using.

    To minimize the resulting size of the JSONs, we use Serde's
    `skip_serializing_if` attribute to check if the thread is currently
    serializing Lean JSONs. If so, those fields will be skipped.

    While Rust really, *really* discourages programmers using global state,
    the only way to accomplish this in a state-dependent way (and not through
    compile-time options or field-dependent options) is to use global state.
    Hence this solution.
*/
lazy_static! {
    static ref LEAN_SERIALIZING_THREADS: Arc<RwLock<HashSet<ThreadId>>> = {
        let hs: HashSet<ThreadId> = HashSet::new();
        let lock = RwLock::new(hs);
        Arc::new(lock)
    };
}

/// Called by `serde` `skip_serializing_if` attribute on the enum or struct itself.
/// See `SpannedTyped` and `Spanned` in `vir/src/ast.rs` and `vir/src/def.rs`.
pub fn should_skip_lean_fields<T>(_: &T) -> bool {
    let tid = std::thread::current().id();
    let hs = &LEAN_SERIALIZING_THREADS.read().unwrap();
    hs.contains(&tid)
    // Read-lock automatically dropped when function returns
}

fn this_thread_start_skipping_nonlean_fields() {
    let tid = std::thread::current().id();
    let mut hs = LEAN_SERIALIZING_THREADS.write().unwrap();
    hs.insert(tid);
    // Write-lock automatically dropped when function returns
}

fn this_thread_stop_skipping_nonlean_fields() {
    let tid = std::thread::current().id();
    let mut hs = LEAN_SERIALIZING_THREADS.write().unwrap();
    hs.remove(&tid);
    // Write-lock automatically dropped when function returns
}

////////////////////////////////////////////////////////////////////////////////

// CC TODO: This should probably be a trait like this.
// so that eg Spanned, SpannedTyped, Binder, VarBinder, etc. can be polymorphically implemented
// trait LeanVisitor {
//     fn lvisit(lctx: &mut LeanCtx, x: &Self);
// }

fn lvisit_datatype(lctx: &mut LeanCtx, datatype: &Datatype) {
    if !is_by_lean_active(lctx) { return; }

    let DatatypeX { variants, .. } = &datatype.x;
    for variant in variants.iter() {
        let Variant { fields, .. } = variant;
        for field in fields.iter() {
            let typ = &field.a.0;
            lvisit_typ(lctx, typ);
        }
    }
}

fn lvisit_dt(lctx: &mut LeanCtx, dt: &Dt) {
    if !is_by_lean_active(lctx) { return; }

    // Only process this datatype if we haven't seen it before
    if lctx.dts.contains(dt) { return; }
    lctx.dts.insert(dt.clone());

    // See if that datatype depends on other types
    let datatype = lctx.ctx.datatype_map.get(dt).unwrap();
    lvisit_datatype(lctx, datatype);
}

fn lvisit_typ(lctx: &mut LeanCtx, typ: &Typ) {
    if !is_by_lean_active(lctx) { return; }

    // Note: Because `TypX` cannot implement the traits `Eq` or `PartialEq`
    //       (see the note in vir/src/ast.rs), we cannot use a `HashSet`
    //       to prevent duplicate type visits. Oh well.
    // Instead, we use a list of types
    for typ2 in lctx.typs.iter() {
        if types_equal(typ, typ2) { return; }
    }
    lctx.typs.push(typ.clone());

    // CC: TODO implement the FnDef branch, because traits are somewhat like Lean type classes
    match &**typ {
        TypX::SpecFn(typs, typ) => {
            lvisit_typs(lctx, typs);
            lvisit_typ(lctx, typ);
        }
        TypX::AnonymousClosure(typs, typ, _) => {
            lvisit_typs(lctx, typs);
            lvisit_typ(lctx, typ);
        }
        TypX::Datatype(dt, typs, _) => {
            lvisit_dt(lctx, dt);
            lvisit_typs(lctx, typs);
        }
        TypX::Primitive(_, typs) => { lvisit_typs(lctx, typs); }
        TypX::Decorate(_, _, typ) => { lvisit_typ(lctx, typ); }
        TypX::Boxed(typ) => { lvisit_typ(lctx, typ); }
        TypX::Projection { trait_typ_args, .. } => {
            // Skip the 0th type because it is the same as the given `typ`
            // See the comment for `Projection` in `TypX` in `vir/src/ast.rs`
            for typ in trait_typ_args.iter().skip(1) {
                lvisit_typ(lctx, typ);
            }
        }
        _ => {}
    }
}

fn lvisit_typs(lctx: &mut LeanCtx, typs: &Typs) {
    if !is_by_lean_active(lctx) { return; }

    for typ in typs.iter() {
        lvisit_typ(lctx, &typ);
    }
}

// CC: This should really be a trait
fn lvisit_varbinder_typ(lctx: &mut LeanCtx, binder: &VarBinder<Typ>) {
    lvisit_typ(lctx, &binder.a);
}

fn lvisit_varbinder_exp(lctx: &mut LeanCtx, binder: &VarBinder<Exp>) {
    lvisit_exp(lctx, &binder.a);
}

fn lvisit_varbinders_typ(lctx: &mut LeanCtx, binders: &VarBinders<Typ>) {
    for binder in binders.iter() {
        lvisit_varbinder_typ(lctx, binder);
    }
}

fn lvisit_varbinders_exp(lctx: &mut LeanCtx, binders: &VarBinders<Exp>) {
    for binder in binders.iter() {
        lvisit_varbinder_exp(lctx, binder);
    }
}

fn lvisit_bnd(lctx: &mut LeanCtx, bnd: &Bnd) {
    if !is_by_lean_active(lctx) { return; }

    match &bnd.x {
        BndX::Let(binders) => {
            lvisit_varbinders_exp(lctx, binders);
        }
        BndX::Quant(_, typ_binders, _, _) => {
            lvisit_varbinders_typ(lctx, typ_binders);
        }
        BndX::Lambda(typ_binders, _) => {
            lvisit_varbinders_typ(lctx, typ_binders);
        }
        BndX::Choose(typ_binders, _, exp) => {
            lvisit_varbinders_typ(lctx, typ_binders);
            lvisit_exp(lctx, exp)
        }
    }
}

fn lvisit_loop_inv(lctx: &mut LeanCtx, inv: &LoopInv) {
    lvisit_exp(lctx, &inv.inv);
}

fn lvisit_loop_invs(lctx: &mut LeanCtx, invs: &LoopInvs) {
    for inv in invs.iter() {
        lvisit_loop_inv(lctx, inv);
    }
}

fn lvisit_fun(lctx: &mut LeanCtx, fun: &Fun) {
    if !is_by_lean_active(lctx) { return; }
    if lctx.fns.contains(fun) { return; }

    // TODO are there any problems with one polymorphic function but multiple instantiations?
    let sst= lctx.ctx.func_sst_map.get(fun).unwrap();
    lvisit_func_sst(lctx, sst);
}

fn lvisit_call_fun(lctx: &mut LeanCtx, call_fun: &CallFun) {
    match call_fun {
        CallFun::Fun(fun, _) => {
            lvisit_fun(lctx, fun);
            // TODO implement the optional resolved typs here?
        }
        CallFun::Recursive(fun) => {
            lvisit_fun(lctx, fun);
        }
        _ => {}
    }
}

fn lvisit_nullary_opr(lctx: &mut LeanCtx, op: &NullaryOpr) {
    match op {
        // TODO: Visit traits? (Add them as type-classes later)
        NullaryOpr::ConstGeneric(typ) => {
            lvisit_typ(lctx, typ);
        }
        NullaryOpr::TraitBound(_, typs) => {
            lvisit_typs(lctx, typs);
        }
        NullaryOpr::TypEqualityBound(_, typs, _, typ) => {
            lvisit_typs(lctx, typs);
            lvisit_typ(lctx, typ);
        }
        NullaryOpr::ConstTypBound(typ1, typ2) => {
            lvisit_typ(lctx, typ1);
            lvisit_typ(lctx, typ2);
        }
        _ => {}
    }
}

fn lvisit_exp(lctx: &mut LeanCtx, exp: &Exp) {
    if !is_by_lean_active(lctx) { return; }

    // To ensure we don't miss any types, we visit the type of *every* expression
    // However, we keep around a list of unique types, so while these calls are
    // redundant, we don't end up doing too much extra work
    lvisit_typ(lctx, &exp.typ);

    match &exp.x {
        // Skip ExpX::Const     (no new context to visit)
        // Skip ExpX::Var       (no new context to visit)
        ExpX::StaticVar(fun) => {
            lvisit_fun(lctx, fun);
        }
        // Skip ExpX::VarLoc    (no new context to visit)
        // Skip ExpX::VarAt     (no new context to visit)
        ExpX::Loc(exp) => {
            lvisit_exp(lctx, exp);
        }
        // Skip ExpX::Old       (no new context to visit)
        ExpX::Call(call_fun, typs, exps) => {
            lvisit_call_fun(lctx, call_fun);
            lvisit_typs(lctx, typs);
            lvisit_exps(lctx, exps);
        }
        ExpX::CallLambda(exp, exps) => {
            lvisit_exp(lctx, exp);
            lvisit_exps(lctx, exps);
        }
        ExpX::Ctor(dt, _, binders) => {
            lvisit_dt(lctx, dt);
            for binder in binders.iter() {
                lvisit_exp(lctx, &binder.a);
            }
        }
        ExpX::NullaryOpr(op) => {
            lvisit_nullary_opr(lctx, op);
        }
        ExpX::Unary(_, exp)
        | ExpX::UnaryOpr(_, exp) => {
            lvisit_exp(lctx, exp);
        }
        ExpX::Binary(_, exp1, exp2)
        | ExpX::BinaryOpr(_, exp1, exp2) => {
            lvisit_exp(lctx, exp1);
            lvisit_exp(lctx, exp2);
        }
        ExpX::If(exp1, exp2, exp3) => {
            lvisit_exp(lctx, exp1);
            lvisit_exp(lctx, exp2);
            lvisit_exp(lctx, exp3);
        }
        ExpX::Bind(bnd, exp) => {
            lvisit_bnd(lctx, bnd);
            lvisit_exp(lctx, exp);
        }
        ExpX::ExecFnByName(fun) => {
            lvisit_fun(lctx, fun);
        }
        ExpX::ArrayLiteral(exps) => {
            lvisit_exps(lctx, exps);
        }
        _ => {}
    }
}

fn lvisit_exps(lctx: &mut LeanCtx, exps: &Exps) {
    for exp in exps.iter() {
        lvisit_exp(lctx, exp);
    }
}

fn lvisit_dest(lctx: &mut LeanCtx, dest: &Dest) {
    lvisit_exp(lctx, &dest.dest);
}

fn lvisit_stm<'lctx>(lctx: &mut LeanCtx<'lctx>, stm: &'lctx Stm) {
    match &stm.x {
        StmX::Call { fun, typ_args, args, dest, .. } => {
            // TODO resolved method?
            lvisit_fun(lctx, fun);
            lvisit_typs(lctx, typ_args);
            lvisit_exps(lctx, args);
            if let Some(dest) = dest {
                lvisit_dest(lctx, dest);
            }
        }
        StmX::Assert(_, _, exp) => {
            lvisit_exp(lctx, exp);
        }
        StmX::AssertBitVector { requires, ensures } => {
            lvisit_exps(lctx, requires);
            lvisit_exps(lctx, ensures);
        }
        StmX::AssertQuery { typ_inv_exps, typ_inv_vars, body, .. } => {
            lvisit_exps(lctx, typ_inv_exps);
            for p in typ_inv_vars.iter() {
                lvisit_typ(lctx, &p.1);
            }
            lvisit_stm(lctx, body);
        }
        StmX::AssertCompute(_, exp, _) => {
            lvisit_exp(lctx, exp);
        }
        // TODO: requires/ensures?
        StmX::AssertLean { body, .. } => {
            start_by_lean(lctx);
            add_by_lean_assertion(lctx, body);
            lvisit_exp(lctx, body);
            stop_by_lean(lctx);
        }
        StmX::Assume(exp) => {
            lvisit_exp(lctx, exp);
        }
        StmX::Assign { lhs, rhs } => {
            lvisit_dest(lctx, lhs);
            lvisit_exp(lctx, rhs);
        }
        StmX::DeadEnd(stm) => {
            lvisit_stm(lctx, stm);
        }
        StmX::Return { ret_exp, .. } => {
            ret_exp.as_ref().map(|r| lvisit_exp(lctx, r));
        }
        StmX::If(exp, stm1, stm2) => {
            lvisit_exp(lctx, exp);
            lvisit_stm(lctx, stm1);
            if let Some(stm2) = stm2 {
                lvisit_stm(lctx, stm2);
            }
        }
        StmX::Loop { cond, body, invs, typ_inv_vars, .. } => {
            // CC: TODO missing decrease, etc.

            if let Some((stm, exp)) = cond {
                lvisit_stm(lctx, stm);
                lvisit_exp(lctx, exp);
            }

            lvisit_stm(lctx, body);
            lvisit_loop_invs(lctx, invs);
            for p in typ_inv_vars.iter() {
                lvisit_typ(lctx, &p.1);
            }
        }
        StmX::OpenInvariant(stm) => {
            lvisit_stm(lctx, stm);
        }
        StmX::ClosureInner { body, typ_inv_vars } => {
            lvisit_stm(lctx, body);
            for p in typ_inv_vars.iter() {
                lvisit_typ(lctx, &p.1);
            }
        }
        StmX::Block(stms) => {
            lvisit_stms(lctx, stms);
        }
        _ => {}
    }
}

fn lvisit_stms<'lctx>(lctx: &mut LeanCtx<'lctx>, stms: &'lctx Stms) {
    for stm in stms.iter() {
        lvisit_stm(lctx, stm);
    }
}

fn lvisit_par(lctx: &mut LeanCtx, par: &Par) {
    let typ = &par.x.typ;
    lvisit_typ(lctx, typ);
}

fn lvisit_pars(lctx: &mut LeanCtx, pars: &Pars) {
    for par in pars.iter() {
        lvisit_par(lctx, par);
    }
}

fn lvisit_func_sst<'lctx>(lctx: &mut LeanCtx<'lctx>, sst: &'lctx FunctionSst) {
    let sst = &sst.x;
    let f = &sst.name;

    // Skip the function if we've done a Lean analysis
    if lctx.fns.contains(f) { return; }

    if !is_by_lean_active(lctx) {
        // If we haven't encountered a `by (lean)` yet,
        // see if this is a proof function with a `by (lean)` attribute
        let Some(proof) = &sst.exec_proof_check else { return; };

        if sst.attrs.lean {
            lctx.fns.insert(f.clone());
            start_by_lean(lctx);
            lctx.current_fun = Some(f.clone());

            lvisit_pars(lctx, &sst.pars);
            // lvisit_par(lctx, &sst.ret); // Enforced to be empty
            lvisit_exps(lctx, &proof.reqs);
            lvisit_exps(lctx, &proof.post_condition.ens_exps);
            // lvisit_stm(lctx, &proof.body); // Enforced to be empty

            lctx.current_fun = None;
            stop_by_lean(lctx);
        } else {
            // Ignore the function's parameters and its requires/ensures
            // Instead, scan the function body to find any Lean asserts
            lctx.current_fun = Some(f.clone());
            lvisit_stm(lctx, &proof.body);
            lctx.current_fun = None;
        }
    } else {
        match sst.mode {
            Mode::Proof => { unreachable!("Cannot call proof functions from a `by (lean)` statement"); }
            Mode::Exec => { unreachable!("Cannot call exec functions from a `by (lean)` statement"); }
            Mode::Spec => {
                lctx.fns.insert(f.clone());
                lvisit_pars(lctx, &sst.pars);
                lvisit_par(lctx, &sst.ret);

                // A spec function's body is found in the `spec_axioms`
                sst.axioms.spec_axioms.as_ref()
                    .map(|axioms| lvisit_exp(lctx, &axioms.body_exp));
            }
        }
    }
}

////////////////////////////////////////////////////////////////////////////////

fn add_deps_for_typ(lctx: &LeanCtx, graph: &mut Graph<Dt>, src_dt: &Dt, typ: &Typ) {
    match &**typ {
        TypX::SpecFn(typs, typ) => {
            add_deps_for_typs(lctx, graph, src_dt, typs);
            add_deps_for_typ(lctx, graph, src_dt, typ);
        }
        TypX::AnonymousClosure(typs, typ, _) => {
            add_deps_for_typs(lctx, graph, src_dt, typs);
            add_deps_for_typ(lctx, graph, src_dt, typ);
        }
        TypX::FnDef(_, typs, _) => {
            // TODO: Handle `Fun` argument(?)
            add_deps_for_typs(lctx, graph, src_dt, typs);
        }
        TypX::Datatype(dt, typs, _) => {
            add_deps_for_dt(lctx, graph, src_dt, dt);
            add_deps_for_typs(lctx, graph, src_dt, typs);
        }
        TypX::Primitive(_, typs) => { add_deps_for_typs(lctx, graph, src_dt, typs) }
        TypX::Decorate(_, _, typ) => { add_deps_for_typ(lctx, graph, src_dt, typ) }
        TypX::Boxed(typ) => { add_deps_for_typ(lctx, graph, src_dt, typ) }
        TypX::Projection { trait_typ_args, .. } => {
            // Drop the 0th element, since it is Self
            for typ in trait_typ_args.iter().skip(1) {
                add_deps_for_typ(lctx, graph, src_dt, typ);
            }
        }
        _ => {}
    }
}

fn add_deps_for_typs(lctx: &LeanCtx, graph: &mut Graph<Dt>, src_dt: &Dt, typs: &Typs) {
    for typ in typs.iter() {
        add_deps_for_typ(lctx, graph, src_dt, typ);
    }
}

fn add_deps_for_dt(lctx: &LeanCtx, graph: &mut Graph<Dt>, src_dt: &Dt, dt: &Dt) {
    if src_dt == dt || graph.does_edge_exist(src_dt, dt) { return; }
    graph.add_edge(src_dt.clone(), dt.clone());

    let datatype = lctx.ctx.datatype_map.get(dt).unwrap();
    let DatatypeX { variants, .. } = &datatype.x;
    for variant in variants.iter() {
        for field in variant.fields.iter() {
            let typ = &field.a.0;
            add_deps_for_typ(lctx, graph, src_dt, typ);
        }
    }
}

fn compute_dt_deps(lctx: &LeanCtx, graph: &mut Graph<Dt>, dt: &Dt) {
    let datatype = lctx.ctx.datatype_map.get(dt).unwrap();
    let DatatypeX { variants, .. } = &datatype.x;
    for variant in variants.iter() {
        let Variant { fields, .. } = variant;
        for field in fields.iter() {
            let typ = &field.a.0;
            add_deps_for_typ(lctx, graph, dt, typ);
        }
    }
}

fn compute_all_dt_deps(lctx: &LeanCtx, graph: &mut Graph<Dt>) {
    for dt in lctx.dts.iter() {
        compute_dt_deps(lctx, graph, dt);
    }
}

/// If any `by (lean)` attributes in the crate, the crate gets serialized to a JSON.
///
/// This is the entrypoint for Lean serialization.
pub fn serialize_crate_for_lean(ctx: &Ctx, krate: &KrateSst) {
    let mut lctx = LeanCtx {
        ctx,
        current_fun: None,
        found_by_lean: false,
        total_by_lean: 0,
        typs: Vec::new(),
        dts: HashSet::new(),
        fns: HashSet::new(),
        asserts_to_serialize: Vec::new(),
    };

    // Visit all of the functions to check for `by (lean)` attributes
    for sst in krate.functions.iter() {
        // Spec functions cannot contain `by (lean)`, so we skip them
        if sst.x.mode == Mode::Spec { continue; }
        lvisit_func_sst(&mut lctx, sst);
    }
    
    // Don't serialize anything if there are no `by (lean)` attributes
    if lctx.total_by_lean == 0 { return; }

    // The top-level JSON object is an array under the key "decls"
    let mut decls: Vec<serde_json::Value> = Vec::new();

    // Take the values in the `dts` and sort them topologically
    let mut graph = Graph::new();
    for dt in lctx.dts.iter() {
        graph.add_node(dt.clone());
    }

    compute_all_dt_deps(&lctx, &mut graph);
    graph.compute_sccs(); 

    // Serialize everything!
    this_thread_start_skipping_nonlean_fields();

    // Loop through the datatype connected components and serialize them as they come
    let representatives = graph.sort_sccs();
    for rep in representatives.iter() {
        let scc = graph.get_scc_nodes(rep);
        // TODO: Mutual blocks around sccs of length greater than 1
        for dt in scc.iter() {
            // Skip tuples, since they are handled natively by `Prod` in Lean
            match dt {
                Dt::Tuple(..) => { continue }
                Dt::Path(..) => { decls.push(serialize_dt(ctx, dt)) }
            }
        }
    }

    // Loop through the functions in the connected component, serializing in order
    for node in ctx.global.func_call_sccs.iter() {
        match node {
            Node::Fun(f) => {
                if lctx.fns.contains(f) {
                    decls.push(serialize_fn(ctx, f).unwrap());
                }
            }
            // TODO traits, etc.
            _ => { continue; }
        }
    }

    // Serialize any `assert(...) by (lean)` as independent Lean theorems
    // Each assertion is associated with its containing function
    // The `fun_assert_map` maintains a per-function count of assertions
    // TODO: Serialize the assertions in order of the functions in the SCCs
    let mut fun_assert_map: HashMap<&Fun, u32> = HashMap::new();
    for (assert, f) in lctx.asserts_to_serialize.iter() {
        let counter = *fun_assert_map.get(f).unwrap_or(&1);
        let assert = serialize_assert(ctx, assert, f, counter);
        decls.push(assert);
        fun_assert_map.insert(f, counter + 1);
    }

    // We are done serializing the SST objects now
    this_thread_stop_skipping_nonlean_fields();

    let module_name = ctx.module_path().to_str();
    let path = std::env::current_dir().unwrap().join(
        format!("serialized_{}.json", module_name)
    );

    let mut file = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .truncate(true)
        .open(path)
        .unwrap();

    let json = serde_json::json! {
        {
            "krate": module_name,
            "decls": decls,
        }
    };

    let _ = writeln!(file, "{}", json.to_string());
}

/*

Format:

{ "decls": [ ... ] }
 
where

SpecFn: {
  "decl_type": "SpecFn",
  "x": { serde_serialization of FunctionSst }
}

Exp: {
  decl_type: "Assert",
} "SpecFns": [ ... ],
    "Datatypes": [ ... ],
    "AssertId": 0,
    "Assert": { ... }
}

*/

const DECL_TYPE: &str = "DeclType";
const DECL_VAL: &str = "x";
const DATATYPE_DECL: &str = "Datatype";
const SPEC_FUN_DECL: &str = "SpecFn";
const PROOF_FUN_DECL: &str = "ProofFn";
const ASSERT_DECL: &str = "Assert";

impl PathX {
    pub fn to_str(&self) -> String {
        self.krate.iter().chain(self.segments.iter())
            .map(|x| x.as_ref().as_str()).collect::<Vec<&str>>().join("_")
    }
}

fn serialize_dt(ctx: &Ctx, dt: &Dt) -> serde_json::Value {
    let datatype = &ctx.datatype_map.get(dt).unwrap().x;
    serde_json::json! {
        {
            DECL_TYPE: DATATYPE_DECL,
            DECL_VAL: datatype,
        }
    }
}

fn serialize_fn(ctx: &Ctx, fun: &Fun) -> Option<serde_json::Value> {
    let Some(sst) = &ctx.func_sst_map.get(fun) else { return None };
    let sst = &sst.x;
    if sst.mode == Mode::Exec { return None; }

    let fun_type = match sst.mode {
        Mode::Spec => SPEC_FUN_DECL,
        Mode::Proof => PROOF_FUN_DECL,
        Mode::Exec => unreachable!(),
    };
    
    Some (serde_json::json! {
        {
            DECL_TYPE: fun_type,
            DECL_VAL: sst,
        }
    })
}

// Serializes the expression under the assertion
fn serialize_assert(_ : &Ctx, e: &Exp, f: &Fun, id: u32) -> serde_json::Value {
    serde_json::json! {
        {
            DECL_TYPE: ASSERT_DECL,
            "AssertId": id,
            "ParentFn": f,
            DECL_VAL: e,
        }
    }
}
