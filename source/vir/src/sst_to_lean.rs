use crate::context::Ctx;
use air::ast::Binders;
use crate::ast::{
    Typ, TypX, Typs, Datatype, DatatypeX, Dt, Fun, PathX, Mode, Variant, VarBinder, VarBinders,
};
use crate::ast_util::types_equal;
use crate::sst::{
    Bnd, BndX, Dest, Exp, Exps, ExpX, FuncDeclSst, LoopInv, LoopInvs, Par, Pars, Stm, Stms, StmX, CallFun, KrateSst, FunctionSst, FuncCheckSst
};
use crate::recursion::Node;

use std::collections::HashSet;

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
    typs: Vec<Typ>, // CC: Replace with manual hash set/map later?
    fns: HashSet<Fun>,
    dts: HashSet<Dt>,
}

/*
    Global hash set storing the thread IDs of threads doing Lean serialization.
    Added to by `this_thread_start_skipping_nonlean_fields()`,
    and removed from by `this_thread_stop_skipping_nonlean_fields()`.

    In general, we use the default `serde_json::to_value` serialization
    for our Lean serialization. However, the `Span`, `Spanned`, and `SpannedTyped`
    objects include a `RawSpan` object that contains important disambiguation
    data for Verus, but which Lean isn't (currently) using.

    We 
    Rust really, *really* discourages programmers using global state.
    
    adding `mut` 
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
trait LeanVisitor {
    fn lean_visit(lctx: &mut LeanCtx, x: &Self);
}


fn lean_visit_datatype(lctx: &mut LeanCtx, datatype: &Datatype) {
    // println!("lean_visit_datatype: {:?}", datatype.x.name);
    let DatatypeX { variants, .. } = &datatype.x;
    for variant in variants.iter() {
        let Variant { fields, .. } = variant;
        for field in fields.iter() {
            let typ = &field.a.0;
            lean_visit_typ(lctx, typ);
        }
    }
}

fn lean_visit_dt(lctx: &mut LeanCtx, dt: &Dt) {
    // Only process this datatype if we haven't seen it before
    if lctx.dts.contains(dt) { return; }
    lctx.dts.insert(dt.clone());

    // See if that datatype depends on other types
    let datatype = lctx.ctx.datatype_map.get(dt).unwrap();
    lean_visit_datatype(lctx, datatype);
}

fn lean_visit_typ(lctx: &mut LeanCtx, typ: &Typ) {
    // Note: Because `TypX` cannot implement `Eq` or `PartialEq` traits
    //       (see the note in vir/src/ast.rs), we cannot use a `HashSet`
    //       to prevent duplicate type visits. Oh well.
    // Instead, we use a list of types
    for typ2 in lctx.typs.iter() {
        if types_equal(typ, typ2) { return; }
    }
        
    lctx.typs.push(typ.clone());
    // println!("lean_visit_typ: {:?}", typ);

    // CC: TODO implement the FnDef branch, because traits are somewhat like Lean type classes
    match &**typ {
        TypX::SpecFn(typs, typ) => {
            lean_visit_typs(lctx, typs);
            lean_visit_typ(lctx, typ);
        }
        TypX::AnonymousClosure(typs, typ, _) => {
            lean_visit_typs(lctx, typs);
            lean_visit_typ(lctx, typ);
        }
        TypX::Datatype(dt, typs, _) => {
            lean_visit_dt(lctx, dt);
            lean_visit_typs(lctx, typs);
        }
        TypX::Primitive(_, typs) => { lean_visit_typs(lctx, typs); }
        TypX::Decorate(_, _, typ) => { lean_visit_typ(lctx, typ); }
        TypX::Boxed(typ) => { lean_visit_typ(lctx, typ); }
        TypX::Projection { trait_typ_args, .. } => {
            // Skip the 0th element because it is the same type as `typ` given to the function
            // See the comment for `Projection` in `TypX` in `vir/src/ast.rs`
            for typ in trait_typ_args.iter().skip(1) {
                lean_visit_typ(lctx, typ);
            }
        }
        _ => {}
    }
}

fn lean_visit_typs(lctx: &mut LeanCtx, typs: &Typs) {
    for typ in typs.iter() {
        lean_visit_typ(lctx, &typ);
    }
}

// CC: This should really be a trait
fn lean_visit_varbinder_typ(lctx: &mut LeanCtx, binder: &VarBinder<Typ>) {
    lean_visit_typ(lctx, &binder.a);
}

fn lean_visit_varbinder_exp(lctx: &mut LeanCtx, binder: &VarBinder<Exp>) {
    lean_visit_exp(lctx, &binder.a);
}

fn lean_visit_varbinders_typ(lctx: &mut LeanCtx, binders: &VarBinders<Typ>) {
    for binder in binders.iter() {
        lean_visit_varbinder_typ(lctx, binder);
    }
}

fn lean_visit_varbinders_exp(lctx: &mut LeanCtx, binders: &VarBinders<Exp>) {
    for binder in binders.iter() {
        lean_visit_varbinder_exp(lctx, binder);
    }
}

fn lean_visit_bnd(lctx: &mut LeanCtx, bnd: &Bnd) {
    match &bnd.x {
        BndX::Let(binders) => {
            lean_visit_varbinders_exp(lctx, binders);
        }
        BndX::Quant(_, typ_binders, _, _) => {
            lean_visit_varbinders_typ(lctx, typ_binders);
        }
        BndX::Lambda(typ_binders, _) => {
            lean_visit_varbinders_typ(lctx, typ_binders);
        }
        BndX::Choose(typ_binders, _, exp) => {
            lean_visit_varbinders_typ(lctx, typ_binders);
            lean_visit_exp(lctx, exp)
        }
    }
}

fn lean_visit_loop_inv(lctx: &mut LeanCtx, inv: &LoopInv) {
    lean_visit_exp(lctx, &inv.inv);
}

fn lean_visit_loop_invs(lctx: &mut LeanCtx, invs: &LoopInvs) {
    for inv in invs.iter() {
        lean_visit_loop_inv(lctx, inv);
    }
}

fn lean_visit_fun(lctx: &mut LeanCtx, fun: &Fun) {
    if !lctx.fns.contains(fun) {
        lctx.fns.insert(fun.clone());

        // TODO are there any problems with one polymorphic function but multiple instantiations?
        let sst= lctx.ctx.func_sst_map.get(fun).unwrap();
        lean_visit_func_sst(lctx, sst);
    }
}

fn lean_visit_call_fun(lctx: &mut LeanCtx, call_fun: &CallFun) {
    match call_fun {
        CallFun::Fun(fun, _) => {
            lean_visit_fun(lctx, fun);
            // TODO implement the optional resolved typs here?
        }
        CallFun::Recursive(fun) => {
            lean_visit_fun(lctx, fun);
        }
        _ => {}
    }
}

fn lean_visit_exp(lctx: &mut LeanCtx, exp: &Exp) {
    // Visiting the type of the expression will lead to TONS of redundant calls
    // But, this allows us to catch any types that slip through the cracks
    // (e.g., a body of a proof function refers to an otherwise unmentioned datatype)
    lean_visit_typ(lctx, &exp.typ);

    match &exp.x {
        ExpX::StaticVar(fun) => {
            lean_visit_fun(lctx, fun);
        }
        ExpX::Loc(exp) => {
            lean_visit_exp(lctx, exp);
        }
        ExpX::Call(call_fun, typs, exps) => {
            lean_visit_call_fun(lctx, call_fun);
            lean_visit_typs(lctx, typs);
            lean_visit_exps(lctx, exps);
        }
        ExpX::CallLambda(exp, exps) => {
            lean_visit_exp(lctx, exp);
            lean_visit_exps(lctx, exps);
        }
        ExpX::Ctor(dt, _, binders) => {
            lean_visit_dt(lctx, dt);
            for binder in binders.iter() {
                lean_visit_exp(lctx, &binder.a);
            }
        }
        ExpX::Unary(_, exp) => {
            lean_visit_exp(lctx, exp);
        }
        ExpX::UnaryOpr(_, exp) => {
            lean_visit_exp(lctx, exp);
        }
        ExpX::Binary(_, exp1, exp2) => {
            lean_visit_exp(lctx, exp1);
            lean_visit_exp(lctx, exp2);
        }
        ExpX::BinaryOpr(_, exp1, exp2) => {
            lean_visit_exp(lctx, exp1);
            lean_visit_exp(lctx, exp2);
        }
        ExpX::If(exp1, exp2, exp3) => {
            lean_visit_exp(lctx, exp1);
            lean_visit_exp(lctx, exp2);
            lean_visit_exp(lctx, exp3);
        }
        ExpX::Bind(bnd, exp) => {
            lean_visit_bnd(lctx, bnd);
            lean_visit_exp(lctx, exp);
        }
        ExpX::ExecFnByName(fun) => {
            lean_visit_fun(lctx, fun);
        }
        ExpX::ArrayLiteral(exps) => {
            lean_visit_exps(lctx, exps);
        }
        _ => {}
    }
}

fn lean_visit_exps(lctx: &mut LeanCtx, exps: &Exps) {
    for exp in exps.iter() {
        lean_visit_exp(lctx, exp);
    }
}

fn lean_visit_dest(lctx: &mut LeanCtx, dest: &Dest) {
    lean_visit_exp(lctx, &dest.dest);
}

// CC: This might not be sufficient, as `by (lean)` might be hidden elsewhere
//     See, for example, `stm_assign()` in `sst_vars.rs`
fn lean_visit_stm(lctx: &mut LeanCtx, stm: &Stm) {
    match &stm.x {
        StmX::Call { fun, typ_args, args, dest, .. } => {
            // TODO resolved method?
            // TODO skip if mode is exec?
            lean_visit_fun(lctx, fun);
            lean_visit_typs(lctx, typ_args);
            lean_visit_exps(lctx, args);
            if let Some(dest) = dest {
                lean_visit_dest(lctx, dest);
            }
        }
        StmX::Assert(_, _, exp) => {
            lean_visit_exp(lctx, exp);
        }
        StmX::AssertBitVector { requires, ensures } => {
            lean_visit_exps(lctx, requires);
            lean_visit_exps(lctx, ensures);
        }
        StmX::AssertQuery { typ_inv_exps, typ_inv_vars, body, .. } => {
            lean_visit_exps(lctx, typ_inv_exps);
            for p in typ_inv_vars.iter() {
                lean_visit_typ(lctx, &p.1);
            }
            lean_visit_stm(lctx, body);
        }
        StmX::AssertCompute(_, exp, _) => {
            lean_visit_exp(lctx, exp);
        }
        StmX::AssertLean(exp) => {
            // lctx.num_by_lean_attrs += 1;
            lean_visit_exp(lctx, exp);
        }
        StmX::Assume(exp) => {
            lean_visit_exp(lctx, exp);
        }
        StmX::Assign { lhs, rhs } => {
            lean_visit_dest(lctx, lhs);
            lean_visit_exp(lctx, rhs);
        }
        StmX::DeadEnd(stm) => {
            lean_visit_stm(lctx, stm);
        }
        StmX::Return { ret_exp, .. } => {
            if let Some(ret_exp) = ret_exp {
                lean_visit_exp(lctx, ret_exp);
            }
        }
        StmX::If(exp, stm1, stm2) => {
            lean_visit_exp(lctx, exp);
            lean_visit_stm(lctx, stm1);
            if let Some(stm2) = stm2 {
                lean_visit_stm(lctx, stm2);
            }
        }
        StmX::Loop { cond, body, invs, typ_inv_vars, .. } => {
            // CC: TODO missing decrease, etc.

            if let Some((stm, exp)) = cond {
                lean_visit_stm(lctx, stm);
                lean_visit_exp(lctx, exp);
            }

            lean_visit_stm(lctx, body);
            lean_visit_loop_invs(lctx, invs);
            for p in typ_inv_vars.iter() {
                lean_visit_typ(lctx, &p.1);
            }
        }
        StmX::OpenInvariant(stm) => {
            lean_visit_stm(lctx, stm);
        }
        StmX::ClosureInner { body, typ_inv_vars } => {
            lean_visit_stm(lctx, body);
            for p in typ_inv_vars.iter() {
                lean_visit_typ(lctx, &p.1);
            }
        }
        StmX::Block(stms) => {
            lean_visit_stms(lctx, stms);
        }
        _ => {}
    }
}

fn lean_visit_stms(lctx: &mut LeanCtx, stms: &Stms) {
    for stm in stms.iter() {
        lean_visit_stm(lctx, stm);
    }
}

fn lean_visit_par(lctx: &mut LeanCtx, par: &Par) {
    let typ = &par.x.typ;
    lean_visit_typ(lctx, typ);
}

fn lean_visit_pars(lctx: &mut LeanCtx, pars: &Pars) {
    for par in pars.iter() {
        lean_visit_par(lctx, par);
    }
}

fn lean_visit_func_decl_sst(lctx: &mut LeanCtx, sst: &FuncDeclSst) {
    lean_visit_pars(lctx, &sst.req_inv_pars);
    lean_visit_pars(lctx, &sst.ens_pars);
    lean_visit_pars(lctx, &sst.post_pars);
    lean_visit_exps(lctx, &sst.reqs);
    lean_visit_exps(lctx, &sst.enss);
}

fn lean_visit_func_sst(lctx: &mut LeanCtx, sst: &FunctionSst) {
    let f = &sst.x;

    // Skip the function if we've already seen it
    // CC: TODO This assumes no variable shadowing and distinct namespacing
    // In other words, assumes that Verus handles name clashes reasonably
    if lctx.fns.contains(&f.name) { return; }
    lctx.fns.insert(f.name.clone());
    
    // Skip functions that are executable
    if f.mode == Mode::Exec { return; }

    // Skip functions that have no exec proof to check
    let Some(proof) = &f.exec_proof_check else { return; };

    // Note if the whole function has the `by (lean)` attribute
    // if f.attrs.lean { lctx.num_by_lean_attrs += 1; }

    // TODO: Only serialize up to the `by (lean)` attributes
    // For example, if there are 3 asserts, but `by (lean)` in only on the first
    lean_visit_pars(lctx, &f.pars);
    lean_visit_par(lctx, &f.ret);
    lean_visit_func_decl_sst(lctx, &f.decl);
    lean_visit_stm(lctx, &proof.body);
}

////////////////////////////////////////////////////////////////////////////////

/*

CC: For this section, we shallowly try to determine if any `FunctionSst`
has any `by (lean)` attributes. We don't care if "outside definitions"
(for example, a called `Fun`, or types with invariants)
have `by (lean)` attributes, only if the proof/spec function itself has one.
So rather than deep accumulating all the needed context, we return a bool.

TODO: This should also be a trait.

*/

fn loop_inv_has_lean(inv: &LoopInv) -> bool {
    exp_has_lean(&inv.inv)
}

fn loop_invs_has_lean(invs: &LoopInvs) -> bool {
    for inv in invs.iter() {
        if loop_inv_has_lean(inv) { return true; }
    }
    false
}

fn dest_has_lean(dest: &Dest) -> bool {
    exp_has_lean(&dest.dest)
}

fn varbinder_exp_has_lean(binder: &VarBinder<Exp>) -> bool {
    exp_has_lean(&binder.a)
}

fn varbinders_exp_has_lean(binders: &VarBinders<Exp>) -> bool {
    for binder in binders.iter() {
        if varbinder_exp_has_lean(binder) { return true; }
    }
    false
}

fn bnd_has_lean(bnd: &Bnd) -> bool {
    match &bnd.x {
        BndX::Let(binders) => {
            varbinders_exp_has_lean(binders)
        }
        BndX::Choose(_, _, exp) => {
            exp_has_lean(exp)
        }
        _ => false
    } 
}

fn stm_has_lean(stm: &Stm) -> bool {
    match &stm.x {
        StmX::Call { args, dest, .. } => {
            exps_has_lean(args)
            || (if let Some(dest) = dest {
                    dest_has_lean(dest)
                } else { false })
        }
        StmX::Assert(_, _, exp) => {
            exp_has_lean(exp)
        }
        StmX::AssertBitVector { requires, ensures } => {
            exps_has_lean(requires)
            || exps_has_lean(ensures)
        }
        StmX::AssertQuery { typ_inv_exps, body, .. } => {
            stm_has_lean(body)
            || exps_has_lean(typ_inv_exps)
        }
        StmX::AssertCompute(_, exp, _) => {
            exp_has_lean(exp)
        }
        StmX::AssertLean(_) => { true }
        StmX::Assume(exp) => {
            exp_has_lean(exp)
        }
        StmX::Assign { lhs, rhs } => {
            dest_has_lean(lhs)
            || exp_has_lean(rhs)
        }
        StmX::DeadEnd(stm) => {
            stm_has_lean(stm)
        }
        StmX::Return { ret_exp, ..} => {
            if let Some(ret_exp) = ret_exp {
                exp_has_lean(ret_exp)
            } else { false }
        }
        StmX::If(cond, stm1, stm2) => {
            exp_has_lean(cond)
            || stm_has_lean(stm1)
            || (if let Some(stm2) = stm2 {
                    stm_has_lean(stm2)
                } else { false })
        }
        StmX::Loop { cond, body, invs, decrease, .. } => {
            (if let Some((stm, exp)) = cond {
                stm_has_lean(stm) || exp_has_lean(exp)
            } else { false })
            || stm_has_lean(body)
            || loop_invs_has_lean(invs)
            || exps_has_lean(decrease)
        }
        StmX::OpenInvariant(stm) => {
            stm_has_lean(stm)
        }
        StmX::ClosureInner { body, .. } => {
            stm_has_lean(body)
        }
        StmX::Block(stms) => {
            stms_has_lean(stms)
        }
        _ => false
    }
}

fn stms_has_lean(stms: &Stms) -> bool {
    for stm in stms.iter() {
        if stm_has_lean(stm) { return true; }
    }
    false
}

fn exp_has_lean(exp: &Exp) -> bool {
    match &exp.x {
        ExpX::Loc(exp) => {
            exp_has_lean(exp)
        }
        ExpX::Call(_, _, exps) => {
            exps_has_lean(exps)
        }
        ExpX::CallLambda(exp, exps) => {
            exp_has_lean(exp)
            || exps_has_lean(exps)
        }
        ExpX::Ctor(_, _, binders) => {
            exp_binders_has_lean(binders)
        }
        ExpX::Unary(_, exp) => {
            exp_has_lean(exp)
        }
        ExpX::UnaryOpr(_, exp) => {
            exp_has_lean(exp)
        }
        ExpX::Binary(_, exp1, exp2) => {
            exp_has_lean(exp1)
            || exp_has_lean(exp2)
        }
        ExpX::BinaryOpr(_, exp1, exp2) => {
            exp_has_lean(exp1)
            || exp_has_lean(exp2)
        }
        ExpX::If(exp1, exp2, exp3) => {
            exp_has_lean(exp1)
            || exp_has_lean(exp2)
            || exp_has_lean(exp3)
        }
        ExpX::WithTriggers(_, exp) => {
            exp_has_lean(exp)
        }
        ExpX::Bind(bnd, exp) => {
            bnd_has_lean(bnd)
            || exp_has_lean(exp)
        }
        ExpX::ArrayLiteral(exps) => {
            exps_has_lean(exps)
        }
        _ => false
    }
}

fn exps_has_lean(exps: &Exps) -> bool {
    for exp in exps.iter() {
        if exp_has_lean(exp) { return true; }
    }
    false
}

// CC: This *really* should be a trait
fn exp_binders_has_lean(binders: &Binders<Exp>) -> bool {
    for binder in binders.iter() {
        if exp_has_lean(&binder.a) { return true; }
    }
    false
}

fn func_sst_has_lean(sst: &FunctionSst) -> bool {
    let f = &sst.x;

    // We don't want to consider/serialize exec functions
    if f.mode == Mode::Exec { return false; }

    // We don't want to consider/serialize missing spec/proof functions
    let Some(proof) = &f.exec_proof_check else { return false; };

    // If the entire function is marked `by (lean)`, we accept it
    if f.attrs.lean { return true; }

    // Otherwise, we shallowly check the function's body for `by (lean)` attributes
    stm_has_lean(&proof.body)
}

/// If any `by (lean)` attributes in the crate, the crate gets serialized to a JSON.
///
/// This is the entrypoint for Lean serialization.
pub fn serialize_crate_for_lean(ctx: &Ctx, krate: &KrateSst) {
    let mut lctx = LeanCtx {
        ctx,
        typs: Vec::new(),
        fns: HashSet::new(),
        dts: HashSet::new(),
    };

    let mut has_ctr = 0;

    // lean_visit_krate_sst(&mut lctx, krate);
    // Visit all the necessary context to see if there are any `by (lean)` attributes
    for sst in krate.functions.iter() {
        if func_sst_has_lean(sst) {
            has_ctr += 1;
            // CC TODO: Think about how much of a function we need to visit/serialize
            lean_visit_func_sst(&mut lctx, sst); 
        }
    }
    
    // Don't serialize anything if there are no `by (lean)` attributes
    if has_ctr == 0 { return; }

    // TODO: Handle `mutual` definitions. See James' code
    
    // The top-level JSON object is an array, so we push declarations onto `decls`
    let mut decls: Vec<serde_json::Value> = Vec::new();

    // Do datatypes first, then spec functions, then proof functions

    this_thread_start_skipping_nonlean_fields();

    // Loop through the connected component, serializing in order
    /*
    for node in ctx.global.func_call_sccs.iter() {
        match node {
            Node::Fun(f) => {
                if !lctx.fns.contains(f) { continue; }
                // println!("Function: {:?}", f);
                if let Some(decl) = serialize_fn(ctx, f) {
                    decls.push(decl);
                }
            }
            Node::Datatype(dt) => {
                if !lctx.dts.contains(dt) { continue; }
                // println!("Datatype: {:?}", dt);
                decls.push(serialize_dt(ctx, dt));
            }
            Node::Trait(path) => {
                // println!("Trait: {:?}", path);
            }
            Node::TraitImpl(path) => {
                // println!("TraitImpl: {:?}", path);
            }
            Node::TraitReqEns(path, b) => {
                // println!("TraitReqEns: {:?}", path);
            }
            Node::ModuleReveal(path) => {
                // println!("ModuleReveal: {:?}", path);
            }
            Node::SpanInfo { span_infos_index, text} => {
                // println!("SpanInfo: {:?}", text);
            }
        }
    } */

    for dt in lctx.dts.iter() {
        match dt {
            Dt::Tuple(..) => { continue }
            Dt::Path(..) => { decls.push(serialize_dt(ctx, dt)) }
        }
    }

    for f in lctx.fns.iter() {
        let sst = &lctx.ctx.func_sst_map.get(f).unwrap().x;
        if sst.mode == Mode::Spec {
            if let Some(decl) = serialize_fn(ctx, f) {
                decls.push(decl);
            }
        }
    }

    for f in lctx.fns.iter() {
        let sst = &lctx.ctx.func_sst_map.get(f).unwrap().x;
        if sst.mode == Mode::Proof {
            if let Some(decl) = serialize_fn(ctx, f) {
                decls.push(decl);
            }
        }
    }

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
const FUNC_CHECK_SST_DECL: &str = "FuncCheckSst";

// These are for facts proven by Verus
const AXIOM_DECL: &str = "VerusTheorem";

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

fn serialize_exp(_ : &Ctx, e: &ExpX) -> serde_json::Value {
    serde_json::json! {
        {
            DECL_TYPE: ASSERT_DECL,
            DECL_VAL: e,
        }
    }
}

fn serialize_func_check_sst(_: &Ctx, fun: &Fun, sst: &FuncCheckSst) -> serde_json::Value {
    serde_json::json! {
        {
            DECL_TYPE: FUNC_CHECK_SST_DECL,
            "name": fun,
            DECL_VAL: sst,
        }
    }
}
