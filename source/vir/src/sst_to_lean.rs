use crate::context::Ctx;
use air::ast::Binders;
use crate::ast::{
    Typ, TypX, Typs, Datatype, DatatypeX, Dt, Fun, PathX, Mode, Variant, VarBinder, VarBinders,
};
use crate::sst::{
    Bnd, BndX, Dest, Exp, Exps, ExpX, LoopInv, LoopInvs, Stm, Stms, StmX, CallFun, KrateSst, FunctionSst, FuncCheckSst
};

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

fn lean_visit_typ(lctx: &mut LeanCtx, typ: &TypX) {
    // Note: Because `TypX` cannot implement `Eq` or `PartialEq` traits
    //       (see the note in vir/src/ast.rs), we cannot use a `HashSet`
    //       to prevent duplicate type visits. Oh well.

    // CC: TODO implement the FnDef branch, because traits are somewhat like Lean type classes
    match typ {
        TypX::SpecFn(typs, typ) => {
            lean_visit_typs(lctx, typs);
            lean_visit_typ(lctx, typ);
        }
        TypX::AnonymousClosure(typs, typ, _) => {
            lean_visit_typs(lctx, typs);
            lean_visit_typ(lctx, typ);
        }
        TypX::Datatype(dt, _, _) => {
            lean_visit_dt(lctx, dt);
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

    for dt in lctx.dts.iter() {
        match dt {
            Dt::Tuple(..) => { continue }
            Dt::Path(..) => { decls.push(serialize_dt(ctx, dt)) }
        }
    }

    for fun in lctx.fns.iter() {
        let sst = &lctx.ctx.func_sst_map.get(fun).unwrap().x;
        if sst.mode == Mode::Spec {
            decls.push(serialize_fn(ctx, fun));
        }
    }

    for fun in lctx.fns.iter() {
        let sst = &lctx.ctx.func_sst_map.get(fun).unwrap().x;
        if sst.mode == Mode::Proof {
            decls.push(serialize_fn(ctx, fun));
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

fn serialize_fn(ctx: &Ctx, fun: &Fun) -> serde_json::Value {
    let sst = &ctx.func_sst_map.get(fun).unwrap().x;
    serde_json::json! {
        {
            DECL_TYPE: SPEC_FUN_DECL,
            "name": fun,
            DECL_VAL: sst,
        }
    }
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

/*
pub fn serialize_leanables(ctx: &Ctx, to_lean: &Vec<Leanable>) {
    if to_lean.len() == 0 {
        return;
    }

    let mut lctx = LeanableCtx {
        fns: HashSet::new(),
        dts: HashSet::new(),
    };

    // Accumulate all necessary context from the Leanables
    for l in to_lean.iter() {
        match l {
            Leanable::Exp(e) => {
                visit_exp(&mut lctx, &e.x);
            }
            Leanable::Func(_, sst) => {
                visit_func_check_sst(&mut lctx, sst);
            }
        }
    }

    // Now serialize all data types, then spec functions, then asserts/proof fns
    let mut decls: Vec<serde_json::Value> = Vec::new();

    inc_skip_lean_fields();

    for dt in lctx.dts.iter() {
        decls.push(serialize_dt(ctx, dt));
    }

    for fun in lctx.fns.iter() {
        decls.push(serialize_fn(ctx, fun));
    }

    // Now visit the Leanables once again and serialize each
    for l in to_lean.iter() {
        match l {
            Leanable::Exp(e) => {
                decls.push(serialize_exp(ctx, &e.x));
            }
            Leanable::Func(fun, sst) => {
                decls.push(serialize_func_check_sst(ctx, fun, sst));
            }
       }
    }

    dec_skip_lean_fields();

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
            "decls": decls,
        }
    };

    let _ = writeln!(file, "{}", json.to_string());

        // CC: It appears that to interpret the expression, you need to pass a compute mode
      //     Since lean isn't a compute mode, we can't(?) use this function
      /*
      let interp_exp = crate::interpreter::eval_expr(
          &ctx.global,
          exp,
          diagnostics,
          fun_ssts.clone(),
          ctx.global.rlimit,
          ctx.global.arch,
          ComputeMode::Z3,
          &mut ctx.global.interpreter_log.lock().unwrap(),
      )?; */
      // let res = crate::interpreter::eval_expr_internal()

      // Use the unique ID from the span to disambiguate elab_one goals
      /*
      let span_id = stm.span.id;

      // TODO: Some way to uniquely identify the assert?
      // Across two files, the IDs might clash
      let path = std::env::current_dir().unwrap().join(
          format!("serialized_assert_{}.json", span_id)
      );

      let mut file = std::fs::OpenOptions::new()
          .create(true)
          .write(true)
          .truncate(true)
          .open(path)
          .unwrap();

  /*
              let serialized_val = serde_json::to_value(func_check_sst)
          .expect("Failed to serialize SST to JSON");
      let wrapped_serialized_val = serde_json::json!({
          "FnName": func_display_name,
          "FuncCheckSst": serialized_val,
      });
      let _ = writeln!(file, "{}", wrapped_serialized_val.to_string()); 
    */

      // let context = serde_json::to_value(&ctx.global).unwrap();
      // write a function to get fun objects recursively
      // let context : Collection<Fun> = ...
      // for col in context: let col_sst = fun_ssts.get(col).unwrap();
      // let col_value = serde_json::to_value(&col_sst).unwrap();

      // Accumulate Fun objects from inner_exp
      accumulate_fun_objects(&exp.x, fun_accumulator);
      // println!("fun_accumulator: {:?}", fun_accumulator);
      // let accumulated_strings: Vec<String> = fun_accumulator.iter()
      //     .map(|col_value| col_value).collect();

      let mut accumulated_values = Vec::new();
      for col in fun_accumulator.iter() {
          let col_sst = fun_ssts.get(col).unwrap();
          accumulated_values.push(col_sst.clone());
      }

      let mut datatype_values = Vec::new();
      for dt in ctx.datatype_map.values() {
          datatype_values.push(dt.clone());
      }

      inc_skip_lean_fields();
      let top_level = serde_json::json!({
          "SpecFns": accumulated_values, // list of serialized spec function bodies
          "Datatypes": datatype_values, // list of serialized datatypes
          "PriorAsserts": [], // list of prior assertions
          "AssertId": span_id,
          "Assert": exp,
      });
      let _ = writeln!(file, "{}", top_level.to_string());
      dec_skip_lean_fields();
      */
}
      */

// Implement slimmer serializations

/*impl<X: Serialize> SpannedTyped<X> {
  pub fn to_lean_json(&self) -> serde_json::Value {
      serde_json::json! ({
          "typ": self.typ,
          "x": self.x
      })
  }
} */

/*impl<X: Serialize> {
  pub fn to_lean_json(&self) -> serde_json::Value {
      serde_json::json! ({
          "span": self.span,
          "x": self.x
      })
  }
} */

/*

        #[cfg(any(feature = "lean", feature = "lean-export"))]
        // Now export the SST to a new tempfile
        // CC: For now, use helloworld.json
        // CC: Depends on whether `lean` or `lean-export` is used? 

        // If "lean-export" is provided, then we export a serlialized version
        // of the function's SST to a JSON file. We then do *NOT* add a Command
        // to `state.commands`, as we assume here that the Lean obligations
        // will be correctly discharged.
        //#[cfg(feature = "lean-export")]
        //{

            // Get some name for the function
            // For now, the last element of its krate/segments

            // Hmm this implementation doesn't work...
            let func_display_name = func_name.path.segments.last().unwrap();
            let path = std::env::current_dir().unwrap().join(
                format!("serialized_fn_{}.json", func_display_name)
            );

            let mut file = std::fs::OpenOptions::new()
                .create(true)
                .write(true)
                .truncate(true)
                .open(path)
                .unwrap();

            let serialized_val = serde_json::to_value(func_check_sst)
                .expect("Failed to serialize SST to JSON");

            let fun_accumulator: &mut HashSet<Fun> = &mut HashSet::new();
            for req in reqs.iter() {
                accumulate_fun_objects(&req.x, fun_accumulator);
            }
            for ens in post_condition.ens_exps.iter() {
                accumulate_fun_objects(&ens.x, fun_accumulator);
            }
            let mut spec_fns = Vec::new();
            for col in fun_accumulator.iter() {
                let col_sst = ctx.func_sst_map.get(col).unwrap();
                spec_fns.push(col_sst.to_lean_json());
            }
            
            let mut datatype_values = Vec::new();
            for dt in ctx.datatype_map.values() {
                datatype_values.push(dt.to_lean_json());
            }

            let wrapped_serialized_val = serde_json::json!({
                "SpecFns": spec_fns,
                "Datatypes": datatype_values,
                "FnName": func_display_name,
                "FuncCheckSst": serialized_val,
            });
            let _ = writeln!(file, "{}", wrapped_serialized_val.to_string());
            // let _ = serde_json::to_writer(file, &wrapped_serialized_val);
        //}
        

        // If "lean" is provided, then we add a Command to `state.commands`
        // to verify that the Lean proofs are correct.
        // CC: Still hash the serialization to ensure that the statement is
        //     correct?
        #[cfg(feature = "lean")]
        {

        }

        /*
        let f: crate::vlir::Theorem = crate::vlir::Theorem {
            name: path.clone().into(),
            typ_params: typ_params.clone(),
            params: crate::vlir::params(params.clone()).map_err(crate::messages::error_bare)?,
            require: reqs.clone().try_into().map_err(crate::messages::error_bare)?,
            ensure: Arc::new(post_condition.ens_exps.clone()).try_into().map_err(crate::messages::error_bare)?,
        };
        let path = std::env::current_dir().unwrap().join(
            format!("{}.json",
                path.krate.iter().chain(path.segments.iter())
                    .map(|x| x.as_ref().as_str()).collect::<Vec<&str>>().join("_")));
        let file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)
            .unwrap();

        let _ = serde_json::to_writer_pretty(file, &f);
        //if is_lean {
            let path = ctx.fun.as_ref().map(|x| x.current_fun.path.clone()).expect("lean call not in function context");
            let path: PathX = (*path.as_ref()).clone();
            let path = PathX {
                krate: path.krate,
                segments: {
                    //let mut orig = (*path.segments.as_ref()).clone();
                    let orig = (*path.segments.as_ref()).clone();
                    //orig.push(rand::random::<u16>().to_string().into());
                    orig.into()
                },
            };

            let path = std::env::current_dir().unwrap().join(
                format!("{}.json",
                    path.krate.iter().chain(path.segments.iter())
                        .map(|x| x.as_ref().as_str()).collect::<Vec<&str>>().join("_")));

            /*
            let mut file = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open(path)
                .unwrap();
            */

            //let _ = writeln!(file, "Hello world");
            //drop(file);
            // let _ = println!("Would have written to {}", path.display());
            //}
        */

    pub(crate) fn accumulate_fun_objects(exp: &ExpX, fun_accumulator: &mut HashSet<Fun>) {
    // println!("accumulating fun objects, exp={:?}", exp);
    match exp {
        ExpX::Call(CallFun::Fun(fun, _), _, _) => {
            fun_accumulator.insert(fun.clone());
        }
        ExpX::Bind(_, body) => {
            accumulate_fun_objects(&body.x, fun_accumulator);
        }
        ExpX::Unary(_, e) => {
            accumulate_fun_objects(&e.x, fun_accumulator);
        }
        ExpX::Binary(_, e1, e2) => {
            accumulate_fun_objects(&e1.x, fun_accumulator);
            accumulate_fun_objects(&e2.x, fun_accumulator);
        }
        ExpX::If(e1, e2, e3) => {
            accumulate_fun_objects(&e1.x, fun_accumulator);
            accumulate_fun_objects(&e2.x, fun_accumulator);
            accumulate_fun_objects(&e3.x, fun_accumulator);
        }
        _ => {}
    }
}
*/