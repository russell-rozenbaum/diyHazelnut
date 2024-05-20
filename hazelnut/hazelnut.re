open Sexplib.Std;
open Monad_lib.Monad; 

let compare_string = String.compare;
let compare_int = Int.compare;

module Htyp = {
  [@deriving (sexp, compare)]
  type t =
    | Arrow(t, t)
    | Num
    | Hole;
};

module Hexp = {
  [@deriving (sexp, compare)]
  type t =
    | Var(string)
    | Lam(string, t)
    | Ap(t, t)
    | Lit(int)
    | Plus(t, t)
    | Asc(t, Htyp.t)
    | EHole
    | NEHole(t);
};

module Ztyp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Htyp.t)
    | LArrow(t, Htyp.t)
    | RArrow(Htyp.t, t);
};

module Zexp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Hexp.t)
    | Lam(string, t)
    | LAp(t, Hexp.t)
    | RAp(Hexp.t, t)
    | LPlus(t, Hexp.t)
    | RPlus(Hexp.t, t)
    | LAsc(t, Htyp.t)
    | RAsc(Hexp.t, Ztyp.t)
    | NEHole(t);
};

module Child = {
  [@deriving (sexp, compare)]
  type t =
    | One
    | Two;
};

module Dir = {
  [@deriving (sexp, compare)]
  type t =
    | Child(Child.t)
    | Parent;
};

module Shape = {
  [@deriving (sexp, compare)]
  type t =
    | Arrow
    | Num
    | Asc
    | Var(string)
    | Lam(string)
    | Ap
    | Lit(int)
    | Plus
    | NEHole;
};

module Action = {
  [@deriving (sexp, compare)]
  type t =
    | Move(Dir.t)
    | Construct(Shape.t)
    | Del
    | Finish;
};

module TypCtx = Map.Make(String);
type typctx = TypCtx.t(Htyp.t);

exception Unimplemented;

let rec erase_typ = (t: Ztyp.t) : Htyp.t => {
  switch(t) {
    | Cursor(ht) => ht
    | LArrow(t', ht) => Arrow(erase_typ(t'), ht)
    | RArrow(ht, t') => Arrow(ht, erase_typ(t'))
  }
}

// Expression Cursor Erasure
let rec erase_exp = (e: Zexp.t) : Hexp.t => {
  switch(e) {
    | Cursor(he') => he'
    | Lam(x, ze') => Lam(x, erase_exp(ze'))
    | LAp(ze', he') => Ap(erase_exp(ze'), he')
    | RAp(he', ze') => Ap(he', erase_exp(ze'))
    | LPlus(ze', he') => Plus(erase_exp(ze'), he')
    | RPlus(he', ze') => Plus(he', erase_exp(ze'))
    | LAsc(ze', ht') =>  Asc(erase_exp(ze'), ht')
    | RAsc(he', zt') => Asc(he', erase_typ(zt'))
    | NEHole(ze') => NEHole(erase_exp(ze'))
  }
};

// Function Type Matching
let matched_arrow = (t: Htyp.t) : (option(Htyp.t), option(Htyp.t)) => {
  switch(t) {
    // MAArr
    | Arrow(t_in, t_out) => (Some(t_in), Some(t_out))
    // MAHole
    | Hole => (Some(Hole), Some(Hole))
    // Exhaust
    | _ => (None, None);
  }
};

// Type Compatibility
let rec consistent = (t: Htyp.t, t': Htyp.t) : bool => {
  switch(t, t') {
    // TCHole1
    | (_, Hole) => true
    // TCHole2
    | (Hole, _) => true
    // TCArr
    | (Arrow(t_in, t_out), Arrow(t_in', t_out')) => 
    consistent(t_in, t_in') && consistent(t_out, t_out')
    // TCRefl
    | (_, _) => t == t'
  }
}

// Synthesis and Analysis
let rec syn = (ctx: typctx, e: Hexp.t): option(Htyp.t) => {
  switch (e) {
    // SVar
    | Var(x) => TypCtx.find_opt(x, ctx)
    // SAp
    | Ap(e_1, e_2) => 
      let* t = syn(ctx, e_1);
      let (t_in, t_out) = matched_arrow(t);
      switch (t_in) {
        | Some(t_in') => ana(ctx, e_2, t_in') ? t_out : None
        | _ => None
      }
    // SNum
    | Lit(_) => Some(Num)
    // SPlus
    | Plus(e_1, e_2) => (ana(ctx, e_1, Num) && ana(ctx, e_2, Num))
      ? Some(Num) : None
    // SAsc
    | Asc(e', t) => ana(ctx, e', t) ? Some(t) : None 
    // SHole
    | EHole => Some(Hole)
    // SNEHole
    | NEHole(e') => switch(syn(ctx, e')) {
      | Some(_) => Some(Hole)
      | _ => None
    }
    // Exhaust
    | _ => None
  }
}

and ana = (ctx: typctx, e: Hexp.t, t: Htyp.t): bool => {
  switch(e) {
    // ALam
    | Lam(x, e') => 
      let (t_in, t_out) = matched_arrow(t);
      switch(t_in, t_out) {
        | (Some(t_in'), Some(t_out')) => 
        let ctx' = TypCtx.add(x, t_in', ctx); 
        ana(ctx', e', t_out')
        | _ => false
      }
    // ASubsume
    | _ => 
      switch(syn(ctx, e)) {
        | Some(t') => consistent(t, t')
        | None => false
      }
  }
};

/* 
module Hexp = {
  [@deriving (sexp, compare)]
  type t =
    | Var(string)
    | Lam(string, t)
    | Ap(t, t)
    | Lit(int)
    | Plus(t, t)
    | Asc(t, Htyp.t)
    | EHole
    | NEHole(t);
};
*/

/*
module Zexp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Hexp.t)
    | Lam(string, t)
    | LAp(t, Hexp.t)
    | RAp(Hexp.t, t)
    | LPlus(t, Hexp.t)
    | RPlus(Hexp.t, t)
    | LAsc(t, Htyp.t)
    | RAsc(Hexp.t, Ztyp.t)
    | NEHole(t);
};
*/

/*
module Ztyp = {
  [@deriving (sexp, compare)]
  type t =
    | Cursor(Htyp.t)
    | LArrow(t, Htyp.t)
    | RArrow(Htyp.t, t);
};
*/

// Type Actions
let move_typ = (t: Ztyp.t, a: Action.t) : option(Ztyp.t) => {
  switch(a) {
    | Move(d) => switch(d, t) {
      | (Parent, LArrow(z_t_in, h_t_out)) => switch(z_t_in) {
        // TMArrParent1
        | Cursor(h_t_in) => Some(Cursor(Arrow(h_t_in, h_t_out)))
        // TMArrZip1
        | _ => move_typ(z_t_in, a)
      }
      | (Parent, RArrow(h_t_in, z_t_out)) => switch(z_t_out) {
        // TMArrParent2
        | Cursor(h_t_out) => Some(Cursor(Arrow(h_t_in, h_t_out)))
        // TMArrZip2
        | _ => move_typ(z_t_out, a)
      }
      | (Child(which), Cursor(h_t)) => switch(which, h_t) {
        // TMArrChild1
        | (One, Arrow(t_in, t_out)) => Some(Cursor(t_in))
        // TMArrChild2
        | (Two, Arrow(t_in, t_out)) => Some(Cursor(t_out))
        | _ => None
      }
      | _ => None
    }
    // TMDel
    | Del => Cursor(Hole)
    | Construct(s) => switch(s, t) {
      // TMConArrow
      | (Arrow, Cursor(h_t)) => Some(RArrow(h_t, Cursor(Hole)))
      | (Num, Cursor(h_t)) => switch(h_t) {
        // TMConNum
        | Hole => Some(Cursor(Num))
        | _ => None
      }
      | _ => None
    }
    | _ => None
  }
}

// Expression Movement Actions
let move_exp = (e: Zexp.t, d: Dir.t) : option(Zexp.t) => {
  switch(d) {
    | Parent => 
    switch(e) {
      // EMascParent1
    | LAsc(z_e, h_t) => Some(Cursor(Asc(erase_exp(z_e), h_t)))
    // EMascParent2
    | RAsc(h_e, z_t) => Some(Cursor(Asc(h_e, erase_typ(z_t))))
    // EMLamParent
    | Lam(x, z_e) => Some(Cursor(Lam(x, erase_exp(z_e))))
    // EMPlusParent1
    | LPlus(z_e, h_e) => Some(Cursor(Plus(erase_exp(z_e), h_e)))
    // EMPlusParent2
    | RPlus(h_e, z_e) => Some(Cursor(Plus(h_e, erase_exp(z_e))))
    // EMapParent1
    | LAp(z_e, h_e) => Some(Cursor(Ap(erase_exp(z_e), h_e)))
    // EmapParent2
    | RAp(h_e, z_e) => Some(Cursor(Ap(h_e, erase_exp(z_e))))
    // EMNEHoleParent
    | NEHole(z_e) => Some(Cursor(NEHole(erase_exp(z_e))))
    | _ => None
    }
    | Child(which) => 
    switch(e) {
      | Cursor(h_e) => 
      switch(which, h_e) {
        // EMAscChild1
        | (One, Asc(h_e, h_t)) => Some(LAsc(Cursor(h_e), h_t))
        // EMAscChild2
        | (Two, Asc(h_e, h_t)) => Some(RAsc(h_e, Cursor(h_t)))
        // EMLamChild1
        | (One, Lam(x, h_e)) => Some(Lam(x, Cursor(h_e)))
        // EMPlusChild1
        | (One, Plus(h_e_l, h_e_r)) => Some(LPlus(Cursor(h_e_l), h_e_r))
        // EMPlusChild2
        | (Two, Plus(h_e_r, h_e_l)) => Some(RPlus(h_e_l, Cursor(h_e_r)))
        // EMApChild1
        | (One, Ap(h_e_1, h_e_2)) => Some(LAp(Cursor(h_e_1), h_e_2))
        // EMApChild2
        | (Two, Ap(h_e_1, h_e_2)) => Some(RAp(h_e_1, Cursor(h_e_2)))
        // EMNEHoleChild1
        | (One, NEHole(h_e)) => Some(NEHole(Cursor(h_e)))
        | _ => None
      }
      | _ => None
    }
  }
}

/*
module Action = {
  [@deriving (sexp, compare)]
  type t =
    | Move(Dir.t)
    | Construct(Shape.t)
    | Del
    | Finish;
};
*/

/*
module Shape = {
  [@deriving (sexp, compare)]
  type t =
    | Arrow
    | Num
    | Asc
    | Var(string)
    | Lam(string)
    | Ap
    | Lit(int)
    | Plus
    | NEHole;
};
*/

// Synthetic and Analytic Expression Actions
let rec syn_action =
    (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
    : option((Zexp.t, Htyp.t)) => {
  switch(a) {
    // SAMove
    | Move(d) => switch(move_exp(e, d)) {
      | Some(z_e) => Some((z_e, t))
      | None => None
    }
    // SADel
    | Del => Some((Cursor(EHole), Hole))
    // SAFinish
    | Finish => switch(erase_exp(e)) {
      | NEHole(h_e) => switch(syn(ctx, h_e)) {
        | Some(h_t) => Some((Cursor(erase_exp(e)), h_t))
        | None => None 
      }
      | _ => None
    }
    | Construct(s) => switch(s) {
      // SAConApArr
      | Arrow => raise(Unimplemented)
      // SAConNumLit
      | Num => raise(Unimplemented)
      // SAConAsc
      | Asc => raise(Unimplemented)
      // SAConVar
      | Var(x) => let _ = x; raise(Unimplemented)
      // SAConLam
      | Lam(x) => let _ = x; raise(Unimplemented)
      // SAConApOtw
      | Ap => raise(Unimplemented)
      // SAConNumLit
      | Lit(n) => let _ = n; raise(Unimplemented)
      | Plus => raise(Unimplemented)
      | NEHole => raise(Unimplemented)
    }
  }
}

and ana_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;
  let _ = a;
  let _ = t;

  raise(Unimplemented);
};
