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

// Synthetic and Analytic Expression Actions
let syn_action =
    (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
    : option((Zexp.t, Htyp.t)) => {
  // Used to suppress unused variable warnings
  // Okay to remove
  let _ = ctx;
  let _ = e;
  let _ = t;
  let _ = a;

  raise(Unimplemented);
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
