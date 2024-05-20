open Sexplib.Std;
// open Monad_lib.Monad; 

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
let matched_arrow = (t: Htyp.t) : option((Htyp.t, Htyp.t)) => {
  switch(t) {
    // MAArr
    | Arrow(t_in, t_out) => Some((t_in, t_out))
    // MAHole
    | Hole => Some((Hole, Hole))
    // Exhaust
    | _ => None;
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
    switch(syn(ctx, e_1)) {
      | Some(t) => switch(matched_arrow(t)) {
        | Some((t_in, t_out)) => ana(ctx, e_2, t_in) ? Some(t_out) : None
        | None => None
      }
      | None => None
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
      switch(matched_arrow(t)) {
        | Some((t_in, t_out)) => ana(TypCtx.add(x, t_in, ctx), e', t_out)
        | None => false
      }
    // ASubsume
    | _ => 
      switch(syn(ctx, e)) {
        | Some(t') => consistent(t, t')
        | None => false
      }
  }
};

// Type Actions
let rec typ_action = (t: Ztyp.t, a: Action.t) : option(Ztyp.t) => {
  switch(a) {
    | Move(d) => switch(d, t) {
      | (Parent, LArrow(z_t_in, h_t_out)) => switch(z_t_in) {
        // TMArrParent1
        | Cursor(h_t_in) => Some(Cursor(Arrow(h_t_in, h_t_out)))
        // TMArrZip1
        | _ => typ_action(z_t_in, a)
      }
      | (Parent, RArrow(h_t_in, z_t_out)) => switch(z_t_out) {
        // TMArrParent2
        | Cursor(h_t_out) => Some(Cursor(Arrow(h_t_in, h_t_out)))
        // TMArrZip2
        | _ => typ_action(z_t_out, a)
      }
      | (Child(which), Cursor(h_t)) => switch(which, h_t) {
        // TMArrChild1
        | (One, Arrow(t_in, _)) => Some(Cursor(t_in))
        // TMArrChild2
        | (Two, Arrow(_, t_out)) => Some(Cursor(t_out))
        | _ => None
      }
      | _ => None
    }
    // TMDel
    | Del => Some(Cursor(Hole))
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

// Synthetic and Analytic Expression Actions
let rec syn_action =
    (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
    : option((Zexp.t, Htyp.t)) => {
      switch(e, a) {
        // SADel
        | (Cursor(_), Del) => Some((Cursor(EHole), Hole))
        // SAfinish
        | (Cursor(h_e), Finish) => switch(h_e) {
          | NEHole(h_e) => switch(syn(ctx, h_e)) {
            | Some(h_t) => Some((Cursor(h_e), h_t))
            | None => None
          }
          | _ => None
        }
        // Construction
        | (Cursor(h_e), Construct(s)) => switch(s) {
          // SAConAsc
          | Asc => Some((RAsc(h_e, Cursor(t)), t))
          // SAConVar
          | Var(x) => switch(h_e) {
            | EHole => Some((Cursor(Var(x)), t))
            | _ => None
          }
          // SAConLam
          | Lam(x) => switch(h_e) {
            | EHole => 
            Some((RAsc(Lam(x, EHole), LArrow(Cursor(Hole), Hole)), Arrow(Hole, Hole)))
            | _ => None
          }
          // SAConApOtw : SAConApArr
          | Ap => raise(Unimplemented)
          // SAConNumLit
          | Lit(n) => switch(h_e) {
            | EHole => Some((Cursor(Lit(n)), Num))
            | _ => None
          }
          // SAConPlus1 : SAConPlus2
          | Plus => consistent(t, Num) ? 
          Some((RPlus(h_e, Cursor(EHole)), Num)) : 
          Some((RPlus(NEHole(h_e), Cursor(EHole)), Num))
          | NEHole => Some((NEHole(Cursor(h_e)), Hole))
          | _ => None
        }
        // SAMove
        | (_, Move(d)) => switch(move_exp(e, d)) {
          | Some(z_e) => Some((z_e, t))
          | None => None
        }
        // Zipper Cases
        | _ => switch(e) {
          // SAZipAsc1
          | LAsc(z_e, h_t) => 
          switch(ana_action(ctx, z_e, a, t)) {
            | Some(z_e') => syn_action(ctx, (LAsc(z_e', h_t), t), a)
            | None => None
          }
          // SAZipAsc2
          | RAsc(h_e, z_t) => 
          switch(typ_action(z_t, a)) {
            | Some(z_t') => ana(ctx, h_e, erase_typ(z_t')) ? 
            syn_action(ctx, (RAsc(h_e, z_t'), erase_typ(z_t')), a) : None
            | None => None
          }
          // SAZipApArr
          | LAp(z_e, h_e) => 
          switch(syn(ctx, erase_exp(z_e))) {
            | Some(t_2) => switch(syn_action(ctx, (z_e, t_2), a)) {
              | Some((z_e', t_3)) => switch(matched_arrow(t_3)) {
                | Some((t_4, t_5)) => 
                ana(ctx, h_e, t_4) ? 
                syn_action(ctx, (LAp(z_e', h_e), t_5), a) : None
                | None => None
              }
              | None => None
            }
            | None => None
          }
          // SAZipApAna
          | RAp(h_e, z_e) => switch(syn(ctx, h_e)) {
            | Some(t_2) => switch(matched_arrow(t_2)) {
              | Some((t_3, t_4)) => switch(ana_action(ctx, z_e, a, t_3)) {
                | Some(z_e') => syn_action(ctx, (RAp(h_e, z_e'), t_4), a)
                | None => None
              }
              | None => None
            }
            | None => None
          }
          // SAZipPlus1
          | LPlus(z_e, h_e) => switch(ana_action(ctx, z_e, a, Num)) {
            | Some(z_e') => syn_action(ctx, (LPlus(z_e', h_e), Num), a)
            | None => None
          }
          // SAZipPlus2
          | RPlus(h_e, z_e) => switch(ana_action(ctx, z_e, a, Num)) {
            | Some(z_e') => syn_action(ctx, (RPlus(h_e, z_e'), Num), a)
            | None => None
          }
          // SAZipHole
          | NEHole(z_e) => switch(syn(ctx, erase_exp(z_e))) {
            | Some(h_t) => switch(syn_action(ctx, (z_e, h_t), a)) {
              | Some((z_e', _)) => syn_action(ctx, (NEHole(z_e'), Hole), a)
              | None => None
            }
            | None => None
          }
          // Exhaust
          | _ => None
        }
      }
    }

and ana_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  switch(e, a) {
    // AAMove
    | (_, Move(d)) => move_exp(e, d)
    // AADel
    | (Cursor(_), Del) => Some(Cursor(EHole))
    // Construction
    | (Cursor(h_e), Construct(s)) => 
    switch(h_e, s) {
      // AAConAsc
      | (_, Asc) => Some(RAsc(h_e, Cursor(t)))
      // AAConVar
      | (EHole, Var(x)) => consistent(TypCtx.find(x, ctx), t) ? 
      None : Some(NEHole(Cursor(Var(x))))
      // AAConLam1 : AAConLam2
      | (EHole, Lam(x)) => switch(matched_arrow(t)) {
        | Some((_, _)) => Some(Lam(x, Cursor(EHole)))
        | None => Some(NEHole(RAsc(Lam(x, EHole), LArrow(Cursor(Hole), Hole))))
      }
      // AAConNumLit
      | (EHole, Lit(n)) => consistent(t, Num) ? None : Some(NEHole(Cursor(Lit(n))))
      | _ => None
    }
    // AAFinish
    | (Cursor(h_e), Finish) => switch(h_e) {
      | NEHole(h_e) => ana(ctx, h_e, t) ? Some(Cursor(h_e)) : None
      | _ => None
    }
    // Zipper Case
    // AAZipLam
    | (Lam(x, z_e) , _) => switch(matched_arrow(t)) {
      | Some((t_1, t_2)) => switch(ana_action(TypCtx.add(x, t_1, ctx), z_e, a, t_2)) {
        | Some(z_e') => Some(Lam(x, z_e'))
        | None => None 
      }
      | None => None
    }
    // Exhaust
    | _ => None
  }
};
