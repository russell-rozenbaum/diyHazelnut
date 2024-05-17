open Sexplib.Std;
open Monad_lib.Monad; // Uncomment this line to use the maybe monad

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
exception NoRuleApplies;

/* A.1.1 */
let rec consistent = (t: Htyp.t, t': Htyp.t): bool =>
  switch (t, t') {
  | (Num, Num) => true // TCRefl*
  | (Hole, _) => true // TCHole1
  | (_, Hole) => true // TCHole2
  | (Arrow(t1, t2), Arrow(t1', t2')) =>
    // TCArr
    consistent(t1, t1') && consistent(t2, t2')
  | _ => false
  };

let rec inconsistent = (t: Htyp.t, t': Htyp.t): bool =>
  switch (t, t') {
  | (Num, Arrow(_, _)) => true // ICNumArr1
  | (Arrow(_, _), Num) => true // ICNumArr2
  | (Arrow(t1, t2), Arrow(t1', t2')) =>
    // ICArr*
    inconsistent(t1, t1') || inconsistent(t2, t2')
  | _ => false
  };

/* A.1.2 */
let matched_arrow = (t: Htyp.t): option((Htyp.t, Htyp.t)) =>
  switch (t) {
  | Hole => Some((Hole, Hole)) // MAHole
  | Arrow(t1, t2) => Some((t1, t2)) // MAArr
  | _ => None
  };

/* A.1.3 */
let rec syn = (ctx: typctx, e: Hexp.t): option(Htyp.t) => {
  switch (e) {
  | Asc(e, t) =>
    // SAsc
    if (ana(ctx, e, t)) {
      Some(t);
    } else {
      None;
    }
  | Var(x) => Some(TypCtx.find(x, ctx)) // SVar
  | Ap(e1, e2) =>
    // SAp
    let* t = syn(ctx, e1);
    let* (t2, t') = matched_arrow(t);
    if (ana(ctx, e2, t2)) {
      Some(t');
    } else {
      None;
    };
  | Lit(_) => Some(Num) // SNum
  | Plus(e1, e2) =>
    // SPlus
    if (ana(ctx, e1, Num) && ana(ctx, e2, Num)) {
      Some(Num);
    } else {
      None;
    }
  | EHole => Some(Hole) // SHole
  | NEHole(e) =>
    // SNEHole
    let* _ = syn(ctx, e);
    Some(Htyp.Hole);
  | _ => None
  };
}

and ana = (ctx: typctx, e: Hexp.t, t: Htyp.t): bool => {
  switch (syn(ctx, e)) {
  | Some(t') => consistent(t, t') // ASubsume
  | None =>
    switch (e, matched_arrow(t)) {
    // ALam
    | (Lam(x, e), Some((t1, t2))) => ana(TypCtx.add(x, t1, ctx), e, t2)
    | _ => false
    }
  };
};

/* A.2.1 */
let rec erase_typ = (t: Ztyp.t): Htyp.t => {
  switch (t) {
  | Cursor(t) => t // ETTop
  | LArrow(t', t) => Arrow(erase_typ(t'), t) // ETArrL
  | RArrow(t, t') => Arrow(t, erase_typ(t')) // ETArrR
  };
};

/* A.2.2 */
let rec erase_exp = (e: Zexp.t): Hexp.t => {
  switch (e) {
  | Cursor(e) => e // EETop
  | LAsc(e', t) => Asc(erase_exp(e'), t) // EEAscL
  | RAsc(e, t') => Asc(e, erase_typ(t')) // EEAscR
  | Lam(s, e') => Lam(s, erase_exp(e')) // EELam
  | LAp(e', e) => Ap(erase_exp(e'), e) // EEApL
  | RAp(e, e') => Ap(e, erase_exp(e')) // EEApR
  | LPlus(e', e) => Plus(erase_exp(e'), e) // EEPlusL
  | RPlus(e, e') => Plus(e, erase_exp(e')) // EEPlusR
  | NEHole(e') => NEHole(erase_exp(e')) // EENEHole
  };
};

/* A.3.1 */
let rec typ_action = (t: Ztyp.t, a: Action.t): option(Ztyp.t) => {
  switch (t, a) {
  | (Cursor(Arrow(t1, t2)), Move(Child(One))) =>
    // TMArrChild1
    Some(Ztyp.LArrow(Cursor(t1), t2))
  | (Cursor(Arrow(t1, t2)), Move(Child(Two))) =>
    // TMArrChild2
    Some(Ztyp.RArrow(t1, Cursor(t2)))
  | (LArrow(Cursor(t1), t2), Move(Parent)) =>
    // TMArrParent1
    Some(Cursor(Arrow(t1, t2)))
  | (RArrow(t1, Cursor(t2)), Move(Parent)) =>
    // TMArrParent2
    Some(Cursor(Arrow(t1, t2)))
  | (Cursor(_), Del) => Some(Cursor(Hole)) // TMDel
  | (Cursor(t), Construct(Arrow)) =>
    // TMConsArr
    Some(RArrow(t, Cursor(Hole)))
  | (Cursor(Hole), Construct(Num)) =>
    // TMConsNum
    Some(Cursor(Num))
  | (LArrow(t', t), _) =>
    // TMArrZip1
    let* t' = typ_action(t', a);
    Some(Ztyp.LArrow(t', t));
  | (RArrow(t, t'), _) =>
    // TMArrZip2
    let* t' = typ_action(t', a);
    Some(Ztyp.RArrow(t, t'));
  | _ => None
  };
}

/* A.3.2 */
and exp_action = (e: Zexp.t, d: Dir.t): option(Zexp.t) => {
  switch (e, d) {
  | (Cursor(Asc(e, t)), Child(One)) =>
    // EMAscChild1
    Some(LAsc(Cursor(e), t))
  | (Cursor(Asc(e, t)), Child(Two)) =>
    // EMAscChild2
    Some(RAsc(e, Cursor(t)))
  | (LAsc(Cursor(e), t), Parent) =>
    // EMAscParent1
    Some(Cursor(Asc(e, t)))
  | (RAsc(e, Cursor(t)), Parent) =>
    // EMAscParent2
    Some(Cursor(Asc(e, t)))
  | (Cursor(Lam(x, e)), Child(One)) =>
    // EMLamChild1
    Some(Lam(x, Cursor(e)))
  | (Lam(x, Cursor(e)), Parent) =>
    // EMLamParent
    Some(Cursor(Lam(x, e)))
  | (Cursor(Plus(e1, e2)), Child(One)) =>
    // EMPlusChild1
    Some(LPlus(Cursor(e1), e2))
  | (Cursor(Plus(e1, e2)), Child(Two)) =>
    // EMPlusChild2
    Some(RPlus(e1, Cursor(e2)))
  | (LPlus(Cursor(e1), e2), Parent) =>
    // EMPlusParent1
    Some(Cursor(Plus(e1, e2)))
  | (RPlus(e1, Cursor(e2)), Parent) =>
    // EMPlusParent2
    Some(Cursor(Plus(e1, e2)))
  | (Cursor(Ap(e1, e2)), Child(One)) =>
    // EMApChild1
    Some(LAp(Cursor(e1), e2))
  | (Cursor(Ap(e1, e2)), Child(Two)) =>
    // EMApChild2
    Some(RAp(e1, Cursor(e2)))
  | (LAp(Cursor(e1), e2), Parent) =>
    // EMApParent1
    Some(Cursor(Ap(e1, e2)))
  | (RAp(e1, Cursor(e2)), Parent) =>
    // EMApParent2
    Some(Cursor(Ap(e1, e2)))
  | (Cursor(NEHole(e)), Child(One)) =>
    // EMNEHoleChild1
    Some(NEHole(Cursor(e)))
  | (NEHole(Cursor(e)), Parent) =>
    // EMNEHoleParent
    Some(Cursor(NEHole(e)))
  | _ => None
  };
};

/* A.3.3 */
let rec syn_action =
        (ctx: typctx, (e: Zexp.t, t: Htyp.t), a: Action.t)
        : option((Zexp.t, Htyp.t)) => {
  switch (e, t, a) {
  | (_, _, Move(d)) =>
    // SAMove
    let* e' = exp_action(e, d);
    Some((e', t));
  | (Cursor(_), _, Del) =>
    // SADel
    Some((Cursor(EHole), Hole))
  | (Cursor(e), _, Construct(Asc)) =>
    // SAConAsc
    Some((RAsc(e, Cursor(t)), t))
  | (Cursor(EHole), Hole, Construct(Var(x))) =>
    // SAConVar
    Some((Cursor(Var(x)), TypCtx.find(x, ctx)))
  | (Cursor(EHole), Hole, Construct(Lam(x))) =>
    // SAConLam
    Some((
      RAsc(Lam(x, EHole), LArrow(Cursor(Hole), Hole)),
      Arrow(Hole, Hole),
    ))
  | (Cursor(e), _, Construct(Ap)) =>
    // SAConApArr
    switch (matched_arrow(t)) {
    | Some((_, t2)) =>
      // SAConApArr
      Some((RAp(e, Cursor(EHole)), t2))
    | None =>
      // SAConApOtw
      Some((RAp(NEHole(e), Cursor(EHole)), Hole))
    }
  | (Cursor(_), Hole, Construct(Lit(n))) =>
    // SAConNumLit
    Some((Cursor(Lit(n)), Num))
  | (Cursor(e), _, Construct(Plus)) =>
    if (consistent(t, Num)) {
      // SAConPlus1
      Some((RPlus(e, Cursor(EHole)), Num));
    } else {
      // SAConPlus2
      Some((RPlus(NEHole(e), Cursor(EHole)), Num));
    }
  | (Cursor(e), _, Construct(NEHole)) =>
    // SAConNEHole
    Some((NEHole(Cursor(e)), Hole))
  | (Cursor(NEHole(e)), Hole, Finish) =>
    // SAFinish
    let* t' = syn(ctx, e);
    Some((Zexp.Cursor(e), t'));
  | (LAsc(e', _), _, _) =>
    // SAZipAsc1 // TODO: Check if this is correct
    let* e' = ana_action(ctx, e', a, t);
    Some((Zexp.LAsc(e', t), t));
  | (RAsc(e, t'), _, _) =>
    // SAZipAsc2 // TODO: Check if this is correct
    let* t' = typ_action(t', a);
    if (ana(ctx, e, erase_typ(t'))) {
      Some((Zexp.RAsc(e, t'), erase_typ(t')));
    } else {
      None;
    };
  | (LAp(e', e), _, _) =>
    // SAZipApArr
    let* t2 = syn(ctx, erase_exp(e'));
    let* (e', t3) = syn_action(ctx, (e', t2), a);
    let* (t4, t5) = matched_arrow(t3);
    if (ana(ctx, e, t4)) {
      Some((Zexp.LAp(e', e), t5));
    } else {
      None;
    };
  | (RAp(e, e'), _, _) =>
    // SAZipApAna
    let* t2 = syn(ctx, e);
    let* (t3, t4) = matched_arrow(t2);
    let* e' = ana_action(ctx, e', a, t3);
    Some((Zexp.RAp(e, e'), t4));
  | (LPlus(e', e), Num, _) =>
    // SAZipPlus1
    let* e' = ana_action(ctx, e', a, Num);
    Some((Zexp.LPlus(e', e), Htyp.Num));
  | (RPlus(e, e'), Num, _) =>
    // SAZipPlus2
    let* e' = ana_action(ctx, e', a, Num);
    Some((Zexp.RPlus(e, e'), Htyp.Num));
  | (NEHole(e'), Hole, _) =>
    // SAZipNEHole
    let* t = syn(ctx, erase_exp(e'));
    let* (e', t') = syn_action(ctx, (e', t), a);
    Some((Zexp.NEHole(e'), t'));
  | _ => None
  };
}

and ana_action =
    (ctx: typctx, e: Zexp.t, a: Action.t, t: Htyp.t): option(Zexp.t) => {
  switch (e, t, a) {
  | (e', _, Move(d)) =>
    // AAMove
    exp_action(e', d)
  | (Cursor(_), _, Del) =>
    // AADel
    Some(Cursor(EHole))
  | (Cursor(e), _, Construct(Asc)) =>
    // AAConAsc
    Some(RAsc(e, Cursor(t)))
  | (Cursor(EHole), _, Construct(Var(x))) =>
    // AAConVar
    let t' = TypCtx.find(x, ctx);
    if (inconsistent(t, t')) {
      Some(NEHole(Cursor(Var(x))));
    } else {
      None;
    }; // FIXME: This could be a bug
  | (Cursor(EHole), _, Construct(Lam(x))) =>
    switch (matched_arrow(t)) {
    | Some((_, _)) =>
      // AAConLam1
      Some(Zexp.Lam(x, Cursor(EHole)))
    | None =>
      // AAConLam2
      Some(NEHole(RAsc(Lam(x, EHole), LArrow(Cursor(Hole), Hole))))
    }
  | (Cursor(EHole), _, Construct(Lit(n))) =>
    // AAConNumLit
    if (inconsistent(t, Num)) {
      Some(NEHole(Cursor(Lit(n))));
    } else {
      None;
    } // FIXME: This could be a bug
  | (Cursor(e), _, Finish) =>
    // AAFinish
    if (ana(ctx, e, t)) {
      Some(Cursor(e));
    } else {
      None;
    }
  | (Lam(x, e'), _, _) =>
    // AAZipLam
    let* (t1, t2) = matched_arrow(t);
    let* e' = ana_action(TypCtx.add(x, t1, ctx), e', a, t2);
    Some(Zexp.Lam(x, e'));
  | (_, _, _) =>
    // AASubsume
    let* t' = syn(ctx, erase_exp(e));
    let* (e', t'') = syn_action(ctx, (e, t'), a);
    if (consistent(t, t'')) {
      Some(e');
    } else {
      None;
    };
  };
};
