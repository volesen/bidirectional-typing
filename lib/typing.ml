open Syntax

let lookup = List.assoc

let extend = List.cons

type constr = ty * ty

let fresh =
  let counter = ref 0 in
  fun () -> incr counter ; TVar !counter

(** [check ctx e t] returns a list of constraints that must hold for [e] to have
    type [t] in context [ctx]. *)
let rec check ctx e t : constr list =
  match (e, t) with
  | EInt _, TInt ->
      []
  | EBool _, TBool ->
      []
  | EVar x, ty ->
      [(lookup x ctx, ty)]
  | EFun (x, e), TArr (ty1, ty2) ->
      check (extend (x, ty1) ctx) e ty2
  | _ ->
      let t', constr = infer ctx e in
      (t', t) :: constr

(** [infer ctx e] returns a pair [(t, constr)] where [t] is the type of [e] in
    context [ctx] and [constr] is a list of constraints that must hold for [e]
    to have type [t]. *)
and infer ctx e : ty * constr list =
  match e with
  | EInt _ ->
      (TInt, [])
  | EBool _ ->
      (TBool, [])
  | EVar x ->
      (lookup x ctx, [])
  | EApp (func, arg) ->
      let arg_ty, arg_constr = infer ctx arg in
      let ret_ty = fresh () in
      let func_ty = TArr (arg_ty, ret_ty) in
      let func_constr = check ctx func func_ty in
      (ret_ty, arg_constr @ func_constr)
  | EFun (x, e) ->
      let arg_ty = fresh () in
      let ret_ty, constr = infer (extend (x, arg_ty) ctx) e in
      (TArr (arg_ty, ret_ty), constr)
  | ELet (x, e1, e2) ->
      let e1_ty, e1_constr = infer ctx e1 in
      let e2_ty, e2_constr = infer (extend (x, e1_ty) ctx) e2 in
      (e2_ty, e1_constr @ e2_constr)
  | EBinop ((Add | Sub), e1, e2) ->
      let e2_constr = check ctx e2 TInt in
      let e1_constr = check ctx e1 TInt in
      (TInt, e1_constr @ e2_constr)
  | EIf (e1, e2, e3) ->
      let e1_constr = check ctx e1 TBool in
      let e2_ty, e2_constr = infer ctx e2 in
      let e3_constr = check ctx e3 e2_ty in
      (e2_ty, e1_constr @ e2_constr @ e3_constr)

(** [occurs x t] returns [true] if [x] occurs in [t] *)
let rec occurs x t =
  match t with
  | TInt | TBool ->
      false
  | TVar y ->
      x = y
  | TArr (t1, t2) ->
      occurs x t1 || occurs x t2

(** [subst x t t'] returns [t'] with all occurrences of [x] replaced by [t]. *)
let rec subst x t t' =
  match t' with
  | TInt | TBool ->
      t'
  | TVar y ->
      if x = y then t else t'
  | TArr (t1, t2) ->
      TArr (subst x t t1, subst x t t2)

let subst_constr x t (t1, t2) = (subst x t t1, subst x t t2)

exception Infinite_type

exception Unification_failed of constr

(** [unify constrs] returns a substitution that satisfies all the constraints in
    [constrs]. *)
let rec unify constrs =
  match constrs with
  | [] ->
      []
  | (t1, t2) :: constrs' when t1 = t2 ->
      unify constrs'
  | (TVar x, t) :: _ when occurs x t ->
      raise Infinite_type
  | (t, TVar x) :: _ when occurs x t ->
      raise Infinite_type
  | (TVar x, t) :: constrs' ->
      (x, t) :: unify (List.map (subst_constr x t) constrs')
  | (t, TVar x) :: constrs' ->
      (x, t) :: unify (List.map (subst_constr x t) constrs')
  | (TArr (t1, t2), TArr (t1', t2')) :: constrs' ->
      unify ((t1, t1') :: (t2, t2') :: constrs')
  | constr :: _ ->
      raise (Unification_failed constr)

(** [infer_top ctx e] returns the type of [e] in context [ctx] or raises
    [Infinite_type] or [Unification_failed] if inference fails. *)
let infer_top ctx e =
  let t, constr = infer ctx e in
  let substs = unify constr in
  (* Apply the substitution to the type of the expression *)
  let t' = List.fold_right (fun (x, t) t' -> subst x t t') substs t in
  t'
