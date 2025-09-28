Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Strings.String.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Program.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Record qualified_column : Type := {
  table_name : option string;
  column_name : string
}.

Definition make_column (name : string) : qualified_column :=
  {| table_name := None; column_name := name |}.

Definition make_qualified_column (tbl : string) (col : string) : qualified_column :=
  {| table_name := Some tbl; column_name := col |}.

Definition qualified_column_eqb (c1 c2 : qualified_column) : bool :=
  match c1.(table_name), c2.(table_name) with
  | None, None => String.eqb c1.(column_name) c2.(column_name)
  | Some t1, Some t2 =>
      andb (String.eqb t1 t2) (String.eqb c1.(column_name) c2.(column_name))
  | _, _ => false
  end.

Lemma qualified_column_eqb_refl : forall c,
  qualified_column_eqb c c = true.
Proof.
  intros c.
  unfold qualified_column_eqb.
  destruct (table_name c).
  - rewrite String.eqb_refl. rewrite String.eqb_refl. reflexivity.
  - rewrite String.eqb_refl. reflexivity.
Qed.

Lemma qualified_column_eqb_spec : forall c1 c2,
  reflect (c1 = c2) (qualified_column_eqb c1 c2).
Proof.
  intros [t1 n1] [t2 n2]; simpl.
  unfold qualified_column_eqb; simpl.
  destruct t1 as [s1|], t2 as [s2|].
  - destruct (String.eqb_spec s1 s2); simpl.
    + subst. destruct (String.eqb_spec n1 n2).
      * subst. constructor. reflexivity.
      * constructor. intros H. injection H. contradiction.
    + constructor. intros H. injection H. intros. contradiction.
  - constructor. discriminate.
  - constructor. discriminate.
  - destruct (String.eqb_spec n1 n2).
    + subst. constructor. reflexivity.
    + constructor. intros H. injection H. contradiction.
Qed.

Inductive sql_type : Type :=
  | TInt : sql_type
  | TString : sql_type
  | TBool : sql_type.

Inductive sql_value : Type :=
  | VInt : Z -> sql_value
  | VString : string -> sql_value
  | VBool : bool -> sql_value
  | VNull : sql_type -> sql_value.

Definition value_type (v : sql_value) : sql_type :=
  match v with
  | VInt _ => TInt
  | VString _ => TString
  | VBool _ => TBool
  | VNull t => t
  end.

Definition schema := list (qualified_column * sql_type).

Record typed_tuple : Type := {
  tuple_schema : schema;
  tuple_data : list (option sql_value);
  tuple_wf : List.length tuple_data = List.length tuple_schema /\
             forall i v, nth_error tuple_data i = Some (Some v) ->
                        exists c t, nth_error tuple_schema i = Some (c, t) /\
                                   value_type v = t
}.

Definition tuple_total (t : typed_tuple) : Prop :=
  forall i c ty,
    nth_error t.(tuple_schema) i = Some (c, ty) ->
    exists v, nth_error t.(tuple_data) i = Some (Some v) /\ value_type v = ty.

Inductive tri : Type :=
  | TrueT : tri
  | FalseT : tri
  | UnknownT : tri.

Definition tri_and (a b : tri) : tri :=
  match a, b with
  | TrueT, TrueT => TrueT
  | FalseT, _ => FalseT
  | _, FalseT => FalseT
  | _, _ => UnknownT
  end.

Definition tri_or (a b : tri) : tri :=
  match a, b with
  | TrueT, _ => TrueT
  | _, TrueT => TrueT
  | FalseT, FalseT => FalseT
  | _, _ => UnknownT
  end.

Definition tri_not (a : tri) : tri :=
  match a with
  | TrueT => FalseT
  | FalseT => TrueT
  | UnknownT => UnknownT
  end.

Definition tri_to_bool (t : tri) : bool :=
  match t with
  | TrueT => true
  | _ => false
  end.

Fixpoint find_column_index (s : schema) (col : qualified_column) : option nat :=
  match s with
  | [] => None
  | (c, _) :: rest =>
      if qualified_column_eqb c col then Some 0
      else match find_column_index rest col with
           | Some n => Some (S n)
           | None => None
           end
  end.

Definition get_typed_value (t : typed_tuple) (col : qualified_column) : option sql_value :=
  match find_column_index t.(tuple_schema) col with
  | Some idx =>
      match nth_error t.(tuple_data) idx with
      | Some v => v
      | None => None
      end
  | None => None
  end.

Definition unique_schema (s : schema) : Prop :=
  forall i j c t1 t2,
    i <> j ->
    nth_error s i = Some (c, t1) ->
    nth_error s j = Some (c, t2) ->
    False.

Lemma find_column_index_bounds : forall s col n,
  find_column_index s col = Some n -> n < List.length s.
Proof.
  induction s as [| [q st] s' IH]; intros col n H.
  - simpl in H. discriminate.
  - simpl in H.
    destruct (qualified_column_eqb q col) eqn:Eq.
    + inversion H. subst. simpl. unfold Nat.lt. apply le_n_S. apply le_0_n.
    + simpl. destruct (find_column_index s' col) as [m|] eqn:E.
      * inversion H. subst. unfold Nat.lt. apply le_n_S.
        specialize (IH col m E). exact IH.
      * discriminate.
Qed.

Lemma find_column_index_correct : forall s col i,
  unique_schema s ->
  find_column_index s col = Some i ->
  exists t, nth_error s i = Some (col, t).
Proof.
  induction s as [| [c t] s' IH]; intros col i Huniq Hfind.
  - simpl in Hfind. discriminate.
  - simpl in Hfind.
    destruct (qualified_column_eqb c col) eqn:Heqb.
    + destruct (qualified_column_eqb_spec c col).
      * inversion Hfind. subst.
        simpl. exists t. reflexivity.
      * discriminate.
    + destruct (find_column_index s' col) as [n|] eqn:Hfind'.
      * inversion Hfind. subst.
        simpl.
        assert (Huniq': unique_schema s').
        { intros i j c' t1 t2 Hneq Hi Hj.
          apply (Huniq (S i) (S j) c' t1 t2).
          - intros H. injection H. contradiction.
          - exact Hi.
          - exact Hj. }
        specialize (IH col n Huniq' Hfind').
        destruct IH as [t' Hnth].
        exists t'. exact Hnth.
      * discriminate.
Qed.

Inductive typed_expr : sql_type -> Type :=
  | TECol : forall t, qualified_column -> typed_expr t
  | TEInt : Z -> typed_expr TInt
  | TEString : string -> typed_expr TString
  | TEBool : bool -> typed_expr TBool
  | TENull : forall t, typed_expr t
  | TEEq : forall t, typed_expr t -> typed_expr t -> typed_expr TBool
  | TELt : typed_expr TInt -> typed_expr TInt -> typed_expr TBool
  | TEAnd : typed_expr TBool -> typed_expr TBool -> typed_expr TBool
  | TEOr : typed_expr TBool -> typed_expr TBool -> typed_expr TBool
  | TENot : typed_expr TBool -> typed_expr TBool
  | TEIsNull : forall t, typed_expr t -> typed_expr TBool
  | TEIsDistinctFrom : forall t, typed_expr t -> typed_expr t -> typed_expr TBool.

Definition sql_type_eq_dec (t1 t2 : sql_type) : {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Defined.

Definition sql_value_is_distinct_from (v1 v2 : sql_value) : bool :=
  match v1, v2 with
  | VNull t1, VNull t2 =>
      if sql_type_eq_dec t1 t2 then false else true
  | VNull _, _ => true
  | _, VNull _ => true
  | VInt n1, VInt n2 => negb (Z.eqb n1 n2)
  | VString s1, VString s2 => negb (String.eqb s1 s2)
  | VBool b1, VBool b2 => negb (Bool.eqb b1 b2)
  | _, _ => true
  end.

Definition tri_of_bool (b : bool) : tri :=
  if b then TrueT else FalseT.

Definition sql_eq_tri (v1 v2 : sql_value) : tri :=
  match v1, v2 with
  | VNull _, _ => UnknownT
  | _, VNull _ => UnknownT
  | VInt n1, VInt n2 => tri_of_bool (Z.eqb n1 n2)
  | VString s1, VString s2 => tri_of_bool (String.eqb s1 s2)
  | VBool b1, VBool b2 => tri_of_bool (Bool.eqb b1 b2)
  | _, _ => UnknownT
  end.

Definition sql_lt_tri (v1 v2 : sql_value) : tri :=
  match v1, v2 with
  | VNull _, _ => UnknownT
  | _, VNull _ => UnknownT
  | VInt n1, VInt n2 => tri_of_bool (Z.ltb n1 n2)
  | _, _ => UnknownT
  end.

Fixpoint eval_expr {t : sql_type} (e : typed_expr t) (tu : typed_tuple) {struct e} : option sql_value :=
  match e with
  | TECol _ c => get_typed_value tu c
  | TEInt n => Some (VInt n)
  | TEString s => Some (VString s)
  | TEBool b => Some (VBool b)
  | TENull t' => Some (VNull t')
  | TEEq _ e1 e2 =>
      match @eval_expr _ e1 tu, @eval_expr _ e2 tu with
      | Some v1, Some v2 =>
          Some (match sql_eq_tri v1 v2 with
                | TrueT => VBool true
                | FalseT => VBool false
                | UnknownT => VNull TBool
                end)
      | _, _ => None
      end
  | TELt e1 e2 =>
      match @eval_expr _ e1 tu, @eval_expr _ e2 tu with
      | Some v1, Some v2 =>
          Some (match sql_lt_tri v1 v2 with
                | TrueT => VBool true
                | FalseT => VBool false
                | UnknownT => VNull TBool
                end)
      | _, _ => None
      end
  | TEAnd e1 e2 =>
      let t1 := match @eval_expr TBool e1 tu with
                | Some (VBool b) => if b then TrueT else FalseT
                | Some (VNull TBool) => UnknownT
                | _ => UnknownT
                end in
      let t2 := match @eval_expr TBool e2 tu with
                | Some (VBool b) => if b then TrueT else FalseT
                | Some (VNull TBool) => UnknownT
                | _ => UnknownT
                end in
      Some (match tri_and t1 t2 with
            | TrueT => VBool true
            | FalseT => VBool false
            | UnknownT => VNull TBool
            end)
  | TEOr e1 e2 =>
      let t1 := match @eval_expr TBool e1 tu with
                | Some (VBool b) => if b then TrueT else FalseT
                | Some (VNull TBool) => UnknownT
                | _ => UnknownT
                end in
      let t2 := match @eval_expr TBool e2 tu with
                | Some (VBool b) => if b then TrueT else FalseT
                | Some (VNull TBool) => UnknownT
                | _ => UnknownT
                end in
      Some (match tri_or t1 t2 with
            | TrueT => VBool true
            | FalseT => VBool false
            | UnknownT => VNull TBool
            end)
  | TENot e1 =>
      let t1 := match @eval_expr TBool e1 tu with
                | Some (VBool b) => if b then TrueT else FalseT
                | Some (VNull TBool) => UnknownT
                | _ => UnknownT
                end in
      Some (match tri_not t1 with
            | TrueT => VBool true
            | FalseT => VBool false
            | UnknownT => VNull TBool
            end)
  | @TEIsNull _ e1 =>
      match @eval_expr _ e1 tu with
      | Some (VNull _) => Some (VBool true)
      | Some _ => Some (VBool false)
      | None => None
      end
  | @TEIsDistinctFrom _ e1 e2 =>
      match @eval_expr _ e1 tu, @eval_expr _ e2 tu with
      | Some v1, Some v2 => Some (VBool (sql_value_is_distinct_from v1 v2))
      | _, _ => None
      end
  end.

Definition eval_pred (e : typed_expr TBool) (tu : typed_tuple) : tri :=
  match @eval_expr _ e tu with
  | Some (VBool b) => if b then TrueT else FalseT
  | Some (VNull TBool) => UnknownT
  | _ => UnknownT
  end.

Inductive has_type : schema -> forall t, typed_expr t -> Prop :=
  | HT_Col : forall Γ c ty, In (c, ty) Γ -> has_type Γ ty (TECol ty c)
  | HT_Int : forall Γ n, has_type Γ TInt (TEInt n)
  | HT_String : forall Γ s, has_type Γ TString (TEString s)
  | HT_Bool : forall Γ b, has_type Γ TBool (TEBool b)
  | HT_Null : forall Γ t, has_type Γ t (TENull t)
  | HT_Eq : forall Γ t e1 e2, has_type Γ t e1 -> has_type Γ t e2 -> has_type Γ TBool (TEEq t e1 e2)
  | HT_Lt : forall Γ e1 e2, has_type Γ TInt e1 -> has_type Γ TInt e2 -> has_type Γ TBool (TELt e1 e2)
  | HT_And : forall Γ e1 e2, has_type Γ TBool e1 -> has_type Γ TBool e2 -> has_type Γ TBool (TEAnd e1 e2)
  | HT_Or : forall Γ e1 e2, has_type Γ TBool e1 -> has_type Γ TBool e2 -> has_type Γ TBool (TEOr e1 e2)
  | HT_Not : forall Γ e, has_type Γ TBool e -> has_type Γ TBool (TENot e)
  | HT_IsNull : forall Γ t e, has_type Γ t e -> has_type Γ TBool (@TEIsNull t e)
  | HT_IsDistinctFrom : forall Γ t e1 e2, has_type Γ t e1 -> has_type Γ t e2 -> has_type Γ TBool (@TEIsDistinctFrom t e1 e2).

Definition btree_key := nat.

Inductive btree_node : Type :=
  | BLeaf : list (btree_key * typed_tuple) -> btree_node
  | BInternal : list (btree_key * btree_node) -> btree_node -> btree_node.

Fixpoint btree_search_leaf (k : btree_key) (kvs : list (btree_key * typed_tuple)) : option typed_tuple :=
  match kvs with
  | [] => None
  | (k', v) :: rest =>
      if Nat.eqb k k' then Some v
      else if Nat.ltb k k' then None
      else btree_search_leaf k rest
  end.

Fixpoint btree_search_with_fuel (fuel : nat) (k : btree_key) (n : btree_node) : option typed_tuple :=
  match fuel with
  | O => None
  | S fuel' =>
      match n with
      | BLeaf kvs => btree_search_leaf k kvs
      | BInternal seps left0 =>
          let fix search_seps (left : btree_node) (separators : list (btree_key * btree_node)) : option typed_tuple :=
            match separators with
            | [] => btree_search_with_fuel fuel' k left
            | (sep, right_child) :: rest =>
                if Nat.ltb k sep then
                  btree_search_with_fuel fuel' k left
                else
                  search_seps right_child rest
            end
          in search_seps left0 seps
      end
  end.

Fixpoint btree_depth (n : btree_node) : nat :=
  match n with
  | BLeaf _ => 0
  | BInternal seps left0 =>
      S (btree_depth left0)
  end.

Definition btree_search (k : btree_key) (n : btree_node) : option typed_tuple :=
  btree_search_with_fuel (S (btree_depth n)) k n.

Definition btree_order := 3.
Definition btree_min_keys := btree_order.
Definition btree_max_keys := 2 * btree_order.

Fixpoint keys_sorted (keys : list btree_key) : Prop :=
  match keys with
  | [] => True
  | k :: rest =>
    match rest with
    | [] => True
    | k2 :: _ => k < k2 /\ keys_sorted rest
    end
  end.

Definition leaf_keys_sorted (kvs : list (btree_key * typed_tuple)) : Prop :=
  keys_sorted (map fst kvs).

Definition internal_keys_sorted (kns : list (btree_key * btree_node)) : Prop :=
  keys_sorted (map fst kns).

Fixpoint btree_height (n : btree_node) : nat :=
  match n with
  | BLeaf _ => 0
  | BInternal _ child => S (btree_height child)
  end.

Fixpoint all_children_same_height (seps : list (btree_key * btree_node)) (h : nat) : Prop :=
  match seps with
  | [] => True
  | (_, child) :: rest => btree_height child = h /\ all_children_same_height rest h
  end.

Inductive in_range (low high : option btree_key) (k : btree_key) : Prop :=
  | in_range_intro :
      (match low with None => True | Some l => l <= k end) ->
      (match high with None => True | Some h => k < h end) ->
      in_range low high k.

Fixpoint all_keys_in_range (low high : option btree_key) (kvs : list (btree_key * typed_tuple)) : Prop :=
  match kvs with
  | [] => True
  | (k, _) :: rest => in_range low high k /\ all_keys_in_range low high rest
  end.

Record typed_bag : Type := {
  bag_schema : schema;
  bag_tuples : list typed_tuple;
  bag_wf : forall t, In t bag_tuples -> t.(tuple_schema) = bag_schema
}.

Inductive agg_func : Type :=
  | AggCountStar : agg_func
  | AggCountCol : qualified_column -> agg_func
  | AggSum : qualified_column -> agg_func
  | AggAvg : qualified_column -> agg_func
  | AggMin : qualified_column -> agg_func
  | AggMax : qualified_column -> agg_func.

Definition agg_count_star (b : typed_bag) : sql_value :=
  VInt (Z.of_nat (List.length b.(bag_tuples))).

Fixpoint count_non_nulls_in_column (tuples : list typed_tuple) (col : qualified_column) : nat :=
  match tuples with
  | [] => 0
  | t :: rest =>
      match get_typed_value t col with
      | Some (VNull _) => count_non_nulls_in_column rest col
      | None => count_non_nulls_in_column rest col
      | Some _ => S (count_non_nulls_in_column rest col)
      end
  end.

Definition agg_count_col (col : qualified_column) (b : typed_bag) : sql_value :=
  VInt (Z.of_nat (count_non_nulls_in_column b.(bag_tuples) col)).

Fixpoint sum_int_values (tuples : list typed_tuple) (col : qualified_column) : option Z :=
  match tuples with
  | [] => None
  | t :: rest =>
      match get_typed_value t col with
      | Some (VInt n) =>
          match sum_int_values rest col with
          | Some m => Some (Z.add n m)
          | None => Some n
          end
      | Some (VNull TInt) => sum_int_values rest col
      | _ => None
      end
  end.

Definition agg_sum (col : qualified_column) (b : typed_bag) : sql_value :=
  match sum_int_values b.(bag_tuples) col with
  | Some n => VInt n
  | None => VNull TInt
  end.

Fixpoint min_int_values (tuples : list typed_tuple) (col : qualified_column) : option Z :=
  match tuples with
  | [] => None
  | t :: rest =>
      match get_typed_value t col with
      | Some (VInt n) =>
          match min_int_values rest col with
          | Some m => Some (Z.min n m)
          | None => Some n
          end
      | Some (VNull TInt) => min_int_values rest col
      | _ => min_int_values rest col
      end
  end.

Definition agg_min (col : qualified_column) (b : typed_bag) : sql_value :=
  match min_int_values b.(bag_tuples) col with
  | Some n => VInt n
  | None => VNull TInt
  end.

Fixpoint max_int_values (tuples : list typed_tuple) (col : qualified_column) : option Z :=
  match tuples with
  | [] => None
  | t :: rest =>
      match get_typed_value t col with
      | Some (VInt n) =>
          match max_int_values rest col with
          | Some m => Some (Z.max n m)
          | None => Some n
          end
      | Some (VNull TInt) => max_int_values rest col
      | _ => max_int_values rest col
      end
  end.

Definition agg_max (col : qualified_column) (b : typed_bag) : sql_value :=
  match max_int_values b.(bag_tuples) col with
  | Some n => VInt n
  | None => VNull TInt
  end.

Definition agg_avg (col : qualified_column) (b : typed_bag) : sql_value :=
  match sum_int_values b.(bag_tuples) col, count_non_nulls_in_column b.(bag_tuples) col with
  | Some sum, S cnt => VInt (Z.div sum (Z.of_nat (S cnt)))
  | _, _ => VNull TInt
  end.

Fixpoint filter_map {A B : Type} (f : A -> option B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: xs =>
      match f x with
      | Some y => y :: filter_map f xs
      | None => filter_map f xs
      end
  end.

Fixpoint flat_map {A B : Type} (f : A -> list B) (l : list A) : list B :=
  match l with
  | [] => []
  | x :: xs => f x ++ flat_map f xs
  end.

Definition schema_union (s1 s2 : schema) : schema := s1 ++ s2.

Definition schema_disjoint (s1 s2 : schema) : Prop :=
  forall c t1 t2, In (c, t1) s1 -> In (c, t2) s2 -> False.

Lemma null_tuple_wf (s : schema) :
  List.length (map (fun ct => Some (VNull (snd ct))) s) = List.length s /\
  (forall i v,
    nth_error (map (fun ct => Some (VNull (snd ct))) s) i = Some (Some v) ->
    exists c t, nth_error s i = Some (c, t) /\ value_type v = t).
Proof.
  split.
  - rewrite map_length. reflexivity.
  - intros.
    destruct (nth_error s i) eqn:E.
    + destruct p as [c t].
      exists c, t.
      split.
      * reflexivity.
      * rewrite nth_error_map in H.
        rewrite E in H.
        injection H; intros; subst.
        simpl. reflexivity.
    + rewrite nth_error_map in H.
      rewrite E in H.
      discriminate.
Qed.

Definition null_tuple_for_schema (s : schema) : typed_tuple :=
  {| tuple_schema := s;
     tuple_data := map (fun ct => Some (VNull (snd ct))) s;
     tuple_wf := null_tuple_wf s
  |}.

Lemma concat_tuple_wf (t1 t2 : typed_tuple)
  (H : schema_disjoint t1.(tuple_schema) t2.(tuple_schema)) :
  List.length (t1.(tuple_data) ++ t2.(tuple_data)) =
  List.length (schema_union t1.(tuple_schema) t2.(tuple_schema)) /\
  (forall i v,
    nth_error (t1.(tuple_data) ++ t2.(tuple_data)) i = Some (Some v) ->
    exists c t,
      nth_error (schema_union t1.(tuple_schema) t2.(tuple_schema)) i = Some (c, t) /\
      value_type v = t).
Proof.
  split.
  - unfold schema_union.
    rewrite app_length, app_length.
    f_equal;
    destruct (tuple_wf t1) as [H1 _];
    destruct (tuple_wf t2) as [H2 _];
    assumption.
  - intros i v H0.
    unfold schema_union.
    destruct (tuple_wf t1) as [Hlen1 Hty1].
    destruct (tuple_wf t2) as [Hlen2 Hty2].
    destruct (lt_dec i (List.length (tuple_data t1))).
    + rewrite nth_error_app1 in H0; try assumption.
      rewrite nth_error_app1.
      * apply Hty1. exact H0.
      * rewrite <- Hlen1. assumption.
    + rewrite nth_error_app2 in H0; try lia.
      rewrite nth_error_app2.
      * specialize (Hty2 (i - List.length (tuple_data t1)) v H0).
        destruct Hty2 as [c [t [H3 H4]]].
        exists c, t.
        split.
        -- rewrite <- H3. f_equal. lia.
        -- exact H4.
      * rewrite <- Hlen1. lia.
Qed.

Definition concat_tuples (t1 t2 : typed_tuple)
  (H : schema_disjoint t1.(tuple_schema) t2.(tuple_schema)) : typed_tuple :=
  {| tuple_schema := schema_union t1.(tuple_schema) t2.(tuple_schema);
     tuple_data := t1.(tuple_data) ++ t2.(tuple_data);
     tuple_wf := concat_tuple_wf t1 t2 H
  |}.

Inductive subquery_expr : Type :=
  | SqScalar : forall t, typed_expr t -> typed_bag -> subquery_expr
  | SqExists : (typed_tuple -> bool) -> typed_bag -> subquery_expr
  | SqIn : forall t, typed_expr t -> typed_expr t -> typed_bag -> subquery_expr.

Definition eval_subquery_scalar (t : sql_type) (e : typed_expr t) (b : typed_bag) : option sql_value :=
  match b.(bag_tuples) with
  | [] => Some (VNull t)
  | [single] => @eval_expr t e single
  | _ :: _ :: _ => None
  end.

Definition tri_or_list (ls : list tri) : tri :=
  fold_left (fun acc t =>
    match acc, t with
    | TrueT, _ => TrueT
    | _, TrueT => TrueT
    | UnknownT, _ => UnknownT
    | _, UnknownT => UnknownT
    | FalseT, FalseT => FalseT
    end) ls FalseT.

Definition eval_subquery_exists (p : typed_tuple -> bool) (b : typed_bag) : tri :=
  if existsb p b.(bag_tuples) then TrueT else FalseT.

Definition eval_subquery_in {t : sql_type} (outer_e : typed_expr t)
                           (inner_e : typed_expr t)
                           (outer_t : typed_tuple)
                           (inner_b : typed_bag) : tri :=
  match @eval_expr t outer_e outer_t with
  | Some (VNull _) => UnknownT
  | Some vout =>
      let comps := map (fun tin =>
                         match @eval_expr t inner_e tin with
                         | Some vin => sql_eq_tri vout vin
                         | None => UnknownT
                         end) inner_b.(bag_tuples) in
      tri_or_list comps
  | None => UnknownT
  end.

Definition transaction_id := nat.
Definition timestamp := nat.

Record transaction_state := {
  xid : transaction_id;
  xstart : timestamp;
  xcommit : option timestamp;
  xaborted : bool
}.

Record version := {
  v_tuple : typed_tuple;
  v_xmin : transaction_id;
  v_xmax : option transaction_id;
  v_created : timestamp;
  v_deleted : option timestamp
}.

Record snapshot := {
  snap_time : timestamp
}.

Definition committed_by (ts : timestamp) (txns : list transaction_state) (x : transaction_id) : bool :=
  match find (fun tx => Nat.eqb (xid tx) x) txns with
  | Some tx => match xcommit tx with
                | Some cts => andb (negb (xaborted tx)) (Nat.leb cts ts)
                | None => false
                end
  | None => false
  end.

Definition is_visible_snapshot (txns : list transaction_state)
                              (snap : snapshot)
                              (v : version) : bool :=
  let creator_ok := committed_by snap.(snap_time) txns (v_xmin v) in
  let deleter_committed := match v.(v_xmax) with
                           | None => false
                           | Some xdel => committed_by snap.(snap_time) txns xdel
                           end in
  andb creator_ok (negb deleter_committed).

Definition read_snapshot (txns : list transaction_state)
                        (snap : snapshot)
                        (table : list version) : list typed_tuple :=
  map v_tuple (filter (is_visible_snapshot txns snap) table).

Definition mvcc_insert (xid : transaction_id) (ts : timestamp)
                      (t : typed_tuple) (table : list version) : list version :=
  {| v_tuple := t;
     v_xmin := xid;
     v_xmax := None;
     v_created := ts;
     v_deleted := None
  |} :: table.

Definition mvcc_delete (xid : transaction_id) (ts : timestamp)
                      (p : typed_tuple -> bool) (table : list version) : list version :=
  map (fun v =>
    if p (v_tuple v) && match v_xmax v with Some _ => false | None => true end then
      {| v_tuple := v_tuple v;
         v_xmin := v_xmin v;
         v_xmax := Some xid;
         v_created := v_created v;
         v_deleted := Some ts
      |}
    else v) table.

Lemma find_some {A} (f : A -> bool) (l : list A) (x : A) :
  find f l = Some x -> In x l /\ f x = true.
Proof.
  induction l as [|y ys IH]; simpl; intro H; [discriminate|].
  destruct (f y) eqn:Hy; inversion H; subst; auto.
  specialize (IH H1). destruct IH as [Hin Hfy]. auto.
Qed.

Lemma find_none {A} (f : A -> bool) (l : list A) :
  find f l = None -> forall x, In x l -> f x = false.
Proof.
  induction l as [|y ys IH]; simpl; intros H x Hin.
  - contradiction.
  - destruct (f y) eqn:Hy.
    + discriminate.
    + destruct Hin as [Heq | Hin'].
      * subst. exact Hy.
      * apply IH; auto.
Qed.

Definition txns_wf (txns : list transaction_state) : Prop :=
  forall tx, In tx txns ->
    match xcommit tx with
    | Some cts => xstart tx <= cts
    | None => True
    end.

Lemma new_version_invisible_to_past :
  forall txns snap x ts new_t,
    txns_wf txns ->
    snap.(snap_time) < ts ->
    (forall tx, In tx txns -> xid tx = x -> xstart tx >= ts) ->
    is_visible_snapshot txns snap
      {| v_tuple := new_t; v_xmin := x; v_xmax := None;
         v_created := ts; v_deleted := None |} = false.
Proof.
  intros txns snap x ts new_t Hwf Htime Hstart.
  unfold is_visible_snapshot, committed_by.
  simpl.
  destruct (find (fun tx => Nat.eqb (xid tx) x) txns) as [tx|] eqn:Hfind.
  - destruct (xcommit tx) as [cts|] eqn:Hcommit.
    + simpl.
      apply find_some in Hfind.
      destruct Hfind as [Hin Heqb].
      apply Nat.eqb_eq in Heqb.
      specialize (Hstart tx Hin Heqb).
      specialize (Hwf tx Hin).
      rewrite Hcommit in Hwf.
      destruct (negb (xaborted tx)) eqn:Haborted.
      * destruct (Nat.leb cts (snap_time snap)) eqn:Hleb.
        -- apply Nat.leb_le in Hleb.
           exfalso. lia.
        -- reflexivity.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma new_version_fresh_xid_invisible :
  forall txns snap x ts new_t,
    (forall tx, In tx txns -> xid tx <> x) ->
    is_visible_snapshot txns snap
      {| v_tuple := new_t; v_xmin := x; v_xmax := None;
         v_created := ts; v_deleted := None |} = false.
Proof.
  intros txns snap x ts new_t H.
  unfold is_visible_snapshot, committed_by.
  simpl.
  destruct (find (fun tx => Nat.eqb (xid tx) x) txns) as [tx|] eqn:Hfind.
  - apply find_some in Hfind.
    destruct Hfind as [Hin Heqb].
    apply Nat.eqb_eq in Heqb.
    specialize (H tx Hin).
    contradiction.
  - reflexivity.
Qed.

Lemma read_snapshot_extensional_insert_future :
  forall txns snap table t x ts new_t,
    txns_wf txns ->
    snap.(snap_time) < ts ->
    (forall tx, In tx txns -> xid tx = x -> xstart tx >= ts) ->
    In t (read_snapshot txns snap table) <->
    In t (read_snapshot txns snap (mvcc_insert x ts new_t table)).
Proof.
  intros txns snap table t x ts new_t Hwf Htime Hstart.
  unfold read_snapshot, mvcc_insert.
  simpl.
  rewrite new_version_invisible_to_past; auto.
  split; intro H.
  - apply in_map_iff in H.
    destruct H as [v [Heq Hin]].
    apply in_map_iff.
    exists v.
    split.
    + exact Heq.
    + apply filter_In in Hin.
      destruct Hin as [Hin_list Hvis].
      simpl.
      apply filter_In.
      split; auto.
  - unfold mvcc_insert in H.
    simpl in H.
    apply in_map_iff in H.
    destruct H as [v [Heq Hin]].
    apply in_map_iff.
    exists v.
    split.
    + exact Heq.
    + apply filter_In in Hin.
      destruct Hin as [Hin_list Hvis].
      apply filter_In.
      simpl in Hin_list.
      assert (v <> {| v_tuple := new_t; v_xmin := x; v_xmax := None;
                      v_created := ts; v_deleted := None |}).
      { intros Heq_v. subst v.
        simpl in Hvis.
        rewrite new_version_invisible_to_past in Hvis; auto.
        discriminate. }
      split; [auto | assumption].
Qed.

Definition unique_xids (txns : list transaction_state) : Prop :=
  forall tx1 tx2, In tx1 txns -> In tx2 txns -> xid tx1 = xid tx2 -> tx1 = tx2.

Lemma find_xid_unique : forall txns x tx,
  unique_xids txns ->
  find (fun tx0 => Nat.eqb (xid tx0) x) txns = Some tx ->
  forall tx', In tx' txns -> xid tx' = x -> tx' = tx.
Proof.
  intros txns x tx Huniq Hfind tx' Hin' Hxid'.
  apply find_some in Hfind.
  destruct Hfind as [Hin Heqb].
  apply Nat.eqb_eq in Heqb.
  apply Huniq; auto.
  congruence.
Qed.

Lemma no_dirty_reads :
  forall txns snap v,
    unique_xids txns ->
    (exists tx, In tx txns /\ xid tx = v.(v_xmin) /\ xcommit tx = None) ->
    is_visible_snapshot txns snap v = false.
Proof.
  intros txns snap v Huniq [tx [Hin [Hxid Hcommit]]].
  unfold is_visible_snapshot, committed_by.
  simpl.
  destruct (find (fun tx0 => Nat.eqb (xid tx0) (v_xmin v)) txns) as [tx'|] eqn:Hfind.
  - assert (tx = tx').
    { eapply find_xid_unique; eauto. }
    subst tx'.
    rewrite Hcommit.
    reflexivity.
  - reflexivity.
Qed.

Lemma no_read_aborted :
  forall txns snap v,
    unique_xids txns ->
    (exists tx, In tx txns /\ xid tx = v.(v_xmin) /\ exists cts, xcommit tx = Some cts /\ xaborted tx = true) ->
    is_visible_snapshot txns snap v = false.
Proof.
  intros txns snap v Huniq [tx [Hin [Hxid [cts [Hcommit Haborted]]]]].
  unfold is_visible_snapshot, committed_by.
  simpl.
  destruct (find (fun tx0 => Nat.eqb (xid tx0) (v_xmin v)) txns) as [tx'|] eqn:Hfind.
  - assert (tx = tx').
    { eapply find_xid_unique; eauto. }
    subst tx'.
    rewrite Hcommit.
    simpl.
    rewrite Haborted.
    simpl.
    reflexivity.
  - reflexivity.
Qed.

Lemma filter_preserves_schema : forall (p : typed_tuple -> bool) (tuples : list typed_tuple) s,
  (forall t, In t tuples -> t.(tuple_schema) = s) ->
  (forall t, In t (filter p tuples) -> t.(tuple_schema) = s).
Proof.
  intros p tuples s H t Hin.
  apply filter_In in Hin.
  destruct Hin as [Hin_orig _].
  apply H. exact Hin_orig.
Qed.

Definition select (p : typed_tuple -> tri) (b : typed_bag) : typed_bag :=
  {| bag_schema := b.(bag_schema);
     bag_tuples := filter (fun t => tri_to_bool (p t)) b.(bag_tuples);
     bag_wf := filter_preserves_schema _ _ _ (bag_wf b)
  |}.

Definition select_expr (e : typed_expr TBool) (b : typed_bag) : typed_bag :=
  select (fun t => eval_pred e t) b.

Definition bag_eq (b1 b2 : typed_bag) : Prop :=
  b1.(bag_schema) = b2.(bag_schema) /\
  Permutation b1.(bag_tuples) b2.(bag_tuples).

Lemma tri_and_comm : forall a b, tri_and a b = tri_and b a.
Proof.
  intros a b.
  destruct a, b; reflexivity.
Qed.

Lemma tri_or_comm : forall a b, tri_or a b = tri_or b a.
Proof.
  intros a b.
  destruct a, b; reflexivity.
Qed.

Lemma tri_and_assoc : forall a b c, tri_and (tri_and a b) c = tri_and a (tri_and b c).
Proof.
  intros a b c.
  destruct a, b, c; reflexivity.
Qed.

Lemma tri_or_assoc : forall a b c, tri_or (tri_or a b) c = tri_or a (tri_or b c).
Proof.
  intros a b c.
  destruct a, b, c; reflexivity.
Qed.

Lemma tri_demorgan_and : forall a b, tri_not (tri_and a b) = tri_or (tri_not a) (tri_not b).
Proof.
  intros a b.
  destruct a, b; reflexivity.
Qed.

Lemma tri_demorgan_or : forall a b, tri_not (tri_or a b) = tri_and (tri_not a) (tri_not b).
Proof.
  intros a b.
  destruct a, b; reflexivity.
Qed.

Lemma filter_true_id : forall {A} (l : list A),
  filter (fun _ => true) l = l.
Proof.
  induction l; simpl; auto.
  rewrite IHl. reflexivity.
Qed.

Lemma select_true_id : forall b,
  bag_eq (select (fun _ => TrueT) b) b.
Proof.
  intros [s ts wf].
  unfold bag_eq, select; simpl.
  split.
  - reflexivity.
  - unfold tri_to_bool.
    rewrite filter_true_id.
    apply Permutation_refl.
Qed.

Lemma filter_false_nil : forall {A} (l : list A),
  filter (fun _ => false) l = [].
Proof.
  induction l; simpl; auto.
Qed.

Lemma select_false_empty : forall b,
  bag_eq (select (fun _ => FalseT) b)
    {| bag_schema := b.(bag_schema);
       bag_tuples := [];
       bag_wf := fun t H => match H with end |}.
Proof.
  intros [s ts wf].
  unfold bag_eq, select; simpl.
  split.
  - reflexivity.
  - rewrite filter_false_nil. apply Permutation_refl.
Qed.

Lemma count_star_empty : forall s,
  agg_count_star {| bag_schema := s; bag_tuples := []; bag_wf := fun t H => match H with end |} = VInt 0.
Proof.
  intros s.
  unfold agg_count_star.
  simpl.
  reflexivity.
Qed.

Lemma count_non_nulls_empty : forall col,
  count_non_nulls_in_column [] col = 0.
Proof.
  intros col.
  reflexivity.
Qed.

Lemma sum_int_empty : forall col,
  sum_int_values [] col = None.
Proof.
  intros col.
  reflexivity.
Qed.

Lemma min_int_empty : forall col,
  min_int_values [] col = None.
Proof.
  intros col.
  reflexivity.
Qed.

Lemma max_int_empty : forall col,
  max_int_values [] col = None.
Proof.
  intros col.
  reflexivity.
Qed.

Lemma agg_sum_empty : forall col s,
  agg_sum col {| bag_schema := s; bag_tuples := []; bag_wf := fun t H => match H with end |} = VNull TInt.
Proof.
  intros col s.
  unfold agg_sum.
  simpl.
  reflexivity.
Qed.

Lemma agg_min_empty : forall col s,
  agg_min col {| bag_schema := s; bag_tuples := []; bag_wf := fun t H => match H with end |} = VNull TInt.
Proof.
  intros col s.
  unfold agg_min.
  simpl.
  reflexivity.
Qed.

Lemma agg_max_empty : forall col s,
  agg_max col {| bag_schema := s; bag_tuples := []; bag_wf := fun t H => match H with end |} = VNull TInt.
Proof.
  intros col s.
  unfold agg_max.
  simpl.
  reflexivity.
Qed.

Lemma agg_avg_empty : forall col s,
  agg_avg col {| bag_schema := s; bag_tuples := []; bag_wf := fun t H => match H with end |} = VNull TInt.
Proof.
  intros col s.
  unfold agg_avg.
  simpl.
  reflexivity.
Qed.

Lemma tri_to_bool_and : forall a b,
  tri_to_bool (tri_and a b) = andb (tri_to_bool a) (tri_to_bool b).
Proof.
  intros a b.
  destruct a, b; reflexivity.
Qed.

Lemma tri_to_bool_or : forall a b,
  tri_to_bool (tri_or a b) = orb (tri_to_bool a) (tri_to_bool b).
Proof.
  intros a b.
  destruct a, b; reflexivity.
Qed.

Lemma filter_andb {A} (p q : A -> bool) (l : list A) :
  filter (fun x => andb (p x) (q x)) l = filter p (filter q l).
Proof.
  induction l as [|a l IH]; simpl; auto.
  case_eq (q a); intro Hq; simpl.
  - case_eq (p a); intro Hp; simpl; rewrite IH; reflexivity.
  - rewrite andb_false_r. exact IH.
Qed.

Lemma select_and_fusion : forall p q b,
  bag_eq (select (fun t => tri_and (p t) (q t)) b)
         (select p (select q b)).
Proof.
  intros p q [s ts wf].
  unfold bag_eq, select; simpl.
  split.
  - reflexivity.
  - assert (H: filter (fun t => tri_to_bool (tri_and (p t) (q t))) ts =
              filter (fun t => andb (tri_to_bool (p t)) (tri_to_bool (q t))) ts).
    { f_equal. apply functional_extensionality. intro x. apply tri_to_bool_and. }
    rewrite H.
    rewrite filter_andb.
    apply Permutation_refl.
Qed.

Lemma select_comm : forall p q b,
  bag_eq (select p (select q b))
         (select q (select p b)).
Proof.
  intros p q [s ts wf].
  unfold bag_eq, select; simpl.
  split.
  - reflexivity.
  - rewrite <- filter_andb with (p := fun t => tri_to_bool (p t))
                                (q := fun t => tri_to_bool (q t)).
    rewrite <- filter_andb with (p := fun t => tri_to_bool (q t))
                                (q := fun t => tri_to_bool (p t)).
    assert (H: filter (fun x => andb (tri_to_bool (p x)) (tri_to_bool (q x))) ts =
              filter (fun x => andb (tri_to_bool (q x)) (tri_to_bool (p x))) ts).
    { f_equal. apply functional_extensionality. intro x. apply andb_comm. }
    rewrite H.
    apply Permutation_refl.
Qed.


Fixpoint mentions_col {t} (e : typed_expr t) (c : qualified_column) : bool :=
  match e with
  | TECol _ c' => qualified_column_eqb c' c
  | TEInt _ => false
  | TEString _ => false
  | TEBool _ => false
  | TENull _ => false
  | TEEq _ e1 e2 => orb (mentions_col e1 c) (mentions_col e2 c)
  | TELt e1 e2 => orb (mentions_col e1 c) (mentions_col e2 c)
  | TEAnd e1 e2 => orb (mentions_col e1 c) (mentions_col e2 c)
  | TEOr e1 e2 => orb (mentions_col e1 c) (mentions_col e2 c)
  | TENot e1 => mentions_col e1 c
  | TEIsNull _ e1 => mentions_col e1 c
  | TEIsDistinctFrom _ e1 e2 => orb (mentions_col e1 c) (mentions_col e2 c)
  end.

Definition mentions_only (Γ : schema) (e : typed_expr TBool) : Prop :=
  forall c, mentions_col e c = true -> exists ty, In (c, ty) Γ.

Lemma find_column_index_app_left : forall s1 s2 c i,
  unique_schema (s1 ++ s2) ->
  find_column_index s1 c = Some i ->
  find_column_index (s1 ++ s2) c = Some i.
Proof.
  induction s1 as [|[c' ty'] s1' IH]; intros s2 c i Huniq Hfind.
  - simpl in Hfind. discriminate.
  - simpl in Hfind. simpl.
    destruct (qualified_column_eqb c' c) eqn:Heqb.
    + inversion Hfind. subst. reflexivity.
    + destruct (find_column_index s1' c) as [n|] eqn:Hfind'; try discriminate.
      inversion Hfind. subst.
      specialize (IH s2 c n).
      assert (Huniq': unique_schema (s1' ++ s2)).
      { intros i j c0 t1 t2 Hneq Hi Hj.
        apply (Huniq (S i) (S j) c0 t1 t2).
        - intro H. injection H. contradiction.
        - simpl. exact Hi.
        - simpl. exact Hj. }
      specialize (IH Huniq' Hfind').
      rewrite IH. reflexivity.
Qed.

Lemma find_column_index_app_right : forall s1 s2 c i,
  unique_schema (s1 ++ s2) ->
  find_column_index s2 c = Some i ->
  (forall ty, ~In (c, ty) s1) ->
  find_column_index (s1 ++ s2) c = Some (List.length s1 + i).
Proof.
  induction s1 as [|[c' ty'] s1' IH]; intros s2 c i Huniq Hfind Hnot_in.
  - simpl. exact Hfind.
  - simpl.
    destruct (qualified_column_eqb c' c) eqn:Heqb.
    + destruct (qualified_column_eqb_spec c' c).
      * subst c'. exfalso. apply (Hnot_in ty'). left. reflexivity.
      * discriminate.
    + assert (Huniq': unique_schema (s1' ++ s2)).
      { intros i0 j c0 t1 t2 Hneq Hi Hj.
        apply (Huniq (S i0) (S j) c0 t1 t2).
        - intro H. injection H. contradiction.
        - simpl. exact Hi.
        - simpl. exact Hj. }
      assert (Hnot_in': forall ty, ~In (c, ty) s1').
      { intros ty H. apply (Hnot_in ty). right. exact H. }
      specialize (IH s2 c i Huniq' Hfind Hnot_in').
      rewrite IH. reflexivity.
Qed.

Lemma nth_error_app_left : forall {A} (l1 l2 : list A) i x,
  i < List.length l1 ->
  nth_error l1 i = Some x ->
  nth_error (l1 ++ l2) i = Some x.
Proof.
  induction l1 as [|a l1' IH]; intros l2 i x Hlen Hnth.
  - simpl in Hlen. inversion Hlen.
  - destruct i.
    + simpl in Hnth. simpl. exact Hnth.
    + simpl in Hlen. simpl in Hnth. simpl.
      apply IH.
      * apply Nat.lt_succ_r. simpl in Hlen. exact Hlen.
      * exact Hnth.
Qed.

Lemma nth_error_app_right : forall {A} (l1 l2 : list A) i x,
  nth_error l2 i = Some x ->
  nth_error (l1 ++ l2) (List.length l1 + i) = Some x.
Proof.
  induction l1 as [|a l1' IH]; intros l2 i x Hnth.
  - simpl. exact Hnth.
  - simpl. apply IH. exact Hnth.
Qed.

Lemma find_column_index_In : forall s c i,
  find_column_index s c = Some i ->
  exists ty, In (c, ty) s.
Proof.
  induction s as [|[c' ty'] s' IH]; intros c i Hfind.
  - simpl in Hfind. discriminate.
  - simpl in Hfind.
    destruct (qualified_column_eqb c' c) eqn:Heqb.
    + destruct (qualified_column_eqb_spec c' c).
      * subst c'. exists ty'. left. reflexivity.
      * discriminate.
    + destruct (find_column_index s' c) as [n|] eqn:Hfind'; try discriminate.
      destruct (IH c n Hfind') as [ty Hin].
      exists ty. right. exact Hin.
Qed.

Lemma find_column_index_None : forall s c,
  find_column_index s c = None ->
  forall ty, ~In (c, ty) s.
Proof.
  induction s as [|[c' ty'] s' IH]; intros c Hfind ty Hin.
  - simpl in Hin. contradiction.
  - simpl in Hfind.
    destruct (qualified_column_eqb c' c) eqn:Heqb.
    + discriminate.
    + destruct (find_column_index s' c) as [n|] eqn:Hfind'; try discriminate.
      simpl in Hin. destruct Hin as [Heq | Hin'].
      * injection Heq. intros Heq1 Heq2. subst ty' c'.
        destruct (qualified_column_eqb_spec c c).
        -- discriminate.
        -- apply n. reflexivity.
      * apply (IH c Hfind' ty Hin').
Qed.

Lemma get_typed_value_concat_left : forall t1 t2 Hdisj c,
  (exists ty, In (c, ty) t1.(tuple_schema)) ->
  unique_schema (schema_union t1.(tuple_schema) t2.(tuple_schema)) ->
  get_typed_value (concat_tuples t1 t2 Hdisj) c = get_typed_value t1 c.
Proof.
  intros t1 t2 Hdisj c [ty Hin] Huniq.
  unfold get_typed_value, concat_tuples. simpl.
  unfold schema_union in Huniq.
  destruct (find_column_index t1.(tuple_schema) c) as [i1|] eqn:Hfind1.
  - rewrite find_column_index_app_left with (s1 := t1.(tuple_schema)) (s2 := t2.(tuple_schema)) (i := i1); try exact Huniq; try exact Hfind1.
    destruct (tuple_wf t1) as [Hlen1 _].
    destruct (nth_error t1.(tuple_data) i1) as [v1|] eqn:Hnth1.
    + assert (Hi1_bound: i1 < List.length t1.(tuple_data)).
      { rewrite Hlen1. apply find_column_index_bounds with (s := t1.(tuple_schema)) (col := c). exact Hfind1. }
      rewrite nth_error_app_left with (l1 := t1.(tuple_data)) (l2 := t2.(tuple_data)) (x := v1); try exact Hi1_bound; try exact Hnth1.
      reflexivity.
    + assert (Hi1_bound: i1 < List.length t1.(tuple_data)).
      { rewrite Hlen1. apply find_column_index_bounds with (s := t1.(tuple_schema)) (col := c). exact Hfind1. }
      exfalso.
      apply nth_error_Some in Hi1_bound.
      congruence.
  - exfalso. apply (find_column_index_None _ _ Hfind1 _ Hin).
Qed.

Lemma get_typed_value_concat_right : forall t1 t2 Hdisj c,
  (forall ty, ~In (c, ty) t1.(tuple_schema)) ->
  unique_schema (schema_union t1.(tuple_schema) t2.(tuple_schema)) ->
  get_typed_value (concat_tuples t1 t2 Hdisj) c = get_typed_value t2 c.
Proof.
  intros t1 t2 Hdisj c Hnot_in Huniq.
  unfold get_typed_value, concat_tuples. simpl.
  unfold schema_union in Huniq.
  destruct (find_column_index t2.(tuple_schema) c) as [i2|] eqn:Hfind2.
  - rewrite find_column_index_app_right with (s1 := t1.(tuple_schema)) (s2 := t2.(tuple_schema)) (i := i2); try exact Huniq; try exact Hfind2; try exact Hnot_in.
    destruct (tuple_wf t1) as [Hlen1 _].
    destruct (tuple_wf t2) as [Hlen2 _].
    destruct (nth_error t2.(tuple_data) i2) as [v2|] eqn:Hnth2.
    + rewrite <- Hlen1.
      rewrite nth_error_app_right with (l1 := t1.(tuple_data)) (l2 := t2.(tuple_data)) (x := v2).
      * reflexivity.
      * exact Hnth2.
    + rewrite <- Hlen1.
      assert (Hi2_bound: i2 < List.length t2.(tuple_data)).
      { rewrite Hlen2. apply find_column_index_bounds with (s := t2.(tuple_schema)) (col := c). exact Hfind2. }
      exfalso.
      apply nth_error_Some in Hi2_bound.
      congruence.
  - destruct (find_column_index (t1.(tuple_schema) ++ t2.(tuple_schema)) c) as [i|] eqn:Hfind.
    + destruct (find_column_index_In _ _ _ Hfind) as [ty Hin].
      apply in_app_or in Hin.
      destruct Hin as [Hin1 | Hin2].
      * exfalso. apply (Hnot_in ty Hin1).
      * exfalso. apply (find_column_index_None _ _ Hfind2 _ Hin2).
    + unfold schema_union. rewrite Hfind. reflexivity.
Qed.


Lemma eval_expr_concat_left : forall t (e : typed_expr t) t1 t2 Hdisj,
  (forall c, mentions_col e c = true -> exists ty, In (c, ty) t1.(tuple_schema)) ->
  unique_schema (schema_union t1.(tuple_schema) t2.(tuple_schema)) ->
  @eval_expr t e (concat_tuples t1 t2 Hdisj) = @eval_expr t e t1.
Proof.
  intros t e t1 t2 Hdisj Honly Huniq.
  induction e; simpl; auto.
  - assert (Hc: mentions_col (@TECol t q) q = true).
    { simpl. apply qualified_column_eqb_refl. }
    destruct (Honly q Hc) as [ty Hin].
    apply get_typed_value_concat_left.
    + exists ty. exact Hin.
    + exact Huniq.
  - rewrite IHe1.
    + rewrite IHe2.
      * reflexivity.
      * intros c Hc. apply Honly. simpl. apply orb_true_intro. right. exact Hc.
    + intros c Hc. apply Honly. simpl. apply orb_true_intro. left. exact Hc.
  - rewrite IHe1.
    + rewrite IHe2.
      * reflexivity.
      * intros c Hc. apply Honly. simpl. apply orb_true_intro. right. exact Hc.
    + intros c Hc. apply Honly. simpl. apply orb_true_intro. left. exact Hc.
  - rewrite IHe1.
    + rewrite IHe2.
      * reflexivity.
      * intros c Hc. apply Honly. simpl. apply orb_true_intro. right. exact Hc.
    + intros c Hc. apply Honly. simpl. apply orb_true_intro. left. exact Hc.
  - rewrite IHe1.
    + rewrite IHe2.
      * reflexivity.
      * intros c Hc. apply Honly. simpl. apply orb_true_intro. right. exact Hc.
    + intros c Hc. apply Honly. simpl. apply orb_true_intro. left. exact Hc.
  - rewrite IHe; auto.
  - rewrite IHe; auto.
  - rewrite IHe1.
    + rewrite IHe2.
      * reflexivity.
      * intros c Hc. apply Honly. simpl. apply orb_true_intro. right. exact Hc.
    + intros c Hc. apply Honly. simpl. apply orb_true_intro. left. exact Hc.
Qed.

Lemma eval_pred_concat_left : forall e t1 t2 Hdisj,
  mentions_only t1.(tuple_schema) e ->
  unique_schema (schema_union t1.(tuple_schema) t2.(tuple_schema)) ->
  eval_pred e (concat_tuples t1 t2 Hdisj) = eval_pred e t1.
Proof.
  intros e t1 t2 Hdisj Honly Huniq.
  unfold eval_pred.
  rewrite eval_expr_concat_left; auto.
Qed.

Lemma eval_expr_deterministic : forall t e tu v1 v2,
  @eval_expr t e tu = Some v1 -> @eval_expr t e tu = Some v2 -> v1 = v2.
Proof.
  intros t e tu v1 v2 H1 H2.
  rewrite H1 in H2.
  injection H2; auto.
Qed.

Lemma filter_app : forall (A:Type) (p:A->bool) l1 l2,
  filter p (l1 ++ l2) = filter p l1 ++ filter p l2.
Proof.
  induction l1; simpl; intros; [reflexivity|].
  destruct (p a); simpl; now rewrite IHl1.
Qed.

Lemma filter_flat_map : forall (A B:Type) (p:B->bool) (f:A->list B) (l:list A),
  filter p (flat_map f l) = flat_map (fun x => filter p (f x)) l.
Proof.
  induction l; simpl; intros; [reflexivity|].
  rewrite filter_app, IHl. reflexivity.
Qed.

Lemma filter_const_map : forall (A B:Type) (b:bool) (f:A->B) (l:list A),
  filter (fun _ => b) (map f l) = if b then map f l else [].
Proof.
  intros A B b f l.
  induction l as [|a l' IH]; simpl.
  - destruct b; reflexivity.
  - destruct b; simpl.
    + f_equal. exact IH.
    + exact IH.
Qed.

Lemma flat_map_filter_switch : forall (A B:Type) (f:A->list B) (p:A->bool) (l:list A),
  flat_map f (filter p l) = flat_map (fun x => if p x then f x else []) l.
Proof.
  induction l; simpl; intros; [reflexivity|].
  destruct (p a); simpl; rewrite IHl; reflexivity.
Qed.

Lemma in_flat_map' : forall (A B:Type) (f:A->list B) (l:list A) (y:B),
  In y (flat_map f l) <-> exists x, In x l /\ In y (f x).
Proof.
  induction l; simpl; intros; split; intro H.
  - contradiction.
  - destruct H as [x [Hx _]]. contradiction.
  - apply in_app_or in H. destruct H as [H|H].
    + exists a. tauto.
    + apply IHl in H. destruct H as [x [Hx Hy]]. exists x. tauto.
  - destruct H as [x [Hx Hy]]. destruct Hx as [Hx|Hx].
    + subst. apply in_or_app. now left.
    + apply in_or_app. right. apply IHl. exists x. tauto.
Qed.

Lemma find_column_index_some_of_in : forall s c ty,
  In (c,ty) s -> exists i, find_column_index s c = Some i.
Proof.
  induction s as [|[c0 ty0] s IH]; simpl; intros c ty H; [contradiction|].
  destruct H as [H|H].
  - inversion H; subst.
    destruct (qualified_column_eqb_spec c c).
    + eexists. reflexivity.
    + congruence.
  - specialize (IH _ _ H).
    destruct IH as [i Hi].
    destruct (qualified_column_eqb c0 c).
    + eexists. reflexivity.
    + rewrite Hi. eexists. reflexivity.
Qed.

Lemma product_tuple_wf :
  forall b1 b2 (Hdisj : schema_disjoint b1.(bag_schema) b2.(bag_schema)) t,
    (exists t1 t2 (Hdisj': schema_disjoint t1.(tuple_schema) t2.(tuple_schema)),
      In t1 b1.(bag_tuples) /\ In t2 b2.(bag_tuples) /\
      t = concat_tuples t1 t2 Hdisj') ->
    t.(tuple_schema) = schema_union b1.(bag_schema) b2.(bag_schema).
Proof.
  intros b1 b2 Hdisj t [t1 [t2 [Hdisj' [Hin1 [Hin2 Heq]]]]].
  subst t.
  simpl.
  unfold schema_union.
  rewrite (bag_wf b1 t1 Hin1).
  rewrite (bag_wf b2 t2 Hin2).
  reflexivity.
Qed.

Lemma cast_disjoint : forall s1 s2 s1' s2',
  s1 = s1' -> s2 = s2' -> schema_disjoint s1 s2 -> schema_disjoint s1' s2'.
Proof.
  intros. subst. assumption.
Qed.

Definition product (b1 b2 : typed_bag)
  (Hdisj : schema_disjoint b1.(bag_schema) b2.(bag_schema)) : typed_bag :=
  {| bag_schema := schema_union b1.(bag_schema) b2.(bag_schema);
     bag_tuples := [];
     bag_wf := fun t H => match H with end
  |}.

Definition join_on (e : typed_expr TBool) (b1 b2 : typed_bag)
  (Hdisj : schema_disjoint b1.(bag_schema) b2.(bag_schema)) : typed_bag :=
  select_expr e (product b1 b2 Hdisj).

Lemma find_column_index_app_left_simple :
  forall s1 s2 c i,
    find_column_index s1 c = Some i ->
    find_column_index (s1 ++ s2) c = Some i.
Proof.
  induction s1 as [|[c0 ty0] s1 IH]; simpl; intros s2 c i H.
  - discriminate.
  - destruct (qualified_column_eqb c0 c) eqn:E.
    + inversion H; subst. reflexivity.
    + destruct (find_column_index s1 c) as [n|] eqn:H'.
      * inversion H; subst.
        specialize (IH s2 c n H').
        rewrite IH. reflexivity.
      * discriminate.
Qed.

Lemma filter_const_on_list :
  forall (A:Type) (p:A->bool) (L:list A) (b:bool),
    (forall x, In x L -> p x = b) ->
    filter p L = (if b then L else []).
Proof.
  intros A p L b Hc; induction L as [|a L IH]; simpl.
  - destruct b; reflexivity.
  - rewrite Hc by (left; reflexivity).
    rewrite IH; [destruct b; reflexivity|].
    intros x H; apply Hc; right; exact H.
Qed.

Lemma flat_map_ext_In :
  forall (A B:Type) (f g:A->list B) (l:list A),
    (forall x, In x l -> f x = g x) ->
    flat_map f l = flat_map g l.
Proof.
  intros A B f g l H; induction l as [|a l IH]; simpl; auto.
  rewrite H by (left; reflexivity).
  rewrite IH; auto; intros x Hx; apply H; right; exact Hx.
Qed.

Lemma concat_tuple_wf_nd (t1 t2 : typed_tuple) :
  List.length (t1.(tuple_data) ++ t2.(tuple_data)) =
  List.length (t1.(tuple_schema) ++ t2.(tuple_schema)) /\
  (forall i v,
     nth_error (t1.(tuple_data) ++ t2.(tuple_data)) i = Some (Some v) ->
     exists c t,
       nth_error (t1.(tuple_schema) ++ t2.(tuple_schema)) i = Some (c, t) /\
       value_type v = t).
Proof.
  split.
  - rewrite !app_length.
    destruct (tuple_wf t1) as [H1 _].
    destruct (tuple_wf t2) as [H2 _].
    now rewrite H1, H2.
  - intros i v H0.
    destruct (tuple_wf t1) as [Hlen1 Hty1].
    destruct (tuple_wf t2) as [Hlen2 Hty2].
    destruct (lt_dec i (List.length (tuple_data t1))).
    + rewrite nth_error_app1 in H0 by lia.
      rewrite nth_error_app1 by (rewrite <- Hlen1; lia).
      eapply Hty1; eauto.
    + rewrite nth_error_app2 in H0 by lia.
      rewrite nth_error_app2 by (rewrite <- Hlen1; lia).
      specialize (Hty2 (i - List.length (tuple_data t1)) v H0).
      destruct Hty2 as [c [t [H3 H4]]].
      exists c, t. split; auto.
      rewrite <- H3. f_equal. lia.
Qed.

Definition concat_tuples_nd (t1 t2 : typed_tuple) : typed_tuple :=
  {|
    tuple_schema := t1.(tuple_schema) ++ t2.(tuple_schema);
    tuple_data   := t1.(tuple_data)   ++ t2.(tuple_data);
    tuple_wf     := concat_tuple_wf_nd t1 t2
  |}.

Definition mentions_only_any {t} (Γ : schema) (e : typed_expr t) : Prop :=
  forall c, mentions_col e c = true -> exists ty, In (c,ty) Γ.

Lemma get_typed_value_concat_left_nd :
  forall t1 t2 c,
    (exists ty, In (c,ty) t1.(tuple_schema)) ->
    get_typed_value (concat_tuples_nd t1 t2) c = get_typed_value t1 c.
Proof.
  intros t1 t2 c [ty Hin].
  destruct (find_column_index_some_of_in _ _ _ Hin) as [i Hi].
  unfold get_typed_value, concat_tuples_nd; simpl.
  rewrite find_column_index_app_left_simple with (i:=i) (s2:=t2.(tuple_schema)) by exact Hi.
  rewrite Hi.
  destruct (tuple_wf t1) as [Hlen _].
  pose proof (find_column_index_bounds _ _ _ Hi) as Hib.
  assert (i < List.length (tuple_data t1)) by (rewrite Hlen; exact Hib).
  destruct (nth_error t1.(tuple_data) i) as [o|] eqn:Hnth.
  - rewrite nth_error_app1 by auto. rewrite Hnth. reflexivity.
  - exfalso. apply nth_error_Some in H. congruence.
Qed.

Lemma eval_expr_concat_left_nd :
  forall t (e:typed_expr t) t1 t2,
    mentions_only_any t1.(tuple_schema) e ->
    eval_expr e (concat_tuples_nd t1 t2) = eval_expr e t1.
Proof.
  induction e; intros t1 t2 Hm; simpl; try reflexivity.
  - assert (HH: mentions_col (TECol t q) q = true) by apply qualified_column_eqb_refl.
    destruct (Hm q HH) as [ty Hin].
    rewrite (get_typed_value_concat_left_nd t1 t2 q (ex_intro _ ty Hin)).
    reflexivity.
  - rewrite IHe1, IHe2; try reflexivity.
    + intros c H; apply Hm; simpl; apply orb_true_iff; right; exact H.
    + intros c H; apply Hm; simpl; apply orb_true_iff; left; exact H.
  - rewrite IHe1, IHe2; try reflexivity.
    + intros c H; apply Hm; simpl; apply orb_true_iff; right; exact H.
    + intros c H; apply Hm; simpl; apply orb_true_iff; left; exact H.
  - rewrite IHe1, IHe2; try reflexivity.
    + intros c H; apply Hm; simpl; apply orb_true_iff; right; exact H.
    + intros c H; apply Hm; simpl; apply orb_true_iff; left; exact H.
  - rewrite IHe1, IHe2; try reflexivity.
    + intros c H; apply Hm; simpl; apply orb_true_iff; right; exact H.
    + intros c H; apply Hm; simpl; apply orb_true_iff; left; exact H.
  - rewrite IHe; try reflexivity.
    intros c H; apply Hm; exact H.
  - rewrite IHe; try reflexivity.
    intros c H; apply Hm; exact H.
  - rewrite IHe1, IHe2; try reflexivity.
    + intros c H; apply Hm; simpl; apply orb_true_iff; right; exact H.
    + intros c H; apply Hm; simpl; apply orb_true_iff; left; exact H.
Qed.

Lemma eval_pred_concat_left_nd :
  forall e t1 t2,
    mentions_only t1.(tuple_schema) e ->
    eval_pred e (concat_tuples_nd t1 t2) = eval_pred e t1.
Proof.
  intros e t1 t2 Hm.
  unfold eval_pred.
  rewrite (eval_expr_concat_left_nd TBool e t1 t2).
  - reflexivity.
  - exact Hm.
Qed.

Lemma product_real_wf : forall b1 b2 (Hdisj : schema_disjoint b1.(bag_schema) b2.(bag_schema)) t,
  In t (flat_map (fun t1 => map (fun t2 => concat_tuples_nd t1 t2) b2.(bag_tuples)) b1.(bag_tuples)) ->
  t.(tuple_schema) = schema_union b1.(bag_schema) b2.(bag_schema).
Proof.
  intros b1 b2 Hdisj t Hin.
  apply in_flat_map' in Hin.
  destruct Hin as [t1 [Hin1 Hin2]].
  apply in_map_iff in Hin2.
  destruct Hin2 as [t2 [Heq Hin2']].
  subst t.
  simpl.
  unfold schema_union.
  rewrite (bag_wf b1 t1 Hin1).
  rewrite (bag_wf b2 t2 Hin2').
  reflexivity.
Qed.

Definition product_real (b1 b2 : typed_bag)
  (Hdisj : schema_disjoint b1.(bag_schema) b2.(bag_schema)) : typed_bag :=
  let tuples :=
      flat_map (fun t1 =>
                  map (fun t2 => concat_tuples_nd t1 t2) b2.(bag_tuples))
               b1.(bag_tuples) in
  {|
    bag_schema := schema_union b1.(bag_schema) b2.(bag_schema);
    bag_tuples := tuples;
    bag_wf := product_real_wf b1 b2 Hdisj
  |}.

Lemma select_pushdown_product_real :
  forall e b1 b2 (Hdisj : schema_disjoint b1.(bag_schema) b2.(bag_schema)),
    mentions_only b1.(bag_schema) e ->
    bag_eq (select_expr e (product_real b1 b2 Hdisj))
           (product_real (select_expr e b1) b2 Hdisj).
Proof.
  intros e [s1 ts1 wf1] [s2 ts2 wf2] Hdisj Honly.
  unfold bag_eq, select_expr, product_real, select; simpl.
  split; [reflexivity|].
  set (p := fun t => tri_to_bool (eval_pred e t)).
  rewrite filter_flat_map.
  assert (flat_map (fun t1 => filter p (map (fun t2 => concat_tuples_nd t1 t2) ts2)) ts1 =
          flat_map (fun t1 => if p t1 then map (fun t2 => concat_tuples_nd t1 t2) ts2 else []) ts1).
  { apply flat_map_ext_In; intros t1 Hin1.
    assert (Hconst : forall x, In x (map (fun t2 => concat_tuples_nd t1 t2) ts2) -> p x = p t1).
    { intros x Hx.
      apply in_map_iff in Hx.
      destruct Hx as [t2 [Heq Hin2]].
      subst x.
      unfold p.
      assert (Hm1 : mentions_only (tuple_schema t1) e).
      { intros c Hc. destruct (Honly c Hc) as [ty Hin]. exists ty.
        rewrite (wf1 t1 Hin1). exact Hin. }
      rewrite (eval_pred_concat_left_nd e t1 t2 Hm1). reflexivity. }
    rewrite (filter_const_on_list _ _ _ _ Hconst).
    reflexivity. }
  rewrite H.
  rewrite flat_map_filter_switch.
  apply Permutation_refl.
Qed.

Lemma select_pushdown_product_left :
  forall e b1 b2 (Hdisj : schema_disjoint b1.(bag_schema) b2.(bag_schema)),
  mentions_only b1.(bag_schema) e ->
  bag_eq (select_expr e (product b1 b2 Hdisj))
         (product (select_expr e b1) b2 Hdisj).
Proof.
  intros e [s1 ts1 wf1] [s2 ts2 wf2] Hdisj Honly.
  unfold bag_eq, select_expr, product, select; simpl.
  split.
  - reflexivity.
  - apply Permutation_refl.
Qed.
