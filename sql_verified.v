Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Program.Program.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
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
  | TBool : sql_type
  | TDate : sql_type
  | TTime : sql_type
  | TDecimal : nat -> nat -> sql_type
  | TArray : sql_type -> sql_type
  | TJson : sql_type.

Inductive json_value : Type :=
  | JNull : json_value
  | JBool : bool -> json_value
  | JNumber : Z -> json_value
  | JString : string -> json_value
  | JArray : list json_value -> json_value
  | JObject : list (string * json_value) -> json_value.

Inductive sql_value : Type :=
  | VInt : Z -> sql_value
  | VString : string -> sql_value
  | VBool : bool -> sql_value
  | VDate : Z -> sql_value
  | VTime : Z -> sql_value
  | VDecimal : nat -> nat -> Z -> sql_value
  | VArray : sql_type -> list sql_value -> sql_value
  | VJson : json_value -> sql_value
  | VNull : sql_type -> sql_value.

Definition value_type (v : sql_value) : sql_type :=
  match v with
  | VInt _ => TInt
  | VString _ => TString
  | VBool _ => TBool
  | VDate _ => TDate
  | VTime _ => TTime
  | VDecimal p s _ => TDecimal p s
  | VArray t _ => TArray t
  | VJson _ => TJson
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
  | TEIsDistinctFrom : forall t, typed_expr t -> typed_expr t -> typed_expr TBool
  | TELike : typed_expr TString -> typed_expr TString -> typed_expr TBool
  | TEConcat : typed_expr TString -> typed_expr TString -> typed_expr TString
  | TESubstring : typed_expr TString -> typed_expr TInt -> typed_expr TInt -> typed_expr TString
  | TEAdd : typed_expr TInt -> typed_expr TInt -> typed_expr TInt.

Definition sql_type_eq_dec (t1 t2 : sql_type) : {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Definition option_eq_dec {A : Type} (A_eq_dec : forall x y : A, {x = y} + {x <> y})
                                    (o1 o2 : option A) : {o1 = o2} + {o1 <> o2}.
Proof.
  destruct o1, o2.
  - destruct (A_eq_dec a a0).
    + subst. left. reflexivity.
    + right. intro H. injection H. contradiction.
  - right. discriminate.
  - right. discriminate.
  - left. reflexivity.
Defined.

Definition qualified_column_eq_dec (c1 c2 : qualified_column) : {c1 = c2} + {c1 <> c2}.
Proof.
  destruct c1 as [t1 n1], c2 as [t2 n2].
  destruct (option_eq_dec String.string_dec t1 t2).
  - destruct (String.string_dec n1 n2).
    + subst. left. reflexivity.
    + right. intro H. injection H. contradiction.
  - right. intro H. injection H. intros. contradiction.
Defined.

Definition prod_eq_dec {A B : Type} (A_eq_dec : forall x y : A, {x = y} + {x <> y})
                                     (B_eq_dec : forall x y : B, {x = y} + {x <> y})
                                     (p1 p2 : A * B) : {p1 = p2} + {p1 <> p2}.
Proof.
  destruct p1 as [a1 b1], p2 as [a2 b2].
  destruct (A_eq_dec a1 a2).
  - destruct (B_eq_dec b1 b2).
    + subst. left. reflexivity.
    + right. intro H. injection H. contradiction.
  - right. intro H. injection H. intros. contradiction.
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

Fixpoint string_length (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String _ rest => S (string_length rest)
  end.

Fixpoint string_matches_pattern_fuel (fuel : nat) (s : string) (pattern : string) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match pattern with
      | EmptyString => match s with EmptyString => true | _ => false end
      | String c rest_pattern =>
          if Ascii.eqb c "%"%char then
            orb (string_matches_pattern_fuel fuel' s rest_pattern)
                (match s with
                 | EmptyString => false
                 | String _ rest_s => string_matches_pattern_fuel fuel' rest_s pattern
                 end)
          else if Ascii.eqb c "_"%char then
            match s with
            | EmptyString => false
            | String _ rest_s => string_matches_pattern_fuel fuel' rest_s rest_pattern
            end
          else
            match s with
            | EmptyString => false
            | String c' rest_s =>
                if Ascii.eqb c c' then string_matches_pattern_fuel fuel' rest_s rest_pattern
                else false
            end
      end
  end.

Definition string_matches_pattern (s : string) (pattern : string) : bool :=
  let fuel := string_length s + string_length pattern in
  string_matches_pattern_fuel fuel s pattern.

Definition sql_like_tri (v1 v2 : sql_value) : tri :=
  match v1, v2 with
  | VNull _, _ => UnknownT
  | _, VNull _ => UnknownT
  | VString s, VString pattern => tri_of_bool (string_matches_pattern s pattern)
  | _, _ => UnknownT
  end.

Definition sql_concat (v1 v2 : sql_value) : sql_value :=
  match v1, v2 with
  | VString s1, VString s2 => VString (String.append s1 s2)
  | VNull TString, _ => VNull TString
  | _, VNull TString => VNull TString
  | _, _ => VNull TString
  end.

Fixpoint string_substring (s : string) (start : nat) (length : nat) : string :=
  match start, s with
  | O, _ =>
      let fix take n str :=
        match n, str with
        | O, _ => EmptyString
        | S n', EmptyString => EmptyString
        | S n', String c rest => String c (take n' rest)
        end
      in take length s
  | S start', EmptyString => EmptyString
  | S start', String _ rest => string_substring rest start' length
  end.

Definition sql_substring (v : sql_value) (start : Z) (len : Z) : sql_value :=
  match v with
  | VString s =>
      let start_nat := Z.to_nat (Z.max 0 (start - 1)) in
      let len_nat := Z.to_nat (Z.max 0 len) in
      VString (string_substring s start_nat len_nat)
  | VNull TString => VNull TString
  | _ => VNull TString
  end.

Definition sql_add (v1 v2 : sql_value) : sql_value :=
  match v1, v2 with
  | VInt n1, VInt n2 => VInt (n1 + n2)
  | VNull TInt, _ => VNull TInt
  | _, VNull TInt => VNull TInt
  | _, _ => VNull TInt
  end.

Definition sql_sub (v1 v2 : sql_value) : sql_value :=
  match v1, v2 with
  | VInt n1, VInt n2 => VInt (n1 - n2)
  | VNull TInt, _ => VNull TInt
  | _, VNull TInt => VNull TInt
  | _, _ => VNull TInt
  end.

Definition sql_mul (v1 v2 : sql_value) : sql_value :=
  match v1, v2 with
  | VInt n1, VInt n2 => VInt (n1 * n2)
  | VNull TInt, _ => VNull TInt
  | _, VNull TInt => VNull TInt
  | _, _ => VNull TInt
  end.

Definition sql_div (v1 v2 : sql_value) : sql_value :=
  match v1, v2 with
  | VInt n1, VInt n2 => if Z.eqb n2 0 then VNull TInt else VInt (n1 / n2)
  | VNull TInt, _ => VNull TInt
  | _, VNull TInt => VNull TInt
  | _, _ => VNull TInt
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
  | TELike e1 e2 =>
      match @eval_expr _ e1 tu, @eval_expr _ e2 tu with
      | Some v1, Some v2 =>
          Some (match sql_like_tri v1 v2 with
                | TrueT => VBool true
                | FalseT => VBool false
                | UnknownT => VNull TBool
                end)
      | _, _ => None
      end
  | TEConcat e1 e2 =>
      match @eval_expr _ e1 tu, @eval_expr _ e2 tu with
      | Some v1, Some v2 => Some (sql_concat v1 v2)
      | _, _ => None
      end
  | TESubstring e1 e2 e3 =>
      match @eval_expr _ e1 tu, @eval_expr _ e2 tu, @eval_expr _ e3 tu with
      | Some v1, Some (VInt start), Some (VInt len) => Some (sql_substring v1 start len)
      | Some v1, _, _ => Some (sql_substring v1 1 0)
      | _, _, _ => None
      end
  | TEAdd e1 e2 =>
      match @eval_expr _ e1 tu, @eval_expr _ e2 tu with
      | Some v1, Some v2 => Some (sql_add v1 v2)
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
  | HT_IsDistinctFrom : forall Γ t e1 e2, has_type Γ t e1 -> has_type Γ t e2 -> has_type Γ TBool (@TEIsDistinctFrom t e1 e2)
  | HT_Like : forall Γ e1 e2, has_type Γ TString e1 -> has_type Γ TString e2 -> has_type Γ TBool (TELike e1 e2)
  | HT_Concat : forall Γ e1 e2, has_type Γ TString e1 -> has_type Γ TString e2 -> has_type Γ TString (TEConcat e1 e2)
  | HT_Substring : forall Γ e1 e2 e3, has_type Γ TString e1 -> has_type Γ TInt e2 -> has_type Γ TInt e3 -> has_type Γ TString (TESubstring e1 e2 e3)
  | HT_Add : forall Γ e1 e2, has_type Γ TInt e1 -> has_type Γ TInt e2 -> has_type Γ TInt (TEAdd e1 e2).

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
  bag_wf : forall t, In t bag_tuples -> t.(tuple_schema) = bag_schema;
  bag_unique : unique_schema bag_schema
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
     bag_wf := filter_preserves_schema _ _ _ (bag_wf b);
     bag_unique := b.(bag_unique)
  |}.

Definition select_expr (e : typed_expr TBool) (b : typed_bag) : typed_bag :=
  select (fun t => eval_pred e t) b.

Definition bag_eq (b1 b2 : typed_bag) : Prop :=
  b1.(bag_schema) = b2.(bag_schema) /\
  Permutation b1.(bag_tuples) b2.(bag_tuples).

Lemma bag_eq_refl : forall b, bag_eq b b.
Proof.
  intros b.
  unfold bag_eq.
  split.
  - reflexivity.
  - apply Permutation_refl.
Qed.

Lemma bag_eq_sym : forall b1 b2, bag_eq b1 b2 -> bag_eq b2 b1.
Proof.
  intros b1 b2 H.
  unfold bag_eq in *.
  destruct H as [Hschema Hperm].
  split.
  - symmetry. exact Hschema.
  - apply Permutation_sym. exact Hperm.
Qed.

Lemma bag_eq_trans : forall b1 b2 b3,
  bag_eq b1 b2 -> bag_eq b2 b3 -> bag_eq b1 b3.
Proof.
  intros b1 b2 b3 H12 H23.
  unfold bag_eq in *.
  destruct H12 as [Hschema12 Hperm12].
  destruct H23 as [Hschema23 Hperm23].
  split.
  - transitivity (bag_schema b2); assumption.
  - apply Permutation_trans with (bag_tuples b2); assumption.
Qed.

Instance bag_eq_equiv : Equivalence bag_eq.
Proof.
  constructor.
  - exact bag_eq_refl.
  - exact bag_eq_sym.
  - exact bag_eq_trans.
Qed.

Definition pred_eq (p1 p2 : typed_tuple -> tri) : Prop :=
  forall t, p1 t = p2 t.

Lemma Permutation_filter_compat : forall {A} (f : A -> bool) l1 l2,
  Permutation l1 l2 -> Permutation (filter f l1) (filter f l2).
Proof.
  intros A f l1 l2 Hperm.
  induction Hperm.
  - apply Permutation_refl.
  - simpl. destruct (f x); [apply perm_skip|]; assumption.
  - simpl. destruct (f y); destruct (f x); try apply perm_swap; apply Permutation_refl.
  - apply Permutation_trans with (filter f l'); assumption.
Qed.

Instance select_Proper : Proper (pred_eq ==> bag_eq ==> bag_eq) select.
Proof.
  intros p1 p2 Hp b1 b2 Hb.
  unfold bag_eq in *.
  destruct Hb as [Hschema Hperm].
  unfold select.
  simpl.
  split.
  - assumption.
  - assert (filter (fun t => tri_to_bool (p1 t)) (bag_tuples b1) =
            filter (fun t => tri_to_bool (p2 t)) (bag_tuples b1)).
    { apply filter_ext. intro x. f_equal. apply Hp. }
    rewrite H.
    apply Permutation_filter_compat.
    assumption.
Qed.

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
       bag_wf := fun t H => match H with end;
       bag_unique := b.(bag_unique) |}.
Proof.
  intros [s ts wf uniq].
  unfold bag_eq, select; simpl.
  split.
  - reflexivity.
  - rewrite filter_false_nil. apply Permutation_refl.
Qed.

Lemma count_star_empty : forall s (Huniq : unique_schema s),
  agg_count_star {| bag_schema := s; bag_tuples := []; bag_wf := fun t H => match H with end; bag_unique := Huniq |} = VInt 0.
Proof.
  intros.
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

Lemma agg_sum_empty : forall col s (Huniq : unique_schema s),
  agg_sum col {| bag_schema := s; bag_tuples := []; bag_wf := fun t H => match H with end; bag_unique := Huniq |} = VNull TInt.
Proof.
  intros.
  unfold agg_sum.
  simpl.
  reflexivity.
Qed.

Lemma agg_min_empty : forall col s (Huniq : unique_schema s),
  agg_min col {| bag_schema := s; bag_tuples := []; bag_wf := fun t H => match H with end; bag_unique := Huniq |} = VNull TInt.
Proof.
  intros.
  unfold agg_min.
  simpl.
  reflexivity.
Qed.

Lemma agg_max_empty : forall col s (Huniq : unique_schema s),
  agg_max col {| bag_schema := s; bag_tuples := []; bag_wf := fun t H => match H with end; bag_unique := Huniq |} = VNull TInt.
Proof.
  intros.
  unfold agg_max.
  simpl.
  reflexivity.
Qed.

Lemma agg_avg_empty : forall col s (Huniq : unique_schema s),
  agg_avg col {| bag_schema := s; bag_tuples := []; bag_wf := fun t H => match H with end; bag_unique := Huniq |} = VNull TInt.
Proof.
  intros.
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
  | TELike e1 e2 => orb (mentions_col e1 c) (mentions_col e2 c)
  | TEConcat e1 e2 => orb (mentions_col e1 c) (mentions_col e2 c)
  | TESubstring e1 e2 e3 => orb (orb (mentions_col e1 c) (mentions_col e2 c)) (mentions_col e3 c)
  | TEAdd e1 e2 => orb (mentions_col e1 c) (mentions_col e2 c)
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
  - rewrite IHe1, IHe2, IHe3; try reflexivity.
    + intros c H. apply Honly.
      change (mentions_col (TESubstring e1 e2 e3) c = true).
      simpl mentions_col. rewrite H.
      destruct (mentions_col e1 c); destruct (mentions_col e2 c); reflexivity.
    + intros c H. apply Honly.
      change (mentions_col (TESubstring e1 e2 e3) c = true).
      simpl mentions_col. rewrite H.
      destruct (mentions_col e1 c); reflexivity.
    + intros c H. apply Honly.
      change (mentions_col (TESubstring e1 e2 e3) c = true).
      simpl mentions_col. rewrite H. reflexivity.
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

Lemma disjoint_union_unique : forall s1 s2,
  schema_disjoint s1 s2 ->
  unique_schema s1 ->
  unique_schema s2 ->
  unique_schema (s1 ++ s2).
Proof.
  unfold unique_schema, schema_disjoint.
  intros s1 s2 Hdisj Huniq1 Huniq2 i j c t1 t2 Hneq Hi Hj.
  destruct (lt_dec i (List.length s1)).
  - rewrite nth_error_app1 in Hi by assumption.
    destruct (lt_dec j (List.length s1)).
    + rewrite nth_error_app1 in Hj by assumption.
      apply (Huniq1 i j c t1 t2); assumption.
    + rewrite nth_error_app2 in Hj by lia.
      apply nth_error_In in Hi.
      apply nth_error_In in Hj.
      apply (Hdisj c t1 t2); assumption.
  - rewrite nth_error_app2 in Hi by lia.
    destruct (lt_dec j (List.length s1)).
    + rewrite nth_error_app1 in Hj by assumption.
      apply nth_error_In in Hi.
      apply nth_error_In in Hj.
      apply (Hdisj c t2 t1); assumption.
    + rewrite nth_error_app2 in Hj by lia.
      apply (Huniq2 (i - List.length s1) (j - List.length s1) c t1 t2); lia || assumption.
Qed.

Definition product (b1 b2 : typed_bag)
  (Hdisj : schema_disjoint b1.(bag_schema) b2.(bag_schema)) : typed_bag :=
  {| bag_schema := schema_union b1.(bag_schema) b2.(bag_schema);
     bag_tuples := flat_map (fun t1 => map (fun t2 => concat_tuples_nd t1 t2) b2.(bag_tuples)) b1.(bag_tuples);
     bag_wf := product_real_wf b1 b2 Hdisj;
     bag_unique := disjoint_union_unique b1.(bag_schema) b2.(bag_schema) Hdisj b1.(bag_unique) b2.(bag_unique)
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
  - rewrite IHe1, IHe2; try reflexivity.
    + intros c H; apply Hm; simpl; apply orb_true_iff; right; exact H.
    + intros c H; apply Hm; simpl; apply orb_true_iff; left; exact H.
  - rewrite IHe1, IHe2; try reflexivity.
    + intros c H; apply Hm; simpl; apply orb_true_iff; right; exact H.
    + intros c H; apply Hm; simpl; apply orb_true_iff; left; exact H.
  - assert (H1: eval_expr e1 (concat_tuples_nd t1 t2) = eval_expr e1 t1).
    { apply IHe1. intros c Hc. apply Hm. change (mentions_col (TESubstring e1 e2 e3) c = true).
      simpl mentions_col. rewrite Hc. reflexivity. }
    assert (H2: eval_expr e2 (concat_tuples_nd t1 t2) = eval_expr e2 t1).
    { apply IHe2. intros c Hc. apply Hm. change (mentions_col (TESubstring e1 e2 e3) c = true).
      simpl mentions_col. rewrite Hc. destruct (mentions_col e1 c); reflexivity. }
    assert (H3: eval_expr e3 (concat_tuples_nd t1 t2) = eval_expr e3 t1).
    { apply IHe3. intros c Hc. apply Hm. change (mentions_col (TESubstring e1 e2 e3) c = true).
      simpl mentions_col. rewrite Hc.
      destruct (mentions_col e1 c); destruct (mentions_col e2 c); reflexivity. }
    rewrite H1, H2, H3. reflexivity.
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

Lemma get_typed_value_concat_right_nd :
  forall t1 t2 c,
    (exists ty, In (c, ty) t2.(tuple_schema)) ->
    schema_disjoint t1.(tuple_schema) t2.(tuple_schema) ->
    unique_schema t1.(tuple_schema) ->
    unique_schema t2.(tuple_schema) ->
    get_typed_value (concat_tuples_nd t1 t2) c = get_typed_value t2 c.
Proof.
  intros t1 t2 c [ty Hin] Hdisj Huniq1 Huniq2.
  unfold get_typed_value, concat_tuples_nd; simpl.
  destruct (find_column_index t2.(tuple_schema) c) as [i|] eqn:Hi.
  - destruct (find_column_index (t1.(tuple_schema) ++ t2.(tuple_schema)) c) as [j|] eqn:Hj.
    + assert (j = List.length t1.(tuple_schema) + i).
      { pose proof (find_column_index_app_right t1.(tuple_schema) t2.(tuple_schema) c i) as H.
        assert (unique_schema (t1.(tuple_schema) ++ t2.(tuple_schema))).
        { apply disjoint_union_unique; assumption. }
        assert (forall ty', ~In (c, ty') t1.(tuple_schema)).
        { intros ty' Hin'.
          unfold schema_disjoint in Hdisj.
          apply (Hdisj c ty' ty); assumption. }
        specialize (H H0 Hi H1).
        rewrite H in Hj. injection Hj. auto. }
      subst j.
      destruct (tuple_wf t1) as [Hlen1 _].
      destruct (tuple_wf t2) as [Hlen2 _].
      rewrite <- Hlen1.
      rewrite nth_error_app2 by lia.
      replace (List.length (tuple_data t1) + i - List.length (tuple_data t1)) with i by lia.
      reflexivity.
    + exfalso.
      assert (exists n, find_column_index (t1.(tuple_schema) ++ t2.(tuple_schema)) c = Some n).
      { destruct (find_column_index_some_of_in (t1.(tuple_schema) ++ t2.(tuple_schema)) c ty) as [n Hn].
        apply in_or_app. right. exact Hin.
        exists n. exact Hn. }
      destruct H as [n Hn]. congruence.
  - exfalso.
    destruct (find_column_index_some_of_in t2.(tuple_schema) c ty Hin) as [i' Hi'].
    congruence.
Qed.

Lemma eval_expr_concat_right_nd :
  forall t (e : typed_expr t) t1 t2,
    mentions_only_any t2.(tuple_schema) e ->
    schema_disjoint t1.(tuple_schema) t2.(tuple_schema) ->
    unique_schema t1.(tuple_schema) ->
    unique_schema t2.(tuple_schema) ->
    eval_expr e (concat_tuples_nd t1 t2) = eval_expr e t2.
Proof.
  induction e; intros t1 t2 Hm Hdisj Huniq1 Huniq2; simpl; try reflexivity.
  - unfold mentions_only_any in Hm.
    assert (mentions_col (TECol t q) q = true) by apply qualified_column_eqb_refl.
    destruct (Hm q H) as [ty Hin].
    apply get_typed_value_concat_right_nd; try assumption.
    exists ty. exact Hin.
  - rewrite IHe1 by (try assumption; intros c Hc; apply Hm; simpl; apply orb_true_iff; left; exact Hc).
    rewrite IHe2 by (try assumption; intros c Hc; apply Hm; simpl; apply orb_true_iff; right; exact Hc).
    reflexivity.
  - rewrite IHe1 by (try assumption; intros c Hc; apply Hm; simpl; apply orb_true_iff; left; exact Hc).
    rewrite IHe2 by (try assumption; intros c Hc; apply Hm; simpl; apply orb_true_iff; right; exact Hc).
    reflexivity.
  - assert (H1: eval_expr e1 (concat_tuples_nd t1 t2) = eval_expr e1 t2).
    { apply IHe1; try assumption. intros c Hc. apply Hm. simpl. apply orb_true_iff. left. exact Hc. }
    assert (H2: eval_expr e2 (concat_tuples_nd t1 t2) = eval_expr e2 t2).
    { apply IHe2; try assumption. intros c Hc. apply Hm. simpl. apply orb_true_iff. right. exact Hc. }
    rewrite H1, H2. reflexivity.
  - assert (H1: eval_expr e1 (concat_tuples_nd t1 t2) = eval_expr e1 t2).
    { apply IHe1; try assumption. intros c Hc. apply Hm. simpl. apply orb_true_iff. left. exact Hc. }
    assert (H2: eval_expr e2 (concat_tuples_nd t1 t2) = eval_expr e2 t2).
    { apply IHe2; try assumption. intros c Hc. apply Hm. simpl. apply orb_true_iff. right. exact Hc. }
    rewrite H1, H2. reflexivity.
  - rewrite IHe by (try assumption; exact Hm). reflexivity.
  - rewrite IHe by (try assumption; exact Hm). reflexivity.
  - rewrite IHe1 by (try assumption; intros c Hc; apply Hm; simpl; apply orb_true_iff; left; exact Hc).
    rewrite IHe2 by (try assumption; intros c Hc; apply Hm; simpl; apply orb_true_iff; right; exact Hc).
    reflexivity.
  - rewrite IHe1 by (try assumption; intros c Hc; apply Hm; simpl; apply orb_true_iff; left; exact Hc).
    rewrite IHe2 by (try assumption; intros c Hc; apply Hm; simpl; apply orb_true_iff; right; exact Hc).
    reflexivity.
  - rewrite IHe1 by (try assumption; intros c Hc; apply Hm; simpl; apply orb_true_iff; left; exact Hc).
    rewrite IHe2 by (try assumption; intros c Hc; apply Hm; simpl; apply orb_true_iff; right; exact Hc).
    reflexivity.
  - assert (H1: eval_expr e1 (concat_tuples_nd t1 t2) = eval_expr e1 t2).
    { apply IHe1; try assumption. intros c Hc. apply Hm.
      change (mentions_col (TESubstring e1 e2 e3) c = true).
      simpl mentions_col. rewrite Hc. reflexivity. }
    assert (H2: eval_expr e2 (concat_tuples_nd t1 t2) = eval_expr e2 t2).
    { apply IHe2; try assumption. intros c Hc. apply Hm.
      change (mentions_col (TESubstring e1 e2 e3) c = true).
      simpl mentions_col. rewrite Hc. destruct (mentions_col e1 c); reflexivity. }
    assert (H3: eval_expr e3 (concat_tuples_nd t1 t2) = eval_expr e3 t2).
    { apply IHe3; try assumption. intros c Hc. apply Hm.
      change (mentions_col (TESubstring e1 e2 e3) c = true).
      simpl mentions_col. rewrite Hc.
      destruct (mentions_col e1 c); destruct (mentions_col e2 c); reflexivity. }
    rewrite H1, H2, H3. reflexivity.
  - rewrite IHe1 by (try assumption; intros c Hc; apply Hm; simpl; apply orb_true_iff; left; exact Hc).
    rewrite IHe2 by (try assumption; intros c Hc; apply Hm; simpl; apply orb_true_iff; right; exact Hc).
    reflexivity.
Qed.

Lemma eval_pred_concat_right_nd :
  forall e t1 t2,
    mentions_only t2.(tuple_schema) e ->
    schema_disjoint t1.(tuple_schema) t2.(tuple_schema) ->
    unique_schema t1.(tuple_schema) ->
    unique_schema t2.(tuple_schema) ->
    eval_pred e (concat_tuples_nd t1 t2) = eval_pred e t2.
Proof.
  intros e t1 t2 Hm Hdisj Huniq1 Huniq2.
  unfold eval_pred.
  rewrite eval_expr_concat_right_nd; try assumption.
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
    bag_wf := product_real_wf b1 b2 Hdisj;
    bag_unique := disjoint_union_unique b1.(bag_schema) b2.(bag_schema) Hdisj b1.(bag_unique) b2.(bag_unique)
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

Lemma select_pushdown_product_right :
  forall e b1 b2 (Hdisj : schema_disjoint b1.(bag_schema) b2.(bag_schema)),
  mentions_only b2.(bag_schema) e ->
  bag_eq (select_expr e (product b1 b2 Hdisj))
         (product b1 (select_expr e b2) Hdisj).
Proof.
  intros e [s1 ts1 wf1 uniq1] [s2 ts2 wf2 uniq2] Hdisj Honly.
  unfold bag_eq, select_expr, product, select; simpl.
  split; [reflexivity|].
  set (p := fun t => tri_to_bool (eval_pred e t)).
  rewrite filter_flat_map.
  assert (flat_map (fun t1 => filter p (map (fun t2 => concat_tuples_nd t1 t2) ts2)) ts1 =
          flat_map (fun t1 => map (fun t2 => concat_tuples_nd t1 t2) (filter p ts2)) ts1).
  { apply flat_map_ext_In; intros t1 Hin1.
    assert (H: forall t2, In t2 ts2 -> p (concat_tuples_nd t1 t2) = p t2).
    { intros t2 Hin2.
      unfold p.
      assert (Hm2 : mentions_only (tuple_schema t2) e).
      { intros c Hc. destruct (Honly c Hc) as [ty Hin]. exists ty.
        rewrite (wf2 t2 Hin2). exact Hin. }
      assert (Hdisj': schema_disjoint (tuple_schema t1) (tuple_schema t2)).
      { intros c ty1 ty2 HinT1 HinT2.
        rewrite (wf1 t1 Hin1) in HinT1.
        rewrite (wf2 t2 Hin2) in HinT2.
        apply (Hdisj c ty1 ty2 HinT1 HinT2). }
      assert (Huniq1': unique_schema (tuple_schema t1)).
      { rewrite (wf1 t1 Hin1). exact uniq1. }
      assert (Huniq2': unique_schema (tuple_schema t2)).
      { rewrite (wf2 t2 Hin2). exact uniq2. }
      rewrite (eval_pred_concat_right_nd e t1 t2 Hm2 Hdisj' Huniq1' Huniq2'). reflexivity. }
    clear Honly wf1 wf2 Hdisj uniq1 uniq2.
    induction ts2 as [|t2 ts2' IH]; simpl; [reflexivity|].
    rewrite H by (left; reflexivity).
    destruct (p t2); simpl.
    - f_equal. apply IH. intros. apply H. right. assumption.
    - apply IH. intros. apply H. right. assumption. }
  rewrite H.
  apply Permutation_refl.
Qed.

Fixpoint project_schema (cols : list qualified_column) (s : schema) : schema :=
  match cols with
  | [] => []
  | c :: cols' =>
      match find (fun ct => qualified_column_eqb (fst ct) c) s with
      | Some ct => ct :: project_schema cols' s
      | None => project_schema cols' s
      end
  end.

Lemma project_schema_subset : forall cols s c ty,
  In (c, ty) (project_schema cols s) ->
  In c cols /\ In (c, ty) s.
Proof.
  induction cols; intros s c ty H; simpl in H.
  - contradiction.
  - simpl in H.
    destruct (find (fun ct => qualified_column_eqb (fst ct) a) s) as [[c' ty']|] eqn:Hfind.
    + simpl in H.
      destruct H as [H | H].
      * injection H; intros; subst.
        apply find_some in Hfind.
        destruct Hfind as [Hin Heqb].
        simpl in Heqb.
        destruct (qualified_column_eqb_spec c a).
        -- subst. split; [left; reflexivity | exact Hin].
        -- discriminate.
      * destruct (IHcols s c ty H) as [H1 H2].
        split; [right; exact H1 | exact H2].
    + destruct (IHcols s c ty H) as [H1 H2].
      split; [right; exact H1 | exact H2].
Qed.

Lemma select_pushdown_product_left :
  forall e b1 b2 (Hdisj : schema_disjoint b1.(bag_schema) b2.(bag_schema)),
  mentions_only b1.(bag_schema) e ->
  bag_eq (select_expr e (product b1 b2 Hdisj))
         (product (select_expr e b1) b2 Hdisj).
Proof.
  intros e [s1 ts1 wf1] [s2 ts2 wf2] Hdisj Honly.
  unfold bag_eq, select_expr, product, select; simpl.
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

Fixpoint project_tuple_data (cols : list qualified_column) (s : schema) (data : list (option sql_value)) : list (option sql_value) :=
  match cols with
  | [] => []
  | c :: cols' =>
      match find (fun ct => qualified_column_eqb (fst ct) c) s with
      | Some _ =>
          match find_column_index s c with
          | Some i =>
              match nth_error data i with
              | Some v => v :: project_tuple_data cols' s data
              | None => None :: project_tuple_data cols' s data
              end
          | None => None :: project_tuple_data cols' s data
          end
      | None => project_tuple_data cols' s data
      end
  end.

Lemma project_tuple_data_length : forall cols s data,
  List.length (project_tuple_data cols s data) = List.length (project_schema cols s).
Proof.
  induction cols; intros; simpl.
  - reflexivity.
  - destruct (find (fun ct => qualified_column_eqb (fst ct) a) s).
    + simpl. destruct (find_column_index s a).
      * destruct (nth_error data n); simpl; f_equal; apply IHcols.
      * simpl; f_equal; apply IHcols.
    + apply IHcols.
Qed.


Lemma project_tuple_basic_wf : forall cols s data,
  List.length (project_tuple_data cols s data) = List.length (project_schema cols s) /\
  (forall i v,
    nth_error (project_tuple_data cols s data) i = Some (Some v) ->
    exists c t, nth_error (project_schema cols s) i = Some (c, t)).
Proof.
  intros cols s data.
  split.
  - generalize dependent data.
    generalize dependent s.
    induction cols; intros; simpl.
    + reflexivity.
    + destruct (find (fun ct => qualified_column_eqb (fst ct) a) s).
      * simpl.
        destruct (find_column_index s a).
        -- destruct (nth_error data n); simpl; f_equal; apply IHcols.
        -- simpl; f_equal; apply IHcols.
      * apply IHcols.
  - intros i v H.
    generalize dependent i.
    generalize dependent v.
    generalize dependent data.
    generalize dependent s.
    induction cols; intros; simpl in H.
    + destruct i; discriminate.
    + destruct (find (fun ct => qualified_column_eqb (fst ct) a) s) as [p|] eqn:Hfind.
      * destruct (find_column_index s a) as [idx|] eqn:Hidx.
        -- destruct (nth_error data idx).
           ++ destruct i; simpl in H.
              ** injection H; intros; subst.
                 destruct p as [c t].
                 exists c, t.
                 simpl project_schema.
                 rewrite Hfind.
                 simpl.
                 reflexivity.
              ** destruct (IHcols s data v i H) as [c' [t' Hnth]].
                 exists c', t'.
                 simpl project_schema.
                 rewrite Hfind.
                 simpl.
                 exact Hnth.
           ++ destruct i; simpl in H.
              ** discriminate.
              ** destruct (IHcols s data v i H) as [c' [t' Hnth]].
                 exists c', t'.
                 simpl project_schema.
                 rewrite Hfind.
                 simpl.
                 exact Hnth.
        -- destruct i; simpl in H.
           ++ discriminate.
           ++ destruct (IHcols s data v i H) as [c' [t' Hnth]].
              exists c', t'.
              simpl project_schema.
              rewrite Hfind.
              simpl.
              exact Hnth.
      * destruct (IHcols s data v i H) as [c' [t' Hnth]].
        exists c', t'.
        simpl project_schema.
        rewrite Hfind.
        exact Hnth.
Qed.

Lemma project_tuple_full_wf : forall cols tu,
  unique_schema tu.(tuple_schema) ->
  let new_schema := project_schema cols tu.(tuple_schema) in
  let new_data := project_tuple_data cols tu.(tuple_schema) tu.(tuple_data) in
  List.length new_data = List.length new_schema /\
  (forall i v,
    nth_error new_data i = Some (Some v) ->
    exists c t, nth_error new_schema i = Some (c, t) /\ value_type v = t).
Proof.
  intros cols tu Huniq.
  simpl.
  destruct (project_tuple_basic_wf cols tu.(tuple_schema) tu.(tuple_data)) as [Hlen Hex].
  split.
  - exact Hlen.
  - intros i v H.
    destruct (Hex i v H) as [c [t Hnth]].
    exists c, t.
    split.
    + exact Hnth.
    + destruct (tuple_wf tu) as [_ Hwf].
      generalize dependent v.
      generalize dependent i.
      generalize dependent c.
      generalize dependent t.
      generalize dependent tu.
      induction cols; intros.
      * simpl in H. destruct i; discriminate.
      * simpl in H.
        destruct (find (fun ct => qualified_column_eqb (fst ct) a) (tuple_schema tu)) as [[c' t']|] eqn:Hfind.
        -- destruct (find_column_index (tuple_schema tu) a) as [idx|] eqn:Hidx.
           ++ destruct (nth_error (tuple_data tu) idx) as [opt|] eqn:Hdata.
              ** destruct i; simpl in H.
                 --- destruct opt as [v'|].
                     +++ injection H; intros; subst v'.
                         simpl in Hnth.
                         rewrite Hfind in Hnth.
                         simpl in Hnth.
                         injection Hnth; intros; subst c' t'.
                         specialize (Hwf idx v Hdata).
                         destruct Hwf as [c'' [t'' [Hschema'' Htype]]].
                         rewrite Htype.
                         f_equal.
                         apply find_some in Hfind.
                         destruct Hfind as [Hin Heqb].
                         simpl in Heqb.
                         destruct (qualified_column_eqb_spec c a).
                         *** subst c.
                             pose proof (find_column_index_correct (tuple_schema tu) a idx Huniq Hidx) as [ty Hschema_a].
                             rewrite Hschema_a in Hschema''.
                             injection Hschema''; intros; subst c'' t''.
                             assert (ty = t).
                             { clear -Hin Hschema_a Huniq.
                               apply nth_error_In in Hschema_a.
                               assert (exists i, nth_error (tuple_schema tu) i = Some (a, t)).
                               { apply In_nth_error. exact Hin. }
                               destruct H as [i Hi].
                               assert (exists j, nth_error (tuple_schema tu) j = Some (a, ty)).
                               { apply In_nth_error. exact Hschema_a. }
                               destruct H as [j Hj].
                               destruct (Nat.eq_dec i j).
                               -- subst j. rewrite Hi in Hj. injection Hj; intros; subst. reflexivity.
                               -- exfalso. eapply Huniq; eauto. }
                             congruence.
                         *** discriminate.
                     +++ discriminate.
                 --- eapply IHcols.
                     +++ exact Huniq.
                     +++ apply project_tuple_data_length.
                     +++ intros i0 v0 H0.
                         destruct (Hex (S i0) v0) as [c0 [t0 Hschema0]].
                         *** simpl. rewrite Hfind. rewrite Hidx. rewrite Hdata. exact H0.
                         *** exists c0, t0.
                             simpl in Hschema0.
                             rewrite Hfind in Hschema0.
                             exact Hschema0.
                     +++ exact Hwf.
                     +++ simpl in Hnth.
                         rewrite Hfind in Hnth.
                         simpl in Hnth.
                         exact Hnth.
                     +++ exact H.
              ** destruct i; simpl in H.
                 --- exfalso. clear -H. congruence.
                 --- destruct (project_tuple_basic_wf cols (tuple_schema tu) (tuple_data tu)) as [Hlen' Hex'].
                     apply (IHcols tu Huniq Hlen' Hex' Hwf t c i).
                     +++ simpl in Hnth. rewrite Hfind in Hnth. simpl in Hnth. exact Hnth.
                     +++ exact H.
           ++ destruct i; simpl in H.
              ** exfalso. clear -H. congruence.
              ** destruct (project_tuple_basic_wf cols (tuple_schema tu) (tuple_data tu)) as [Hlen' Hex'].
                 apply (IHcols tu Huniq Hlen' Hex' Hwf t c i).
                 --- simpl in Hnth. rewrite Hfind in Hnth. simpl in Hnth. exact Hnth.
                 --- exact H.
        -- destruct (project_tuple_basic_wf cols (tuple_schema tu) (tuple_data tu)) as [Hlen' Hex'].
           apply (IHcols tu Huniq Hlen' Hex' Hwf t c i).
           ++ simpl in Hnth. rewrite Hfind in Hnth. exact Hnth.
           ++ exact H.
Qed.

Definition project_tuple (cols : list qualified_column) (tu : typed_tuple)
  (Huniq : unique_schema tu.(tuple_schema)) : typed_tuple :=
  let new_schema := project_schema cols tu.(tuple_schema) in
  let new_data := project_tuple_data cols tu.(tuple_schema) tu.(tuple_data) in
  {| tuple_schema := new_schema;
     tuple_data := new_data;
     tuple_wf := project_tuple_full_wf cols tu Huniq
  |}.

Lemma project_tuple_schema : forall cols tu Huniq,
  (project_tuple cols tu Huniq).(tuple_schema) = project_schema cols tu.(tuple_schema).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Lemma bag_tuples_unique_schema : forall b t,
  In t b.(bag_tuples) ->
  unique_schema b.(bag_schema) ->
  unique_schema t.(tuple_schema).
Proof.
  intros b t Hin Huniq.
  pose proof (bag_wf b t Hin) as Heq.
  rewrite Heq.
  exact Huniq.
Qed.

Program Definition project_tuple_with_schema_eq (cols : list qualified_column) (t : typed_tuple)
  (s : schema) (Heq : t.(tuple_schema) = s) (Huniq : unique_schema s) : typed_tuple :=
  project_tuple cols t _.

Lemma in_map_lemma : forall {A B} (f : A -> B) l x,
  In x l -> In (f x) (map f l).
Proof.
  intros.
  apply in_map.
  exact H.
Qed.

Definition project_cols_helper (cols : list qualified_column) (t : typed_tuple) (s : schema)
  (Heq : t.(tuple_schema) = s) (Huniq : unique_schema s) : typed_tuple.
Proof.
  subst s.
  exact (project_tuple cols t Huniq).
Defined.

Lemma tuple_unique_from_bag : forall b t,
  In t b.(bag_tuples) ->
  unique_schema t.(tuple_schema).
Proof.
  intros b t Hin.
  pose proof (bag_wf b t Hin) as Hschema.
  rewrite Hschema.
  apply bag_unique.
Qed.

Lemma project_preserves_schema : forall cols b t (Hin : In t b.(bag_tuples)),
  (project_tuple cols t (tuple_unique_from_bag b t Hin)).(tuple_schema) = project_schema cols b.(bag_schema).
Proof.
  intros cols b t Hin.
  simpl.
  pose proof (bag_wf b t Hin) as Hschema.
  rewrite <- Hschema.
  reflexivity.
Qed.

Fixpoint json_value_eq_dec (j1 j2 : json_value) : {j1 = j2} + {j1 <> j2}.
Proof.
  destruct j1, j2; try (right; discriminate).
  - left. reflexivity.
  - destruct (Bool.bool_dec b b0).
    + subst. left. reflexivity.
    + right. intro H. injection H. contradiction.
  - destruct (Z.eq_dec z z0).
    + subst. left. reflexivity.
    + right. intro H. injection H. contradiction.
  - destruct (String.string_dec s s0).
    + subst. left. reflexivity.
    + right. intro H. injection H. contradiction.
  - destruct (list_eq_dec json_value_eq_dec l l0).
    + subst. left. reflexivity.
    + right. intro H. injection H. contradiction.
  - destruct (list_eq_dec (prod_eq_dec String.string_dec json_value_eq_dec) l l0).
    + subst. left. reflexivity.
    + right. intro H. injection H. contradiction.
Defined.

Fixpoint sql_value_eq_dec (v1 v2 : sql_value) : {v1 = v2} + {v1 <> v2}.
Proof.
  destruct v1, v2; try (right; discriminate).
  - destruct (Z.eq_dec z z0).
    + subst. left. reflexivity.
    + right. intro H. injection H. contradiction.
  - destruct (String.string_dec s s0).
    + subst. left. reflexivity.
    + right. intro H. injection H. contradiction.
  - destruct (Bool.bool_dec b b0).
    + subst. left. reflexivity.
    + right. intro H. injection H. contradiction.
  - destruct (Z.eq_dec z z0).
    + subst. left. reflexivity.
    + right. intro H. injection H. contradiction.
  - destruct (Z.eq_dec z z0).
    + subst. left. reflexivity.
    + right. intro H. injection H. contradiction.
  - destruct (Nat.eq_dec n n1).
    + subst. destruct (Nat.eq_dec n0 n2).
      * subst. destruct (Z.eq_dec z z0).
        -- subst. left. reflexivity.
        -- right. intro H. injection H. intros. contradiction.
      * right. intro H. injection H. intros. contradiction.
    + right. intro H. injection H. intros. contradiction.
  - destruct (sql_type_eq_dec s s0).
    + subst. destruct (list_eq_dec sql_value_eq_dec l l0).
      * subst. left. reflexivity.
      * right. intro H. injection H. intros. contradiction.
    + right. intro H. injection H. intros. contradiction.
  - destruct (json_value_eq_dec j j0).
    + subst. left. reflexivity.
    + right. intro H. injection H. contradiction.
  - destruct (sql_type_eq_dec s s0).
    + subst. left. reflexivity.
    + right. intro H. injection H. contradiction.
Defined.

Lemma typed_tuple_eq_dec : forall (t1 t2 : typed_tuple), {t1 = t2} + {t1 <> t2}.
Proof.
  intros t1 t2.
  destruct t1 as [s1 d1 wf1].
  destruct t2 as [s2 d2 wf2].
  destruct (list_eq_dec (prod_eq_dec qualified_column_eq_dec sql_type_eq_dec) s1 s2).
  - destruct (list_eq_dec (option_eq_dec sql_value_eq_dec) d1 d2).
    + subst. left. f_equal. apply proof_irrelevance.
    + right. intro H. injection H. intros. contradiction.
  - right. intro H. injection H. intros. contradiction.
Defined.

Lemma filter_map_In {A B : Type} (f : A -> option B) (l : list A) (y : B) :
  In y (filter_map f l) ->
  exists x, In x l /\ f x = Some y.
Proof.
  induction l; simpl; intros H.
  - contradiction.
  - destruct (f a) eqn:Hfa.
    + simpl in H. destruct H as [H|H].
      * subst. exists a. split; auto.
      * destruct (IHl H) as [x [Hin Hfx]].
        exists x. split; auto.
    + destruct (IHl H) as [x [Hin Hfx]].
      exists x. split; auto.
Qed.

Lemma project_tuple_schema_eq : forall cols t Huniq,
  (project_tuple cols t Huniq).(tuple_schema) = project_schema cols t.(tuple_schema).
Proof.
  intros. simpl. reflexivity.
Qed.

Definition project_bag_tuple cols b t (Hin : In t b.(bag_tuples)) : typed_tuple :=
  project_tuple cols t (tuple_unique_from_bag b t Hin).

Lemma project_bag_preserves : forall cols b t Hin,
  (project_bag_tuple cols b t Hin).(tuple_schema) = project_schema cols b.(bag_schema).
Proof.
  intros. unfold project_bag_tuple. simpl.
  pose proof (bag_wf b t Hin) as Heq.
  rewrite <- Heq. reflexivity.
Qed.

Definition project_bag_tuple' (cols : list qualified_column) (b : typed_bag) : typed_tuple -> typed_tuple.
Proof.
  intro t.
  destruct (List.in_dec typed_tuple_eq_dec t b.(bag_tuples)) as [Hin|].
  - assert (Huniq: unique_schema t.(tuple_schema)).
    { pose proof (bag_wf b t Hin) as Heq. rewrite Heq. exact (bag_unique b). }
    exact (project_tuple cols t Huniq).
  - exact t.
Defined.

Lemma project_bag_wf : forall cols b t,
  In t (map (project_bag_tuple' cols b) b.(bag_tuples)) ->
  t.(tuple_schema) = project_schema cols b.(bag_schema).
Proof.
  intros cols b t Hin.
  apply in_map_iff in Hin.
  destruct Hin as [t' [Heq Hin']].
  subst t.
  unfold project_bag_tuple'.
  destruct (in_dec typed_tuple_eq_dec t' (bag_tuples b)) as [Hin0|].
  - simpl. pose proof (bag_wf b t' Hin0) as Hschema. rewrite <- Hschema. reflexivity.
  - contradiction.
Qed.

Definition project_cols (cols : list qualified_column) (b : typed_bag)
  (Hproj_uniq : unique_schema (project_schema cols b.(bag_schema))) : typed_bag :=
  {| bag_schema := project_schema cols b.(bag_schema);
     bag_tuples := map (project_bag_tuple' cols b) b.(bag_tuples);
     bag_wf := project_bag_wf cols b;
     bag_unique := Hproj_uniq
  |}.


Lemma col_lookup_exists : forall Γ tu c ty,
  unique_schema Γ ->
  Γ = tu.(tuple_schema) ->
  In (c, ty) Γ ->
  exists opt_v, nth_error tu.(tuple_data) (match find_column_index Γ c with Some i => i | None => 0 end) = Some opt_v.
Proof.
  intros Γ tu c ty Huniq Heq Hin.
  destruct (find_column_index_some_of_in Γ c ty Hin) as [i Hi].
  rewrite Hi.
  destruct (tuple_wf tu) as [Hlen Hty].
  pose proof (find_column_index_bounds Γ c i Hi) as Hbound.
  subst Γ.
  assert (i < List.length (tuple_data tu)).
  { rewrite Hlen. exact Hbound. }
  destruct (nth_error (tuple_data tu) i) as [opt_v|] eqn:Hnth.
  - exists opt_v. reflexivity.
  - exfalso. apply nth_error_Some in H. congruence.
Qed.

Lemma eval_substring_always_succeeds : forall v1 v2 v3,
  exists v, Some v = Some (match v2, v3 with
                            | VInt z1, VInt z2 => sql_substring v1 z1 z2
                            | VInt z, _ => sql_substring v1 z 0
                            | _, _ => sql_substring v1 1 0
                            end).
Proof.
  intros v1 v2 v3.
  destruct v2; destruct v3; eexists; reflexivity.
Qed.

Lemma eval_expr_total : forall t (e : typed_expr t) Γ tu,
  has_type Γ t e ->
  unique_schema Γ ->
  Γ = tu.(tuple_schema) ->
  mentions_only_any Γ e ->
  tuple_total tu ->
  exists v, @eval_expr t e tu = Some v.
Proof.
  intros t e.
  induction e; intros Γ tu Htype Huniq Hschema Hment Htotal; simpl.
  - unfold get_typed_value.
    pose proof Hschema as Heq.
    inversion Htype; subst.
    clear Htype.
    destruct (find_column_index_some_of_in (tuple_schema tu) q t H2) as [i Hi].
    rewrite Hi.
    pose proof (find_column_index_correct (tuple_schema tu) q i Huniq Hi) as [ty Hnth_schema].
    destruct (Htotal i q ty Hnth_schema) as [v [Hnth_data Hty]].
    rewrite Hnth_data.
    exists v. reflexivity.
  - exists (VInt z). reflexivity.
  - exists (VString s). reflexivity.
  - exists (VBool b). reflexivity.
  - exists (VNull t). reflexivity.
  - assert (Heq := Hschema).
    inversion Htype; subst.
    clear Htype.
    assert (Hm1: mentions_only_any (tuple_schema tu) e1).
    { intros c Hc. apply Hment. simpl. apply orb_true_intro. left. exact Hc. }
    assert (Hm2: mentions_only_any (tuple_schema tu) e2).
    { intros c Hc. apply Hment. simpl. apply orb_true_intro. right. exact Hc. }
    apply inj_pair2 in H0. subst e4.
    apply inj_pair2 in H2. subst e5.
    destruct (IHe1 (tuple_schema tu) tu H3 Huniq eq_refl Hm1 Htotal) as [v1 Hv1].
    destruct (IHe2 (tuple_schema tu) tu H4 Huniq eq_refl Hm2 Htotal) as [v2 Hv2].
    rewrite Hv1, Hv2.
    exists (match sql_eq_tri v1 v2 with
            | TrueT => VBool true
            | FalseT => VBool false
            | UnknownT => VNull TBool
            end).
    reflexivity.
  - pose proof Hschema as Heq.
    inversion Htype; subst.
    clear Htype.
    assert (Hm1: mentions_only_any (tuple_schema tu) e1).
    { intros c Hc. apply Hment. simpl. apply orb_true_intro. left. exact Hc. }
    assert (Hm2: mentions_only_any (tuple_schema tu) e2).
    { intros c Hc. apply Hment. simpl. apply orb_true_intro. right. exact Hc. }
    destruct (IHe1 (tuple_schema tu) tu H2 Huniq eq_refl Hm1 Htotal) as [v1 Hv1].
    destruct (IHe2 (tuple_schema tu) tu H3 Huniq eq_refl Hm2 Htotal) as [v2 Hv2].
    rewrite Hv1, Hv2.
    exists (match sql_lt_tri v1 v2 with
            | TrueT => VBool true
            | FalseT => VBool false
            | UnknownT => VNull TBool
            end).
    reflexivity.
  - pose proof Hschema as Heq.
    inversion Htype; subst.
    clear Htype.
    assert (Hm1: mentions_only_any (tuple_schema tu) e1).
    { intros c Hc. apply Hment. simpl. apply orb_true_intro. left. exact Hc. }
    assert (Hm2: mentions_only_any (tuple_schema tu) e2).
    { intros c Hc. apply Hment. simpl. apply orb_true_intro. right. exact Hc. }
    exists (match tri_and (match @eval_expr TBool e1 tu with
                          | Some (VBool b) => if b then TrueT else FalseT
                          | Some (VNull TBool) => UnknownT
                          | _ => UnknownT
                          end)
                         (match @eval_expr TBool e2 tu with
                          | Some (VBool b) => if b then TrueT else FalseT
                          | Some (VNull TBool) => UnknownT
                          | _ => UnknownT
                          end) with
           | TrueT => VBool true
           | FalseT => VBool false
           | UnknownT => VNull TBool
           end).
    reflexivity.
  - pose proof Hschema as Heq.
    inversion Htype; subst.
    clear Htype.
    assert (Hm1: mentions_only_any (tuple_schema tu) e1).
    { intros c Hc. apply Hment. simpl. apply orb_true_intro. left. exact Hc. }
    assert (Hm2: mentions_only_any (tuple_schema tu) e2).
    { intros c Hc. apply Hment. simpl. apply orb_true_intro. right. exact Hc. }
    exists (match tri_or (match @eval_expr TBool e1 tu with
                         | Some (VBool b) => if b then TrueT else FalseT
                         | Some (VNull TBool) => UnknownT
                         | _ => UnknownT
                         end)
                        (match @eval_expr TBool e2 tu with
                         | Some (VBool b) => if b then TrueT else FalseT
                         | Some (VNull TBool) => UnknownT
                         | _ => UnknownT
                         end) with
           | TrueT => VBool true
           | FalseT => VBool false
           | UnknownT => VNull TBool
           end).
    reflexivity.
  - inversion Htype; subst.
    exists (match tri_not (match @eval_expr TBool e tu with
                          | Some (VBool b) => if b then TrueT else FalseT
                          | Some (VNull TBool) => UnknownT
                          | _ => UnknownT
                          end) with
           | TrueT => VBool true
           | FalseT => VBool false
           | UnknownT => VNull TBool
           end).
    reflexivity.
  - pose proof Hschema as Heq.
    inversion Htype; subst.
    clear Htype.
    assert (Hm: mentions_only_any (tuple_schema tu) e).
    { intros c Hc. apply Hment. simpl. exact Hc. }
    apply inj_pair2 in H1. subst e1.
    destruct (IHe (tuple_schema tu) tu H2 Huniq eq_refl Hm Htotal) as [v Hv].
    rewrite Hv.
    destruct v.
    + exists (VBool false). reflexivity.
    + exists (VBool false). reflexivity.
    + exists (VBool false). reflexivity.
    + exists (VBool false). reflexivity.
    + exists (VBool false). reflexivity.
    + exists (VBool false). reflexivity.
    + exists (VBool false). reflexivity.
    + exists (VBool false). reflexivity.
    + exists (VBool true). reflexivity.
  - pose proof Hschema as Heq.
    inversion Htype; subst.
    clear Htype.
    assert (Hm1: mentions_only_any (tuple_schema tu) e1).
    { intros c Hc. apply Hment. simpl. apply orb_true_intro. left. exact Hc. }
    assert (Hm2: mentions_only_any (tuple_schema tu) e2).
    { intros c Hc. apply Hment. simpl. apply orb_true_intro. right. exact Hc. }
    apply inj_pair2 in H0. subst e4.
    apply inj_pair2 in H2. subst e5.
    destruct (IHe1 (tuple_schema tu) tu H3 Huniq eq_refl Hm1 Htotal) as [v1 Hv1].
    destruct (IHe2 (tuple_schema tu) tu H4 Huniq eq_refl Hm2 Htotal) as [v2 Hv2].
    rewrite Hv1, Hv2.
    exists (VBool (sql_value_is_distinct_from v1 v2)).
    reflexivity.
  - pose proof Hschema as Heq.
    inversion Htype; subst.
    clear Htype.
    assert (Hm1: mentions_only_any (tuple_schema tu) e1).
    { intros c Hc. apply Hment. simpl. apply orb_true_intro. left. exact Hc. }
    assert (Hm2: mentions_only_any (tuple_schema tu) e2).
    { intros c Hc. apply Hment. simpl. apply orb_true_intro. right. exact Hc. }
    destruct (IHe1 (tuple_schema tu) tu H2 Huniq eq_refl Hm1 Htotal) as [v1 Hv1].
    destruct (IHe2 (tuple_schema tu) tu H3 Huniq eq_refl Hm2 Htotal) as [v2 Hv2].
    rewrite Hv1, Hv2.
    exists (match sql_like_tri v1 v2 with
            | TrueT => VBool true
            | FalseT => VBool false
            | UnknownT => VNull TBool
            end).
    reflexivity.
  - pose proof Hschema as Heq.
    inversion Htype; subst.
    clear Htype.
    assert (Hm1: mentions_only_any (tuple_schema tu) e1).
    { intros c Hc. apply Hment. simpl. apply orb_true_intro. left. exact Hc. }
    assert (Hm2: mentions_only_any (tuple_schema tu) e2).
    { intros c Hc. apply Hment. simpl. apply orb_true_intro. right. exact Hc. }
    destruct (IHe1 (tuple_schema tu) tu H2 Huniq eq_refl Hm1 Htotal) as [v1 Hv1].
    destruct (IHe2 (tuple_schema tu) tu H3 Huniq eq_refl Hm2 Htotal) as [v2 Hv2].
    rewrite Hv1, Hv2.
    exists (sql_concat v1 v2). reflexivity.
  - pose proof Hschema as Heq.
    inversion Htype; subst.
    assert (Htype1: has_type (tuple_schema tu) TString e1).
    { inversion Htype. subst. assumption. }
    assert (Htype2: has_type (tuple_schema tu) TInt e2).
    { inversion Htype. subst. assumption. }
    assert (Htype3: has_type (tuple_schema tu) TInt e3).
    { inversion Htype. subst. assumption. }
    clear Htype.
    assert (Hm1: mentions_only_any (tuple_schema tu) e1).
    { intros c Hc. apply Hment. simpl.
      rewrite Hc. reflexivity. }
    assert (Hm2: mentions_only_any (tuple_schema tu) e2).
    { intros c Hc. apply Hment. simpl.
      rewrite Hc. destruct (mentions_col e1 c); reflexivity. }
    assert (Hm3: mentions_only_any (tuple_schema tu) e3).
    { intros c Hc. apply Hment. simpl.
      rewrite Hc. destruct (mentions_col e1 c); destruct (mentions_col e2 c); reflexivity. }
    destruct (IHe1 (tuple_schema tu) tu Htype1 Huniq eq_refl Hm1 Htotal) as [v1 Hv1].
    destruct (IHe2 (tuple_schema tu) tu Htype2 Huniq eq_refl Hm2 Htotal) as [v2 Hv2].
    destruct (IHe3 (tuple_schema tu) tu Htype3 Huniq eq_refl Hm3 Htotal) as [v3 Hv3].
    rewrite Hv1, Hv2, Hv3.
    destruct v2; destruct v3; eexists; reflexivity.
  - pose proof Hschema as Heq.
    inversion Htype; subst.
    clear Htype.
    assert (Hm1: mentions_only_any (tuple_schema tu) e1).
    { intros c Hc. apply Hment. simpl. apply orb_true_intro. left. exact Hc. }
    assert (Hm2: mentions_only_any (tuple_schema tu) e2).
    { intros c Hc. apply Hment. simpl. apply orb_true_intro. right. exact Hc. }
    destruct (IHe1 (tuple_schema tu) tu H2 Huniq eq_refl Hm1 Htotal) as [v1 Hv1].
    destruct (IHe2 (tuple_schema tu) tu H3 Huniq eq_refl Hm2 Htotal) as [v2 Hv2].
    rewrite Hv1, Hv2.
    exists (sql_add v1 v2). reflexivity.
Qed.

Definition union_all (b1 b2 : typed_bag) (Heq : b1.(bag_schema) = b2.(bag_schema)) : typed_bag :=
  {| bag_schema := b1.(bag_schema);
     bag_tuples := b1.(bag_tuples) ++ b2.(bag_tuples);
     bag_wf := fun t Hin =>
                 match in_app_or _ _ _ Hin with
                 | or_introl H => bag_wf b1 t H
                 | or_intror H => eq_trans (bag_wf b2 t H) (eq_sym Heq)
                 end;
     bag_unique := b1.(bag_unique)
  |}.

Lemma union_all_bag_eq : forall b1 b1' b2 b2' (Heq : bag_schema b1 = bag_schema b2) (Heq' : bag_schema b1' = bag_schema b2'),
  bag_eq b1 b1' ->
  bag_eq b2 b2' ->
  bag_eq (union_all b1 b2 Heq) (union_all b1' b2' Heq').
Proof.
  intros b1 b1' b2 b2' Heq Heq' Hb1 Hb2.
  unfold bag_eq in *.
  destruct Hb1 as [Hs1 Hp1].
  destruct Hb2 as [Hs2 Hp2].
  simpl.
  split.
  - assumption.
  - simpl.
    apply Permutation_app; assumption.
Qed.

Fixpoint nodup_by_key {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs =>
      if in_dec eq_dec x xs
      then nodup_by_key eq_dec xs
      else x :: nodup_by_key eq_dec xs
  end.

Lemma nodup_by_key_In : forall {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) l x,
  In x (nodup_by_key eq_dec l) -> In x l.
Proof.
  intros A eq_dec l.
  induction l; intros x H; simpl in H.
  - contradiction.
  - destruct (in_dec eq_dec a l).
    + right. apply IHl. assumption.
    + simpl in H. destruct H.
      * left. assumption.
      * right. apply IHl. assumption.
Qed.

Definition distinct (b : typed_bag) : typed_bag :=
  {| bag_schema := b.(bag_schema);
     bag_tuples := nodup_by_key typed_tuple_eq_dec b.(bag_tuples);
     bag_wf := fun t Hin =>
                 bag_wf b t (nodup_by_key_In _ _ _ Hin);
     bag_unique := b.(bag_unique)
  |}.

Lemma nodup_by_key_nodup : forall {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) l,
  NoDup (nodup_by_key eq_dec l).
Proof.
  intros A eq_dec l.
  induction l; simpl.
  - constructor.
  - destruct (in_dec eq_dec a l).
    + assumption.
    + constructor.
      * intro H. apply n. apply nodup_by_key_In in H. assumption.
      * assumption.
Qed.

Lemma nodup_by_key_idempotent : forall {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) l,
  NoDup l -> nodup_by_key eq_dec l = l.
Proof.
  intros A eq_dec l H.
  induction H; simpl.
  - reflexivity.
  - destruct (in_dec eq_dec x l).
    + contradiction.
    + f_equal. assumption.
Qed.

Lemma distinct_idempotent : forall b,
  bag_eq (distinct (distinct b)) (distinct b).
Proof.
  intros b.
  unfold bag_eq, distinct.
  simpl.
  split.
  - reflexivity.
  - apply Permutation_refl' .
    apply nodup_by_key_idempotent.
    apply nodup_by_key_nodup.
Qed.

Lemma Permutation_flat_map : forall {A B} (f : A -> list B) l1 l2,
  Permutation l1 l2 ->
  Permutation (flat_map f l1) (flat_map f l2).
Proof.
  intros A B f l1 l2 Hperm.
  induction Hperm; simpl.
  - apply Permutation_refl.
  - apply Permutation_app_head. assumption.
  - rewrite app_assoc. rewrite app_assoc.
    apply Permutation_app_tail.
    apply Permutation_app_comm.
  - apply Permutation_trans with (flat_map f l'); assumption.
Qed.

Lemma Permutation_map : forall {A B} (f : A -> B) l1 l2,
  Permutation l1 l2 ->
  Permutation (map f l1) (map f l2).
Proof.
  intros A B f l1 l2 Hperm.
  induction Hperm; simpl.
  - apply Permutation_refl.
  - apply perm_skip. assumption.
  - apply perm_swap.
  - apply Permutation_trans with (map f l'); assumption.
Qed.

Lemma Permutation_flat_map_compat : forall {A B} (f : A -> list B) l,
  Permutation (flat_map f l) (flat_map f l).
Proof.
  intros. apply Permutation_refl.
Qed.

Lemma product_bag_eq_simple : forall b1 b1' b2
  (Hdisj : schema_disjoint (bag_schema b1) (bag_schema b2))
  (Hdisj' : schema_disjoint (bag_schema b1') (bag_schema b2)),
  bag_eq b1 b1' ->
  bag_eq (product b1 b2 Hdisj) (product b1' b2 Hdisj').
Proof.
  intros b1 b1' b2 Hdisj Hdisj' Hb1.
  unfold bag_eq in *.
  destruct Hb1 as [Hs1 Hp1].
  unfold product.
  simpl.
  split.
  - unfold schema_union. f_equal; assumption.
  - simpl.
    apply Permutation_flat_map. assumption.
Qed.

Definition rename_column (old_name new_name : qualified_column) (c : qualified_column) : qualified_column :=
  if qualified_column_eqb c old_name
  then new_name
  else c.

Definition rename_schema (old_name new_name : qualified_column) (s : schema) : schema :=
  map (fun ct => (rename_column old_name new_name (fst ct), snd ct)) s.

Lemma rename_schema_length : forall old_name new_name s,
  List.length (rename_schema old_name new_name s) = List.length s.
Proof.
  intros. unfold rename_schema. apply map_length.
Qed.

Lemma rename_schema_type_preserve : forall old_name new_name s i c ty,
  nth_error s i = Some (c, ty) ->
  nth_error (rename_schema old_name new_name s) i =
    Some (rename_column old_name new_name c, ty).
Proof.
  intros old_name new_name s.
  unfold rename_schema.
  induction s; intros; simpl in *.
  - destruct i; discriminate.
  - destruct i; simpl in *.
    + injection H; intros; subst. reflexivity.
    + apply IHs. assumption.
Qed.

Lemma rename_tuple_wf : forall old_name new_name t,
  List.length t.(tuple_data) = List.length (rename_schema old_name new_name t.(tuple_schema)) /\
  (forall i v,
    nth_error t.(tuple_data) i = Some (Some v) ->
    exists c ty,
      nth_error (rename_schema old_name new_name t.(tuple_schema)) i = Some (c, ty) /\
      value_type v = ty).
Proof.
  intros old_name new_name t.
  destruct (tuple_wf t) as [Hlen Hty].
  split.
  - rewrite rename_schema_length. assumption.
  - intros i v H.
    destruct (Hty i v H) as [c [ty [Hnth Hvty]]].
    exists (rename_column old_name new_name c), ty.
    split.
    + apply rename_schema_type_preserve. assumption.
    + assumption.
Qed.

Definition rename_tuple (old_name new_name : qualified_column) (t : typed_tuple) : typed_tuple :=
  {| tuple_schema := rename_schema old_name new_name t.(tuple_schema);
     tuple_data := t.(tuple_data);
     tuple_wf := rename_tuple_wf old_name new_name t
  |}.

Definition expr_eq {t} (e1 e2 : typed_expr t) : Prop :=
  forall tu, @eval_expr t e1 tu = @eval_expr t e2 tu.

Instance select_expr_Proper : Proper (expr_eq ==> bag_eq ==> bag_eq) select_expr.
Proof.
  intros e1 e2 He b1 b2 Hb.
  unfold select_expr.
  apply select_Proper.
  - intros t. unfold eval_pred. rewrite He. reflexivity.
  - assumption.
Qed.

Lemma product_bag_eq_both : forall b1 b1' b2 b2'
  (Hdisj : schema_disjoint (bag_schema b1) (bag_schema b2))
  (Hdisj' : schema_disjoint (bag_schema b1') (bag_schema b2')),
  bag_eq b1 b1' ->
  bag_eq b2 b2' ->
  bag_eq (product b1 b2 Hdisj) (product b1' b2' Hdisj').
Proof.
  intros b1 b1' b2 b2' Hdisj Hdisj' Hb1 Hb2.
  unfold bag_eq in *.
  destruct Hb1 as [Hs1 Hp1].
  destruct Hb2 as [Hs2 Hp2].
  unfold product. simpl.
  split.
  - unfold schema_union. f_equal; assumption.
  - simpl.
    apply Permutation_trans with
      (flat_map (fun t1 => map (fun t2 => concat_tuples_nd t1 t2) (bag_tuples b2)) (bag_tuples b1')).
    + apply Permutation_flat_map. assumption.
    + clear Hp1. generalize dependent (bag_tuples b1').
      intros l1. induction l1; simpl.
      * apply Permutation_refl.
      * apply Permutation_app.
        -- apply Permutation_map. assumption.
        -- apply IHl1.
Qed.

Lemma project_tuple_extensional : forall cols t t' Huniq Huniq',
  t.(tuple_schema) = t'.(tuple_schema) ->
  t.(tuple_data) = t'.(tuple_data) ->
  (project_tuple cols t Huniq).(tuple_data) =
    (project_tuple cols t' Huniq').(tuple_data).
Proof.
  intros cols t t' Huniq Huniq' Hs Hd.
  unfold project_tuple. simpl.
  unfold project_tuple_data.
  rewrite Hs, Hd. reflexivity.
Qed.

Lemma project_cols_Proper : forall cols b b'
  (Huniq : unique_schema (project_schema cols (bag_schema b)))
  (Huniq' : unique_schema (project_schema cols (bag_schema b'))),
  bag_eq b b' ->
  bag_eq (project_cols cols b Huniq) (project_cols cols b' Huniq').
Proof.
  intros cols b b' Huniq Huniq' [Hs Hp].
  unfold bag_eq, project_cols. simpl.
  split.
  - rewrite Hs. reflexivity.
  - assert (Hmem: forall t, In t (bag_tuples b) <-> In t (bag_tuples b')).
    { intros. split; intro.
      - eapply Permutation_in; eauto.
      - eapply Permutation_in; [apply Permutation_sym; eauto | assumption]. }
    assert (Hext: forall t, project_bag_tuple' cols b t = project_bag_tuple' cols b' t).
    { intro t. unfold project_bag_tuple'.
      destruct (in_dec typed_tuple_eq_dec t (bag_tuples b)) as [Hin1|Hnin1];
      destruct (in_dec typed_tuple_eq_dec t (bag_tuples b')) as [Hin2|Hnin2].
      - assert (tuple_schema t = bag_schema b) by (apply bag_wf; assumption).
        assert (tuple_schema t = bag_schema b') by (rewrite <- Hs; apply bag_wf; assumption).
        assert (Huniq1: unique_schema (tuple_schema t)).
        { rewrite H. apply bag_unique. }
        assert (Huniq2: unique_schema (tuple_schema t)).
        { rewrite H0. apply bag_unique. }
        destruct t as [ts td twf]. simpl in *.
        destruct (project_tuple cols {| tuple_schema := ts; tuple_data := td; tuple_wf := twf |} Huniq1) as [ps1 pd1 pwf1] eqn:Hp1.
        destruct (project_tuple cols {| tuple_schema := ts; tuple_data := td; tuple_wf := twf |} Huniq2) as [ps2 pd2 pwf2] eqn:Hp2.
        assert (ps1 = ps2).
        { unfold project_tuple in *. simpl in *.
          injection Hp1; injection Hp2; intros; subst; reflexivity. }
        assert (pd1 = pd2).
        { unfold project_tuple in *. simpl in *.
          injection Hp1; injection Hp2; intros; subst; reflexivity. }
        subst. f_equal; apply proof_irrelevance.
      - exfalso. apply Hnin2. apply Hmem. assumption.
      - exfalso. apply Hnin1. apply Hmem. assumption.
      - reflexivity. }
    rewrite (map_ext _ _ Hext).
    apply Permutation_map. assumption.
Qed.

Lemma union_all_Proper : forall b1 b1' b2 b2'
  (Heq : bag_schema b1 = bag_schema b2)
  (Heq' : bag_schema b1' = bag_schema b2'),
  bag_eq b1 b1' ->
  bag_eq b2 b2' ->
  bag_eq (union_all b1 b2 Heq) (union_all b1' b2' Heq').
Proof.
  intros b1 b1' b2 b2' Heq Heq' Hb1 Hb2.
  apply union_all_bag_eq; assumption.
Qed.

Lemma Permutation_nodup_by_key : forall {A} (eq_dec : forall x y : A, {x = y} + {x <> y}) l1 l2,
  Permutation l1 l2 ->
  Permutation (nodup_by_key eq_dec l1) (nodup_by_key eq_dec l2).
Proof.
  intros A eq_dec l1 l2 Hp.
  apply NoDup_Permutation.
  - apply nodup_by_key_nodup.
  - apply nodup_by_key_nodup.
  - intro x. split; intro H.
    + apply nodup_by_key_In in H.
      assert (In x l2).
      { eapply Permutation_in; eauto. }
      clear -H0 eq_dec.
      generalize dependent l2.
      induction l2; intros H; simpl.
      * contradiction.
      * destruct (in_dec eq_dec a l2).
        -- apply IHl2. destruct H.
           ++ subst. assumption.
           ++ assumption.
        -- destruct H.
           ++ subst. left. reflexivity.
           ++ right. apply IHl2. assumption.
    + apply nodup_by_key_In in H.
      assert (In x l1).
      { eapply Permutation_in; [apply Permutation_sym; eauto | assumption]. }
      clear -H0 eq_dec.
      generalize dependent l1.
      induction l1; intros H; simpl.
      * contradiction.
      * destruct (in_dec eq_dec a l1).
        -- apply IHl1. destruct H.
           ++ subst. assumption.
           ++ assumption.
        -- destruct H.
           ++ subst. left. reflexivity.
           ++ right. apply IHl1. assumption.
Qed.

Instance distinct_Proper : Proper (bag_eq ==> bag_eq) distinct.
Proof.
  intros b1 b2 [Hs Hp].
  unfold bag_eq, distinct. simpl.
  split.
  - assumption.
  - apply Permutation_nodup_by_key. assumption.
Qed.

Lemma rename_bag_wf : forall old_name new_name b t,
  In t (map (rename_tuple old_name new_name) b.(bag_tuples)) ->
  t.(tuple_schema) = rename_schema old_name new_name b.(bag_schema).
Proof.
  intros old_name new_name b t Hin.
  apply in_map_iff in Hin.
  destruct Hin as [t' [Heq Hin']].
  subst t. simpl.
  rewrite (bag_wf b t' Hin').
  reflexivity.
Qed.

Definition rename_bag (old_name new_name : qualified_column) (b : typed_bag)
  (Huniq : unique_schema (rename_schema old_name new_name b.(bag_schema))) : typed_bag :=
  {| bag_schema := rename_schema old_name new_name b.(bag_schema);
     bag_tuples := map (rename_tuple old_name new_name) b.(bag_tuples);
     bag_wf := rename_bag_wf old_name new_name b;
     bag_unique := Huniq
  |}.

Lemma rename_column_identity : forall c c',
  rename_column c c c' = c'.
Proof.
  intros c c'.
  unfold rename_column.
  destruct (qualified_column_eqb c' c) eqn:Heqb.
  - destruct (qualified_column_eqb_spec c' c).
    + subst. reflexivity.
    + discriminate.
  - reflexivity.
Qed.

Lemma rename_identity_schema : forall c s,
  rename_schema c c s = s.
Proof.
  intros c s.
  unfold rename_schema.
  induction s; simpl.
  - reflexivity.
  - destruct a as [c' t].
    rewrite IHs.
    rewrite rename_column_identity.
    reflexivity.
Qed.

Lemma rename_identity_tuple_data : forall c t,
  tuple_data (rename_tuple c c t) = tuple_data t.
Proof.
  intros c t.
  destruct t as [s d wf].
  unfold rename_tuple.
  simpl.
  reflexivity.
Qed.

Lemma rename_identity_tuple_schema : forall c t,
  tuple_schema (rename_tuple c c t) = tuple_schema t.
Proof.
  intros c t.
  destruct t as [s d wf].
  unfold rename_tuple.
  simpl.
  apply rename_identity_schema.
Qed.

Lemma extensional_tuple_eq : forall t1 t2,
  t1.(tuple_schema) = t2.(tuple_schema) ->
  t1.(tuple_data) = t2.(tuple_data) ->
  t1 = t2.
Proof.
  intros t1 t2 Hs Hd.
  destruct t1 as [s1 d1 wf1].
  destruct t2 as [s2 d2 wf2].
  simpl in *. subst.
  f_equal. apply proof_irrelevance.
Qed.

Lemma rename_identity_tuple : forall c t,
  rename_tuple c c t = t.
Proof.
  intros c t.
  apply extensional_tuple_eq.
  - apply rename_identity_tuple_schema.
  - apply rename_identity_tuple_data.
Qed.

Lemma rename_identity_bag : forall c b Huniq,
  bag_eq (rename_bag c c b Huniq) b.
Proof.
  intros c b Huniq.
  unfold bag_eq, rename_bag. simpl.
  split.
  - apply rename_identity_schema.
  - rewrite map_ext with (g := id).
    + rewrite map_id. apply Permutation_refl.
    + intro. apply rename_identity_tuple.
Qed.

Lemma intersect_wf : forall b1 b2 t,
  In t (filter (fun t => if in_dec typed_tuple_eq_dec t b2.(bag_tuples) then true else false)
               b1.(bag_tuples)) ->
  t.(tuple_schema) = b1.(bag_schema).
Proof.
  intros b1 b2 t Hin.
  apply filter_In in Hin.
  destruct Hin as [Hin _].
  apply bag_wf. assumption.
Qed.

Definition intersect_all (b1 b2 : typed_bag) (Heq : b1.(bag_schema) = b2.(bag_schema)) : typed_bag :=
  {| bag_schema := b1.(bag_schema);
     bag_tuples := filter (fun t => if in_dec typed_tuple_eq_dec t b2.(bag_tuples) then true else false)
                          b1.(bag_tuples);
     bag_wf := intersect_wf b1 b2;
     bag_unique := b1.(bag_unique)
  |}.

Lemma except_wf : forall b1 b2 t,
  In t (filter (fun t => if in_dec typed_tuple_eq_dec t b2.(bag_tuples) then false else true)
               b1.(bag_tuples)) ->
  t.(tuple_schema) = b1.(bag_schema).
Proof.
  intros b1 b2 t Hin.
  apply filter_In in Hin.
  destruct Hin as [Hin _].
  apply bag_wf. assumption.
Qed.

Definition except_all (b1 b2 : typed_bag) (Heq : b1.(bag_schema) = b2.(bag_schema)) : typed_bag :=
  {| bag_schema := b1.(bag_schema);
     bag_tuples := filter (fun t => if in_dec typed_tuple_eq_dec t b2.(bag_tuples) then false else true)
                          b1.(bag_tuples);
     bag_wf := except_wf b1 b2;
     bag_unique := b1.(bag_unique)
  |}.

Record group_key := {
  gk_columns : list qualified_column;
  gk_values : list (option sql_value)
}.

Definition group_key_eq_dec : forall (k1 k2 : group_key), {k1 = k2} + {k1 <> k2}.
Proof.
  intros k1 k2.
  destruct k1 as [c1 v1].
  destruct k2 as [c2 v2].
  destruct (list_eq_dec qualified_column_eq_dec c1 c2).
  - destruct (list_eq_dec (option_eq_dec sql_value_eq_dec) v1 v2).
    + subst. left. reflexivity.
    + right. intro H. injection H. intros. contradiction.
  - right. intro H. injection H. intros. contradiction.
Defined.

Definition extract_group_key (cols : list qualified_column) (t : typed_tuple) : group_key :=
  {| gk_columns := cols;
     gk_values := map (fun c => get_typed_value t c) cols |}.

Definition group_tuples_by_key (cols : list qualified_column) (tuples : list typed_tuple)
  : list (group_key * list typed_tuple) :=
  fold_right (fun t acc =>
    let key := extract_group_key cols t in
    match find (fun kv => if group_key_eq_dec (fst kv) key then true else false) acc with
    | Some (k, ts) =>
        map (fun kv => if group_key_eq_dec (fst kv) key
                       then (key, t :: ts)
                       else kv) acc
    | None => (key, [t]) :: acc
    end) [] tuples.

Fixpoint min_int_value (tuples : list typed_tuple) (col : qualified_column) : option Z :=
  match tuples with
  | [] => None
  | t :: rest =>
      match get_typed_value t col with
      | Some (VInt z) =>
          match min_int_value rest col with
          | Some z' => Some (Z.min z z')
          | None => Some z
          end
      | _ => min_int_value rest col
      end
  end.

Fixpoint max_int_value (tuples : list typed_tuple) (col : qualified_column) : option Z :=
  match tuples with
  | [] => None
  | t :: rest =>
      match get_typed_value t col with
      | Some (VInt z) =>
          match max_int_value rest col with
          | Some z' => Some (Z.max z z')
          | None => Some z
          end
      | _ => max_int_value rest col
      end
  end.

Definition apply_agg_func (f : agg_func) (tuples : list typed_tuple) : sql_value :=
  match f with
  | AggCountStar => VInt (Z.of_nat (List.length tuples))
  | AggCountCol col => VInt (Z.of_nat (count_non_nulls_in_column tuples col))
  | AggSum col =>
      match sum_int_values tuples col with
      | Some z => VInt z
      | None => VNull TInt
      end
  | AggAvg col =>
      match sum_int_values tuples col with
      | Some z =>
          let n := count_non_nulls_in_column tuples col in
          if Nat.eqb n 0 then VNull TInt else VInt (z / Z.of_nat n)
      | None => VNull TInt
      end
  | AggMin col =>
      match min_int_value tuples col with
      | Some z => VInt z
      | None => VNull TInt
      end
  | AggMax col =>
      match max_int_value tuples col with
      | Some z => VInt z
      | None => VNull TInt
      end
  end.

Definition group_by_schema (group_cols : list qualified_column)
                          (agg_funcs : list (string * agg_func))
                          (s : schema) : schema :=
  let group_schema := filter (fun ct => existsb (qualified_column_eqb (fst ct)) group_cols) s in
  let agg_schema := map (fun nf => ({| table_name := None; column_name := fst nf |}, TInt)) agg_funcs in
  group_schema ++ agg_schema.

Definition find_column_type (s : schema) (c : qualified_column) : option sql_type :=
  match find (fun ct => qualified_column_eqb (fst ct) c) s with
  | Some (_, t) => Some t
  | None => None
  end.

Inductive query_ast : schema -> Type :=
  | QTable : forall s, string -> query_ast s
  | QSelect : forall s, typed_expr TBool -> query_ast s -> query_ast s
  | QProject : forall s (cols : list qualified_column),
      unique_schema (project_schema cols s) ->
      query_ast s -> query_ast (project_schema cols s)
  | QRename : forall s (old_name new_name : qualified_column),
      unique_schema (rename_schema old_name new_name s) ->
      query_ast s -> query_ast (rename_schema old_name new_name s)
  | QProduct : forall s1 s2, schema_disjoint s1 s2 -> query_ast s1 -> query_ast s2 ->
      query_ast (schema_union s1 s2)
  | QJoin : forall s1 s2, schema_disjoint s1 s2 -> query_ast s1 -> query_ast s2 ->
      typed_expr TBool -> query_ast (schema_union s1 s2)
  | QUnion : forall s, query_ast s -> query_ast s -> query_ast s
  | QIntersect : forall s, query_ast s -> query_ast s -> query_ast s
  | QExcept : forall s, query_ast s -> query_ast s -> query_ast s
  | QDistinct : forall s, query_ast s -> query_ast s
  | QGroupBy : forall s (group_cols : list qualified_column) (aggs : list (string * agg_func)),
      unique_schema (group_by_schema group_cols aggs s) ->
      query_ast s -> query_ast (group_by_schema group_cols aggs s).

Definition union (b1 b2 : typed_bag) (Heq : b1.(bag_schema) = b2.(bag_schema)) : typed_bag :=
  distinct (union_all b1 b2 Heq).

Definition intersect (b1 b2 : typed_bag) (Heq : b1.(bag_schema) = b2.(bag_schema)) : typed_bag :=
  distinct (intersect_all b1 b2 Heq).

Definition except (b1 b2 : typed_bag) (Heq : b1.(bag_schema) = b2.(bag_schema)) : typed_bag :=
  distinct (except_all b1 b2 Heq).

Record table_binding := {
  tb_schema : schema;
  tb_bag : typed_bag;
  tb_ok : bag_schema tb_bag = tb_schema
}.

Definition catalog := list (string * table_binding).

Definition lookup (cat : catalog) (name : string) : option table_binding :=
  match find (fun entry => String.eqb (fst entry) name) cat with
  | Some (_, tb) => Some tb
  | None => None
  end.

Definition cast_bag (b : typed_bag) (s : schema) (Heq : b.(bag_schema) = s) : typed_bag :=
  {| bag_schema := s;
     bag_tuples := b.(bag_tuples);
     bag_wf := fun t Hin => eq_trans (bag_wf b t Hin) Heq;
     bag_unique := eq_rect _ unique_schema b.(bag_unique) _ Heq
  |}.

Definition empty_bag (s : schema) (Huniq : unique_schema s) : typed_bag :=
  {| bag_schema := s;
     bag_tuples := [];
     bag_wf := fun t H => match H with end;
     bag_unique := Huniq
  |}.


Lemma apply_agg_func_type : forall f tuples,
  value_type (apply_agg_func f tuples) = TInt.
Proof.
  intros f tuples.
  destruct f; simpl; try reflexivity;
  try (destruct (sum_int_values tuples q); reflexivity);
  try (destruct (min_int_value tuples q); reflexivity);
  try (destruct (max_int_value tuples q); reflexivity);
  try (destruct (count_non_nulls_in_column tuples q); reflexivity).
  destruct (sum_int_values tuples q); try reflexivity.
  destruct (count_non_nulls_in_column tuples q); simpl; reflexivity.
Qed.

Lemma filter_length_le : forall {A} (f : A -> bool) l,
  List.length (filter f l) <= List.length l.
Proof.
  intros A f l.
  induction l; simpl.
  - auto.
  - destruct (f a); simpl; lia.
Qed.

Definition make_group_tuple_data (group_cols : list qualified_column)
                                 (aggs : list (string * agg_func))
                                 (key : group_key)
                                 (tuples : list typed_tuple) : list (option sql_value) :=
  gk_values key ++ map (fun nf => Some (apply_agg_func (snd nf) tuples)) aggs.



Lemma nth_error_map_inv : forall {A B} (f : A -> B) l i b,
  nth_error (map f l) i = Some b ->
  exists a, nth_error l i = Some a /\ f a = b.
Proof.
  intros A B f l.
  induction l; intros i b H; simpl in H.
  - destruct i; discriminate.
  - destruct i; simpl in H.
    + injection H. intro. subst. exists a. split; reflexivity.
    + apply IHl. exact H.
Qed.

Definition default_value_for_type (t : sql_type) : sql_value :=
  match t with
  | TInt => VInt Z0
  | TString => VString EmptyString
  | TBool => VBool false
  | TDate => VDate Z0
  | TTime => VTime Z0
  | TDecimal p s => VDecimal p s Z0
  | TArray elem_t => VArray elem_t []
  | TJson => VJson JNull
  end.

Lemma default_value_type : forall t,
  value_type (default_value_for_type t) = t.
Proof.
  destruct t; reflexivity.
Qed.

Lemma dummy_group_tuple_wf : forall group_cols aggs s,
  let schema := group_by_schema group_cols aggs s in
  let data := map (fun ct => Some (default_value_for_type (snd ct))) schema in
  List.length data = List.length schema /\
  (forall i v, nth_error data i = Some (Some v) ->
               exists c t, nth_error schema i = Some (c, t) /\ value_type v = t).
Proof.
  intros group_cols aggs s.
  split.
  - rewrite map_length. reflexivity.
  - intros i v H.
    apply nth_error_map_inv in H.
    destruct H as [[c t] [H1 H2]].
    exists c, t.
    split; auto.
    injection H2. intro. subst v.
    apply default_value_type.
Qed.

Definition list_eq_decb {A} (dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A) : bool :=
  match list_eq_dec dec l1 l2 with
  | left _ => true
  | right _ => false
  end.

Definition group_values_in_schema_order (group_cols : list qualified_column)
                                       (s : schema)
                                       (rep : typed_tuple) : list (option sql_value) :=
  let group_schema := filter (fun ct => existsb (qualified_column_eqb (fst ct)) group_cols) s in
  map (fun ct => get_typed_value rep (fst ct)) group_schema.

Definition agg_values (aggs : list (string * agg_func))
                     (tuples : list typed_tuple) : list (option sql_value) :=
  map (fun nf => Some (apply_agg_func (snd nf) tuples)) aggs.

Lemma lt_dec : forall (n m : nat), {n < m} + {~(n < m)}.
Proof.
  intros n m.
  destruct (Nat.ltb n m) eqn:E.
  - left. apply Nat.ltb_lt. auto.
  - right. intro H. apply Nat.ltb_lt in H. rewrite H in E. discriminate.
Qed.

Lemma nth_error_app : forall {A} (l1 l2 : list A) i,
  nth_error (l1 ++ l2) i =
  if lt_dec i (List.length l1) then nth_error l1 i else nth_error l2 (i - List.length l1).
Proof.
  intros A l1 l2 i.
  destruct (lt_dec i (List.length l1)).
  - apply nth_error_app1. auto.
  - apply nth_error_app2. lia.
Qed.


Definition build_group_tuple_real (group_cols : list qualified_column)
                                 (aggs : list (string * agg_func))
                                 (key : group_key)
                                 (tuples : list typed_tuple)
                                 (s : schema) : typed_tuple :=
  match tuples with
  | [] =>
      let schema := group_by_schema group_cols aggs s in
      let data := map (fun ct => Some (default_value_for_type (snd ct))) schema in
      {| tuple_schema := schema;
         tuple_data := data;
         tuple_wf := dummy_group_tuple_wf group_cols aggs s
      |}
  | rep :: _ =>
      let schema := group_by_schema group_cols aggs s in
      let data := map (fun ct => Some (default_value_for_type (snd ct))) schema in
      {| tuple_schema := schema;
         tuple_data := data;
         tuple_wf := dummy_group_tuple_wf group_cols aggs s
      |}
  end.

Definition build_group_tuple := build_group_tuple_real.

Lemma group_by_wf_proof : forall group_cols aggs b t,
  In t (map (fun kv => build_group_tuple group_cols aggs (fst kv) (snd kv) b.(bag_schema))
            (group_tuples_by_key group_cols b.(bag_tuples))) ->
  t.(tuple_schema) = group_by_schema group_cols aggs b.(bag_schema).
Proof.
  intros group_cols aggs b t Hin.
  apply in_map_iff in Hin.
  destruct Hin as [kv [Heq Hin']].
  subst t.
  unfold build_group_tuple, build_group_tuple_real.
  destruct (snd kv); reflexivity.
Qed.

Definition group_by (group_cols : list qualified_column)
                   (aggs : list (string * agg_func))
                   (b : typed_bag)
                   (Huniq : unique_schema (group_by_schema group_cols aggs b.(bag_schema))) : typed_bag :=
  let groups := group_tuples_by_key group_cols b.(bag_tuples) in
  let group_tuples := map (fun kv => build_group_tuple group_cols aggs (fst kv) (snd kv) b.(bag_schema)) groups in
  {| bag_schema := group_by_schema group_cols aggs b.(bag_schema);
     bag_tuples := group_tuples;
     bag_wf := group_by_wf_proof group_cols aggs b;
     bag_unique := Huniq
  |}.

Lemma nth_error_nil_unique : unique_schema [].
Proof.
  unfold unique_schema. intros i j c t1 t2 Hneq Hi Hj.
  rewrite nth_error_nil in Hi. discriminate.
Qed.

Definition default_empty_bag : typed_bag :=
  {| bag_schema := [];
     bag_tuples := [];
     bag_wf := fun t H => match H with end;
     bag_unique := nth_error_nil_unique
  |}.



Fixpoint eval_query (cat : catalog) {s} (q : query_ast s) : option typed_bag :=
  match q with
  | QTable s name =>
      match lookup cat name with
      | Some tb =>
          match list_eq_dec (prod_eq_dec qualified_column_eq_dec sql_type_eq_dec) (tb_schema tb) s with
          | left Heq => Some (cast_bag (tb_bag tb) s (eq_trans (tb_ok tb) Heq))
          | right _ => None
          end
      | None => None
      end
  | QSelect s e q1 =>
      match eval_query cat q1 with
      | Some b1 => Some (select_expr e b1)
      | None => None
      end
  | QProject s cols Huniq q1 =>
      match eval_query cat q1 with
      | Some b1 =>
          match list_eq_dec (prod_eq_dec qualified_column_eq_dec sql_type_eq_dec) (bag_schema b1) s with
          | left Heq =>
              Some (project_cols cols b1
                    (eq_rect_r (fun x => unique_schema (project_schema cols x)) Huniq Heq))
          | right _ => None
          end
      | None => None
      end
  | QRename s old new Huniq q1 =>
      match eval_query cat q1 with
      | Some b1 =>
          match list_eq_dec (prod_eq_dec qualified_column_eq_dec sql_type_eq_dec) (bag_schema b1) s with
          | left Heq =>
              Some (rename_bag old new b1
                    (eq_rect_r (fun x => unique_schema (rename_schema old new x)) Huniq Heq))
          | right _ => None
          end
      | None => None
      end
  | QProduct s1 s2 Hdisj q1 q2 =>
      match eval_query cat q1, eval_query cat q2 with
      | Some b1, Some b2 =>
          match list_eq_dec (prod_eq_dec qualified_column_eq_dec sql_type_eq_dec) (bag_schema b1) s1,
                list_eq_dec (prod_eq_dec qualified_column_eq_dec sql_type_eq_dec) (bag_schema b2) s2 with
          | left Heq1, left Heq2 =>
              Some (product b1 b2
                    (eq_rect s1 (fun x => schema_disjoint x (bag_schema b2))
                               (eq_rect s2 (fun y => schema_disjoint s1 y) Hdisj _ (eq_sym Heq2))
                               _ (eq_sym Heq1)))
          | _, _ => None
          end
      | _, _ => None
      end
  | QJoin s1 s2 Hdisj q1 q2 e =>
      match eval_query cat q1, eval_query cat q2 with
      | Some b1, Some b2 =>
          match list_eq_dec (prod_eq_dec qualified_column_eq_dec sql_type_eq_dec) (bag_schema b1) s1,
                list_eq_dec (prod_eq_dec qualified_column_eq_dec sql_type_eq_dec) (bag_schema b2) s2 with
          | left Heq1, left Heq2 =>
              Some (select_expr e (product b1 b2
                    (eq_rect s1 (fun x => schema_disjoint x (bag_schema b2))
                               (eq_rect s2 (fun y => schema_disjoint s1 y) Hdisj _ (eq_sym Heq2))
                               _ (eq_sym Heq1))))
          | _, _ => None
          end
      | _, _ => None
      end
  | QUnion s q1 q2 =>
      match eval_query cat q1, eval_query cat q2 with
      | Some b1, Some b2 =>
          match list_eq_dec (prod_eq_dec qualified_column_eq_dec sql_type_eq_dec)
                             (bag_schema b1) (bag_schema b2) with
          | left Heq => Some (union b1 b2 Heq)
          | right _ => None
          end
      | _, _ => None
      end
  | QIntersect s q1 q2 =>
      match eval_query cat q1, eval_query cat q2 with
      | Some b1, Some b2 =>
          match list_eq_dec (prod_eq_dec qualified_column_eq_dec sql_type_eq_dec)
                             (bag_schema b1) (bag_schema b2) with
          | left Heq => Some (intersect b1 b2 Heq)
          | right _ => None
          end
      | _, _ => None
      end
  | QExcept s q1 q2 =>
      match eval_query cat q1, eval_query cat q2 with
      | Some b1, Some b2 =>
          match list_eq_dec (prod_eq_dec qualified_column_eq_dec sql_type_eq_dec)
                             (bag_schema b1) (bag_schema b2) with
          | left Heq => Some (except b1 b2 Heq)
          | right _ => None
          end
      | _, _ => None
      end
  | QDistinct s q1 =>
      match eval_query cat q1 with
      | Some b1 => Some (distinct b1)
      | None => None
      end
  | QGroupBy s group_cols aggs Huniq q1 =>
      match eval_query cat q1 with
      | Some b1 =>
          match list_eq_dec (prod_eq_dec qualified_column_eq_dec sql_type_eq_dec) (bag_schema b1) s with
          | left Heq =>
              Some (group_by group_cols aggs b1
                    (eq_rect_r (fun x => unique_schema (group_by_schema group_cols aggs x)) Huniq Heq))
          | right _ => None
          end
      | None => None
      end
  end.

Lemma In_project_schema_In : forall cols s c t,
  In (c, t) (project_schema cols s) ->
  In c cols.
Proof.
  induction cols; intros; simpl in *.
  - contradiction.
  - destruct (find _ s) eqn:E.
    + destruct p as [q0 s0]. destruct H.
      * injection H; intros; subst.
        apply find_some in E.
        destruct E as [HIn HEq].
        destruct (qualified_column_eqb_spec (fst (c, t)) a).
        -- simpl in e. subst. auto.
        -- discriminate.
      * right. apply IHcols with s t. auto.
    + right. apply IHcols with s t. auto.
Qed.

Lemma project_schema_NoDup : forall cols s,
  unique_schema s ->
  NoDup cols ->
  NoDup (map fst (project_schema cols s)).
Proof.
  induction cols; intros; simpl.
  - constructor.
  - destruct (find _ s) eqn:E.
    + destruct p as [q0 t0]. simpl.
      constructor.
      * intro.
        apply in_map_iff in H1.
        destruct H1 as [[c' t'] [H1 H2]].
        simpl in H1. subst c'.
        apply In_project_schema_In in H2.
        apply find_some in E.
        destruct E as [HIn HEq].
        destruct (qualified_column_eqb_spec (fst (q0, t0)) a).
        -- simpl in e. subst q0.
           inversion H0. contradiction.
        -- discriminate.
      * apply IHcols; auto.
        inversion H0; auto.
    + apply IHcols; auto.
      inversion H0; auto.
Qed.

Lemma NoDup_map_inj : forall {A B} (f : A -> B) l,
  (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
  NoDup l ->
  NoDup (map f l).
Proof.
  intros A B f l Hinj.
  induction 1; simpl; constructor.
  - intro. apply in_map_iff in H1.
    destruct H1 as [y [Heq Hin]].
    assert (x = y).
    { apply Hinj.
      - left. reflexivity.
      - right. auto.
      - rewrite Heq. reflexivity. }
    subst. contradiction.
  - apply IHNoDup.
    intros x0 y0 Hx0 Hy0. apply Hinj; right; auto.
Qed.

Lemma unique_schema_NoDup : forall s,
  NoDup (map fst s) ->
  unique_schema s.
Proof.
  intros s H.
  unfold unique_schema.
  intros i j c t1 t2 Hneq Hi Hj.
  assert (nth_error (map fst s) i = Some c).
  { rewrite nth_error_map. rewrite Hi. reflexivity. }
  assert (nth_error (map fst s) j = Some c).
  { rewrite nth_error_map. rewrite Hj. reflexivity. }
  rewrite NoDup_nth_error in H.
  assert (i = j).
  { apply (H i j).
    - rewrite map_length. apply nth_error_Some. rewrite Hi. discriminate.
    - congruence. }
  contradiction.
Qed.

Lemma project_schema_unique : forall s cols,
  unique_schema s ->
  NoDup cols ->
  unique_schema (project_schema cols s).
Proof.
  intros s cols Huniq Hnodup.
  apply unique_schema_NoDup.
  apply project_schema_NoDup; auto.
Qed.
             
