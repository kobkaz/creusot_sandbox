(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require HighOrd.
Require int.Int.
Require int.Abs.
Require int.ComputerDivision.

(* Why3 assumption *)
Inductive ref (a:Type) :=
  | ref'mk : a -> ref a.
Axiom ref_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (ref a).
Existing Instance ref_WhyType.
Arguments ref'mk {a}.

(* Why3 assumption *)
Definition contents {a:Type} {a_WT:WhyType a} (v:ref a) : a :=
  match v with
  | ref'mk x => x
  end.

(* Why3 assumption *)
Inductive borrowed (a:Type) :=
  | borrowed'mk : a -> a -> borrowed a.
Axiom borrowed_WhyType : forall (a:Type) {a_WT:WhyType a},
  WhyType (borrowed a).
Existing Instance borrowed_WhyType.
Arguments borrowed'mk {a}.

(* Why3 assumption *)
Definition current {a:Type} {a_WT:WhyType a} (v:borrowed a) : a :=
  match v with
  | borrowed'mk x x1 => x
  end.

(* Why3 assumption *)
Definition final {a:Type} {a_WT:WhyType a} (v:borrowed a) : a :=
  match v with
  | borrowed'mk x x1 => x1
  end.

Axiom seq : forall (a:Type), Type.
Parameter seq_WhyType : forall (a:Type) {a_WT:WhyType a}, WhyType (seq a).
Existing Instance seq_WhyType.

Parameter length:
  forall {a:Type} {a_WT:WhyType a}, seq a -> Numbers.BinNums.Z.

Axiom length_nonnegative :
  forall {a:Type} {a_WT:WhyType a}, forall (s:seq a), (0%Z <= (length s))%Z.

Parameter get:
  forall {a:Type} {a_WT:WhyType a}, seq a -> Numbers.BinNums.Z -> a.

Parameter infix_eqeq:
  forall {a:Type} {a_WT:WhyType a}, seq a -> seq a -> Prop.

Axiom infix_eqeq'spec :
  forall {a:Type} {a_WT:WhyType a},
  forall (s1:seq a) (s2:seq a),
  (infix_eqeq s1 s2 <->
   ((length s1) = (length s2)) /\
   (forall (i:Numbers.BinNums.Z), (0%Z <= i)%Z /\ (i < (length s1))%Z ->
    ((get s1 i) = (get s2 i)))) /\
  (infix_eqeq s1 s2 -> (s1 = s2)).

Parameter create:
  forall {a:Type} {a_WT:WhyType a}, Numbers.BinNums.Z ->
  (Numbers.BinNums.Z -> a) -> seq a.

Axiom create'spec :
  forall {a:Type} {a_WT:WhyType a},
  forall (len:Numbers.BinNums.Z) (f:Numbers.BinNums.Z -> a),
  (0%Z <= len)%Z ->
  ((length (create len f)) = len) /\
  (forall (i:Numbers.BinNums.Z), (0%Z <= i)%Z /\ (i < len)%Z ->
   ((get (create len f) i) = (f i))).

Parameter empty: forall {a:Type} {a_WT:WhyType a}, seq a.

Axiom empty'def :
  forall {a:Type} {a_WT:WhyType a}, ((length (empty : seq a)) = 0%Z).

Parameter set:
  forall {a:Type} {a_WT:WhyType a}, seq a -> Numbers.BinNums.Z -> a -> seq a.

Parameter result:
  forall {a:Type} {a_WT:WhyType a}, seq a -> Numbers.BinNums.Z -> a ->
  Numbers.BinNums.Z -> a.

Axiom result'def :
  forall {a:Type} {a_WT:WhyType a},
  forall (s:seq a) (i:Numbers.BinNums.Z) (v:a) (j:Numbers.BinNums.Z),
  ((j = i) -> ((result s i v j) = v)) /\
  (~ (j = i) -> ((result s i v j) = (get s j))).

Axiom set'def :
  forall {a:Type} {a_WT:WhyType a},
  forall (s:seq a) (i:Numbers.BinNums.Z) (v:a),
  (0%Z <= i)%Z /\ (i < (length s))%Z ->
  ((set s i v) = (create (length s) (result s i v))).

Axiom set'spec :
  forall {a:Type} {a_WT:WhyType a},
  forall (s:seq a) (i:Numbers.BinNums.Z) (v:a),
  (0%Z <= i)%Z /\ (i < (length s))%Z ->
  ((length (set s i v)) = (length s)) /\
  ((get (set s i v) i) = v) /\
  (forall (j:Numbers.BinNums.Z),
   ((0%Z <= j)%Z /\ (j < (length s))%Z) /\ ~ (j = i) ->
   ((get (set s i v) j) = (get s j))).

Parameter mixfix_lblsmnrb:
  forall {a:Type} {a_WT:WhyType a}, seq a -> Numbers.BinNums.Z -> a -> seq a.

Axiom mixfix_lblsmnrb'def :
  forall {a:Type} {a_WT:WhyType a},
  forall (s:seq a) (i:Numbers.BinNums.Z) (v:a),
  (0%Z <= i)%Z /\ (i < (length s))%Z ->
  ((mixfix_lblsmnrb s i v) = (set s i v)).

(* Why3 assumption *)
Definition singleton {a:Type} {a_WT:WhyType a} (v:a) : seq a :=
  create 1%Z (fun (us:Numbers.BinNums.Z) => v).

Axiom singleton'spec :
  forall {a:Type} {a_WT:WhyType a},
  forall (v:a),
  ((length (singleton v)) = 1%Z) /\ ((get (singleton v) 0%Z) = v).

Parameter result1:
  forall {a:Type} {a_WT:WhyType a}, a -> seq a -> Numbers.BinNums.Z -> a.

Axiom result'def1 :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:a) (s:seq a) (i:Numbers.BinNums.Z),
  ((i = 0%Z) -> ((result1 x s i) = x)) /\
  (~ (i = 0%Z) -> ((result1 x s i) = (get s (i - 1%Z)%Z))).

(* Why3 assumption *)
Definition cons {a:Type} {a_WT:WhyType a} (x:a) (s:seq a) : seq a :=
  create (1%Z + (length s))%Z (result1 x s).

Axiom cons'spec :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:a) (s:seq a),
  ((length (cons x s)) = (1%Z + (length s))%Z) /\
  ((get (cons x s) 0%Z) = x) /\
  (forall (i:Numbers.BinNums.Z), (0%Z < i)%Z /\ (i <= (length s))%Z ->
   ((get (cons x s) i) = (get s (i - 1%Z)%Z))).

Parameter result2:
  forall {a:Type} {a_WT:WhyType a}, seq a -> a -> Numbers.BinNums.Z -> a.

Axiom result'def2 :
  forall {a:Type} {a_WT:WhyType a},
  forall (s:seq a) (x:a) (i:Numbers.BinNums.Z),
  ((i = (length s)) -> ((result2 s x i) = x)) /\
  (~ (i = (length s)) -> ((result2 s x i) = (get s i))).

(* Why3 assumption *)
Definition snoc {a:Type} {a_WT:WhyType a} (s:seq a) (x:a) : seq a :=
  create (1%Z + (length s))%Z (result2 s x).

Axiom snoc'spec :
  forall {a:Type} {a_WT:WhyType a},
  forall (s:seq a) (x:a),
  ((length (snoc s x)) = (1%Z + (length s))%Z) /\
  ((get (snoc s x) (length s)) = x) /\
  (forall (i:Numbers.BinNums.Z), (0%Z <= i)%Z /\ (i < (length s))%Z ->
   ((get (snoc s x) i) = (get s i))).

Parameter mixfix_lbdtdtrb:
  forall {a:Type} {a_WT:WhyType a}, seq a -> Numbers.BinNums.Z ->
  Numbers.BinNums.Z -> seq a.

Axiom mixfix_lbdtdtrb'def :
  forall {a:Type} {a_WT:WhyType a},
  forall (s:seq a) (i:Numbers.BinNums.Z) (j:Numbers.BinNums.Z),
  (0%Z <= i)%Z /\ (i <= j)%Z /\ (j <= (length s))%Z ->
  ((mixfix_lbdtdtrb s i j) =
   (create (j - i)%Z (fun (k:Numbers.BinNums.Z) => get s (i + k)%Z))).

Axiom mixfix_lbdtdtrb'spec :
  forall {a:Type} {a_WT:WhyType a},
  forall (s:seq a) (i:Numbers.BinNums.Z) (j:Numbers.BinNums.Z),
  (0%Z <= i)%Z /\ (i <= j)%Z /\ (j <= (length s))%Z ->
  ((length (mixfix_lbdtdtrb s i j)) = (j - i)%Z) /\
  (forall (k:Numbers.BinNums.Z), (0%Z <= k)%Z /\ (k < (j - i)%Z)%Z ->
   ((get (mixfix_lbdtdtrb s i j) k) = (get s (i + k)%Z))).

Parameter mixfix_lb_dtdtrb:
  forall {a:Type} {a_WT:WhyType a}, seq a -> Numbers.BinNums.Z -> seq a.

Axiom mixfix_lb_dtdtrb'def :
  forall {a:Type} {a_WT:WhyType a},
  forall (s:seq a) (i:Numbers.BinNums.Z),
  (0%Z <= i)%Z /\ (i <= (length s))%Z ->
  ((mixfix_lb_dtdtrb s i) = (mixfix_lbdtdtrb s i (length s))).

Parameter mixfix_lbdtdt_rb:
  forall {a:Type} {a_WT:WhyType a}, seq a -> Numbers.BinNums.Z -> seq a.

Axiom mixfix_lbdtdt_rb'def :
  forall {a:Type} {a_WT:WhyType a},
  forall (s:seq a) (j:Numbers.BinNums.Z),
  (0%Z <= j)%Z /\ (j <= (length s))%Z ->
  ((mixfix_lbdtdt_rb s j) = (mixfix_lbdtdtrb s 0%Z j)).

Parameter result3:
  forall {a:Type} {a_WT:WhyType a}, seq a -> seq a -> Numbers.BinNums.Z ->
  Numbers.BinNums.Z -> a.

Axiom result'def3 :
  forall {a:Type} {a_WT:WhyType a},
  forall (s1:seq a) (s2:seq a) (l:Numbers.BinNums.Z) (i:Numbers.BinNums.Z),
  ((i < l)%Z -> ((result3 s1 s2 l i) = (get s1 i))) /\
  (~ (i < l)%Z -> ((result3 s1 s2 l i) = (get s2 (i - l)%Z))).

(* Why3 assumption *)
Definition infix_plpl {a:Type} {a_WT:WhyType a} (s1:seq a) (s2:seq a) : seq a :=
  let l := length s1 in create (l + (length s2))%Z (result3 s1 s2 l).

Axiom infix_plpl'spec :
  forall {a:Type} {a_WT:WhyType a},
  forall (s1:seq a) (s2:seq a),
  ((length (infix_plpl s1 s2)) = ((length s1) + (length s2))%Z) /\
  (forall (i:Numbers.BinNums.Z), (0%Z <= i)%Z /\ (i < (length s1))%Z ->
   ((get (infix_plpl s1 s2) i) = (get s1 i))) /\
  (forall (i:Numbers.BinNums.Z),
   ((length s1) <= i)%Z /\ (i < (length (infix_plpl s1 s2)))%Z ->
   ((get (infix_plpl s1 s2) i) = (get s2 (i - (length s1))%Z))).

Axiom uint64 : Type.
Parameter uint64_WhyType : WhyType uint64.
Existing Instance uint64_WhyType.

Parameter uint64'int: uint64 -> Numbers.BinNums.Z.

Axiom uint64'axiom :
  forall (i:uint64),
  (0%Z <= (uint64'int i))%Z /\ ((uint64'int i) <= 18446744073709551615%Z)%Z.

(* Why3 assumption *)
Definition in_bounds (n:Numbers.BinNums.Z) : Prop :=
  (0%Z <= n)%Z /\ (n <= 18446744073709551615%Z)%Z.

Axiom to_int_in_bounds : forall (n:uint64), in_bounds (uint64'int n).

Axiom extensionality :
  forall (x:uint64) (y:uint64), ((uint64'int x) = (uint64'int y)) -> (x = y).

Parameter zero_unsigned: uint64.

Axiom zero_unsigned_is_zero : ((uint64'int zero_unsigned) = 0%Z).

(* Why3 assumption *)
Definition usize := uint64.

(* Why3 assumption *)
Inductive t_unionfindmodel :=
  | C_UnionFindModel : seq uint64 -> t_unionfindmodel.
Axiom t_unionfindmodel_WhyType : WhyType t_unionfindmodel.
Existing Instance t_unionfindmodel_WhyType.

(* Why3 assumption *)
Definition unionfindmodel_parent (self:t_unionfindmodel) : seq uint64 :=
  match self with
  | C_UnionFindModel a => a
  end.

(* Why3 assumption *)
Definition in_range (self:t_unionfindmodel) (i:Numbers.BinNums.Z) : Prop :=
  (0%Z <= i)%Z /\ (i < (length (unionfindmodel_parent self)))%Z.

(* Why3 assumption *)
Definition parent (self:t_unionfindmodel) (i:Numbers.BinNums.Z) :
    Numbers.BinNums.Z :=
  uint64'int (get (unionfindmodel_parent self) i).

Parameter reach:
  t_unionfindmodel -> Numbers.BinNums.Z -> Numbers.BinNums.Z ->
  Numbers.BinNums.Z -> Prop.

Axiom def :
  forall (self:t_unionfindmodel) (src:Numbers.BinNums.Z)
    (dst:Numbers.BinNums.Z) (len:Numbers.BinNums.Z),
  (reach self src dst len ->
   ~ (len < 0%Z)%Z /\
   (~ (len < 0%Z)%Z ->
    ((len = 0%Z) -> (src = dst)) /\
    (~ (len = 0%Z) ->
     ~ (src = dst) /\ reach self (parent self src) dst (len - 1%Z)%Z))) /\
  (~ (len < 0%Z)%Z /\
   ((len = 0%Z) /\ (src = dst) \/
    ~ (len = 0%Z) /\
    ~ (src = dst) /\ reach self (parent self src) dst (len - 1%Z)%Z) ->
   reach self src dst len).

Axiom reach_spec : True.

(* Why3 assumption *)
Definition is_root (self:t_unionfindmodel) (i:Numbers.BinNums.Z) : Prop :=
  in_range self i /\ ((parent self i) = i).

Axiom lemma_reach_iff_spec :
  forall (self:t_unionfindmodel), forall (len:Numbers.BinNums.Z),
  forall (dst:Numbers.BinNums.Z), forall (src:Numbers.BinNums.Z),
  reach self src dst len <->
  (src = dst) /\ (len = 0%Z) \/
  ~ (src = dst) /\
  (0%Z < len)%Z /\ reach self (parent self src) dst (len - 1%Z)%Z.

(* Why3 assumption *)
Definition belong (self:t_unionfindmodel) (i:Numbers.BinNums.Z)
    (root:Numbers.BinNums.Z) : Prop :=
  is_root self root /\ (exists len:Numbers.BinNums.Z, reach self i root len).

Lemma root_reachable : forall uf i j n,
    is_root uf i -> reach uf i j n -> j = i.
Proof.
  intros uf i j n [_ Hparent] Hreach.
  induction n as [n IH] using (well_founded_induction (Z.lt_wf 0)).
  rewrite lemma_reach_iff_spec in Hreach.
  destruct Hreach as [|(Hne & Hpos & Hreach)]; [intuition| ].
  rewrite Hparent in Hreach.
  apply IH in Hreach; auto with zarith.
Qed.

(* Why3 goal *)
Theorem lemma_belong_unique'vc :
  forall (self:seq uint64),
  let self1 := C_UnionFindModel self in
  forall (r2:Numbers.BinNums.Z), forall (r1:Numbers.BinNums.Z),
  forall (i:Numbers.BinNums.Z), belong self1 i r1 -> belong self1 i r2 ->
  (r1 = r2).
(* Why3 intros self self1 r2 r1 i h1 h2. *)
Proof.
  intros self_parent self.
  intros r2 r1 i (Hroot1 & len1 & Hreach1) (Hroot2 & len2 & Hreach2).
  revert i len2 Hreach1 Hreach2.
  induction len1 as [len1 IH] using (well_founded_induction (Z.lt_wf 0)).
  intros i len2 Hreach1 Hreach2.
  rewrite lemma_reach_iff_spec in Hreach1.
  destruct Hreach1 as [Hreach1 | Hreach1].
  - destruct Hreach1. subst.
    apply root_reachable in Hreach2; auto.
  - destruct Hreach1 as (Hne & Hpos & Hreach).
    rewrite lemma_reach_iff_spec in Hreach2.
    destruct Hreach2 as [Hreach2 | Hreach2].
    + destruct Hreach2. subst.
      rewrite (proj2 Hroot2) in *.
      eauto using root_reachable.
    + destruct Hreach2 as (_ & _ & Hreach2).
      eapply IH in Hreach; eauto with zarith.
Qed.
