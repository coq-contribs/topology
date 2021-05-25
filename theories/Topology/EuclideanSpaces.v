(* Formalize the standard topologies of the ℝ^n spaces. *)

(* Every closed interval admits a uniform (probability) distribution.
   Does S^1 admit a uniform probability distribution?
   Does every compact manifold (or topological-space (maybe Hausdorff is necessary)) admit a uniform probability distribution?
*)

Require Import FunctionalExtensionality.
Require Import RTopology.
Require Import Vector.
Require Import ProductTopology.
Require Import Ensembles.
Require Import Compactness.
Require Import Psatz.

(* Using [Fin.t] instead of repeated application of ProductTopology2 makes that we don’t have to consider associativity. Using [Vector] instead of [ProductTopology] makes that we don’t have to always consider functional extensionality. *)
Definition FiniteProduct (A : TopologicalSpace) (n : nat) :=
  WeakTopology (fun i : Fin.t n => fun x : t (point_set A) n => nth x i).

Definition FiniteProduct_add_fn (A : TopologicalSpace) (n m : nat) :
  (point_set (ProductTopology2 (FiniteProduct A n) (FiniteProduct A m))) ->
  (point_set (FiniteProduct A (n + m))).
Proof.
  induction n.
  - intros.
    simpl in *.
    destruct X.
    apply t0.
  - intros.
    simpl in *.
    destruct X as [x y].
    induction x using caseS'.
    specialize (IHn (pair x y)).
    apply cons; assumption.
Defined.

Lemma FiniteProduct_add_fn_cts A n m : continuous (FiniteProduct_add_fn A n m).
Admitted.

Definition FiniteProduct_add_split_fn (A : TopologicalSpace) (n m : nat) :
  (point_set (FiniteProduct A (n + m))) ->
  (point_set (ProductTopology2 (FiniteProduct A n) (FiniteProduct A m))).
Proof.
  induction n.
  - intros.
    simpl in *.
    split.
    + apply nil.
    + assumption.
  - intros. simpl in *.
    destruct X using caseS'.
    specialize (IHn X) as [x y].
    split; [|assumption].
    apply cons; assumption.
Defined.

Lemma FiniteProduct_add_split_cts A n m : continuous (FiniteProduct_add_split_fn A n m).
Admitted.

Lemma FiniteProduct_add (A : TopologicalSpace) (n m : nat) :
  homeomorphic (ProductTopology2 (FiniteProduct A n) (FiniteProduct A m)) (FiniteProduct A (n + m)).
Proof.
  unshelve eexists.
  { apply FiniteProduct_add_fn. }
  unshelve eexists.
  { apply FiniteProduct_add_split_fn. }
  - admit.
  - admit.
  - induction n.
    + intros.
      simpl in *.
      destruct x.
      destruct t using case0.
      reflexivity.
    + intros.
      simpl in *.
      destruct x.
      induction t using caseS'.
      simpl.
      rewrite IHn.
      reflexivity.
  - induction n.
    + intros.
      simpl in *.
      reflexivity.
    + intros.
      simpl in *.
      induction y using caseS'.
      simpl in *.
      specialize (IHn y).
      induction (FiniteProduct_add_split_fn _ _ _ _).
      simpl.
      rewrite <- IHn.
      reflexivity.
Admitted.

(* Given functional extensionality, [FiniteProduct] is homeomorphic to [ProductTopology]. *)
Lemma FiniteProduct_char (A : TopologicalSpace) (n : nat) :
  homeomorphic (FiniteProduct A n) (ProductTopology (fun _ : Fin.t n => A)).
Proof.
  exists (fun (x : t (point_set A) n) (i : Fin.t n) => nth x i).
  unshelve econstructor.
  - (* define g *)
    simpl. unfold product_space_point_set.
    intros x. induction n.
    + apply nil.
    + apply cons.
      * apply (x Fin.F1).
      * apply IHn.
        intros i.
        apply (x (Fin.FS i)).
  - apply pointwise_continuity. simpl. intros x.
    apply product_map_continuous. simpl. intros i.
    apply continuous_func_continuous_everywhere.
    apply (weak_topology_makes_continuous_funcs _ _ _ (fun i (x : t (point_set A) n) => nth x i) i).
  - apply weak_topology_continuous_char.
    intros.
    replace (compose _ _) with (product_space_proj a (X := fun _ => A)).
    { apply (product_space_proj_continuous _ (fun _ : Fin.t n => A) a).
    }
    apply functional_extensionality.
    unfold product_space_point_set.
    unfold product_space_proj.
    unfold compose.
    induction a.
    + intros.
      simpl in *.
      reflexivity.
    + intros.
      simpl in *.
      rewrite <- IHa.
      reflexivity.
  - simpl. intros.
    induction x.
    + simpl. reflexivity.
    + simpl in *. rewrite IHx. reflexivity.
  - simpl. unfold product_space_point_set. intros.
    apply functional_extensionality. intros.
    induction x.
    + simpl. reflexivity.
    + simpl. rewrite IHx. reflexivity.
Qed.

Definition EuclideanSpace (n : nat) := FiniteProduct RTop n.

Definition EuclideanSpace_scalarproduct {n : nat} (x y : point_set (EuclideanSpace n)) : R :=
  fold_right Rplus (map2 Rmult x y) 0.

Program Definition EuclideanSpace_scalarproduct_self_nonneg {n : nat} (x : point_set (EuclideanSpace n)) : nonnegreal :=
  {| nonneg := EuclideanSpace_scalarproduct x x; |}.
Next Obligation.
  unfold EuclideanSpace_scalarproduct.
  induction x.
  + simpl. apply Rle_refl.
  + simpl.
    apply Rplus_le_le_0_compat; try assumption.
    apply Rle_0_sqr.
Qed.

Definition EuclideanSpace_norm {n : nat} (x : point_set (EuclideanSpace n)) : R :=
  Rsqrt (EuclideanSpace_scalarproduct_self_nonneg x).

Lemma EuclideanSpace_norm_positivity {n : nat} (x : point_set (EuclideanSpace n)) :
  0 <= EuclideanSpace_norm x.
Proof.
  unfold EuclideanSpace_norm.
  apply Rsqrt_positivity.
Qed.

(* Vector addition on [EuclideanSpace] *)
Definition EuclideanSpace_add {n : nat} (x y : point_set (EuclideanSpace n)) : point_set (EuclideanSpace n) :=
  map2 Rplus x y.

(* The "minus" operation on vectors. *)
Definition EuclideanSpace_opp {n : nat} (x : point_set (EuclideanSpace n)) : point_set (EuclideanSpace n) :=
  map Ropp x.

Definition EuclideanSpace_zero {n : nat} : point_set (EuclideanSpace n).
Proof.
  simpl.
  induction n.
  - apply nil.
  - apply cons.
    + exact 0.
    + assumption.
Defined.

Lemma EuclideanSpace_opp_zero {n : nat} : (EuclideanSpace_opp EuclideanSpace_zero) = @EuclideanSpace_zero n.
Proof.
  induction n.
  - simpl. reflexivity.
  - simpl. rewrite IHn.
    rewrite Ropp_0.
    reflexivity.
Qed.

Lemma EuclideanSpace_add_opp_r {n : nat} (x : point_set (EuclideanSpace n)) :
  EuclideanSpace_add x (EuclideanSpace_opp x) = EuclideanSpace_zero.
Proof.
  induction x.
  - reflexivity.
  - simpl. rewrite IHx.
    rewrite Rplus_opp_r.
    reflexivity.
Qed.

Lemma EuclideanSpace_add_zero_r {n : nat} (x : point_set (EuclideanSpace n)) :
  EuclideanSpace_add x EuclideanSpace_zero = x.
Proof.
  induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx.
    rewrite Rplus_0_r.
    reflexivity.
Qed.

Lemma Rsqr_zero (x : R) :
  Rsqr x = 0 ->
  x = 0.
Proof.
  apply Rsqr_0_uniq.
Qed.

Lemma Rsqrt_zero (x : nonnegreal) :
  nonneg x = 0 ->
  Rsqrt x = 0.
Proof.
  intros.
  unfold Rsqrt.
  destruct (Rsqrt_exists _ _).
  destruct a. induction x. simpl in *. subst.
  apply Rsqr_zero.
  symmetry. assumption.
Qed.

Lemma EuclideanSpace_norm_zero {n : nat} :
  EuclideanSpace_norm (@EuclideanSpace_zero n) = 0.
Proof.
  unfold EuclideanSpace_norm.
  apply Rsqrt_zero.
  simpl.
  unfold EuclideanSpace_scalarproduct.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn.
    rewrite Rplus_0_r.
    rewrite Rmult_0_r.
    reflexivity.
Qed.

Lemma EuclideanSpace_norm_is_zero_eq {n : nat} (x : point_set (EuclideanSpace n)) :
  EuclideanSpace_norm x = 0 ->
  x = EuclideanSpace_zero.
Proof.
Admitted.

Definition Euclidean_metric {n : nat} (x y : point_set (EuclideanSpace n)) : R :=
  EuclideanSpace_norm (EuclideanSpace_add x (EuclideanSpace_opp y)).

(* Alternate definition of euclidean metric:
   Define it on the (finite) product of arbitrary metric spaces. *)

Theorem Euclidean_metric_metric {n : nat} : metric (@Euclidean_metric n).
Proof.
  constructor.
  - intros.
    apply Rle_ge.
    apply EuclideanSpace_norm_positivity.
  - intros.
    admit.
  - intros.
    admit.
  - intros.
    unfold Euclidean_metric.
    rewrite EuclideanSpace_add_opp_r.
    rewrite EuclideanSpace_norm_zero.
    reflexivity.
  - intros.
    unfold Euclidean_metric in H.
    apply EuclideanSpace_norm_is_zero_eq in H.
    (* proof by group theory. *)
    admit.
Admitted.

Definition metrically_bounded {X} (d : X -> X -> R) (S : Ensemble X) :=
  exists r x, Included S (open_ball _ d x r).

(* The Heine-Borel property for metric spaces. *)
Definition metric_HeineBorel_prop (X : Type) (d : X -> X -> R) (H : metric d) :=
  forall S : Ensemble (point_set (MetricTopology d H)),
    closed S /\ metrically_bounded d S -> compact (SubspaceTopology S).

Definition subspace_set_inclusion {X : Type} {S : Ensemble X} (U : Ensemble X) :
  Ensemble { x | In S x } :=
  (fun x => In U (proj1_sig x)).

Lemma subspace_open_char (X : TopologicalSpace) (S : Ensemble (point_set X)) (U : Ensemble (point_set (SubspaceTopology S))) :
  open U <-> exists U', open U' /\ U = subspace_set_inclusion U'.
Proof.
Admitted.

Lemma compact_Subspace (X : TopologicalSpace) (S : Ensemble (point_set X)) :
  compact (SubspaceTopology S) ->
  forall C : Family (point_set X),
    (forall U, In C U -> open U) ->
    FamilyUnion C = Full_set ->
    exists C',
      Finite C' /\ Included C' C /\ Included S (FamilyUnion C').
Proof.
  intros.
  unshelve edestruct H as [C'].
  - red; red. intros U.
    refine (exists U', In C U' /\ _).
    apply (U = subspace_set_inclusion U').
  - intros.
    destruct H2 as [U'].
    apply subspace_open_char.
    exists U'. intuition.
  - apply Extensionality_Ensembles; split; red; intros.
    { constructor. }
    clear H2.
    destruct x as [x].
    assert (In (FamilyUnion C) x).
    { rewrite H1. constructor. }
    destruct H2.
    exists (subspace_set_inclusion S0).
    + exists S0. tauto.
    + assumption.
  - destruct H2 as [? [? ?]].
    (* [C'] is a finite cover of [S] using subsets of [S].
       But we actually want a finite cover of [S] using open sets of [X].
       This shall be constructed now.

       Note that [(fun U => In C' (subspace_set_inclusion U))] isn’t the
       right family, because then we lose finiteness.
     *)
    admit.
Admitted.

Theorem metric_HeineBorel_converse (X : Type) (d : X -> X -> R) (H : metric d) :
  forall S : Ensemble (point_set (MetricTopology d H)),
    compact (SubspaceTopology S) ->
    closed S /\ metrically_bounded d S.
Proof.
  intros.
  split.
  - apply compact_closed.
    + apply metrizable_Hausdorff.
      exists d.
      * assumption.
      * apply MetricTopology_metrizable.
    + assumption.
  - (* Construct the following family of open balls:
       For each x ∈ X include the ball of radius 1 in the family. *)
    pose proof (compact_Subspace _ _ H0).
    pose (C := (fun x : X => open_ball _ d x 1)).
    specialize (H1 (ImageFamily C)).
    destruct H1 as [C'].
    + intros.
      destruct H1; subst. unfold C.
      apply metric_space_open_ball_open; auto.
      * apply MetricTopology_metrizable.
      * apply Rlt_gt.
        apply Rlt_0_1.
    + apply Extensionality_Ensembles; split; red; intros.
      { constructor. }
      clear H1.
      exists (C x).
      * exists x; try reflexivity. constructor.
      * constructor. rewrite metric_zero; try assumption.
        apply Rlt_0_1.
    + destruct H1 as [? [? ?]].
      admit.
Admitted.

Lemma SingletonSpace_is_metrizable (X : TopologicalSpace) :
  (forall x y : point_set X, x = y) ->
  { d : _ -> _ -> R | metrizes X d /\ metric d }.
Proof.
  intros.
  exists (fun _ _ => 0). split.
  + constructor.
    * intros.
      destruct H0.
      constructor.
      -- replace (open_ball _ _ _ _) with (@Full_set (point_set X)).
         { apply open_full. }
         apply Extensionality_Ensembles; split; red; intros.
         2: { constructor. }
         clear H1.
         constructor.
         apply Rgt_lt. assumption.
      -- constructor. apply Rgt_lt. assumption.
    * intros.
      exists (open_ball _ (fun _ _ => 0) x 1). split.
      2: {
        red; intros. rewrite (H x0 x). apply H0.
      }
      constructor.
      apply Rlt_gt. apply Rlt_0_1.
  + constructor.
    * intros. apply Rge_refl.
    * auto.
    * intros. rewrite Rplus_0_r. apply Rle_refl.
    * intros. reflexivity.
    * intros. apply H.
Defined.

Definition FiniteProduct_metric (n : nat) (X : Type) (d : X -> X -> R) (H : metric d) :
  (point_set (FiniteProduct (MetricTopology d H) n)) ->
  (point_set (FiniteProduct (MetricTopology d H) n)) -> R.
Proof.
  intros.
  apply Rsqrt.
  unshelve econstructor.
  - simpl in *. apply (fold_right Rplus (map2 d X0 X1) 0).
  - admit.
Admitted.

Lemma FiniteProduct_metric_metric n X d H :
  metric (FiniteProduct_metric n X d H).
Proof.
Admitted.

Lemma FiniteProduct_metric_metrizes n X d H :
  metrizes (FiniteProduct (MetricTopology d H) n) (FiniteProduct_metric n X d H).
Proof.
Admitted.

Lemma FiniteProduct_HeineBorel (n : nat) (X : Type) (d : X -> X -> R) (H : metric d) :
  metric_HeineBorel_prop X d H ->
  metric_HeineBorel_prop _ (FiniteProduct_metric n X d H) (FiniteProduct_metric_metric n X d H).
Proof.
  intros.
  red. intros.
Admitted.

Theorem RTop_HeineBorel :
  metric_HeineBorel_prop _ R_metric R_metric_is_metric.
Proof.
Admitted.

Lemma EuclideanSpace_HeineBorel (n : nat) :
  metric_HeineBorel_prop _
                         (FiniteProduct_metric n R R_metric R_metric_is_metric)
                         (FiniteProduct_metric_metric n R R_metric R_metric_is_metric).
Proof.
  apply FiniteProduct_HeineBorel.
  apply RTop_HeineBorel.
Qed.

Theorem HeineBorel (n : nat) :
  forall S, closed S /\ (metrically_bounded (@Euclidean_metric n) S) <->
        compact (SubspaceTopology S).
Admitted.

(* Is the HeineBorel-property preserved by finite products? If yes, then the proof of [HeineBorel] for ℝ^n can be deduced from the proof of [HeineBorel] for ℝ, which’d make the whole stuff simpler. *)

Definition Sphere (n : nat) : TopologicalSpace :=
  SubspaceTopology (inverse_image (@EuclideanSpace_norm n) (Singleton 1)).

Lemma Euclidean_norm_cts (n : nat) : continuous (@EuclideanSpace_norm n) (Y := RTop).
Admitted.

Lemma continuity_closed_char {X Y : TopologicalSpace} (f : point_set X -> point_set Y) :
  continuous f <->
  (forall V : Ensemble (point_set Y),
      closed V ->
      closed (inverse_image f V)).
Proof.
  split; intros.
  - unfold closed in *.
    rewrite <- inverse_image_complement.
    apply H. assumption.
  - red; intros.
    apply closed_complement_open.
    rewrite <- inverse_image_complement.
    apply H. unfold closed.
    rewrite Complement_Complement.
    assumption.
Qed.

Theorem Sphere_compact (n : nat) : compact (Sphere n).
  apply HeineBorel.
  split.
  - (* closed *)
    apply (continuity_closed_char (Y := RTop)).
    + apply Euclidean_norm_cts.
    + apply Hausdorff_impl_T1_sep.
      apply metrizable_Hausdorff.
      apply RTop_metrizable.
  - (* metrically bounded *)
    exists 2, EuclideanSpace_zero.
    red; intros.
    destruct H. inversion H; subst; clear H.
    simpl. constructor.
    rewrite metric_sym.
    2: { apply Euclidean_metric_metric. }
    unfold Euclidean_metric.
    rewrite EuclideanSpace_opp_zero.
    rewrite EuclideanSpace_add_zero_r.
    rewrite <- H1.
    lra.
Qed.

(* Conjecture: Every S^n is (homeomorphic to) the one-point-compactification of ℝ^n.
*)
