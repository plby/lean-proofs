import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSkewConjugationExponential
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureCayley
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicUniformSubdivision

/-!
# A common relative-logarithm neighborhood for quaternionic complex structures

Uniqueness of a sufficiently small symplectic logarithm turns reversibility
into anticommutation. The bound is independent of the base complex structure,
because symplectic conjugation does not increase the operator norm. This gives
compatible logarithms for uniform subdivisions of compact path families.
-/

noncomputable section

open Set Metric Filter
open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures.CompatibleLog

open Exponential NoExoticSixSphere.UniformTimePartition

variable {n : ℕ}

private theorem real_norm_neg {V : Type*} [NormedAddCommGroup V] (v : V) :
    ‖-v‖ = ‖v‖ := norm_neg v

def groupLogarithmBall (n : ℕ) (r : ℝ) : Set (symplecticSubgroup n) :=
  {a | a ∈ (Exponential.logarithmChart n).source ∧ ‖Exponential.logarithmChart n a‖ < r}

theorem isOpen_groupLogarithmBall (n : ℕ) (r : ℝ) : IsOpen (groupLogarithmBall n r) := by
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  have hs := (Exponential.logarithmChart n).open_source.mem_nhds ha.1
  have hc : ContinuousAt (Exponential.logarithmChart n) a :=
    (Exponential.logarithmChart n).contMDiffOn_toFun.continuousOn.continuousAt hs
  have hn : ContinuousAt (fun a : symplecticSubgroup n ↦ ‖Exponential.logarithmChart n a‖) a :=
    ContinuousAt.norm (E := SkewSpace n) hc
  have ht := hn (gt_mem_nhds ha.2)
  filter_upwards [hs, ht] with b hb ht
  exact ⟨hb, ht⟩

theorem one_mem_groupLogarithmBall (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (1 : symplecticSubgroup n) ∈ groupLogarithmBall n r := by
  refine ⟨one_mem_logarithmChart_source n, ?_⟩
  rw [Exponential.logarithmChart_one, norm_zero (E := SkewSpace n)]
  exact hr

theorem logarithm_anticommute (J : Space n) (a : symplecticSubgroup n) {r : ℝ}
    (hr : closedBall (0 : SkewSpace n) r ⊆ (Exponential.logarithmChart n).target)
    (ha : a ∈ groupLogarithmBall n r)
    (hrev : toSymplectic J * a = a⁻¹ * toSymplectic J) :
    J.val.val.comp (Exponential.logarithmChart n a).val =
      -((Exponential.logarithmChart n a).val.comp J.val.val) := by
  let K := Exponential.logarithmChart n a
  have hL : conjugateSkew (toSymplectic J) K ∈ (Exponential.logarithmChart n).target := by
    apply hr
    rw [mem_closedBall, dist_zero_right (conjugateSkew (toSymplectic J) K)]
    exact (norm_conjugateSkew_le _ _).trans ha.2.le
  have hneg : -K ∈ (Exponential.logarithmChart n).target := by
    apply hr
    rw [mem_closedBall, dist_zero_right (-K), real_norm_neg (V := SkewSpace n)]
    exact ha.2.le
  have hKexp : exp K = a := exp_logarithmChart a ha.1
  have he : exp (conjugateSkew (toSymplectic J) K) = exp (-K) := by
    rw [exp_conjugateSkew, exp_neg, hKexp, hrev, mul_inv_cancel_right]
  have heq := congrArg (Exponential.logarithmChart n) he
  rw [Exponential.logarithmChart_exp _ hL, Exponential.logarithmChart_exp _ hneg] at heq
  apply ContinuousLinearMap.ext
  intro x
  have hp := DFunLike.congr_fun (congrArg (fun L : SkewSpace n ↦ L.val) heq) (J.val.val x)
  change J.val.val (K.val
      ((NoExoticSixSphere.OrthogonalPaths.inverse (toSymplectic J).val).val.val (J.val.val x))) =
    -(K.val (J.val.val x)) at hp
  have hx : (NoExoticSixSphere.OrthogonalPaths.inverse (toSymplectic J).val).val.val
      (J.val.val x) = x :=
    NoExoticSixSphere.OrthogonalPaths.inverse_apply_self (toSymplectic J).val x
  rw [hx] at hp
  exact hp

theorem exists_compatible_logarithmBall (n : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ J J' : Space n,
      Cayley.relative J J' ∈ groupLogarithmBall n r →
        Cayley.relative J J' ∈ compatibleDomain n ∧
        J.val.val.comp (Exponential.logarithmChart n (Cayley.relative J J')).val =
          -((Exponential.logarithmChart n (Cayley.relative J J')).val.comp J.val.val) := by
  obtain ⟨r, hr0, _, hr⟩ := exists_compatible_radius n
  refine ⟨r, hr0, ?_⟩
  intro J J' h
  have hK : Exponential.logarithmChart n (Cayley.relative J J') ∈
      closedBall (0 : SkewSpace n) r := by
    rw [mem_closedBall,
      dist_zero_right (Exponential.logarithmChart n (Cayley.relative J J'))]
    exact h.2.le
  refine ⟨⟨h.1, (hr hK).2⟩, ?_⟩
  exact logarithm_anticommute J (Cayley.relative J J')
    (fun K hK ↦ (hr hK).1) h (Cayley.relative_reversible J J')

theorem continuous_relative_pair :
    Continuous (fun p : Space n × Space n ↦ Cayley.relative p.1 p.2) :=
  (continuous_toSymplectic.comp continuous_fst).inv.mul
    (continuous_toSymplectic.comp continuous_snd)

theorem exists_compatible_relativeLog_neighborhood (n : ℕ) :
    ∃ U : Set (Space n × Space n), IsOpen U ∧ (∀ J, (J, J) ∈ U) ∧
      ∀ J J', (J, J') ∈ U →
        Cayley.relative J J' ∈ compatibleDomain n ∧
        J.val.val.comp (Exponential.logarithmChart n (Cayley.relative J J')).val =
          -((Exponential.logarithmChart n (Cayley.relative J J')).val.comp J.val.val) := by
  obtain ⟨r, hr, hcontrol⟩ := exists_compatible_logarithmBall n
  let U := (fun p : Space n × Space n ↦ Cayley.relative p.1 p.2) ⁻¹' groupLogarithmBall n r
  refine ⟨U, (isOpen_groupLogarithmBall n r).preimage continuous_relative_pair, ?_, hcontrol⟩
  intro J
  change Cayley.relative J J ∈ groupLogarithmBall n r
  rw [Cayley.relative_self]
  exact one_mem_groupLogarithmBall n hr

theorem exists_uniform_relativeLog_partition {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (H : C(I × X, Space n)) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ ∀ i : Fin (m + 1),
      ∀ u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ), ∀ x,
        Cayley.relative (H (unitTime m i.castSucc, x)) (H (u, x)) ∈ compatibleDomain n ∧
        (H (unitTime m i.castSucc, x)).val.val.comp
            (Exponential.logarithmChart n
              (Cayley.relative (H (unitTime m i.castSucc, x)) (H (u, x)))).val =
          -((Exponential.logarithmChart n
              (Cayley.relative (H (unitTime m i.castSucc, x)) (H (u, x)))).val.comp
                (H (unitTime m i.castSucc, x)).val.val) := by
  obtain ⟨r, hr, hcontrol⟩ := exists_compatible_logarithmBall n
  let F : C(I × X, symplecticSubgroup n) :=
    ⟨fun z ↦ toSymplectic (H z), continuous_toSymplectic.comp H.continuous⟩
  obtain ⟨m, hm, hsmall⟩ := Exponential.exists_uniform_increment_partition F
    (groupLogarithmBall n r)
    ((isOpen_groupLogarithmBall n r).mem_nhds (one_mem_groupLogarithmBall n hr)) N
  exact ⟨m, hm, fun i u hu x ↦ hcontrol _ _ (hsmall i u hu x)⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures.CompatibleLog
