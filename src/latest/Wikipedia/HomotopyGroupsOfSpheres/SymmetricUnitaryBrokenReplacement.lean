import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryIntervalReplacement
import Wikipedia.HomotopyGroupsOfSpheres.OrthogonalBrokenPathIntervals
import Wikipedia.NoExoticSixSphere.ExponentialReplacementFixed
import Wikipedia.NoExoticSixSphere.ClampedUniformPartition
import Wikipedia.NoExoticSixSphere.IntervalPartition

/-!
# Global path replacement within the constrained matrix space

On every subdivision cell, the ambient deformation agrees with the local
constrained replacement. It therefore lies in the actual orthogonal image
of the symmetric determinant-one space throughout the homotopy.
-/

noncomputable section

open Set unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.BrokenReplacement

open ComplexMatrixRealRepresentation NoExoticSixSphere.UniformTimePartition
open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.CayleyTransform

variable {N : Type*} [Fintype N] [DecidableEq N] {X : Type*} [TopologicalSpace X]
variable (H : C(I × X, SpecialSpace N)) (m : ℕ)
  (hsmall : ∀ i : Fin (m + 1),
    ∀ u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ), ∀ x,
      (H (unitTime m i.castSucc, x), H (u, x)) ∈ ShortLog.domain N)

include hsmall in
theorem clampedCondition :
    ∀ k, ∀ u ∈ Icc (clampedTime m k) (clampedTime m (k + 1)), ∀ x,
      (H (clampedTime m k, x), H (u, x)) ∈ ShortLog.domain N := by
  intro k u hu x
  by_cases hk : k < m + 1
  · let i : Fin (m + 1) := ⟨k, hk⟩
    have hl : clampedTime m k = unitTime m i.castSucc := clampedTime_left m i
    have hr : clampedTime m (k + 1) = unitTime m i.succ := clampedTime_right m i
    rw [hl, hr] at hu
    rw [hl]
    exact hsmall i u hu x
  · have hk' : m + 1 ≤ k := Nat.le_of_not_gt hk
    have he : u = 1 := le_antisymm le_top
      (by simpa only [clampedTime_after m k hk'] using hu.1)
    rw [clampedTime_after m k hk', he]
    exact ShortLog.diagonal_mem_domain (H (1, x))

include hsmall in
theorem groupCondition (k : ℕ) (u : I)
    (hu : u ∈ Icc (clampedTime m k) (clampedTime m (k + 1))) (x : X) :
    (orthogonalFamily H (clampedTime m k, x))⁻¹ * orthogonalFamily H (u, x) ∈
      (NoExoticSixSphere.OrthogonalExponential.logarithmChart (2 * Fintype.card N)).source := by
  change (specialOrthogonal (H (clampedTime m k, x)))⁻¹ * specialOrthogonal (H (u, x)) ∈ _
  rw [← ShortLog.orthogonal_relative]
  exact ComplexSkewMatrices.CompatibleLog.orthogonal_mem_source _
    (clampedCondition H m hsmall k u hu x)

def ambientDeformation : C(I × (I × X), OrthogonalOperators (2 * Fintype.card N)) :=
  NoExoticSixSphere.OrthogonalExponential.BrokenPaths.deformation (orthogonalFamily H)
    (clampedTime m) (monotone_clampedTime m) (groupCondition H m hsmall) (m + 1)

theorem ambientDeformation_mem_range (q : I × (I × X)) :
    ambientDeformation H m hsmall q ∈ Set.range (specialOrthogonal (N := N)) := by
  rcases q with ⟨r, v, x⟩
  have hv : (v : ℝ) ∈ Icc (time m 0) (time m (Fin.last (m + 1))) := by
    simpa only [time_zero, time_last] using v.property
  obtain ⟨i, hi⟩ := NoExoticSixSphere.IntervalPartition.exists_mem_adjacent (time m) hv
  have hi' : v ∈ Icc (clampedTime m i.val) (clampedTime m (i.val + 1)) := by
    rw [clampedTime_left, clampedTime_right]
    exact hi
  have he := NoExoticSixSphere.OrthogonalExponential.BrokenPaths.deformation_on_interval
    (orthogonalFamily H) (clampedTime m) (monotone_clampedTime m)
    (groupCondition H m hsmall) (m + 1) i.val i.isLt r v x hi'
  refine ⟨IntervalReplacement.lifted H (clampedTime m i.val) (clampedTime m (i.val + 1))
    ((monotone_clampedTime m) i.val.le_succ) (clampedCondition H m hsmall i.val)
      (r, (v, x)), ?_⟩
  rw [IntervalReplacement.lifted_toOrthogonal]
  exact he.symm

def deformation : C(I × (I × X), SpecialSpace N) :=
  liftOrthogonalFamily (ambientDeformation H m hsmall) (ambientDeformation_mem_range H m hsmall)

theorem deformation_toOrthogonal (q : I × (I × X)) :
    specialOrthogonal (deformation H m hsmall q) = ambientDeformation H m hsmall q :=
  specialOrthogonal_liftOrthogonalFamily _ _ q

def ending : C(I × X, SpecialSpace N) :=
  (deformation H m hsmall).comp ⟨fun p ↦ (1, p), continuous_const.prodMk continuous_id⟩

theorem deformation_zero (p : I × X) : deformation H m hsmall (0, p) = H p := by
  apply specialOrthogonal_injective
  rw [deformation_toOrthogonal]
  exact NoExoticSixSphere.OrthogonalExponential.BrokenPaths.deformation_zero _ _ _ _ _ p

def homotopyRel_exponential (S : Set X)
    (hS : ∀ x ∈ S, ∃ K : SkewOperators (2 * Fintype.card N),
      (∀ u : I, orthogonalFamily H (u, x) = orthogonalFamily H (0, x) *
        NoExoticSixSphere.OrthogonalExponential.exp ((u : ℝ) • K)) ∧
      ∀ i < m + 1, ∀ u ∈ Icc (clampedTime m i) (clampedTime m (i + 1)),
        ((u : ℝ) - (clampedTime m i : ℝ)) • K ∈
          (NoExoticSixSphere.OrthogonalExponential.logarithmChart
            (2 * Fintype.card N)).target) :
    H.HomotopyRel (ending H m hsmall) {p | p.1 = 0 ∨ p.1 = 1 ∨ p.2 ∈ S} where
  toContinuousMap := deformation H m hsmall
  map_zero_left := deformation_zero H m hsmall
  map_one_left _ := rfl
  prop' r p hp := by
    apply specialOrthogonal_injective
    change specialOrthogonal (deformation H m hsmall (r, p)) = specialOrthogonal (H p)
    rw [deformation_toOrthogonal]
    exact (NoExoticSixSphere.OrthogonalExponential.BrokenPaths.homotopyRel_exponential
      (orthogonalFamily H) (clampedTime m) (monotone_clampedTime m)
      (groupCondition H m hsmall) (m + 1) S hS).eq_fst r hp

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.BrokenReplacement
