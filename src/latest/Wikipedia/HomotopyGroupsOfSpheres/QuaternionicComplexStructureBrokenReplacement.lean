import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureIntervalReplacement
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBrokenPathIntervals
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicExponentialReplacementFixed
import Wikipedia.NoExoticSixSphere.ClampedUniformPartition
import Wikipedia.NoExoticSixSphere.IntervalPartition

/-!
# Global broken-path replacement preserves complex structures

On every subdivision cell, the whole homotopy equals its actual local
complex-structure replacement. Thus the assembled symplectic construction
lifts to a continuous homotopy in the smaller locus, with the same fixed paths.
-/

noncomputable section

open Set unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures.BrokenReplacement

open NoExoticSixSphere.UniformTimePartition NoExoticSixSphere.GLOrthonormalization

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
variable (H : C(I × X, Space n)) (m : ℕ)
  (hsmall : ∀ i : Fin (m + 1),
    ∀ u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ), ∀ x,
      (H (unitTime m i.castSucc, x), H (u, x)) ∈ ShortLog.domain n)

include hsmall in
theorem clampedCondition :
    ∀ k, ∀ u ∈ Icc (clampedTime m k) (clampedTime m (k + 1)), ∀ x,
      (H (clampedTime m k, x), H (u, x)) ∈ ShortLog.domain n := by
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
    (symplecticFamily H (clampedTime m k, x))⁻¹ * symplecticFamily H (u, x) ∈
      Exponential.compatibleDomain n :=
  ShortLog.relative_mem_compatibleDomain (clampedCondition H m hsmall k u hu x)

def ambientDeformation : C(I × (I × X), symplecticSubgroup n) :=
  Exponential.BrokenPaths.deformation (symplecticFamily H) (clampedTime m)
    (monotone_clampedTime m) (groupCondition H m hsmall) (m + 1)

theorem ambientDeformation_square (q : I × (I × X)) :
    (ambientDeformation H m hsmall q).val.val.val.comp
      (ambientDeformation H m hsmall q).val.val.val =
        -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) := by
  rcases q with ⟨r, v, x⟩
  have hv : (v : ℝ) ∈ Icc (time m 0) (time m (Fin.last (m + 1))) := by
    simpa only [time_zero, time_last] using v.property
  obtain ⟨i, hi⟩ := NoExoticSixSphere.IntervalPartition.exists_mem_adjacent (time m) hv
  have hi' : v ∈ Icc (clampedTime m i.val) (clampedTime m (i.val + 1)) := by
    rw [clampedTime_left, clampedTime_right]
    exact hi
  have he := Exponential.BrokenPaths.deformation_on_interval (symplecticFamily H)
    (clampedTime m) (monotone_clampedTime m) (groupCondition H m hsmall)
    (m + 1) i.val i.isLt r v x hi'
  change (Exponential.BrokenPaths.deformation _ _ _ _ _ (r, (v, x))).val.val.val.comp
    (Exponential.BrokenPaths.deformation _ _ _ _ _ (r, (v, x))).val.val.val = _
  rw [he, ← IntervalReplacement.lifted_toSymplectic H
    (clampedTime m i.val) (clampedTime m (i.val + 1))
    ((monotone_clampedTime m) i.val.le_succ) (clampedCondition H m hsmall i.val)]
  exact (IntervalReplacement.lifted H (clampedTime m i.val) (clampedTime m (i.val + 1))
    ((monotone_clampedTime m) i.val.le_succ) (clampedCondition H m hsmall i.val)
      (r, (v, x))).property

def deformation : C(I × (I × X), Space n) where
  toFun q := ofSymplecticSquare (ambientDeformation H m hsmall q)
    (ambientDeformation_square H m hsmall q)
  continuous_toFun := by
    apply continuous_of_toSymplectic
    exact (ambientDeformation H m hsmall).continuous.congr
      (fun q ↦ (toSymplectic_ofSymplecticSquare _ _).symm)

theorem deformation_toSymplectic (q : I × (I × X)) :
    toSymplectic (deformation H m hsmall q) = ambientDeformation H m hsmall q :=
  toSymplectic_ofSymplecticSquare _ _

def ending : C(I × X, Space n) :=
  (deformation H m hsmall).comp ⟨fun p ↦ (1, p), continuous_const.prodMk continuous_id⟩

theorem deformation_zero (p : I × X) : deformation H m hsmall (0, p) = H p := by
  apply toSymplectic_injective
  rw [deformation_toSymplectic]
  exact Exponential.BrokenPaths.deformation_zero _ _ _ _ _ p

def homotopyRel_exponential (S : Set X)
    (hS : ∀ x ∈ S, ∃ K : SkewSpace n,
      (∀ u : I, symplecticFamily H (u, x) = symplecticFamily H (0, x) *
        Exponential.exp ((u : ℝ) • K)) ∧
      ∀ i < m + 1, ∀ u ∈ Icc (clampedTime m i) (clampedTime m (i + 1)),
        ((u : ℝ) - (clampedTime m i : ℝ)) • K ∈ Exponential.compatibleTarget n) :
    H.HomotopyRel (ending H m hsmall) {p | p.1 = 0 ∨ p.1 = 1 ∨ p.2 ∈ S} where
  toContinuousMap := deformation H m hsmall
  map_zero_left := deformation_zero H m hsmall
  map_one_left _ := rfl
  prop' r p hp := by
    apply toSymplectic_injective
    change toSymplectic (deformation H m hsmall (r, p)) = toSymplectic (H p)
    rw [deformation_toSymplectic]
    exact (Exponential.BrokenPaths.homotopyRel_exponential (symplecticFamily H)
      (clampedTime m) (monotone_clampedTime m) (groupCondition H m hsmall)
      (m + 1) S hS).eq_fst r hp

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures.BrokenReplacement
