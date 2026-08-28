import Wikipedia.NoExoticSixSphere.SphereCapComparisonDiffeomorphism
import Wikipedia.NoExoticSixSphere.SphereSumSourceCover
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# A whole-sphere homeomorphism extending the northern polynomial fold

Above height one half, use the actual polynomial fold. Below that latitude,
use the existing axial dilation of scale one third. The two maps agree on
the boundary and map their pieces bijectively onto the two corresponding
closed caps. The resulting continuous bijection is a homeomorphism of the
original sphere. Global differentiability of the pasted map is not asserted.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

theorem fold_head (x : Sphere 3) :
    (SphereFold.fold pinchPole x).val 0 = 2 * (x.val 0) ^ 2 - 1 := by
  rw [← pinchPole_height, SphereFold.height_fold, pinchPole_height]

theorem axisDilation_head {c : ℝ} (hc : 0 < c) (x : Sphere 3) :
    (axisDilation c x).val 0 = axisNumerator c (x.val 0) / axisDenominator c (x.val 0) := by
  rw [axisDilation_val hc]
  change (axisDenominator c (x.val 0))⁻¹ * axisNumerator c (x.val 0) = _
  ring

theorem thirdAxis_head_le (x : Sphere 3) :
    (axisDilation (1 / 3) x).val 0 ≤ -(1 / 2 : ℝ) ↔ x.val 0 ≤ 1 / 2 := by
  rw [axisDilation_head (by norm_num), div_le_iff₀ (axisDenominator_pos (by norm_num) x)]
  dsimp [axisNumerator, axisDenominator]
  constructor <;> intro h <;> linarith

theorem thirdAxis_head_lt (x : Sphere 3) :
    (axisDilation (1 / 3) x).val 0 < -(1 / 2 : ℝ) ↔ x.val 0 < 1 / 2 := by
  rw [axisDilation_head (by norm_num), div_lt_iff₀ (axisDenominator_pos (by norm_num) x)]
  dsimp [axisNumerator, axisDenominator]
  constructor <;> intro h <;> linarith

theorem thirdAxis_eq_fold_boundary (x : Sphere 3) (hx : x.val 0 = 1 / 2) :
    axisDilation (1 / 3) x = SphereFold.fold pinchPole x := by
  apply Subtype.ext
  rw [axisDilation_val (by norm_num), SphereFold.fold_val, pinchPole_height, hx]
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change (axisDenominator (1 / 3) (x.val 0))⁻¹ *
      axisNumerator (1 / 3) (x.val 0) = (2 * (1 / 2)) * x.val 0 - 1
    norm_num [axisDenominator, axisNumerator, hx]
  · change (axisDenominator (1 / 3) (x.val 0))⁻¹ *
      ((2 * (1 / 3)) * x.val j.succ) = (2 * (1 / 2)) * x.val j.succ - 0
    norm_num [axisDenominator, hx]
    ring

def foldCapExtension (x : Sphere 3) : Sphere 3 :=
  if (1 / 2 : ℝ) ≤ x.val 0 then SphereFold.fold pinchPole x else axisDilation (1 / 3) x

theorem foldCapExtension_upper (x : Sphere 3) (hx : (1 / 2 : ℝ) ≤ x.val 0) :
    foldCapExtension x = SphereFold.fold pinchPole x := if_pos hx

theorem foldCapExtension_lower (x : Sphere 3) (hx : x.val 0 ≤ (1 / 2 : ℝ)) :
    foldCapExtension x = axisDilation (1 / 3) x := by
  by_cases hn : (1 / 2 : ℝ) ≤ x.val 0
  · rw [foldCapExtension_upper x hn]
    exact (thirdAxis_eq_fold_boundary x (le_antisymm hx hn)).symm
  · exact if_neg hn

theorem continuous_foldCapExtension : Continuous foldCapExtension := by
  let N : Set (Sphere 3) := {x | (1 / 2 : ℝ) ≤ x.val 0}
  let S : Set (Sphere 3) := {x | x.val 0 ≤ (1 / 2 : ℝ)}
  have hN : IsClosed N := isClosed_le continuous_const continuous_sourceHead
  have hS : IsClosed S := isClosed_le continuous_sourceHead continuous_const
  have hcover : N ∪ S = univ := by
    ext x
    exact iff_true_intro (le_total (1 / 2 : ℝ) (x.val 0))
  have hn : ContinuousOn foldCapExtension N :=
    (SphereFold.continuous_fold pinchPole).continuousOn.congr
      (fun x hx ↦ foldCapExtension_upper x hx)
  have hs : ContinuousOn foldCapExtension S :=
    (contMDiff_axisDilation (by norm_num : (0 : ℝ) < 1 / 3)).continuous.continuousOn.congr
      (fun x hx ↦ foldCapExtension_lower x hx)
  exact continuousOn_univ.mp (hcover ▸ hn.union_of_isClosed hs hN hS)

theorem foldCapExtension_head_side (x : Sphere 3) :
    -(1 / 2 : ℝ) ≤ (foldCapExtension x).val 0 ↔ (1 / 2 : ℝ) ≤ x.val 0 := by
  by_cases hx : (1 / 2 : ℝ) ≤ x.val 0
  · rw [foldCapExtension_upper x hx, fold_head]
    exact iff_of_true (by nlinarith) hx
  · rw [foldCapExtension_lower x (le_of_not_ge hx)]
    have ht := (thirdAxis_head_lt x).mpr (lt_of_not_ge hx)
    exact iff_of_false (not_le_of_gt ht) hx

theorem foldCapExtension_injective : Injective foldCapExtension := by
  intro x y h
  have hs : ((1 / 2 : ℝ) ≤ x.val 0) ↔ ((1 / 2 : ℝ) ≤ y.val 0) := by
    rw [← foldCapExtension_head_side x, ← foldCapExtension_head_side y, h]
  by_cases hx : (1 / 2 : ℝ) ≤ x.val 0
  · have hy := hs.mp hx
    rw [foldCapExtension_upper x hx, foldCapExtension_upper y hy] at h
    have hxp : 0 < SphereFold.height pinchPole x := by rw [pinchPole_height]; linarith
    have hyp : 0 < SphereFold.height pinchPole y := by rw [pinchPole_height]; linarith
    have he := congrArg (SphereFold.northInverse pinchPole) h
    rwa [SphereFold.northInverse_fold pinchPole x hxp,
      SphereFold.northInverse_fold pinchPole y hyp] at he
  · have hy : ¬ (1 / 2 : ℝ) ≤ y.val 0 := fun hy ↦ hx (hs.mpr hy)
    rw [foldCapExtension_lower x (le_of_not_ge hx),
      foldCapExtension_lower y (le_of_not_ge hy)] at h
    exact (axisDilationDiffeomorph (1 / 3) (by norm_num)).injective h

theorem foldCapExtension_surjective : Surjective foldCapExtension := by
  intro y
  by_cases hy : -(1 / 2 : ℝ) ≤ y.val 0
  · have hne : y ≠ antipode pinchPole := by
      intro he
      have hz : (antipode pinchPole).val 0 = -1 := by simp [antipode, pinchPole, spherePole]
      rw [he, hz] at hy
      linarith
    let x := SphereFold.northInverse pinchPole y
    have he : SphereFold.fold pinchPole x = y := SphereFold.fold_northInverse pinchPole y hne
    have hxpos : 0 < x.val 0 := by
      rw [← pinchPole_height]
      exact SphereFold.height_northInverse_pos pinchPole y hne
    have hh : 2 * (x.val 0) ^ 2 - 1 = y.val 0 := by rw [← fold_head, he]
    have hx : (1 / 2 : ℝ) ≤ x.val 0 := by nlinarith
    exact ⟨x, (foldCapExtension_upper x hx).trans he⟩
  · let D := axisDilationDiffeomorph (1 / 3) (by norm_num)
    let x := D.symm y
    have he : axisDilation (1 / 3) x = y := D.apply_symm_apply y
    have hx : x.val 0 < (1 / 2 : ℝ) := by
      apply (thirdAxis_head_lt x).mp
      rw [he]
      exact lt_of_not_ge hy
    exact ⟨x, (foldCapExtension_lower x hx.le).trans he⟩

def foldCapHomeomorph : Sphere 3 ≃ₜ Sphere 3 :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective foldCapExtension
      ⟨foldCapExtension_injective, foldCapExtension_surjective⟩) continuous_foldCapExtension

theorem foldCapHomeomorph_apply (x : Sphere 3) :
    foldCapHomeomorph x = foldCapExtension x := rfl

end NoExoticSixSphere.SphereSumNeck
