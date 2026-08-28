import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalClosed
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalBoxes
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeLocalIntegralCutoff

/-!
# A coordinate correction preserves the equations already solved

The nonzero locus of the new cutoff lies in the original larger disc.
The remaining closedness equation is consequently used only at points
where it is known.  Vanishing on the previous open box gives vanishing
of the required derivative there by genuine germ locality.
-/

noncomputable section

open Complex Set Metric Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local

/-- Localize one coefficient only in the coordinate to be integrated. -/
def localizedCoefficient (i : Fin 3) (χ : ℂ → ℂ) (f : Coordinates → ℂ)
    (q : Coordinates) : ℂ := χ (q i) * f q

/-- The actual one-coordinate Cauchy–Green correction. -/
def coordinateCorrection (i : Fin 3) (χ : ℂ → ℂ) (f : Coordinates → ℂ) :
    Coordinates → ℂ := coordinateCauchy i (localizedCoefficient i χ f)

theorem contDiff_localizedCoefficient (i : Fin 3) {χ : ℂ → ℂ}
    {f : Coordinates → ℂ} (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (localizedCoefficient i χ f) :=
  (contDiff_coordinateScalar i hχ).mul hf

theorem localizedCoefficient_eq_zero (i : Fin 3) (χ : ℂ → ℂ)
    (f : Coordinates → ℂ) (q : Coordinates) (hq : q i ∉ tsupport χ) :
    localizedCoefficient i χ f q = 0 := by
  rw [localizedCoefficient, image_eq_zero_of_notMem_tsupport hq, zero_mul]

theorem contDiff_coordinateCorrection (i : Fin 3) {χ : ℂ → ℂ}
    {f : Coordinates → ℂ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (coordinateCorrection i χ f) :=
  contDiff_coordinateCauchy i (contDiff_localizedCoefficient i hχ hf) hcχ
    (localizedCoefficient_eq_zero i χ f)

/-- The correction solves its own equation wherever the cutoff is one. -/
theorem coordinateDbar_coordinateCorrection_self (i : Fin 3) {χ : ℂ → ℂ}
    {f : Coordinates → ℂ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hf : ContDiff ℝ ∞ f) (q : Coordinates) :
    coordinateDbar i (coordinateCorrection i χ f) q = χ (q i) * f q :=
  coordinateDbar_coordinateCauchy i (contDiff_localizedCoefficient i hχ hf) hcχ
    (localizedCoefficient_eq_zero i χ f) q

/-- Previously solved equations are preserved by the next correction on
the smaller open box. -/
theorem coordinateCorrection_preserves_zero
    {S : Finset (Fin 3)} {j : Fin 3} (hj : j ∉ S)
    {x : Coordinates} {r R : ℝ} (hrR : r ≤ R) {χ : ℂ → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hχsupport : ∀ z, χ z ≠ 0 → z ∈ ball (x j) R)
    {f : Fin 3 → Coordinates → ℂ} (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hclosed : IsClosedOn f (polydisc ∅ x r R))
    (hzero : ∀ i ∈ S, ∀ q ∈ polydisc S x r R, f i q = 0)
    {q : Coordinates} (hq : q ∈ polydisc (insert j S) x r R)
    {i : Fin 3} (hi : i ∈ S) :
    coordinateDbar i (coordinateCorrection j χ (f j)) q = 0 := by
  have hij : i ≠ j := by
    intro he
    exact hj (he ▸ hi)
  apply coordinateDbar_coordinateCauchy_eq_zero j i hij
    (contDiff_localizedCoefficient j hχ (hf j)) hcχ
    (localizedCoefficient_eq_zero j χ (f j)) q
  intro z
  let y := Function.update q j z
  change coordinateDbar i (fun p => χ (p j) * f j p) y = 0
  rw [coordinateDbar_mul i
      ((contDiff_coordinateScalar j hχ).differentiable (by simp) y)
      ((hf j).differentiable (by simp) y),
    coordinateDbar_coordinateScalar_of_ne j i hij (hχ.differentiable (by simp) (y j)),
    mul_zero, add_zero]
  by_cases hyzero : χ (y j) = 0
  · rw [hyzero, zero_mul]
  · have hy : y ∈ polydisc S x r R := by
      apply update_mem_polydisc hj hq
      have hz := hχsupport (y j) hyzero
      simpa only [y, Function.update_self] using hz
    rw [hclosed y (polydisc_subset_empty S x hrR hy) i j,
      coordinateDbar_zero_of_eqOn j (isOpen_polydisc S x r R) (hzero i hi) hy,
      mul_zero]

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local
