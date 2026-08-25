import ErdosProblems.Erdos237.SupportedWeights
import ErdosProblems.Erdos237.FiniteBoxWeights
import BoundedGaps.Maynard.ConcreteFractionalTupleBoxSimplex
import BoundedGaps.Maynard.ConcreteFractionalRectangle

/-!
# Linear box masses on the true squarefree tuple support

The collision estimate also applies to bounded weights without squaring.
This is the form used for the positive, extra-coordinate lower bound on S2.
-/

namespace Erdos237

open Finset Filter BoundedGaps.Maynard
open scoped BigOperators

theorem tendsto_normalized_linear_collision {H : Finset ℕ} {alpha B : ℝ}
    (halpha : 0 < alpha) (_hB : 0 ≤ B) (f : ℕ → (H → ℕ) → ℝ)
    (hbound : ∀ N r, |f N r| ≤ B) :
    Tendsto (fun N : ℕ =>
      (∑ u ∈ preSievedSimplexCollisionSupport H (engelsmaMaynardRadius alpha N)
        (engelsmaMaynardModulus N), f N u * reciprocalTotientTupleWeight H u) /
          sieveCoordinateScale alpha N ^ Fintype.card H) atTop (nhds 0) := by
  have hlim := (tendsto_normalized_collision_mass (H := H) halpha).const_mul B
  simp only [mul_zero] at hlim
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_sieveCoordinateScale_pos halpha] with N hA
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hA _), ← mul_div_assoc]
  apply div_le_div_of_nonneg_right ?_ (pow_nonneg hA.le _)
  calc
    _ ≤ _ := abs_sum_le_sum_abs _ _
    _ ≤ ∑ u ∈ preSievedSimplexCollisionSupport H (engelsmaMaynardRadius alpha N)
        (engelsmaMaynardModulus N), B * reciprocalTotientTupleWeight H u := by
      apply sum_le_sum
      intro u _
      have hw : 0 ≤ reciprocalTotientTupleWeight H u := by
        unfold reciprocalTotientTupleWeight
        positivity
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_right (hbound N u) hw
    _ = _ := (mul_sum _ _ _).symm

theorem tendsto_restricted_sum_of_independent {H : Finset ℕ} {alpha B I : ℝ}
    (halpha : 0 < alpha) (hB : 0 ≤ B) (f : ℕ → (H → ℕ) → ℝ)
    (hbound : ∀ N r, |f N r| ≤ B)
    (hind : Tendsto (fun N : ℕ =>
      (∑ u ∈ preSievedSimplexTupleSupport H (engelsmaMaynardRadius alpha N)
        (engelsmaMaynardModulus N), f N u * reciprocalTotientTupleWeight H u) /
          sieveCoordinateScale alpha N ^ Fintype.card H) atTop (nhds I)) :
    Tendsto (fun N : ℕ =>
      (∑ u ∈ maynardDivisorTupleSupport H (engelsmaMaynardRadius alpha N)
        (engelsmaMaynardModulus N), f N u * reciprocalTotientTupleWeight H u) /
          sieveCoordinateScale alpha N ^ Fintype.card H) atTop (nhds I) := by
  have hlim := hind.sub (tendsto_normalized_linear_collision halpha hB f hbound)
  simp only [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [] with N
  rw [sum_preSievedSimplex_eq_maynard_add_collision]
  ring

theorem tendsto_supported_finite_box_mass {ι : Type*} {H : Finset ℕ} {alpha : ℝ}
    (halpha : 0 < alpha) (I : Finset ι) (coeff : ι → ℝ) (beta gamma : ι → H → ℝ)
    (hbeta : ∀ i ∈ I, ∀ h, beta i h ∈ Set.Icc (0 : ℝ) 1)
    (hgamma : ∀ i ∈ I, ∀ h, gamma i h ∈ Set.Icc (0 : ℝ) 1)
    (horder : ∀ i ∈ I, ∀ h, beta i h ≤ gamma i h)
    (hsum : ∀ i ∈ I, (∑ h, gamma i h) < 1) :
    Tendsto (fun N : ℕ =>
      (∑ u ∈ maynardDivisorTupleSupport H (engelsmaMaynardRadius alpha N)
        (engelsmaMaynardModulus N),
        finiteBoxWeight I (fun i => engelsmaFractionalTupleShell H alpha (beta i) (gamma i) N)
          coeff u * reciprocalTotientTupleWeight H u) /
          sieveCoordinateScale alpha N ^ Fintype.card H)
      atTop (nhds (∑ i ∈ I, coeff i * ∏ h, (gamma i h - beta i h))) := by
  apply tendsto_restricted_sum_of_independent halpha (sum_nonneg fun _ _ => abs_nonneg _)
    _ (fun N u => abs_finiteBoxWeight_le I _ coeff u)
  have hlim := tendsto_finite_linear_combination_normalizedEngelsmaFractionalTupleShellMass
    halpha I coeff beta gamma hbeta hgamma horder
  have hsubs : ∀ᶠ N : ℕ in atTop, ∀ i ∈ I,
      engelsmaFractionalTupleShell H alpha (beta i) (gamma i) N ⊆
        preSievedSimplexTupleSupport H (engelsmaMaynardRadius alpha N)
          (engelsmaMaynardModulus N) := by
    apply I.eventually_all.mpr
    intro i hi
    filter_upwards [eventually_engelsmaFractionalTupleBox_subset_preSievedSimplexTupleSupport
      halpha (gamma i) (fun h => (hgamma i hi h).1) (hsum i hi)] with N hN
    intro u hu
    apply hN
    rw [engelsmaFractionalTupleShell, squarefreeCoprimeTupleShell, Fintype.mem_piFinset] at hu
    rw [engelsmaFractionalTupleBox, squarefreeCoprimeTupleBox, Fintype.mem_piFinset]
    intro h
    exact (mem_sdiff.mp (hu h)).1
  apply hlim.congr'
  filter_upwards [hsubs] with N hsub
  rw [sum_finiteBoxWeight_mul I _ _ coeff _ hsub, sum_div]
  apply sum_congr rfl
  intro i _
  simp only [normalizedEngelsmaFractionalTupleShellMass, engelsmaFractionalTupleShellMass,
    sieveCoordinateScale]
  ring

end Erdos237
