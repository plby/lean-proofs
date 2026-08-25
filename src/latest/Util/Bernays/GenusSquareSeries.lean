import Util.Bernays.GenusSquareConvolution
import Util.Bernays.SquareCorrectionSeries
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# Analytic continuation of the square of a nontrivial genus series
-/

open scoped Classical

namespace Bernays

theorem genusLocalAF_apply {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ n : ℕ, genusLocalAF hD ψ n =
      if 0 < n ∧ ParityAdmissible (fun p => discriminantCharacter _ hD.ne p = -1) n ∧
        n.Coprime (discriminantLevel (b ^ 2 + 4 * d))
      then ψ (Additive.ofMul (genusValue hD n)) else 0 := by
  letI := quadraticOrderIsDomain hD
  intro ψ n
  by_cases hn : n = 0
  · subst n
    simp only [ArithmeticFunction.map_zero, lt_self_iff_false, false_and, ↓reduceIte]
  · rw [genusLocalAF, ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply,
      genusWeightAF_apply hD ψ n hn]
    change (localParity _ n : ℂ) * (if 0 < n ∧ n.Coprime _ then 1 else 0) * _ = _
    rw [localParity]
    split_ifs <;> simp_all

theorem genusLocalAF_norm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ n : ℕ, ‖genusLocalAF hD ψ n‖ =
      if 0 < n ∧ ParityAdmissible (fun p => discriminantCharacter _ hD.ne p = -1) n ∧
        n.Coprime (discriminantLevel (b ^ 2 + 4 * d)) then 1 else 0 := by
  letI := quadraticOrderIsDomain hD
  intro ψ n
  rw [genusLocalAF_apply]
  split_ifs
  · exact genusChar_norm ψ _
  · exact norm_zero

theorem genusLocalAF_summable {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ s : ℂ, 1 < s.re → LSeriesSummable (genusLocalAF hD ψ) s := by
  letI := quadraticOrderIsDomain hD
  intro ψ s hs
  apply LSeriesSummable_of_le_const_mul_rpow hs
  refine ⟨1, fun n _ => ?_⟩
  rw [genusLocalAF_norm]
  norm_num only [sub_self, Real.rpow_zero, mul_one]
  split_ifs <;> norm_num

theorem genusIdealAF_summable {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ s : ℂ, 1 < s.re → LSeriesSummable (genusIdealAF hD ψ) s := by
  letI := quadraticOrderIsDomain hD
  intro ψ s hs
  rw [genusIdealAF_eq_coeff]
  exact weightedIdealNormCoeff_summable hD (quadraticBadIdeal d b) _ s hs

theorem genusLocalLSeries_square {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ s : ℂ, 1 < s.re →
      LSeries (genusLocalAF hD ψ) s ^ 2 = LSeries (genusIdealAF hD ψ) s *
        LSeries (squareSupportAF (fun p => discriminantCharacter _ hD.ne p = -1)) s := by
  letI := quadraticOrderIsDomain hD
  intro ψ s hs
  rw [pow_two, ← ArithmeticFunction.LSeries_mul' (genusLocalAF_summable hD ψ s hs)
    (genusLocalAF_summable hD ψ s hs), genusLocalAF_square,
    ArithmeticFunction.LSeries_mul' (genusIdealAF_summable hD ψ s hs)
      (squareSupportAF_summable _ (by linarith))]

theorem genusLocalLSeries_square_continuation {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ, ψ ≠ 0 →
      ∃ F : ℂ → ℂ,
        (∀ s : ℂ, (1 / 2 : ℝ) < s.re → DifferentiableAt ℂ F s) ∧
        (∀ s : ℂ, 1 < s.re → F s = LSeries (genusLocalAF hD ψ) s ^ 2) := by
  letI := quadraticOrderIsDomain hD
  intro ψ hψ
  obtain ⟨G, hG, hGeq⟩ := genusIdealLSeries_continuation hD ψ hψ
  let H := squareSupportAF (fun p => discriminantCharacter _ hD.ne p = -1)
  refine ⟨fun s => G s * LSeries H s, ?_, ?_⟩
  · intro s hs
    exact (hG s hs).mul (squareSupportLSeries_differentiableAt _ hs)
  · intro s hs
    dsimp only
    rw [hGeq s hs, genusLocalLSeries_square hD ψ s hs, genusIdealAF_eq_coeff]

end Bernays
