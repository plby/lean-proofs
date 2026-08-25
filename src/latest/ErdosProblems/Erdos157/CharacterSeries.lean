import ErdosProblems.Erdos157.PolynomialCharacters
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The analytic monic character series

The series over all monic polynomials converges absolutely in the elementary
disk `card K * norm z < 1` and agrees there with the finite character polynomial.
-/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] [Fintype K]

/-- Monic polynomials, with their degree retained as an explicit summation index. -/
abbrev AllMonic (K : Type*) [Field K] := Σ d : ℕ, MonicDegreeEq K d

/-- A summand of the character generating series. -/
noncomputable def monicTerm (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ)
    (z : ℂ) (f : AllMonic K) : ℂ := χ (AdjoinRoot.mk g f.2.1) * z ^ f.1

theorem summable_norm_monicTerm (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (z : ℂ)
    (hz : (Fintype.card K : ℝ) * ‖z‖ < 1) :
    Summable (fun f : AllMonic K => ‖monicTerm g χ z f‖) := by
  let : Finite (AdjoinRoot g) :=
    Finite.of_injective (AdjoinRoot.powerBasisAux' hg).equivFun
      (AdjoinRoot.powerBasisAux' hg).equivFun.injective
  apply (summable_sigma_of_nonneg (fun f => norm_nonneg _)).mpr
  refine ⟨fun d => (hasSum_fintype _).summable, ?_⟩
  apply Summable.of_nonneg_of_le (fun d => tsum_nonneg (fun _ => norm_nonneg _))
    (f := fun d : ℕ => ((Fintype.card K : ℝ) * ‖z‖) ^ d)
  · intro d
    rw [tsum_fintype]
    calc
      _ ≤ ∑ _f : MonicDegreeEq K d, ‖z‖ ^ d := by
        apply Finset.sum_le_sum
        intro f _
        simp only [monicTerm, norm_mul, norm_pow]
        exact mul_le_of_le_one_left (by positivity) (character_norm_le_one χ _)
      _ = _ := by simp [card_monic, mul_pow]
  · exact summable_geometric_of_lt_one (by positivity) hz

theorem hasSum_coefficient (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) (z : ℂ) :
    HasSum (fun d => coefficient g χ d * z ^ d) ((lPolynomial g χ).eval z) := by
  have hfin : ∀ d ∉ Finset.range g.natDegree, coefficient g χ d * z ^ d = 0 := by
    intro d hd
    rw [coefficient_eq_zero g hg χ hχ d (by simpa using hd), zero_mul]
  have hs : HasSum (fun d => coefficient g χ d * z ^ d)
      (∑ d ∈ Finset.range g.natDegree, coefficient g χ d * z ^ d) :=
    hasSum_sum_of_ne_finset_zero hfin
  simpa only [lPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial] using hs

/-- The complete absolutely convergent character series equals its finite polynomial. -/
theorem tsum_monicTerm_eq_lPolynomial (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) (z : ℂ)
    (hz : (Fintype.card K : ℝ) * ‖z‖ < 1) :
    (∑' f : AllMonic K, monicTerm g χ z f) = (lPolynomial g χ).eval z := by
  have hs := (summable_norm_monicTerm g hg χ z hz).of_norm
  rw [hs.tsum_sigma]
  have hinner : ∀ d, (∑' f : MonicDegreeEq K d, monicTerm g χ z ⟨d, f⟩) =
      coefficient g χ d * z ^ d := by
    intro d
    rw [tsum_fintype]
    simp only [monicTerm, coefficient, Finset.sum_mul]
  simp_rw [hinner]
  exact (hasSum_coefficient g hg χ hχ z).tsum_eq

end Erdos157.Elementary.PolynomialCharacters
