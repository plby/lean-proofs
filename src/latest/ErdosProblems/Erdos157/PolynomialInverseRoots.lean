import ErdosProblems.Erdos157.CharacterNonvanishing
import ErdosProblems.Erdos157.CharacterRootBound
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! Indexed inverse roots and their logarithmic-derivative formula. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial
open scoped BigOperators

/-- Index roots with multiplicity, using the finite list supplied by the multiset. -/
noncomputable def rootAt (p : ℂ[X]) : Fin p.roots.toList.length → ℂ := p.roots.toList.get

noncomputable def inverseRootAt (p : ℂ[X]) (i : Fin p.roots.toList.length) : ℂ := (rootAt p i)⁻¹

theorem rootAt_mem (p : ℂ[X]) (i : Fin p.roots.toList.length) : rootAt p i ∈ p.roots := by
  exact Multiset.mem_toList.mp (List.get_mem _ _)

theorem sum_rootAt (p : ℂ[X]) (f : ℂ → ℂ) :
    (∑ i, f (rootAt p i)) = (p.roots.map f).sum := by
  rw [← List.sum_ofFn]
  have hlist : List.ofFn (fun i => f (rootAt p i)) = p.roots.toList.map f := by
    change List.ofFn (f ∘ p.roots.toList.get) = p.roots.toList.map f
    rw [← List.map_ofFn, List.ofFn_get]
  rw [hlist]
  simp

theorem rootAt_ne_zero (p : ℂ[X]) (hp : p.coeff 0 = 1)
    (i : Fin p.roots.toList.length) : rootAt p i ≠ 0 := by
  have hpne : p ≠ 0 := by intro h; simp [h] at hp
  have hr := (Polynomial.mem_roots hpne).mp (rootAt_mem p i)
  intro hz
  have heval : p.eval (rootAt p i) = 0 := hr
  rw [hz] at heval
  have hzero : p.eval 0 = p.coeff 0 := (Polynomial.coeff_zero_eq_eval_zero p).symm
  rw [hzero, hp] at heval
  exact one_ne_zero heval

theorem contribution_inverse_mul (a z : ℂ) (ha : a ≠ 0) :
    ElementaryCharacterBound.contribution (a⁻¹ * z) = z / (z - a) := by
  by_cases hza : z = a
  · simp [hza, ElementaryCharacterBound.contribution, ha]
  have hden : 1 - a⁻¹ * z ≠ 0 := by
    intro h
    have heq : a = z := by
      have hm := congrArg (fun w : ℂ => a * w) h
      apply sub_eq_zero.mp
      simpa [mul_sub, mul_assoc, ha] using hm
    exact hza heq.symm
  unfold ElementaryCharacterBound.contribution
  apply (div_eq_div_iff hden (sub_ne_zero.mpr hza)).mpr
  field_simp
  ring

/-- The polynomial logarithmic derivative in inverse-root coordinates. -/
theorem inverseRoots_logDerivative (p : ℂ[X]) (hp : p.coeff 0 = 1)
    (z : ℂ) (hz : p.eval z ≠ 0) :
    z * (p.derivative.eval z / p.eval z) =
      ∑ i, ElementaryCharacterBound.contribution (inverseRootAt p i * z) := by
  rw [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hz, ← sum_rootAt]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inverseRootAt, contribution_inverse_mul _ _ (rootAt_ne_zero p hp i)]
  ring

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

theorem lPolynomial_inverseRoot_norm_le (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1)
    (i : Fin (lPolynomial g χ).roots.toList.length) :
    ‖inverseRootAt (lPolynomial g χ) i‖ ≤ Fintype.card K := by
  apply norm_inverseRoot_le_card g hg χ hχ
  simp only [inverseRootAt, inv_inv]
  apply (Polynomial.mem_roots ?_).mp (rootAt_mem _ i)
  intro heq
  have hconstant := lPolynomial_constantCoeff g hg χ hχ
  simp [heq] at hconstant

omit [DecidableEq K] in
theorem lPolynomial_root_count_lt (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) :
    (lPolynomial g χ).roots.toList.length < g.natDegree := by
  have hpne : lPolynomial g χ ≠ 0 := by
    intro h
    have hc := lPolynomial_constantCoeff g hg χ hχ
    simp [h] at hc
  have hdeg := (Polynomial.natDegree_lt_iff_degree_lt hpne).mpr (lPolynomial_degree_lt g χ)
  simpa only [Multiset.length_toList] using (Polynomial.card_roots' (lPolynomial g χ)).trans_lt hdeg

end Erdos157.Elementary.PolynomialCharacters
