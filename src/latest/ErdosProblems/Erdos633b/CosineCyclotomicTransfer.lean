import ErdosProblems.Erdos633b.RightTileQuartics
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.NumberTheory.Niven

/-! Coprime conjugacy of twice a rational-angle cosine, proved by
composition with a polynomial at primitive complex roots of unity. -/

namespace Erdos633b
open Polynomial

theorem aeval_complex_ofReal (g : ℚ[X]) (x : ℝ) :
    aeval (x : ℂ) g = (aeval x g : ℝ) :=
  aeval_algHom_apply (IsScalarTower.toAlgHom ℚ ℝ ℂ) x g

theorem primitive_root_polynomial_transfer (M : ℕ) (hM : 0 < M) (z z' : ℂ)
    (hz : IsPrimitiveRoot z M) (hz' : IsPrimitiveRoot z' M)
    (g : ℚ[X]) (hg : aeval z g = 0) : aeval z' g = 0 := by
  have hd : cyclotomic M ℚ ∣ g := by
    rw [cyclotomic_eq_minpoly_rat hz hM]
    exact minpoly.dvd ℚ z hg
  obtain ⟨q, hq⟩ := hd
  rw [hq, map_mul, cyclotomic_eq_minpoly_rat hz' hM, minpoly.aeval, zero_mul]

theorem primitive_pi_root (N k : ℕ) (hN : 0 < N) (hk : k.Coprime (2 * N)) :
    IsPrimitiveRoot (Complex.exp (((k : ℝ) * (Real.pi / N) : ℝ) * Complex.I)) (2 * N) := by
  convert Complex.isPrimitiveRoot_exp_of_coprime k (2 * N) (by omega) hk using 1
  congr 1
  push_cast
  ring

theorem root_sum_pow_pred (M : ℕ) (hM : 0 < M) (x : ℝ)
    (hz : Complex.exp ((x : ℂ) * Complex.I) ^ M = 1) :
    aeval (Complex.exp ((x : ℂ) * Complex.I)) (X + X ^ (M - 1) : ℚ[X]) =
      ((2 * Real.cos x : ℝ) : ℂ) := by
  let z := Complex.exp ((x : ℂ) * Complex.I)
  have hzne : z ≠ 0 := Complex.exp_ne_zero _
  have hp : z ^ (M - 1) = z⁻¹ := by
    apply (mul_left_cancel₀ hzne)
    rw [mul_inv_cancel₀ hzne, ← pow_succ', Nat.sub_add_cancel hM, hz]
  simp only [map_add, map_pow, aeval_X]
  change z + z ^ (M - 1) = _
  rw [hp]
  dsimp only [z]
  rw [← Complex.exp_neg]
  have hn : -((x : ℂ) * Complex.I) = (-x : ℂ) * Complex.I := by ring
  rw [hn, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

theorem cosine_pi_polynomial_transfer (N k : ℕ) (hN : 0 < N) (hk : k.Coprime (2 * N))
    (g : ℚ[X]) (hg : aeval (2 * Real.cos (Real.pi / N)) g = 0) :
    aeval (2 * Real.cos (k * (Real.pi / N))) g = 0 := by
  let L : ℚ[X] := X + X ^ (2 * N - 1)
  let z : ℂ := Complex.exp (((Real.pi / N : ℝ) : ℂ) * Complex.I)
  let z' : ℂ := Complex.exp ((((k : ℝ) * (Real.pi / N) : ℝ) : ℂ) * Complex.I)
  have hz : IsPrimitiveRoot z (2 * N) := by
    simpa only [Nat.cast_one, one_mul] using primitive_pi_root N 1 hN (by simp)
  have hz' : IsPrimitiveRoot z' (2 * N) := primitive_pi_root N k hN hk
  have hL : aeval z L = ((2 * Real.cos (Real.pi / N) : ℝ) : ℂ) :=
    root_sum_pow_pred (2 * N) (by omega) _ hz.pow_eq_one
  have hL' : aeval z' L = ((2 * Real.cos (k * (Real.pi / N)) : ℝ) : ℂ) :=
    root_sum_pow_pred (2 * N) (by omega) _ hz'.pow_eq_one
  have hgz : aeval z (g.comp L) = 0 := by
    rw [aeval_comp, hL, aeval_complex_ofReal, hg, Complex.ofReal_zero]
  have hgz' := primitive_root_polynomial_transfer (2 * N) (by omega) z z' hz hz' (g.comp L) hgz
  rw [aeval_comp, hL', aeval_complex_ofReal, Complex.ofReal_eq_zero] at hgz'
  exact hgz'

theorem cosine_pi_integral (N : ℕ) : IsIntegral ℚ (2 * Real.cos (Real.pi / N)) := by
  have h := Real.isIntegral_two_mul_cos_rat_mul_pi ((N : ℚ)⁻¹)
  have he : (((N : ℚ)⁻¹ : ℚ) : ℝ) * Real.pi = Real.pi / N := by push_cast; ring
  rw [he] at h
  exact h.tower_top

theorem cosine_pi_common_minpoly (N k : ℕ) (hN : 0 < N) (hk : k.Coprime (2 * N)) :
    ∃ f : ℚ[X], Irreducible f ∧ f.Monic ∧
      aeval (2 * Real.cos (Real.pi / N)) f = 0 ∧
      aeval (2 * Real.cos (k * (Real.pi / N))) f = 0 := by
  refine ⟨minpoly ℚ (2 * Real.cos (Real.pi / N)),
    minpoly.irreducible (cosine_pi_integral N), minpoly.monic (cosine_pi_integral N),
    minpoly.aeval _ _, ?_⟩
  exact cosine_pi_polynomial_transfer N k hN hk _ (minpoly.aeval _ _)

end Erdos633b
