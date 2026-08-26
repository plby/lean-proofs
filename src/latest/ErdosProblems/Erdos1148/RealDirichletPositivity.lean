import ErdosProblems.Erdos1148.RealDirichletLFunction

/-! # Positivity of nonprincipal real Dirichlet values at one -/

namespace Erdos1148.DukeArithmetic

open Filter Topology ArithmeticFunction
open scoped ComplexOrder

theorem realDirichletCharacter_isQuadratic {q : ℕ} (χ : DirichletCharacter ℝ q) :
    χ.IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · have h : |χ a| = 1 := by
      simpa only [Real.norm_eq_abs, ha.unit_spec] using χ.unit_norm_eq_one ha.unit
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exact Or.inl (χ.map_nonunit ha)

lemma zeta_mul_LFunction_eq_LSeries_zetaMul {q : ℕ} [NeZero q]
    (ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s * ψ.LFunction s = LSeries ψ.zetaMul s := by
  rw [DirichletCharacter.zetaMul, ← coe_mul, LSeries_convolution']
  · rw [ψ.LFunction_eq_LSeries hs]
    congr 1
    · simp_rw [← LSeries_zeta_eq_riemannZeta hs, ← natCoe_apply]
    · exact LSeries_congr ψ.apply_eq_toArithmeticFunction_apply s
  · exact LSeriesSummable_zeta_iff.mpr hs
  · exact (LSeriesSummable_congr _ fun h => (ψ.apply_eq_toArithmeticFunction_apply h).symm).mpr
      (ZMod.LSeriesSummable_of_one_lt_re ψ hs)

theorem realDirichletValue_pos_of_one_lt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 1 < s) :
    0 < realDirichletValue χ s := by
  let ψ := complexDirichletCharacter χ
  have hψ : ψ ^ 2 = 1 :=
    ((realDirichletCharacter_isQuadratic χ).comp Complex.ofRealHom).sq_eq_one
  have hsum : Summable (LSeries.term ψ.zetaMul (s : ℂ)) := ψ.LSeriesSummable_zetaMul hs
  have hone : 0 < ψ.zetaMul 1 := by rw [ψ.isMultiplicative_zetaMul.map_one]; exact zero_lt_one
  have hpos : 0 < LSeries ψ.zetaMul (s : ℂ) :=
    hsum.tsum_pos (fun n => LSeries.term_nonneg (ψ.zetaMul_nonneg hψ n) s) 1
      (LSeries.term_pos one_ne_zero hone s)
  rw [← zeta_mul_LFunction_eq_LSeries_zetaMul ψ hs] at hpos
  have hre := (Complex.pos_iff.mp hpos).1
  rw [← realDirichletValue_eq_LFunction_of_one_lt χ hχ hs,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hre
  exact pos_of_mul_pos_right hre (riemannZeta_re_pos_of_one_lt hs).le

theorem realDirichletValue_one_pos {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) : 0 < realDirichletValue χ 1 := by
  have hnonneg : 0 ≤ realDirichletValue χ 1 := by
    apply ge_of_tendsto ((realDirichletValue_continuousAt χ hχ zero_lt_one).tendsto.mono_left
      (show 𝓝[>] (1 : ℝ) ≤ 𝓝 1 from nhdsWithin_le_nhds))
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (realDirichletValue_pos_of_one_lt χ hχ hs).le
  exact lt_of_le_of_ne hnonneg (realDirichletValue_one_ne_zero χ hχ).symm

end Erdos1148.DukeArithmetic
