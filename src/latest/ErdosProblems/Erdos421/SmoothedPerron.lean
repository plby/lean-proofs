import ErdosProblems.Erdos421.PerronInterchange
import ErdosProblems.Erdos421.TriangularMellin

/-! # A proved smoothed Perron formula for absolutely convergent Dirichlet series -/

namespace Erdos421

open Complex MeasureTheory

theorem perronSummand_eq_mellin (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x)
    (σ t : ℝ) {n : ℕ} (hn : n ≠ 0) (y : ℝ) :
    perronSummand a x σ t n y = LSeries.term a (t * I) n *
      (((n : ℝ) / x : ℝ) : ℂ) ^ (-((σ : ℂ) + y * I)) *
        perronKernel ((σ : ℂ) + y * I) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hxC : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hp : (x : ℂ) ^ ((σ : ℂ) + y * I) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hxC)
  have he : (σ : ℂ) + (t + y : ℝ) * I = ((σ : ℂ) + y * I) + t * I := by
    push_cast
    ring
  rw [perronSummand, he, LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
    cpow_add _ _ hnC, ofReal_div, div_cpow_ofReal_nonneg hnR.le hx.le,
    ofReal_natCast, cpow_neg, cpow_neg]
  field_simp

theorem perron_integral_term (a : ℕ → ℂ) {x σ : ℝ} (hx : 0 < x) (hσ : 1 / 2 ≤ σ)
    (t : ℝ) (n : ℕ) :
    (1 / (2 * Real.pi) : ℝ) • (∫ y : ℝ, perronSummand a x σ t n y) =
      LSeries.term a (t * I) n * triangularMellinWeight ((n : ℝ) / x) := by
  by_cases hn : n = 0
  · subst n
    simp [perronSummand]
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hpoint : ∀ y : ℝ, perronSummand a x σ t n y = LSeries.term a (t * I) n *
      ((((n : ℝ) / x : ℝ) : ℂ) ^ (-((σ : ℂ) + y * I)) *
        perronKernel ((σ : ℂ) + y * I)) := by
    intro y
    rw [perronSummand_eq_mellin a hx σ t hn y, mul_assoc]
  calc
    _ = LSeries.term a (t * I) n * mellinInv σ perronKernel ((n : ℝ) / x) := by
      simp_rw [hpoint]
      rw [integral_const_mul]
      unfold mellinInv
      simp only [smul_eq_mul, Complex.real_smul]
      ring
    _ = _ := by rw [triangularMellin_inversion hσ (div_pos hnR hx)]

theorem smoothedPerron_formula {a : ℕ → ℂ} {x σ : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (ha : LSeriesSummable a (σ : ℂ)) (t : ℝ) :
    (1 / (2 * Real.pi) : ℝ) • (∫ y : ℝ,
      (x : ℂ) ^ ((σ : ℂ) + y * I) * perronKernel ((σ : ℂ) + y * I) *
        LSeries a ((σ : ℂ) + (t + y : ℝ) * I)) =
      ∑' n : ℕ, LSeries.term a (t * I) n * triangularMellinWeight ((n : ℝ) / x) := by
  rw [perron_integral_LSeries_eq_tsum hx hσ ha t, ← tsum_const_smul'']
  exact tsum_congr (perron_integral_term a hx hσ t)

end Erdos421
