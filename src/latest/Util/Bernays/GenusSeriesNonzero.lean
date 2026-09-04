import Util.Bernays.GenusSquareSeries
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# The continued genus-series square is not identically zero
-/

open Filter Topology

namespace Bernays

theorem LSeries_exists_ne_zero_of_coeff_one {a : ℕ → ℂ} (ha : a 1 ≠ 0)
    (hs : LSeriesSummable a (2 : ℂ)) : ∃ x : ℝ, 1 < x ∧ LSeries a x ≠ 0 := by
  by_contra! h
  have hevent : (fun x : ℝ => LSeries a x) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact h x hx
  have halt : LSeries.abscissaOfAbsConv a ≠ ⊤ := by
    intro htop
    have hb := hs.abscissaOfAbsConv_le
    rw [htop] at hb
    norm_num at hb
  exact ha ((LSeries_eventually_eq_zero_iff'.mp hevent).resolve_right halt 1 (by decide))

theorem genusLocalLSeries_differentiableAt {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ s : ℂ, 1 < s.re → DifferentiableAt ℂ (LSeries (genusLocalAF hD ψ)) s := by
  let := quadraticOrderIsDomain hD
  intro ψ s hs
  have hab : LSeries.abscissaOfAbsConv (genusLocalAF hD ψ) ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (fun x hx =>
      genusLocalAF_summable hD ψ x (by simpa only [Complex.ofReal_re] using hx))
  exact (LSeries_hasDerivAt (hab.trans_lt (by exact_mod_cast hs))).differentiableAt

theorem genusLocalLSeries_continuation_nonzero {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ, ψ ≠ 0 →
      ∃ F : ℂ → ℂ,
        (∀ s : ℂ, (1 / 2 : ℝ) < s.re → DifferentiableAt ℂ F s) ∧
        (∀ s : ℂ, 1 < s.re → F s = LSeries (genusLocalAF hD ψ) s ^ 2) ∧
        (∃ s : ℂ, (1 / 2 : ℝ) < s.re ∧ F s ≠ 0) := by
  let := quadraticOrderIsDomain hD
  intro ψ hψ
  obtain ⟨F, hF, heq⟩ := genusLocalLSeries_square_continuation hD ψ hψ
  have ha : genusLocalAF hD ψ 1 ≠ 0 := by
    rw [(genusLocalAF_isMultiplicative hD ψ).1]
    exact one_ne_zero
  obtain ⟨x, hx, hxne⟩ := LSeries_exists_ne_zero_of_coeff_one ha
    (genusLocalAF_summable hD ψ 2 (by norm_num))
  refine ⟨F, hF, heq, x, by simpa only [Complex.ofReal_re] using (by linarith : (1 / 2 : ℝ) < x), ?_⟩
  rw [heq x (by simpa only [Complex.ofReal_re] using hx)]
  exact pow_ne_zero _ hxne

end Bernays
