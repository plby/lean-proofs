import ErdosProblems.Erdos421.ZetaPrimeErrorHeight

/-! # A uniform strip bound including the removed pole at one -/

namespace Erdos421

open Complex Filter Topology

theorem exists_zetaPrimeError_full_strip_bound :
    ∃ H₀ > 1, ∃ C > 0, ∀ H β t : ℝ, H₀ ≤ H →
      |β - 1| ≤ logPowerZeroWidth H / 64 → |t| ≤ H →
      riemannZeta₁ ((β : ℂ) + t * I) ≠ 0 ∧
        ‖zetaPrimeError ((β : ℂ) + t * I)‖ ≤ C * H := by
  obtain ⟨T₀, hT₀, hhigh⟩ := zetaPrimeError_eventually_linear_height
  obtain ⟨η, hη, C, hC, hcompact⟩ := exists_zetaPrimeError_bounded_height T₀
  have hlim := logPowerZeroWidth_tendsto_zero.div_const (64 : ℝ)
  simp only [zero_div] at hlim
  have hsmall := hlim.eventually (gt_mem_nhds hη)
  have hlarge : ∀ᶠ H : ℝ in atTop, ∀ β t : ℝ,
      |β - 1| ≤ logPowerZeroWidth H / 64 → |t| ≤ H →
      riemannZeta₁ ((β : ℂ) + t * I) ≠ 0 ∧
        ‖zetaPrimeError ((β : ℂ) + t * I)‖ ≤ (C + 2) * H := by
    filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with H hsmall hH
    intro β t hβ ht
    by_cases hlow : |t| ≤ T₀
    · have hb := hcompact β t (hβ.trans hsmall.le) hlow
      refine ⟨hb.1, hb.2.trans ?_⟩
      nlinarith
    · have htT : T₀ ≤ |t| := (lt_of_not_ge hlow).le
      have hw := logPowerZeroWidth_antitone (hT₀.trans_le htT) ht
      have hβ' : |β - 1| ≤ logPowerZeroWidth |t| / 64 := by linarith
      have hb := hhigh t β htT hβ'
      refine ⟨hb.1, hb.2.trans ?_⟩
      nlinarith
  obtain ⟨H₀, hH₀⟩ := eventually_atTop.mp hlarge
  refine ⟨max H₀ 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _),
    C + 2, by linarith, ?_⟩
  intro H β t hH hβ ht
  exact hH₀ H ((le_max_left H₀ 2).trans hH) β t hβ ht

end Erdos421
