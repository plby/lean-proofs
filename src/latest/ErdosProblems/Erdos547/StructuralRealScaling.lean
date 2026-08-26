import ErdosProblems.Erdos547.StructuralScaling

/-!
# Real scaling of part budgets when the degree inequalities have slack
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

theorem exists_positive_nat_ratio_between {x y : ℝ} (hx : 0 < x) (hxy : x < y) :
    ∃ p q : ℕ, 0 < p ∧ 0 < q ∧ x < (p : ℝ) / q ∧ (p : ℝ) / q < y := by
  obtain ⟨q, hq⟩ := exists_nat_gt (y - x)⁻¹
  have hq' : 0 < (q : ℝ) := (inv_pos.mpr (sub_pos.mpr hxy)).trans hq
  obtain ⟨z, hz, hz'⟩ := exists_div_btwn hxy hq
  have hzr : 0 < (z : ℝ) := by
    have hh := (lt_div_iff₀ hq').mp (hx.trans hz)
    simpa only [zero_mul] using hh
  have hzz : 0 < z := by exact_mod_cast hzr
  have hcast : (z.toNat : ℝ) = (z : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hzz.le
  refine ⟨z.toNat, q, by omega, by exact_mod_cast hq', ?_, ?_⟩
  · rwa [hcast]
  · rwa [hcast]

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem HasAnchoredTotals.mono_totals {w : EdgeWeights G} {γ δ a b r s : ℝ}
    (h : HasAnchoredTotals w γ δ a b) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hra : r ≤ a) (hsb : s ≤ b) : HasAnchoredTotals w γ δ r s := by
  obtain ⟨c, d, σ, τ, hp, hσ, hτ⟩ := h
  obtain ⟨σ', hσ', htσ⟩ := σ.exists_suballocation_total r hr (by rwa [hσ])
  obtain ⟨τ', hτ', htτ⟩ := τ.exists_suballocation_total s hs (by rwa [hτ])
  exact ⟨c, d, σ', τ', hp.of_suballocations hσ' hτ', htσ, htτ⟩

/-- Strict surplus in the degrees allows any positive real scale, while
preserving exactly the ratios of the original integer part sizes. -/
theorem exists_anchored_totals_scaled_of_strict_degree (w : EdgeWeights G) (c : V)
    (a₁ a₂ b₁ b₂ : ℕ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (r : ℝ) (hr : 0 < r)
    (hlarge : r * ((a₁ : ℝ) + a₂ + b₁ + b₂) < w.degree c)
    (hdeg : ∀ v, r * ((a₁ : ℝ) + a₂ + b₁ + b₂) / 2 < w.degree v) :
    HasAnchoredTotals w ((a₂ : ℝ) / a₁) ((b₂ : ℝ) / b₁)
      (r * ((a₁ : ℝ) + a₂)) (r * ((b₁ : ℝ) + b₂)) := by
  classical
  let k := (a₁ : ℝ) + a₂ + b₁ + b₂
  have hk : 0 < k := by dsimp [k]; positivity
  obtain ⟨v₀, _hv₀, hmin⟩ := Finset.exists_min_image Finset.univ w.degree ⟨c, Finset.mem_univ _⟩
  have hupper : r < min (w.degree c / k) (2 * w.degree v₀ / k) := by
    apply lt_min
    · exact (lt_div_iff₀ hk).mpr hlarge
    · apply (lt_div_iff₀ hk).mpr
      have hh := hdeg v₀
      change r * k / 2 < w.degree v₀ at hh
      linarith
  obtain ⟨p, q, hp, hq, hlo, hhi⟩ := exists_positive_nat_ratio_between hr hupper
  have hlarge' : (p : ℝ) / q * k ≤ w.degree c :=
    ((lt_div_iff₀ hk).mp (hhi.trans_le (min_le_left _ _))).le
  have hdeg' (v : V) : (p : ℝ) / q * k / 2 ≤ w.degree v := by
    have hh := (lt_div_iff₀ hk).mp (hhi.trans_le (min_le_right _ _))
    linarith [hmin v (Finset.mem_univ _)]
  have h := exists_anchored_totals_scaled_nat w c a₁ a₂ b₁ b₂ p q ha₁ ha₂ hb₁ hb₂ hp hq
    hlarge' hdeg'
  exact h.mono_totals (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_right hlo.le (by positivity))
    (mul_le_mul_of_nonneg_right hlo.le (by positivity))

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_anchored_totals_scaled_of_strict_degree
