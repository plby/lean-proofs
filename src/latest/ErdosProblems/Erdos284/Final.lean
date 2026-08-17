/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos284.Asymptotic
import ErdosProblems.Erdos284.EfficientAssembly

/-!
# Erdős Problem 284: unconditional conclusion

The efficient factorial construction supplies, without any additional
hypothesis, the exact-cardinality witnesses needed in the lower half of the
asymptotic squeeze.  This file combines that construction with the elementary
upper bound from `Asymptotic`.
-/

open Filter
open scoped Topology Real

namespace Erdos284

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The canonical extremal function is genuinely maximal for every
sufficiently large cardinality. -/
theorem eventually_erdosF_isMaximal_proved :
    ∀ᶠ k : ℕ in atTop, IsMaximalFirstDenominator k (erdosF k) := by
  let c : ℝ := ((1 : ℝ) / 2 + erdosConstant) / 2
  have hcpos : 0 < c := by
    dsimp [c]
    linarith [erdosConstant_pos]
  have hchalf : (1 : ℝ) / 2 < c := by
    dsimp [c]
    linarith [half_lt_erdosConstant]
  have hctarget : c < 1 / (Real.exp 1 - 1) := by
    change c < erdosConstant
    dsimp [c]
    linarith [half_lt_erdosConstant]
  have hexact := eventually_exact_card_above hcpos hchalf hctarget
  filter_upwards [hexact] with k hk
  rcases hk with ⟨E, hE, _hbelow⟩
  apply erdosF_isMaximal
  let n : Fin (k + 1) → ℕ := enumerate E hE.card_eq
  refine ⟨n 0, ?_⟩
  rw [mem_firstDenominators]
  exact ⟨n, by simpa only [Nat.succ_eq_add_one] using representation_enumerate hE, rfl⟩

/-- The unconditional lower half of the asymptotic squeeze. -/
theorem eventually_lower_ratio
    {f : ℕ → ℕ}
    (hf : ∀ᶠ k : ℕ in atTop, IsMaximalFirstDenominator k (f k))
    {a : ℝ} (ha : a < erdosConstant) :
    ∀ᶠ k : ℕ in atTop, a < (f k : ℝ) / (k + 1 : ℕ) := by
  let c : ℝ := (max a ((1 : ℝ) / 2) + erdosConstant) / 2
  have hmaxlt : max a ((1 : ℝ) / 2) < erdosConstant :=
    max_lt ha half_lt_erdosConstant
  have hcpos : 0 < c := by
    dsimp [c]
    have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    have hle := le_max_right a ((1 : ℝ) / 2)
    linarith [erdosConstant_pos]
  have hachalf : (1 : ℝ) / 2 < c := by
    dsimp [c]
    have hle := le_max_right a ((1 : ℝ) / 2)
    linarith
  have hca : a < c := by
    dsimp [c]
    have hle := le_max_left a ((1 : ℝ) / 2)
    linarith
  have hctarget : c < erdosConstant := by
    dsimp [c]
    linarith
  have hexact := eventually_exact_card_above hcpos hachalf hctarget
  have hcutratio := lowerCutoff_ratio_tendsto hcpos.le
  have hcutabove : ∀ᶠ k : ℕ in atTop,
      a < (lowerCutoff c k : ℝ) / (k + 1 : ℕ) :=
    (tendsto_order.1 hcutratio).1 a hca
  filter_upwards [hexact, hf, hcutabove] with k hk hfk hratio
  rcases hk with ⟨E, hE, hbelow⟩
  have hnat : lowerCutoff c k < f k :=
    maximalFirstDenominator_gt_of_finset hE hbelow hfk
  have hkpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  exact hratio.trans_le (div_le_div_of_nonneg_right
    (by exact_mod_cast hnat.le) hkpos.le)

/-- Any eventually maximal choice of first denominator has the Erdős
asymptotic. -/
theorem ratio_tendsto
    {f : ℕ → ℕ}
    (hf : ∀ᶠ k : ℕ in atTop, IsMaximalFirstDenominator k (f k)) :
    Tendsto (fun k : ℕ ↦ (f k : ℝ) / (k + 1 : ℕ))
      atTop (nhds erdosConstant) := by
  rw [tendsto_order]
  exact ⟨fun a ha ↦ eventually_lower_ratio hf ha,
    fun b hb ↦ eventually_upper_ratio hf hb⟩

/-- The limit statement used by the public theorem in the main module. -/
theorem erdos_284_limit :
    Tendsto (fun k : ℕ ↦ (erdosF k : ℝ) / (k + 1 : ℕ))
      atTop (nhds erdosConstant) :=
  ratio_tendsto eventually_erdosF_isMaximal_proved

end

end Erdos284

#print axioms Erdos284.eventually_erdosF_isMaximal_proved
#print axioms Erdos284.eventually_lower_ratio
#print axioms Erdos284.ratio_tendsto
#print axioms Erdos284.erdos_284_limit
