import ErdosProblems.Erdos4.DoubleMeanSquare

/-! Finite exceptional sets and explicit cancellation of the common sieve-weight scale. -/

open scoped BigOperators

namespace Erdos4.FGKMT

theorem exists_norm_exceptional_finset (targets : Finset ℕ) (f : ℕ → ℂ)
    {η V : ℝ} (hη : 0 < η) (hV : (∑ q : targets, ‖f q‖ ^ 2) ≤ V) :
    ∃ bad : Finset ℕ, bad ⊆ targets ∧ (bad.card : ℝ) ≤ V / η ^ 2 ∧
      ∀ q ∈ targets, q ∉ bad → ‖f q‖ ≤ η := by
  classical
  let bad₀ := Finset.univ.filter (fun q : targets => η < ‖f q‖)
  let bad := bad₀.image Subtype.val
  refine ⟨bad, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hq
    exact r.property
  · have hh := DoubleMeanSquare.large_values_card_le (fun q : targets => f q) hη hV
    have hcard : (bad.card : ℝ) ≤ bad₀.card := by exact_mod_cast Finset.card_image_le
    exact hcard.trans hh
  · intro q hq hgood
    apply le_of_not_gt
    intro hlarge
    apply hgood
    exact Finset.mem_image.mpr ⟨⟨q, hq⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlarge⟩, rfl⟩

theorem high_error_budget_cancel {x Y L F S j c d : ℝ}
    (hx : 0 < x) (hY : 0 ≤ Y) (hL : 0 < L) (hF : 0 < F)
    (hj : 0 < j) (hc : 0 < c) (hd : 0 < d) (hS : d * x / L ≤ S) :
    (160000 * Y * x * F ^ 2 * S / L ^ 2) / (S * c * j * F / 4) ^ 2 ≤
      (2560000 / (c ^ 2 * d)) * Y / (L * j ^ 2) := by
  have hSpos : 0 < S := (div_pos (mul_pos hd hx) hL).trans_le hS
  calc
    _ = (2560000 * Y * x / (L ^ 2 * c ^ 2 * j ^ 2)) / S := by
      field_simp
      <;> ring
    _ ≤ (2560000 * Y * x / (L ^ 2 * c ^ 2 * j ^ 2)) / (d * x / L) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hS
    _ = _ := by field_simp

theorem low_error_budget {x L F S c j : ℝ}
    (hF : 0 ≤ F) (hS0 : 0 ≤ S) (hS : x / L ^ 2 ≤ S) (hcj : 4 ≤ c * j) :
    F * x / L ^ 2 ≤ S * c * j * F / 4 := by
  have hh := mul_le_mul_of_nonneg_right hcj (mul_nonneg hS0 hF)
  calc
    _ = F * (x / L ^ 2) := by ring
    _ ≤ F * S := mul_le_mul_of_nonneg_left hS hF
    _ ≤ _ := by nlinarith

theorem incidence_gain_budget {x Y L r α E S j P η d : ℝ}
    (hx : 0 ≤ x) (hY : 0 < Y) (hL : 0 < L) (hα : 0 < α) (hE : 0 < E)
    (hj : 0 ≤ j) (hd : 0 < d) (hS : d * x / L ≤ S)
    (hr : L / 100 ≤ r) (hP : α * E * r * j / 24576 ≤ P)
    (hη : η ≤ S * P / 4) :
    (d / 14745600) * j * x / Y ≤ (S * P - η - η) / (3 * (α * Y * E)) := by
  have hS0 : 0 ≤ S := (div_nonneg (mul_nonneg hd.le hx) hL.le).trans hS
  have hr0 : 0 ≤ r := (by positivity : (0 : ℝ) ≤ L / 100).trans hr
  calc
    _ = ((d * x / L) * (L / 100) * j) / (147456 * Y) := by field_simp; ring
    _ ≤ (S * r * j) / (147456 * Y) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ hj
      exact mul_le_mul hS hr (by positivity) hS0
    _ = (S * (α * E * r * j / 24576) / 2) / (3 * (α * Y * E)) := by
      field_simp
      <;> ring
    _ ≤ (S * P / 2) / (3 * (α * Y * E)) :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hP hS0) (by norm_num))
        (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)

end Erdos4.FGKMT
