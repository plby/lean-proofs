import ErdosProblems.Erdos489.RoughCoprimePairs

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open scoped BigOperators

/-- Points in a short interval labelled by divisors force many distinct labels,
unless those labels carry large reciprocal mass. -/
theorem interval_label_card_le_reciprocal_mass
    (S : Finset ℕ) (L G : ℕ) (a label : ℕ → ℕ)
    (ha : ∀ r, 0 < a r)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hdiv : ∀ n ∈ S, a (label n) ∣ n) :
    (S.card : ℝ) ≤
      (G : ℝ) * (∑ r ∈ S.image label, (a r : ℝ)⁻¹) +
        ((S.image label).card : ℝ) := by
  let T := S.image label
  have hmaps : Set.MapsTo label (S : Set ℕ) (T : Set ℕ) := by
    intro n hn
    exact Finset.mem_image.mpr ⟨n, hn, rfl⟩
  have hfiber : ∀ r ∈ T,
      ((S.filter fun n => label n = r).card : ℝ) ≤
        (G : ℝ) * (a r : ℝ)⁻¹ + 1 := by
    intro r hr
    have hsubset : (S.filter fun n => label n = r) ⊆ multiplesIn S (a r) := by
      intro n hn
      have hnS := (Finset.mem_filter.mp hn).1
      have hnr := (Finset.mem_filter.mp hn).2
      apply Finset.mem_filter.mpr
      exact ⟨hnS, hnr ▸ hdiv n hnS⟩
    have hnat : (S.filter fun n => label n = r).card ≤ G / a r + 1 :=
      (Finset.card_le_card hsubset).trans
        (multiplesIn_interval_card_le S L G (a r) (ha r) hinterval)
    have hcast : (((S.filter fun n => label n = r).card : ℕ) : ℝ) ≤
        ((G / a r + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    have hq : ((G / a r : ℕ) : ℝ) ≤ (G : ℝ) / (a r : ℝ) := Nat.cast_div_le
    norm_num only [Nat.cast_add, Nat.cast_one] at hcast
    calc
      ((S.filter fun n => label n = r).card : ℝ) ≤
          (G / a r : ℕ) + 1 := hcast
      _ ≤ (G : ℝ) / (a r : ℝ) + 1 := by linarith
      _ = (G : ℝ) * (a r : ℝ)⁻¹ + 1 := by rw [div_eq_mul_inv]
  have hcard : S.card = ∑ r ∈ T, (S.filter fun n => label n = r).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  rw [hcard]
  norm_num only [Nat.cast_sum]
  calc
    (∑ r ∈ T, ((S.filter fun n => label n = r).card : ℝ)) ≤
        ∑ r ∈ T, ((G : ℝ) * (a r : ℝ)⁻¹ + 1) :=
      Finset.sum_le_sum hfiber
    _ = (G : ℝ) * (∑ r ∈ T, (a r : ℝ)⁻¹) + (T.card : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp [Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]

/-- Rearranged form: if label reciprocal mass is at most `ε`, then the number
of distinct labels is at least `#S-Gε`. -/
theorem image_label_card_lower_of_reciprocal_mass
    (S : Finset ℕ) (L G : ℕ) (a label : ℕ → ℕ)
    (ha : ∀ r, 0 < a r)
    (hinterval : ∀ n ∈ S, L ≤ n ∧ n ≤ L + G)
    (hdiv : ∀ n ∈ S, a (label n) ∣ n)
    (ε : ℝ) (hmass : (∑ r ∈ S.image label, (a r : ℝ)⁻¹) ≤ ε) :
    (S.card : ℝ) - (G : ℝ) * ε ≤ ((S.image label).card : ℝ) := by
  have h := interval_label_card_le_reciprocal_mass
    S L G a label ha hinterval hdiv
  have hG : (0 : ℝ) ≤ G := by positivity
  have hm := mul_le_mul_of_nonneg_left hmass hG
  linarith

end Erdos489
