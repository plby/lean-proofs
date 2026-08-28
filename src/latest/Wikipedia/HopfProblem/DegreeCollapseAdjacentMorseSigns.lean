import Wikipedia.HopfProblem.DegreeCollapseSignedCoordinateMatching
import Wikipedia.HopfProblem.DegreeCollapseMorseCubicEndpoint

/-!
# Adjacent Morse signatures have matching transverse coordinates

The lower-index endpoint supplies a positive scalar square and the
upper-index endpoint a negative scalar square. After removing them, the
remaining signatures agree, and a constructed coordinate permutation
matches every transverse coefficient exactly.
-/

noncomputable section

namespace Wikipedia.HopfProblem.DegreeCollapse.SignedCoordinates

open Classical in
theorem negative_card_split {m n : ℕ} (ρ : Option (Fin m) ≃ Fin n) (w : Fin n → ℝ) :
    Fintype.card {j // w j = -1} = (if w (ρ none) = -1 then 1 else 0) +
      Fintype.card {i : Fin m // w (ρ (some i)) = -1} := by
  have he : {i : Option (Fin m) // w (ρ i) = -1} ≃ {j : Fin n // w j = -1} :=
    ρ.subtypeEquiv (fun _ => Iff.rfl)
  rw [← Fintype.card_congr he]
  simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter,
    Fintype.sum_option]

open Classical in
/-- All coordinate permutations needed for a pair of adjacent Morse indices are constructed. -/
theorem exists_adjacent_sign_enumerations {m : ℕ} (w₀ w₁ : Fin (m + 1) → ℝ)
    (h₀ : ∀ i, w₀ i = -1 ∨ w₀ i = 1) (h₁ : ∀ i, w₁ i = -1 ∨ w₁ i = 1)
    (hindex : Fintype.card {i // w₁ i = -1} = Fintype.card {i // w₀ i = -1} + 1) :
    ∃ ρ₀ ρ₁ : Option (Fin m) ≃ Fin (m + 1),
      w₀ (ρ₀ none) = 1 ∧ w₁ (ρ₁ none) = -1 ∧
        ∀ i, w₀ (ρ₀ (some i)) = w₁ (ρ₁ (some i)) := by
  have hbound := Fintype.card_subtype_le (fun i : Fin (m + 1) => w₁ i = -1)
  have hNpos : 0 < Fintype.card {i // w₁ i = -1} := by omega
  have hPpos : 0 < Fintype.card {i // ¬w₀ i = -1} := by
    rw [Fintype.card_subtype_compl]
    omega
  let j₀ := Classical.choice (Fintype.card_pos_iff.mp hPpos)
  let j₁ := Classical.choice (Fintype.card_pos_iff.mp hNpos)
  obtain ⟨ρ₀, hρ₀⟩ := MorseCancellation.exists_coordinate_enum rfl j₀.1
  obtain ⟨ρ₁, hρ₁⟩ := MorseCancellation.exists_coordinate_enum rfl j₁.1
  have hfirst₀ : w₀ (ρ₀ none) = 1 := by
    rw [hρ₀]
    exact positive_of_not_negative h₀ j₀.2
  have hfirst₁ : w₁ (ρ₁ none) = -1 := by
    rw [hρ₁]
    exact j₁.2
  let σ₀ := fun i : Fin m => w₀ (ρ₀ (some i))
  let σ₁ := fun i : Fin m => w₁ (ρ₁ (some i))
  have hrest : Fintype.card {i // σ₀ i = -1} = Fintype.card {i // σ₁ i = -1} := by
    have hcount₀ := negative_card_split ρ₀ w₀
    have hcount₁ := negative_card_split ρ₁ w₁
    rw [hfirst₀] at hcount₀
    rw [hfirst₁] at hcount₁
    norm_num at hcount₀ hcount₁
    change Fintype.card {i // w₀ (ρ₀ (some i)) = -1} =
      Fintype.card {i // w₁ (ρ₁ (some i)) = -1}
    omega
  obtain ⟨η, hη⟩ := exists_equiv_of_negative_card_eq σ₀ σ₁
    (fun i => h₀ _) (fun i => h₁ _) rfl hrest
  refine ⟨ρ₀, (Equiv.optionCongr η).trans ρ₁, hfirst₀, ?_, ?_⟩
  · simpa using hfirst₁
  · intro i
    exact (hη i).symm

open Classical in
theorem exists_adjacent_sign_enumerations_of_dimension {m n : ℕ} (hn : n = m + 1)
    (w₀ w₁ : Fin n → ℝ)
    (h₀ : ∀ i, w₀ i = -1 ∨ w₀ i = 1) (h₁ : ∀ i, w₁ i = -1 ∨ w₁ i = 1)
    (hindex : Fintype.card {i // w₁ i = -1} = Fintype.card {i // w₀ i = -1} + 1) :
    ∃ ρ₀ ρ₁ : Option (Fin m) ≃ Fin n,
      w₀ (ρ₀ none) = 1 ∧ w₁ (ρ₁ none) = -1 ∧
        ∀ i, w₀ (ρ₀ (some i)) = w₁ (ρ₁ (some i)) := by
  subst n
  exact exists_adjacent_sign_enumerations w₀ w₁ h₀ h₁ hindex

end Wikipedia.HopfProblem.DegreeCollapse.SignedCoordinates
