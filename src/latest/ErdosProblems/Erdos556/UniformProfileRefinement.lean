import ErdosProblems.Erdos556.CleanProfileFaces
import ErdosProblems.Erdos556.ProfileRefinement

/-! A fixed small profile error suffices for the exact four-core finishers. -/

namespace Erdos556

open SimpleGraph Finset

noncomputable def profileRefinementError : ℝ := 1 / 100000000

theorem profileRefinementError_pos : 0 < profileRefinementError := by
  norm_num [profileRefinementError]

theorem refinement_core_size (r d M : ℕ) (η : ℝ) (hr : 10 ≤ r) (hη : η ≤ 1 / 100)
    (hd : (d : ℝ) ≤ η * (2 * r + 1))
    (hM : (1 - η) * (2 * r + 1) ≤ (M : ℝ)) : r + 2 * d + 3 ≤ M := by
  have hrR : (10 : ℝ) ≤ r := by exact_mod_cast hr
  have hηscaled := mul_le_mul_of_nonneg_right hη (by positivity : (0 : ℝ) ≤ 2 * r + 1)
  have hb : (r : ℝ) + 2 * d + 3 ≤ M := by nlinarith
  exact_mod_cast hb

theorem face_size_for_two_colour_structure (r M : ℕ) (hr : 1000000 ≤ r)
    (hM : (2 - profileRefinementError) * (2 * r + 1) ≤ (M : ℝ)) :
    4 * (r + 1) - (r + 1) / 100000 ≤ M := by
  have hMR : (199999999 : ℝ) * (2 * r + 1) ≤ 100000000 * M := by
    dsimp only [profileRefinementError] at hM
    nlinarith
  have hMN : 199999999 * (2 * r + 1) ≤ 100000000 * M := by exact_mod_cast hMR
  omega

theorem exists_uniform_profile_refinements :
    ∃ R₀ : ℕ, ∀ {V : Type*} [DecidableEq V] (c : ThreeColouring V) (r : ℕ),
      R₀ ≤ r → (∀ i, ¬ cycleGraph (2 * r + 1) ⊑ c.graph i) →
      ∀ h : CleanProfileSystem c (2 * r + 1) profileRefinementError,
      ∀ p, 0 < h.weight p →
        Nonempty (ProfileRefinement c p (h.sets p) (r + 2 * h.defect + 3) h.defect) := by
  obtain ⟨R₁, htwo⟩ := exists_uniform_two_colour_set_structure
  refine ⟨max R₁ 1000000, ?_⟩
  intro V _ c r hr hno h p hp
  have hrlarge : 1000000 ≤ r := (le_max_right _ _).trans hr
  have hr₁ : R₁ ≤ r := (le_max_left _ _).trans hr
  have hη : profileRefinementError ≤ 1 / 100 := by norm_num [profileRefinementError]
  have hd : (h.defect : ℝ) ≤ profileRefinementError * (2 * r + 1) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h.defect_le
  have hs := h.size_lower p
  push_cast at hs
  rcases h.tiling.normalized p hp with ⟨hpdim, hpval⟩ | ⟨hpdim, hpval⟩
  · rw [hpval] at hs
    exact exists_edge_profile_refinement c p (h.sets p) _ h.defect hpdim
      (refinement_core_size r h.defect _ _ (by omega) hη hd hs)
  · obtain ⟨i, b, rfl⟩ := (profileDimension_two_iff p).mp hpdim
    rw [hpval] at hs
    have hsize := face_size_for_two_colour_structure r _ hrlarge hs
    have hfree := h.no_fixed_colour_in_face (by omega) hη hno i b hp
    obtain ⟨j, k, hji, hki, hjk, ⟨part⟩⟩ := htwo c (h.sets (cubeFace i b)) r i hr₁ hsize hfree hno
    have hS : (1 - profileRefinementError) * (2 * r + 1) ≤ (part.first.card : ℝ) := by
      have hcov : ((h.sets (cubeFace i b)).card : ℝ) ≤ part.first.card + part.second.card + 1 := by
        exact_mod_cast part.card_cover
      have hTc : (part.second.card : ℝ) ≤ 2 * r := by exact_mod_cast part.second_card_le
      nlinarith
    have hT : (1 - profileRefinementError) * (2 * r + 1) ≤ (part.second.card : ℝ) := by
      have hcov : ((h.sets (cubeFace i b)).card : ℝ) ≤ part.first.card + part.second.card + 1 := by
        exact_mod_cast part.card_cover
      have hSc : (part.first.card : ℝ) ≤ 2 * r := by exact_mod_cast part.first_card_le
      nlinarith
    exact exists_face_profile_refinement c _ r _ h.defect i j k b hji hki hjk part
      (refinement_core_size r h.defect _ _ (by omega) hη hd hS)
      (refinement_core_size r h.defect _ _ (by omega) hη hd hT)

#print axioms exists_uniform_profile_refinements

end Erdos556
