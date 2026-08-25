import StackExchange.Puzzling139335.CentralNonRotation.Classification
import StackExchange.Puzzling139335.CentralNonRotation.SquareTranslation
import StackExchange.Puzzling139335.CentralNonRotation.CutData

/-!
# Central two-piece cuts: translation, reflection, glide, and half-turn

For the actual two closed sides of a proper Jordan crosscut, central symmetry
and a congruence whose square is a translation force the center onto the cut.
The common outer contacts are proved to be the two cut endpoints. The
conjugation relation used for density cancellation is proved from compactness,
not assumed. This includes all translations, reversing isometries, and
half-turns, with no boundary-area or rectifiability hypotheses.
-/

open Set Schoenflies

namespace Puzzling139335.JordanCrosscut

variable {C Γ M N : Set Plane} {p q c : Plane}

/-- The nonrotation branch of the central two-piece theorem in its uniform
form: the square of the actual side congruence is a translation. -/
theorem center_mem_of_square_translation
    (h : JordanCrosscut C Γ p q) (houter : IsCutPair C p q M N)
    (g : Plane ≃ᵃⁱ[ℝ] Plane)
    (hg : g '' closure (inside (M ∪ Γ)) = closure (inside (N ∪ Γ)))
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' C = C)
    (v : Plane) (hg2 : ∀ x, g (g x) = x + v) : c ∈ Γ := by
  have hdis : Disjoint (interior (closure (inside (M ∪ Γ))))
      (interior (g '' closure (inside (M ∪ Γ)))) := by
    rw [hg]
    exact h.closure_sides_disjoint_interiors houter
  have hunion : AffineIsometryEquiv.pointReflection ℝ c ''
      (closure (inside (M ∪ Γ)) ∪ g '' closure (inside (M ∪ Γ))) =
        closure (inside (M ∪ Γ)) ∪ g '' closure (inside (M ∪ Γ)) := by
    rw [hg]
    exact h.closure_sides_pointReflection_image_union houter hsym
  have hcontact : (closure (inside (M ∪ Γ)) ∩ g '' closure (inside (M ∪ Γ)) ∩
      frontier (closure (inside (M ∪ Γ)) ∪ g '' closure (inside (M ∪ Γ)))).Finite := by
    rw [hg]
    exact h.closure_sides_outer_contact_finite houter
  have hnot := CentralNonRotation.not_mem_interiors_of_central_square_translation
    (h.side_isJordanRegion houter) g c v hg2 hdis hunion hcontact
  apply h.center_mem_cut_of_not_mem_sides houter hsym hnot.1
  simpa only [hg] using hnot.2

/-- Any involutive congruence, including a reflection or half-turn, puts the
center on the common cut. Its axis or center is not prescribed in advance. -/
theorem center_mem_of_involutive
    (h : JordanCrosscut C Γ p q) (houter : IsCutPair C p q M N)
    (g : Plane ≃ᵃⁱ[ℝ] Plane)
    (hg : g '' closure (inside (M ∪ Γ)) = closure (inside (N ∪ Γ)))
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' C = C)
    (hinv : Function.Involutive g) : c ∈ Γ := by
  apply h.center_mem_of_square_translation houter g hg hsym 0
  intro x
  rw [hinv x, add_zero]

/-- A translation congruence also forces the center onto the common cut. -/
theorem center_mem_of_translation
    (h : JordanCrosscut C Γ p q) (houter : IsCutPair C p q M N)
    (g : Plane ≃ᵃⁱ[ℝ] Plane)
    (hg : g '' closure (inside (M ∪ Γ)) = closure (inside (N ∪ Γ)))
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' C = C)
    (t : Plane) (htranslation : ∀ x, g x = x + t) : c ∈ Γ :=
  h.center_mem_of_square_translation houter g hg hsym (t + t)
    (CentralNonRotation.square_translation_of_translation g htranslation)

/-- Every reversing affine isometry is covered, whether reflection or glide
reflection. Its axis is derived from symmetry and boundedness of the union. -/
theorem center_mem_of_reversing
    (h : JordanCrosscut C Γ p q) (houter : IsCutPair C p q M N)
    (g : Plane ≃ᵃⁱ[ℝ] Plane)
    (hg : g '' closure (inside (M ∪ Γ)) = closure (inside (N ∪ Γ)))
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' C = C)
    (a : Circle)
    (hreversing : ∀ x, PlaneIsometries.complexEquiv (g x) =
      (a : ℂ) * starRingEnd ℂ (PlaneIsometries.complexEquiv x) +
        PlaneIsometries.complexEquiv (g 0)) : c ∈ Γ :=
  h.center_mem_of_square_translation houter g hg hsym
    (PlaneIsometries.complexEquiv.symm (PlaneIsometries.complexReversingDisplacement a
      (PlaneIsometries.complexEquiv (g 0))))
    (PlaneIsometries.affine_reversing_square g a hreversing)

/-- A half-turn congruence is allowed about any initial point; the central
symmetry of the union forces the required center conclusion. -/
theorem center_mem_of_halfTurn
    (h : JordanCrosscut C Γ p q) (houter : IsCutPair C p q M N) (k : Plane)
    (hg : AffineIsometryEquiv.pointReflection ℝ k '' closure (inside (M ∪ Γ)) =
      closure (inside (N ∪ Γ)))
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' C = C) : c ∈ Γ :=
  h.center_mem_of_involutive houter (AffineIsometryEquiv.pointReflection ℝ k) hg hsym
    (AffineIsometryEquiv.pointReflection_involutive (𝕜 := ℝ) k)

/-- After the nonrotation theorem, the only possible remaining case is a
proper rotation whose coefficient is neither one nor minus one. -/
theorem center_mem_or_other_rotation
    (h : JordanCrosscut C Γ p q) (houter : IsCutPair C p q M N)
    (g : Plane ≃ᵃⁱ[ℝ] Plane)
    (hg : g '' closure (inside (M ∪ Γ)) = closure (inside (N ∪ Γ)))
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' C = C) :
    c ∈ Γ ∨ (∃ a : Circle, a ≠ 1 ∧ a ≠ -1 ∧
      ∀ x, PlaneIsometries.complexEquiv (g x) =
        (a : ℂ) * PlaneIsometries.complexEquiv x + PlaneIsometries.complexEquiv (g 0)) := by
  rcases CentralNonRotation.square_translation_or_other_rotation g with ⟨v, hv⟩ | hrotation
  · exact Or.inl (h.center_mem_of_square_translation houter g hg hsym v hv)
  · exact Or.inr hrotation

end Puzzling139335.JordanCrosscut
