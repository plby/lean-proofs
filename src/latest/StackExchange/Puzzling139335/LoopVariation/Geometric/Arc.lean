import StackExchange.Puzzling139335.LoopVariation.Geometric.Defs

/-!
# Set-level variation of Jordan arcs

The chosen-parametrization definition is independent of the choice. Hence it
has exact isometry invariance and the fixed positive lower bound needed to
cancel a common interface.
-/

open Set

namespace Puzzling139335.LoopVariation

open ArcVariation

noncomputable section

/-- Every continuous injective compact-interval parametrization computes the
same set-level arc variation. Its interval need not be the unit interval. -/
theorem arcVariation_eq_of_parametrization {A : Set Schoenflies.Plane}
    (ε : ℝ) (hA : Schoenflies.IsArc A) {f : ℝ → Schoenflies.Plane} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hfi : InjOn f (Icc a b))
    (himage : f '' Icc a b = A) :
    arcVariation ε A = variationOn ε f (Icc a b) := by
  rw [arcVariation, dif_pos hA]
  obtain ⟨hg, hgi, hgimage⟩ := Classical.choose_spec hA
  exact variationOn_eq_of_continuousOn_injOn_image_eq_Icc ε hg hgi hf hfi
    (hgimage.trans himage.symm)

/-- Arc variation is nonnegative at every positive resolution. -/
theorem arcVariation_nonneg {ε : ℝ} {A : Set Schoenflies.Plane}
    (hA : Schoenflies.IsArc A) (hε : 0 < ε) : 0 ≤ arcVariation ε A := by
  obtain ⟨f, hf, hfi, himage⟩ := hA
  rw [arcVariation_eq_of_parametrization ε ⟨f, hf, hfi, himage⟩ hf hfi himage]
  exact variationOn_Icc_nonneg zero_le_one hf hε

/-- Every simple arc has a fixed positive lower bound at all sufficiently small
positive resolutions. -/
theorem arcVariation_exists_positive_lower_bound {A : Set Schoenflies.Plane}
    (hA : Schoenflies.IsArc A) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε ≤ η → η ≤ arcVariation ε A := by
  obtain ⟨f, hf, hfi, himage⟩ := hA
  obtain ⟨η, hη, hbound⟩ := ArcVariation.exists_positive_lower_bound_of_injOn
    (by norm_num : (0 : ℝ) < 1) hf hfi
  refine ⟨η, hη, ?_⟩
  intro ε hε hsmall
  rw [arcVariation_eq_of_parametrization ε ⟨f, hf, hfi, himage⟩ hf hfi himage]
  exact hbound ε hε hsmall

/-- An isometry takes a genuine arc to a genuine arc. -/
theorem isArc_image_isometry {A : Set Schoenflies.Plane} (hA : Schoenflies.IsArc A)
    {e : Schoenflies.Plane → Schoenflies.Plane} (he : Isometry e) :
    Schoenflies.IsArc (e '' A) := by
  obtain ⟨f, hf, hfi, himage⟩ := hA
  refine ⟨e ∘ f, he.continuous.comp_continuousOn hf, ?_, ?_⟩
  · intro x hx y hy hxy
    exact hfi hx hy (he.injective hxy)
  · rw [Set.image_comp, himage]

/-- Arc variation is exactly preserved by an ambient isometry. -/
theorem arcVariation_image_isometry {A : Set Schoenflies.Plane} (ε : ℝ)
    (hA : Schoenflies.IsArc A) {e : Schoenflies.Plane → Schoenflies.Plane}
    (he : Isometry e) : arcVariation ε (e '' A) = arcVariation ε A := by
  obtain ⟨f, hf, hfi, himage⟩ := hA
  have hA : Schoenflies.IsArc A := ⟨f, hf, hfi, himage⟩
  have hecont : ContinuousOn (e ∘ f) (Icc (0 : ℝ) 1) :=
    he.continuous.comp_continuousOn hf
  have heinj : InjOn (e ∘ f) (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact hfi hx hy (he.injective hxy)
  have heimage : (e ∘ f) '' Icc (0 : ℝ) 1 = e '' A := by
    rw [Set.image_comp, himage]
  rw [arcVariation_eq_of_parametrization ε (isArc_image_isometry hA he)
      hecont heinj heimage,
    arcVariation_eq_of_parametrization ε hA hf hfi himage]
  exact variationOn_comp_isometry he ε f (Icc (0 : ℝ) 1)

end

end Puzzling139335.LoopVariation
