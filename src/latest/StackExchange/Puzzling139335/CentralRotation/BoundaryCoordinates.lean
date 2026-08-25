import StackExchange.Puzzling139335.Definitions
import StackExchange.Puzzling139335.CentralRotation.CircleArcs

/-!
# Compatible coordinates on the two tile boundaries and outer boundary

These data record the actual half-speed traces of three boundary loops.
They contain no orientation claim about a congruence.  Such a claim is
separately expressed by an increasing real lift in `BoundaryLifts`.
-/

open Set

namespace Puzzling139335.CentralRotation

/-- Three compatible circle parametrizations, obtained by traversing the
left outer arc, the shared cut, and the right outer arc. -/
structure BoundaryCoordinates (M Γ N : Set Plane) where
  leftParam : AddCircle (1 : ℝ) → Plane
  rightParam : AddCircle (1 : ℝ) → Plane
  outerParam : AddCircle (1 : ℝ) → Plane
  leftContinuous : Continuous leftParam
  rightContinuous : Continuous rightParam
  outerContinuous : Continuous outerParam
  leftInjective : Function.Injective leftParam
  rightInjective : Function.Injective rightParam
  outerInjective : Function.Injective outerParam
  leftOuterImage : circleParam leftParam '' Icc (0 : ℝ) (1 / 2) = M
  leftCutImage : circleParam leftParam '' Icc (1 / 2 : ℝ) 1 = Γ
  rightOuterImage : circleParam rightParam '' Icc (1 / 2 : ℝ) 1 = N
  outerLeftAgree : EqOn (circleParam leftParam) (circleParam outerParam)
    (Icc (0 : ℝ) (1 / 2))
  outerRightAgree : EqOn (circleParam rightParam) (circleParam outerParam)
    (Icc (1 / 2 : ℝ) 1)
  cutAgree : ∀ t ∈ Icc (1 / 2 : ℝ) 1,
    circleParam leftParam t = circleParam rightParam (1 - t)

namespace BoundaryCoordinates

variable {M Γ N : Set Plane} (d : BoundaryCoordinates M Γ N)

theorem left_eq_outer_of_mem {t : ℝ} (ht : circleParam d.leftParam t ∈ M) :
    circleParam d.leftParam t = circleParam d.outerParam t := by
  have hmem : circleParam d.leftParam t ∈ circleParam d.leftParam '' Icc (0 : ℝ) (1 / 2) := by
    rw [d.leftOuterImage]
    exact ht
  obtain ⟨s, hs, hst⟩ := hmem
  have heq : (s : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ)) := d.leftInjective hst
  exact hst.symm.trans ((d.outerLeftAgree hs).trans (congrArg d.outerParam heq))

theorem right_eq_outer_of_mem {t : ℝ} (ht : circleParam d.rightParam t ∈ N) :
    circleParam d.rightParam t = circleParam d.outerParam t := by
  have hmem : circleParam d.rightParam t ∈ circleParam d.rightParam '' Icc (1 / 2 : ℝ) 1 := by
    rw [d.rightOuterImage]
    exact ht
  obtain ⟨s, hs, hst⟩ := hmem
  have heq : (s : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ)) := d.rightInjective hst
  exact hst.symm.trans ((d.outerRightAgree hs).trans (congrArg d.outerParam heq))

theorem outer_eq_left_of_mem {t : ℝ} (ht : circleParam d.outerParam t ∈ M) :
    circleParam d.outerParam t = circleParam d.leftParam t := by
  have hmem : circleParam d.outerParam t ∈ circleParam d.leftParam '' Icc (0 : ℝ) (1 / 2) := by
    rw [d.leftOuterImage]
    exact ht
  obtain ⟨s, hs, hst⟩ := hmem
  have heq : (s : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ)) :=
    d.outerInjective ((d.outerLeftAgree hs).symm.trans hst)
  exact hst.symm.trans (congrArg d.leftParam heq)

theorem outer_eq_right_of_mem {t : ℝ} (ht : circleParam d.outerParam t ∈ N) :
    circleParam d.outerParam t = circleParam d.rightParam t := by
  have hmem : circleParam d.outerParam t ∈ circleParam d.rightParam '' Icc (1 / 2 : ℝ) 1 := by
    rw [d.rightOuterImage]
    exact ht
  obtain ⟨s, hs, hst⟩ := hmem
  have heq : (s : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ)) :=
    d.outerInjective ((d.outerRightAgree hs).symm.trans hst)
  exact hst.symm.trans (congrArg d.rightParam heq)

theorem left_subset_outer_range : M ⊆ range d.outerParam := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := d.leftOuterImage.symm ▸ hx
  exact ⟨(s : AddCircle (1 : ℝ)), (d.outerLeftAgree hs).symm⟩

theorem right_subset_outer_range : N ⊆ range d.outerParam := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := d.rightOuterImage.symm ▸ hx
  exact ⟨(s : AddCircle (1 : ℝ)), (d.outerRightAgree hs).symm⟩

end BoundaryCoordinates

/-- Actual increasing real lifts of the congruence and central symmetry in
the chosen boundary coordinates.  The existence of these lifts is the
separate geometric boundary-orientation theorem. -/
structure BoundaryLifts {M Γ N : Set Plane} (d : BoundaryCoordinates M Γ N)
    (g h : Plane ≃ᵃⁱ[ℝ] Plane) where
  G : ℝ ≃ₜ ℝ
  H : ℝ ≃ₜ ℝ
  G_increasing : StrictMono G
  H_increasing : StrictMono H
  G_period : ∀ t, G (t + 1) = G t + 1
  H_period : ∀ t, H (t + 1) = H t + 1
  left_to_right : ∀ t, circleParam d.rightParam (G t) = g (circleParam d.leftParam t)
  outer_to_outer : ∀ t, circleParam d.outerParam (H t) = h (circleParam d.outerParam t)

namespace BoundaryLifts

variable {M Γ N : Set Plane} {d : BoundaryCoordinates M Γ N}
variable {g h : Plane ≃ᵃⁱ[ℝ] Plane} (L : BoundaryLifts d g h)

theorem inverse_increasing : StrictMono L.G.symm := by
  intro x y hxy
  by_contra hnot
  have hle : L.G.symm y ≤ L.G.symm x := le_of_not_gt hnot
  have hle' := L.G_increasing.monotone hle
  have hle'' : y ≤ x := by simpa only [L.G.apply_symm_apply] using hle'
  exact hxy.not_ge hle''

theorem inverse_to_left (t : ℝ) :
    g.symm (circleParam d.rightParam t) = circleParam d.leftParam (L.G.symm t) := by
  apply g.injective
  rw [g.apply_symm_apply, ← L.left_to_right, L.G.apply_symm_apply]

/-- The common cut has the opposite direction in the two tile loops. -/
theorem inverse_cut_agrees {t : ℝ} (ht : t ∈ Icc (1 / 2 : ℝ) 1) :
    g.symm (circleParam d.leftParam t) =
      circleParam d.leftParam (L.G.symm (1 - t)) := by
  rw [d.cutAgree t ht, L.inverse_to_left]

theorem inverse_cut_lift_continuous : Continuous (fun t : ℝ => L.G.symm (1 - t)) :=
  L.G.symm.continuous.comp (continuous_const.sub continuous_id)

theorem inverse_cut_lift_antitone : StrictAnti (fun t : ℝ => L.G.symm (1 - t)) := by
  intro s t hst
  apply L.inverse_increasing
  linarith

/-- The map on outer-boundary parameters for one orbit step. -/
def stepParameter (t : ℝ) : ℝ := L.H (L.G.symm t)

theorem stepParameter_continuous : Continuous L.stepParameter :=
  L.H.continuous.comp L.G.symm.continuous

theorem stepParameter_increasing : StrictMono L.stepParameter :=
  L.H_increasing.comp L.inverse_increasing

end BoundaryLifts

end Puzzling139335.CentralRotation
