import Wikipedia.SmoothSixDPoincare.FramedSurgeryBaseChangePatches
import Wikipedia.SmoothSixDPoincare.OpenGluingCongr

/-!
# The exact surgery-boundary homeomorphism induced by matching framed faces

Changing the original boundary changes only the old patch. Every new
handle-patch coordinate and every closed positive-face coordinate is
unchanged, including the common corner.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X X' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {J : ModelWithCorners ℝ G H}
  [TopologicalSpace X] [T2Space X] [ChartedSpace H X]
  [TopologicalSpace X'] [T2Space X'] [ChartedSpace H X']
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (A' : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X')
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]
  (e : X ≃ₜ X') (hface : ∀ z, e (A.map z) = A'.map z)

theorem baseChange_overlap_iff (x : oldPatch A) (y : NewPatch E F) :
    oldMap A n x = newMap A n y ↔
      oldMap A' n (baseChangeOldHomeomorph A A' e hface x) = newMap A' n y := by
  rw [old_eq_new_iff, old_eq_new_iff]
  constructor
  · rintro ⟨z, hx, hy⟩
    exact ⟨z, (baseChangeOldHomeomorph_overlap A A' e hface z).symm.trans
      (congrArg (baseChangeOldHomeomorph A A' e hface) hx), hy⟩
  · rintro ⟨z, hx, hy⟩
    exact ⟨z, (baseChangeOldHomeomorph A A' e hface).injective
      ((baseChangeOldHomeomorph_overlap A A' e hface z).trans hx), hy⟩

def baseChangeBoundary : Boundary A n ≃ₜ Boundary A' n :=
  OpenGluing.congr (transition A n) (transition A' n)
    (baseChangeOldHomeomorph A A' e hface) (Homeomorph.refl (NewPatch E F))
    (baseChange_overlap_iff A A' n e hface)

theorem baseChangeBoundary_old (x : oldPatch A) :
    baseChangeBoundary A A' n e hface (oldMap A n x) =
      oldMap A' n (baseChangeOldHomeomorph A A' e hface x) := rfl

theorem baseChangeBoundary_new (y : NewPatch E F) :
    baseChangeBoundary A A' n e hface (newMap A n y) = newMap A' n y := rfl

theorem baseChangeBoundary_symm :
    (baseChangeBoundary A A' n e hface).symm =
      baseChangeBoundary A' A n e.symm (baseChange_symm_face A A' e hface) := rfl

theorem baseChangeBoundary_closedNewMap (p : ClosedNewFace E F) :
    baseChangeBoundary A A' n e hface (closedNewMap A n p) = closedNewMap A' n p := by
  by_cases hn : ‖p.1.val‖ < 1
  · let y : NewPatch E F := (⟨p.1.val, mem_ball_zero_iff.mpr hn⟩, p.2)
    exact (congrArg (baseChangeBoundary A A' n e hface) (closedNewMap_open A n y)).trans
      ((baseChangeBoundary_new A A' n e hface y).trans (closedNewMap_open A' n y).symm)
  · have he : ‖p.1.val‖ = 1 :=
      le_antisymm (mem_closedBall_zero_iff.mp p.1.property) (le_of_not_gt hn)
    let u : UnitSphere E := ⟨p.1.val, mem_sphere_zero_iff_norm.mpr he⟩
    have hc : baseChangeOldHomeomorph A A' e hface (oldClosedOverlap A (u, boundaryPoint p.2)) =
        oldClosedOverlap A' (u, boundaryPoint p.2) := Subtype.ext (hface _)
    exact (congrArg (baseChangeBoundary A A' n e hface) (closedNewMap_corner A n u p.2)).trans
      ((baseChangeBoundary_old A A' n e hface _).trans
        ((congrArg (oldMap A' n) hc).trans (closedNewMap_corner A' n u p.2).symm))

theorem baseChangeBoundary_refl :
    baseChangeBoundary A A n (Homeomorph.refl X) (fun _ => rfl) = Homeomorph.refl _ := by
  ext z
  rcases cover A n z with ⟨x, rfl⟩ | ⟨y, rfl⟩ <;> rfl

variable {X'' : Type*} [TopologicalSpace X''] [T2Space X''] [ChartedSpace H X'']
  (A'' : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X'')
  (f : X' ≃ₜ X'') (hface' : ∀ z, f (A'.map z) = A''.map z)

theorem baseChangeBoundary_trans :
    (baseChangeBoundary A A' n e hface).trans (baseChangeBoundary A' A'' n f hface') =
      baseChangeBoundary A A'' n (e.trans f)
        (fun z => (congrArg f (hface z)).trans (hface' z)) := by
  ext z
  rcases cover A n z with ⟨x, rfl⟩ | ⟨y, rfl⟩ <;> rfl

end Wikipedia.SmoothSixDPoincare.FramedSurgery
