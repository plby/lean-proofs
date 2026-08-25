import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree.Defs

/-!
# Homotopy invariance of circle-path displacement

A lift of a homotopy of closed circle paths has a continuous endpoint
difference.  The image of that difference in the circle is zero, so uniqueness
of lifts makes it constant.  In particular, the starting point of the loops
need not stay fixed during the homotopy.
-/

noncomputable section

namespace Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree

open Set unitInterval

/-- A path at a fixed time in a homotopy of circle-valued paths. -/
def slice (H : C(I × I, Circle)) (s : I) : C(I, Circle) := H.curry s

@[simp] theorem slice_apply (H : C(I × I, Circle)) (s t : I) :
    slice H s t = H (s, t) := rfl

/-- Displacement is constant throughout a free homotopy of closed paths. -/
theorem displacement_slice_eq (H : C(I × I, Circle))
    (hclosed : ∀ s, H (s, 1) = H (s, 0)) (s t : I) :
    displacement (slice H s) = displacement (slice H t) := by
  let Γ : C(I × I, ℝ) := cover.liftHomotopy H (pathLift (slice H 0))
    (fun u => (coe_pathLift (slice H 0) u).symm)
  have hΓ (a b : I) : (Γ (a, b) : Circle) = H (a, b) :=
    congr_fun (cover.liftHomotopy_lifts H (pathLift (slice H 0))
      (fun u => (coe_pathLift (slice H 0) u).symm)) (a, b)
  have hd (a : I) :
      displacement (slice H a) = Γ (a, 1) - Γ (a, 0) :=
    displacement_eq_sub_of_lift (slice H a) (Γ.curry a) (hΓ a)
  rw [hd s, hd t]
  apply cover.const_of_comp
    ((Γ.continuous.comp (continuous_id.prodMk continuous_const)).sub
      (Γ.continuous.comp (continuous_id.prodMk continuous_const))) _ s t
  intro a b
  change ((Γ (a, 1) - Γ (a, 0) : ℝ) : Circle) =
    ((Γ (b, 1) - Γ (b, 0) : ℝ) : Circle)
  simp only [AddCircle.coe_sub, hΓ, hclosed, sub_self]

@[simp] theorem slice_homotopy_zero {γ δ : C(I, Circle)} (H : γ.Homotopy δ) :
    slice H.toContinuousMap 0 = γ := by
  ext t
  exact H.apply_zero t

@[simp] theorem slice_homotopy_one {γ δ : C(I, Circle)} (H : γ.Homotopy δ) :
    slice H.toContinuousMap 1 = δ := by
  ext t
  exact H.apply_one t

/-- The endpoints of a free homotopy of closed paths have equal displacement. -/
theorem displacement_eq_of_homotopy {γ δ : C(I, Circle)} (H : γ.Homotopy δ)
    (hclosed : ∀ s, H (s, 1) = H (s, 0)) : displacement γ = displacement δ := by
  simpa only [slice_homotopy_zero, slice_homotopy_one] using
    displacement_slice_eq H.toContinuousMap hclosed 0 1

/-- Relative homotopies preserve displacement, also for paths that are not closed. -/
theorem displacement_eq_of_homotopicRel {γ δ : C(I, Circle)}
    (h : γ.HomotopicRel δ {0, 1}) : displacement γ = displacement δ := by
  have hstart : δ 0 = (baseLift γ : Circle) := by
    rw [coe_baseLift]
    exact (h.fst_eq_snd (by simp)).symm
  rw [displacement_eq_liftPath γ (baseLift γ) (coe_baseLift γ).symm,
    displacement_eq_liftPath δ (baseLift γ) hstart]
  rw [cover.liftPath_apply_one_eq_of_homotopicRel h (baseLift γ)
    (coe_baseLift γ).symm hstart]

/-- A path of zero displacement contracts to its initial point while fixing
both endpoints.  The contraction is the projection of a straight homotopy
between its closed real lift and the constant lift. -/
def contractionOfDisplacementZero (γ : C(I, Circle)) (h : displacement γ = 0) :
    γ.HomotopyRel (ContinuousMap.const I (γ 0)) {0, 1} where
  toFun x := (((1 - (x.1 : ℝ)) * pathLift γ x.2 +
    (x.1 : ℝ) * pathLift γ 0 : ℝ) : Circle)
  continuous_toFun := cover.continuous.comp
    (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((pathLift γ).continuous.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).mul continuous_const))
  map_zero_left := by
    intro t
    change (((1 - (0 : ℝ)) * pathLift γ t + 0 * pathLift γ 0 : ℝ) : Circle) = γ t
    simp only [sub_zero, one_mul, zero_mul, add_zero, coe_pathLift]
  map_one_left := by
    intro t
    change (((1 - (1 : ℝ)) * pathLift γ t + 1 * pathLift γ 0 : ℝ) : Circle) = γ 0
    simp only [sub_self, zero_mul, one_mul, zero_add, coe_pathLift]
  prop' := by
    intro s t ht
    change (((1 - (s : ℝ)) * pathLift γ t + (s : ℝ) * pathLift γ 0 : ℝ) : Circle) = γ t
    have hlift : pathLift γ 1 = pathLift γ 0 := sub_eq_zero.mp h
    have hlinear (a : ℝ) : (1 - (s : ℝ)) * a + (s : ℝ) * a = a := by ring
    rcases (show t = 0 ∨ t = 1 from by simpa only [mem_insert_iff, mem_singleton_iff] using ht)
      with rfl | rfl
    · simp only [hlinear, coe_pathLift]
    · simp only [hlift, hlinear]
      exact ((coe_pathLift γ 1).symm.trans
        (congrArg (fun r : ℝ => (r : Circle)) hlift)).symm

/-- A circle-valued path has zero displacement exactly when it contracts
relative to its endpoints. -/
theorem displacement_eq_zero_iff_homotopicRel_const (γ : C(I, Circle)) :
    displacement γ = 0 ↔ γ.HomotopicRel (ContinuousMap.const I (γ 0)) {0, 1} := by
  constructor
  · intro h
    exact ⟨contractionOfDisplacementZero γ h⟩
  · intro h
    simpa only [displacement_const] using displacement_eq_of_homotopicRel h

end Puzzling139335.CentralRotation.BoundaryOrientation.CircleDegree

end
