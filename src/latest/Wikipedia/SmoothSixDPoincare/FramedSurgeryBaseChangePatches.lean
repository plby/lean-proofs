import Wikipedia.SmoothSixDPoincare.FramedSurgeryBoundaryUpdate

/-!
# A matching change of boundary preserves the original surgery patches

Matching every closed-face coordinate preserves its core and interior.
The original homeomorphism, or native diffeomorphism, restricts to the
actual old patches and carries their exact overlap coordinates.
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
  (e : X ≃ₜ X') (hface : ∀ z, e (A.map z) = A'.map z)

include hface in
omit [FiniteDimensional ℝ E] [T2Space X] [T2Space X'] in
theorem baseChange_symm_face (z : UnitSphere E × MorseHandle.UnitDisk F) :
    e.symm (A'.map z) = A.map z := by
  rw [← hface z, Homeomorph.symm_apply_apply]

include hface in
omit [FiniteDimensional ℝ E] [T2Space X] [T2Space X'] in
theorem baseChange_mem_core_iff (x : X) :
    e x ∈ range (coreMap A') ↔ x ∈ range (coreMap A) := by
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, e.injective ((hface (u, ⟨0, by simp⟩)).trans hu)⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, (hface (u, ⟨0, by simp⟩)).symm.trans (congrArg e hu)⟩

include hface in
theorem baseChange_mem_oldPatch_iff (x : X) : e x ∈ oldPatch A' ↔ x ∈ oldPatch A :=
  not_congr (baseChange_mem_core_iff A A' e hface x)

include hface in
omit [FiniteDimensional ℝ E] [T2Space X] [T2Space X'] in
theorem baseChange_mem_faceInterior_iff (x : X) :
    e x ∈ faceInterior A' ↔ x ∈ faceInterior A := by
  rw [faceInterior_eq_interiorImage, faceInterior_eq_interiorImage]
  constructor
  · rintro ⟨z, hz, he⟩
    exact ⟨z, hz, e.injective ((hface z).trans he)⟩
  · rintro ⟨z, hz, he⟩
    exact ⟨z, hz, (hface z).symm.trans (congrArg e he)⟩

def baseChangeOldHomeomorph : oldPatch A ≃ₜ oldPatch A' where
  toFun x := ⟨e x.val, (baseChange_mem_oldPatch_iff A A' e hface x.val).mpr x.property⟩
  invFun y := ⟨e.symm y.val, (baseChange_mem_oldPatch_iff A' A e.symm
    (baseChange_symm_face A A' e hface) y.val).mpr y.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.val)
  right_inv y := Subtype.ext (e.apply_symm_apply y.val)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem baseChangeOldHomeomorph_coe (x : oldPatch A) :
    (baseChangeOldHomeomorph A A' e hface x).val = e x.val := rfl

theorem baseChangeOldHomeomorph_symm_coe (y : oldPatch A') :
    ((baseChangeOldHomeomorph A A' e hface).symm y).val = e.symm y.val := rfl

theorem baseChangeOldHomeomorph_overlap (z : Overlap E F) :
    baseChangeOldHomeomorph A A' e hface (oldOverlap A z) = oldOverlap A' z :=
  Subtype.ext (hface _)

theorem baseChangeOldHomeomorph_symm :
    (baseChangeOldHomeomorph A A' e hface).symm =
      baseChangeOldHomeomorph A' A e.symm (baseChange_symm_face A A' e hface) := rfl

variable (D : Diffeomorph J J X X' ∞) (hD : ∀ z, D (A.map z) = A'.map z)

def baseChangeOldDiffeomorph : Diffeomorph J J (oldPatch A) (oldPatch A') ∞ where
  toEquiv := (baseChangeOldHomeomorph A A' D.toHomeomorph hD).toEquiv
  contMDiff_toFun := (ContMDiff.subtypeVal_comp_iff (oldPatch A') _).mp
    (D.contMDiff.comp contMDiff_subtype_val)
  contMDiff_invFun := (ContMDiff.subtypeVal_comp_iff (oldPatch A) _).mp
    (D.symm.contMDiff.comp contMDiff_subtype_val)

theorem baseChangeOldDiffeomorph_toHomeomorph :
    (baseChangeOldDiffeomorph A A' D hD).toHomeomorph =
      baseChangeOldHomeomorph A A' D.toHomeomorph hD := rfl

end Wikipedia.SmoothSixDPoincare.FramedSurgery
