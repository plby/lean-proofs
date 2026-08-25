import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.JordanNonzero.ModelRetract
import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.JordanNonzero.PointedPlane
import Wikipedia.JordanCurveTheorem.Brouwer

/-!
# Retracting a punctured plane onto a Jordan boundary

A pointed global Schoenflies map sends the chosen interior point to the origin
and the Jordan curve to the model square's boundary. Radial projection then
gives a retraction back to the original circle parameter.
-/

open Set Schoenflies unitInterval

namespace Puzzling139335.CentralRotation.BoundaryOrientation.JordanNonzero

noncomputable section

/-- A point in the Jordan interior is distinct from every boundary point. -/
theorem circle_ne_inside {f : AddCircle (1 : ℝ) → Plane} {x : Plane}
    (hx : x ∈ inside (range f)) (z : AddCircle (1 : ℝ)) : f z ≠ x := by
  intro h
  exact hx.1 (h ▸ mem_range_self z)

/-- The complement of any interior point retracts to the circle parameter of
an actual Jordan boundary. -/
theorem exists_circle_retraction {f : AddCircle (1 : ℝ) → Plane}
    (hf : Continuous f) (hfi : Function.Injective f) {x : Plane}
    (hx : x ∈ inside (range f)) :
    ∃ R : C(({x}ᶜ : Set Plane), AddCircle (1 : ℝ)),
      ∀ z, R ⟨f z, by
        simpa only [mem_compl_iff, mem_singleton_iff] using circle_ne_inside hx z⟩ = z := by
  have hC := isJordanCurve_range_circle hf hfi
  obtain ⟨e⟩ := hC.homeomorph_modelCurve
  have hzero : (0 : Plane) ∈ inside modelCurve := by
    rw [inside_modelCurve, mem_openSquare_zero_one]
    simp [Plane.supNorm]
  obtain ⟨F, hFe, hFx⟩ := jordan_schoenflies_of_homeomorph_pointed hC
    isJordanCurve_modelCurve e hx hzero
  let k : modelCurve ≃ₜ AddCircle (1 : ℝ) :=
    e.symm.trans (circleRangeHomeomorph hf hfi).symm
  have hFavoids : ∀ p : ({x}ᶜ : Set Plane), F p ∈ ({0}ᶜ : Set Plane) := by
    intro p
    simp only [mem_compl_iff, mem_singleton_iff]
    intro hp
    exact p.property (mem_singleton_iff.mpr (F.injective (hp.trans hFx.symm)))
  let puncturedF : C(({x}ᶜ : Set Plane), ({0}ᶜ : Set Plane)) := {
    toFun := fun p => ⟨F p, hFavoids p⟩
    continuous_toFun := (F.continuous.comp continuous_subtype_val).subtype_mk hFavoids }
  let R : C(({x}ᶜ : Set Plane), AddCircle (1 : ℝ)) :=
    (⟨k, k.continuous⟩ : C(modelCurve, AddCircle (1 : ℝ))).comp
      (modelRadial.comp puncturedF)
  refine ⟨R, fun z => ?_⟩
  have hFz : F (f z) = (e ⟨f z, mem_range_self z⟩ : Plane) :=
    hFe ⟨f z, mem_range_self z⟩
  have hrad : modelRadial (puncturedF ⟨f z, by
      simpa only [mem_compl_iff, mem_singleton_iff] using circle_ne_inside hx z⟩) =
      e ⟨f z, mem_range_self z⟩ := by
    apply Subtype.ext
    change (Plane.supNorm (F (f z)))⁻¹ • F (f z) = _
    rw [hFz, show Plane.supNorm (e ⟨f z, mem_range_self z⟩) = 1 from
      (e ⟨f z, mem_range_self z⟩).property, inv_one, one_smul]
  change k (modelRadial (puncturedF _)) = z
  rw [hrad]
  change (circleRangeHomeomorph hf hfi).symm (e.symm (e _)) = z
  rw [e.symm_apply_apply, circleRangeHomeomorph_symm_apply]

/-- The interval loop which traverses the supplied circle embedding once. -/
def boundaryLoop (f : AddCircle (1 : ℝ) → Plane) (hf : Continuous f) : C(I, Plane) :=
  (⟨f, hf⟩ : C(AddCircle (1 : ℝ), Plane)).comp JordanCurve.Brouwer.acLoop

@[simp] theorem boundaryLoop_apply (f : AddCircle (1 : ℝ) → Plane)
    (hf : Continuous f) (t : I) : boundaryLoop f hf t = f ((t : ℝ) : AddCircle (1 : ℝ)) := rfl

theorem boundaryLoop_closed (f : AddCircle (1 : ℝ) → Plane) (hf : Continuous f) :
    boundaryLoop f hf 1 = boundaryLoop f hf 0 := by
  simp only [boundaryLoop_apply, Set.Icc.coe_one, Set.Icc.coe_zero,
    AddCircle.coe_period, AddCircle.coe_zero]

theorem boundaryLoop_avoids {f : AddCircle (1 : ℝ) → Plane}
    (hf : Continuous f) {x : Plane} (hx : x ∈ inside (range f)) :
    ∀ t, boundaryLoop f hf t ≠ x := fun t => circle_ne_inside hx _

end

end Puzzling139335.CentralRotation.BoundaryOrientation.JordanNonzero
