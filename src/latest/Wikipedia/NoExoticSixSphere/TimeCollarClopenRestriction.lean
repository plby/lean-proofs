import Wikipedia.HopfProblem.DegreeCollapseTimeCollarOverlap
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue

/-!
# Restrict a genuine time collar to a clopen ambient subset

Membership in a clopen subset is constant along each connected collar
interval. The restricted collar therefore has exactly those boundary
points whose original zero points belong to the subset. No connectedness
of the whole boundary is assumed, and every point map is inherited.
-/

noncomputable section

open Set Topology TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

variable {M B : Type*} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B) (U : Opens M)

def clopenBoundary : Opens B :=
  ⟨{b | (C.zeroPoint b).val ∈ U}, U.isOpen.preimage
    (continuous_subtype_val.comp
      (C.coordinates.symm.continuous.comp (continuous_const.prodMk continuous_id)))⟩

theorem clopenBoundary_closed (hU : IsClosed (U : Set M)) :
    IsClosed (C.clopenBoundary U : Set B) :=
  hU.preimage (continuous_subtype_val.comp
    (C.coordinates.symm.continuous.comp (continuous_const.prodMk continuous_id)))

theorem inverse_mem_clopen_iff (hU : IsClosed (U : Set M))
    (s : Ioo (-C.width) C.width) (b : B) :
    (C.coordinates.symm (s, b)).val ∈ U ↔ (C.zeroPoint b).val ∈ U := by
  let f : Ioo (-C.width) C.width → M := fun r ↦ (C.coordinates.symm (r, b)).val
  have hf : Continuous f := continuous_subtype_val.comp
    (C.coordinates.symm.continuous.comp (continuous_id.prodMk continuous_const))
  let : PreconnectedSpace (Ioo (-C.width) C.width) :=
    Subtype.preconnectedSpace isPreconnected_Ioo
  have hc : IsClopen (f ⁻¹' (U : Set M)) := (show IsClopen (U : Set M) from ⟨hU, U.isOpen⟩
    ).preimage hf
  change s ∈ f ⁻¹' (U : Set M) ↔
    (⟨0, neg_lt_zero.mpr C.width_pos, C.width_pos⟩ : Ioo (-C.width) C.width) ∈ f ⁻¹' (U : Set M)
  rcases isClopen_iff.mp hc with he | he <;> rw [he] <;> simp

theorem coordinate_mem_clopenBoundary_iff (hU : IsClosed (U : Set M))
    (p : TimeBand t C.width) : (C.coordinates p).2 ∈ C.clopenBoundary U ↔ p.val ∈ U := by
  have h := C.inverse_mem_clopen_iff U hU (C.coordinates p).1 (C.coordinates p).2
  change (C.coordinates.symm (C.coordinates p)).val ∈ U ↔ _ at h
  rw [C.coordinates.symm_apply_apply] at h
  exact h.symm

def clopenCoordinates (hU : IsClosed (U : Set M)) :
    TimeBand (fun p : U ↦ t p.val) C.width ≃ₜ Ioo (-C.width) C.width × C.clopenBoundary U where
  toFun p :=
    ((C.coordinates ⟨p.val.val, p.property⟩).1,
      ⟨(C.coordinates ⟨p.val.val, p.property⟩).2,
        (C.coordinate_mem_clopenBoundary_iff U hU ⟨p.val.val, p.property⟩).mpr p.val.property⟩)
  invFun q :=
    ⟨⟨(C.coordinates.symm (q.1, q.2.val)).val,
      (C.inverse_mem_clopen_iff U hU q.1 q.2.val).mpr q.2.property⟩,
        (C.coordinates.symm (q.1, q.2.val)).property⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    change (C.coordinates.symm (C.coordinates ⟨p.val.val, p.property⟩)).val = p.val.val
    rw [C.coordinates.symm_apply_apply]
  right_inv q := by
    apply Prod.ext
    · change (C.coordinates (C.coordinates.symm (q.1, q.2.val))).1 = q.1
      exact congrArg (fun p : Ioo (-C.width) C.width × B ↦ p.1)
        (C.coordinates.apply_symm_apply (q.1, q.2.val))
    · apply Subtype.ext
      change (C.coordinates (C.coordinates.symm (q.1, q.2.val))).2 = q.2.val
      exact congrArg (fun p : Ioo (-C.width) C.width × B ↦ p.2)
        (C.coordinates.apply_symm_apply (q.1, q.2.val))
  continuous_toFun := by
    have hc : Continuous (fun p : TimeBand (fun q : U ↦ t q.val) C.width ↦
        C.coordinates ⟨p.val.val, p.property⟩) :=
      C.coordinates.continuous.comp
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    exact (continuous_fst.comp hc).prodMk ((continuous_snd.comp hc).subtype_mk _)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (C.coordinates.symm.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))

def restrictClopen (hU : IsClosed (U : Set M)) :
    TimeCollar (fun p : U ↦ t p.val) (C.clopenBoundary U) where
  width := C.width
  width_pos := C.width_pos
  continuous_time := C.continuous_time.comp continuous_subtype_val
  coordinates := C.clopenCoordinates U hU
  coordinate_time p := C.coordinate_time ⟨p.val.val, p.property⟩

theorem restrictClopen_zeroPoint (hU : IsClosed (U : Set M)) (b : C.clopenBoundary U) :
    ((C.restrictClopen U hU).zeroPoint b).val.val = (C.zeroPoint b.val).val := rfl

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
