import Wikipedia.NoExoticSixSphere.FamilyFlatteningPairCoordinates
import Wikipedia.NoExoticSixSphere.PartialHomeomorphSubsets
import Wikipedia.NoExoticSixSphere.FlatLocalClosedDoubleCurve

/-!
# A closed-double-curve chart on the original family track pair space

The actual source-coordinate change transports the flat chart to the
original track double-point closure. Its ambient inverse remains smooth,
and its signed separation coordinate still changes sign under swapping.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace NoExoticSixSphere.FamilyFlattening

open CorankOne SymmetricDifference FlatDoubleCurve

variable {T E F : Type}
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : T → E × ℝ → E × F}

omit [NormedSpace ℝ T] [FiniteDimensional ℝ T] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] in
theorem swap_mem_closedTrackDoublePoints {r : (E × (T × ℝ)) × (E × (T × ℝ))}
    (hr : r ∈ closure (trackDoublePoints f)) : r.swap ∈ closure (trackDoublePoints f) := by
  have hm : MapsTo Prod.swap (trackDoublePoints f) (trackDoublePoints f) :=
    fun _ hq ↦ ⟨hq.1.symm, hq.2.symm⟩
  exact hm.closure continuous_swap hr

def swapTrackClosure (f : T → E × ℝ → E × F) :
    closure (trackDoublePoints f) ≃ₜ closure (trackDoublePoints f) where
  toFun r := ⟨r.val.swap, swap_mem_closedTrackDoublePoints r.property⟩
  invFun r := ⟨r.val.swap, swap_mem_closedTrackDoublePoints r.property⟩
  left_inv r := Subtype.ext (Prod.swap_swap r.val)
  right_inv r := Subtype.ext (Prod.swap_swap r.val)
  continuous_toFun := (continuous_swap.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_swap.comp continuous_subtype_val).subtype_mk _

theorem Data.exists_track_closed_curve (hf : ContDiff ℝ ∞ (uncurry f)) (d : Data f)
    (q : E × (T × ℝ)) (hq : q ∈ d.coord.source) (hz : residual (spatial f q) = 0)
    (hb : Bijective (fderiv ℝ (fun r ↦ residual (spatial f r)) q)) :
    ∃ hc : (q, q) ∈ closure (trackDoublePoints f),
    ∃ c : OpenPartialHomeomorph (closure (trackDoublePoints f)) ℝ,
      (⟨(q, q), hc⟩ : closure (trackDoublePoints f)) ∈ c.source ∧
      c ⟨(q, q), hc⟩ = 0 ∧
      (∀ r ∈ c.source, c r = (r.val.1.2.2 - r.val.2.2.2) / 2) ∧
      (∀ r ∈ c.source, swapTrackClosure f r ∈ c.source) ∧
      (∀ r ∈ c.source, c (swapTrackClosure f r) = -c r) ∧
      ContDiffOn ℝ ∞ (fun s ↦ (c.symm s).val) c.target := by
  have ht := d.forward_mem_target hq
  have hv : vertical d.flattened (d.forward q) = 0 := by
    rw [d.vertical_flattened_eq hf ht, d.inverse_forward hq]
    exact hz
  have hD : Bijective (fderiv ℝ (vertical d.flattened) (d.forward q)) := by
    apply d.bijective_fderiv_vertical hf ht
    simpa only [d.inverse_forward hq] using hb
  obtain ⟨hflat, k, hkq, hkzero, hkapply, hkswap, hkneg, hksmooth⟩ :=
    exists_local_closed_double_curve_chart d.flattened d.target.isOpen
      (d.contDiffOn_flattened hf) (d.forward q) ht hv hD
  have hc : (q, q) ∈ closure (trackDoublePoints f) :=
    (d.isImage_closedTrackDoublePoints (x := (q, q)) ⟨hq, hq⟩).mp hflat
  let s₀ : closure (trackDoublePoints f) := ⟨(q, q), hc⟩
  let t₀ : closure (doublePoints d.flattened) := ⟨(d.forward q, d.forward q), hflat⟩
  let e := SubsetCoordinates.coordinates d.pairCoordinates
    d.isImage_closedTrackDoublePoints s₀ t₀
  have eval {r : closure (trackDoublePoints f)} (hr : r ∈ e.source) :
      (e r).val = d.pairCoordinates r.val :=
    SubsetCoordinates.coordinates_val _ _ _ _ hr
  have he₀ : e s₀ = t₀ := Subtype.ext (eval ⟨hq, hq⟩)
  let c := e.trans k
  have hcq : s₀ ∈ c.source := by
    refine ⟨⟨hq, hq⟩, ?_⟩
    change e s₀ ∈ k.source
    rw [he₀]
    exact hkq
  have hcapply : ∀ r ∈ c.source, c r = (r.val.1.2.2 - r.val.2.2.2) / 2 := by
    intro r hr
    change k (e r) = _
    rw [hkapply (e r) hr.2, eval hr.1]
    change ((d.forward r.val.1).2 - (d.forward r.val.2).2) / 2 = _
    rw [d.forward_apply, d.forward_apply]
  have hcswap : ∀ r ∈ c.source, swapTrackClosure f r ∈ c.source := by
    intro r hr
    have hs : swapTrackClosure f r ∈ e.source := ⟨hr.1.2, hr.1.1⟩
    have hswap : e (swapTrackClosure f r) = swapClosure d.flattened (e r) := by
      apply Subtype.ext
      rw [eval hs]
      change (d.forward r.val.2, d.forward r.val.1) = Prod.swap (e r).val
      rw [eval hr.1]
      rfl
    refine ⟨hs, ?_⟩
    change e (swapTrackClosure f r) ∈ k.source
    rw [hswap]
    exact hkswap (e r) hr.2
  refine ⟨hc, c, hcq, ?_, hcapply, hcswap, ?_, ?_⟩
  · change k (e s₀) = 0
    rw [he₀]
    exact hkzero
  · intro r hr
    rw [hcapply _ (hcswap r hr), hcapply r hr]
    change (r.val.2.2.2 - r.val.1.2.2) / 2 = -((r.val.1.2.2 - r.val.2.2.2) / 2)
    ring
  · have htarget : c.target ⊆ k.target := fun _ hs ↦ hs.1
    have hmaps : MapsTo (fun s ↦ (k.symm s).val) c.target d.pairCoordinates.target :=
      fun _ hs ↦ hs.2
    apply (d.contDiffOn_pairInverse.comp (hksmooth.mono htarget) hmaps).congr
    intro s hs
    change (e.symm (k.symm s)).val = d.pairCoordinates.symm (k.symm s).val
    exact SubsetCoordinates.coordinates_symm_val _ _ _ _ hs.2

end NoExoticSixSphere.FamilyFlattening
