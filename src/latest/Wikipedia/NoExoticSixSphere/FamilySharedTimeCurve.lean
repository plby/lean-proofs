import Wikipedia.NoExoticSixSphere.FamilySharedTimePairs
import Wikipedia.NoExoticSixSphere.FamilyTrackClosedCurve

/-!
# The closed-double-curve chart in the original shared-time family pair space

The equal-time identification transports the actual track chart to the
original family double-point closure. Its inverse is smooth in the original
ambient pair space, and swapping the source points negates its coordinate.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace NoExoticSixSphere.FamilySharedTimePairs

open CorankOne FamilyFlattening

variable {T E F : Type}
  [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {f : T → E × ℝ → E × F}

def swap (r : T × ((E × ℝ) × (E × ℝ))) : T × ((E × ℝ) × (E × ℝ)) :=
  (r.1, (r.2.2, r.2.1))

omit [NormedSpace ℝ T] [FiniteDimensional ℝ T] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] in
theorem swap_mem_closure {r : T × ((E × ℝ) × (E × ℝ))}
    (hr : r ∈ closure (FamilyEmbedding.doublePoints f)) :
    swap r ∈ closure (FamilyEmbedding.doublePoints f) := by
  have hm : MapsTo swap (FamilyEmbedding.doublePoints f) (FamilyEmbedding.doublePoints f) :=
    fun _ hq ↦ ⟨hq.1.symm, hq.2.symm⟩
  exact hm.closure
    (continuous_fst.prodMk (continuous_snd.snd.prodMk continuous_snd.fst)) hr

def swapClosure (f : T → E × ℝ → E × F) :
    closure (FamilyEmbedding.doublePoints f) ≃ₜ closure (FamilyEmbedding.doublePoints f) where
  toFun r := ⟨swap r.val, swap_mem_closure r.property⟩
  invFun r := ⟨swap r.val, swap_mem_closure r.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun :=
    ((continuous_fst.prodMk (continuous_snd.snd.prodMk continuous_snd.fst)).comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((continuous_fst.prodMk (continuous_snd.snd.prodMk continuous_snd.fst)).comp
      continuous_subtype_val).subtype_mk _

omit [FiniteDimensional ℝ T] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] in
theorem closedPairHomeomorph_swap (f : T → E × ℝ → E × F)
    (r : closure (FamilyEmbedding.doublePoints f)) :
    closedPairHomeomorph f (swapClosure f r) =
      swapTrackClosure f (closedPairHomeomorph f r) := Subtype.ext rfl

theorem exists_shared_closed_curve (hf : ContDiff ℝ ∞ (uncurry f)) (d : Data f)
    (q : E × (T × ℝ)) (hq : q ∈ d.coord.source) (hz : residual (spatial f q) = 0)
    (hb : Bijective (fderiv ℝ (fun r ↦ residual (spatial f r)) q)) :
    ∃ hc : fromTrack (q, q) ∈ closure (FamilyEmbedding.doublePoints f),
    ∃ c : OpenPartialHomeomorph (closure (FamilyEmbedding.doublePoints f)) ℝ,
      (⟨fromTrack (q, q), hc⟩ : closure (FamilyEmbedding.doublePoints f)) ∈ c.source ∧
      c ⟨fromTrack (q, q), hc⟩ = 0 ∧
      (∀ r ∈ c.source, c r = (r.val.2.1.2 - r.val.2.2.2) / 2) ∧
      (∀ r ∈ c.source, swapClosure f r ∈ c.source) ∧
      (∀ r ∈ c.source, c (swapClosure f r) = -c r) ∧
      ContDiffOn ℝ ∞ (fun s ↦ (c.symm s).val) c.target := by
  obtain ⟨htrack, k, hkq, hkzero, hkapply, hkswap, hkneg, hksmooth⟩ :=
    d.exists_track_closed_curve hf q hq hz hb
  have hc : fromTrack (q, q) ∈ closure (FamilyEmbedding.doublePoints f) :=
    (fromTrack_doublePoints f).closure contDiff_fromTrack.continuous htrack
  let s₀ : closure (FamilyEmbedding.doublePoints f) := ⟨fromTrack (q, q), hc⟩
  let t₀ : closure (trackDoublePoints f) := ⟨(q, q), htrack⟩
  let e := closedPairHomeomorph f
  have he₀ : e s₀ = t₀ := Subtype.ext (toTrack_fromTrack (q, q) rfl)
  let c := e.toOpenPartialHomeomorph.trans k
  have hcq : s₀ ∈ c.source := by
    refine ⟨mem_univ _, ?_⟩
    change e s₀ ∈ k.source
    rw [he₀]
    exact hkq
  have hcapply : ∀ r ∈ c.source, c r = (r.val.2.1.2 - r.val.2.2.2) / 2 := by
    intro r hr
    change k (e r) = _
    exact hkapply (e r) hr.2
  have hcswap : ∀ r ∈ c.source, swapClosure f r ∈ c.source := by
    intro r hr
    refine ⟨mem_univ _, ?_⟩
    change closedPairHomeomorph f (swapClosure f r) ∈ k.source
    rw [closedPairHomeomorph_swap]
    exact hkswap (e r) hr.2
  refine ⟨hc, c, hcq, ?_, hcapply, hcswap, ?_, ?_⟩
  · change k (e s₀) = 0
    rw [he₀]
    exact hkzero
  · intro r hr
    rw [hcapply _ (hcswap r hr), hcapply r hr]
    change (r.val.2.2.2 - r.val.2.1.2) / 2 = -((r.val.2.1.2 - r.val.2.2.2) / 2)
    ring
  · exact contDiff_fromTrack.comp_contDiffOn (hksmooth.mono (fun _ hs ↦ hs.1))

end NoExoticSixSphere.FamilySharedTimePairs
