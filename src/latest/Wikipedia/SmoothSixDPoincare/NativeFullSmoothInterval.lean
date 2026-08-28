import Wikipedia.SmoothSixDPoincare.NativeFullSmoothStep
import Wikipedia.SmoothSixDPoincare.NativeSmoothHandleStages
import Wikipedia.SmoothSixDPoincare.SmoothSurgeryWindows
import Wikipedia.SmoothSixDPoincare.FullSmoothHandleChainAppend
import Wikipedia.SmoothSixDPoincare.FullSmoothHandleChainRetarget
import Wikipedia.SmoothSixDPoincare.FullSmoothHandleChainLength

/-!
# Full smooth chains through every original native Morse interval

The interval includes every critical index, including births and caps.
Its consecutive regular bands are the original retained band data. The
constructed chain has exactly the original finite index order and its
complete source map is the actual iterated native sublevel map.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
  (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

def intervalEnd (i : Fin S.count) (n : ℕ) (h : i.val + n < S.count) : Fin S.count :=
  ⟨i.val + n, h⟩

def intervalIndices (i : Fin S.count) : (n : ℕ) → (h : i.val + n < S.count) → List ℕ
  | 0, _ => [Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates]
  | n + 1, h =>
      intervalIndices i n (by omega) ++
        [Module.finrank ℝ (S.data (S.point (S.intervalEnd i (n + 1) h))).chart.NegativeCoordinates]

def intervalSource (i : Fin S.count) : (n : ℕ) → (h : i.val + n < S.count) →
    ((S.data (S.point i)).lowerSmoothBody hf).body →
      ((S.data (S.point (S.intervalEnd i n h))).upperSmoothBody hf).body
  | 0, _, x => (S.data (S.point i)).attachmentHomeomorph ⟨x.val, Or.inl x.property⟩
  | n + 1, h, x =>
      let prev := S.intervalEnd i n (by omega)
      let last := S.intervalEnd i (n + 1) h
      let B := S.consecutiveBandData hf prev last (by dsimp [prev, last, intervalEnd]; omega)
      let y := B.sublevelHomeomorph (intervalSource i n (by omega) x)
      (S.data (S.point last)).attachmentHomeomorph ⟨y.val, Or.inl y.property⟩

open Classical in
theorem exists_fullSmoothInterval (hs : S.HasSmoothExteriors hf) (i : Fin S.count)
    (n : ℕ) (h : i.val + n < S.count) :
    ∃ c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (Module.finrank ℝ E)
        ((S.data (S.point i)).lowerSmoothBody hf)
        ((S.data (S.point (S.intervalEnd i n h))).upperSmoothBody hf) (n + 1),
      c.indices = S.intervalIndices i n h ∧
      ∀ x, c.sourceMap x = S.intervalSource hf i n h x := by
  induction n with
  | zero => exact (S.data (S.point i)).exists_fullSmoothStep hf (hs (S.point i))
  | succ n ih =>
      have hp : i.val + n < S.count := by omega
      let prev := S.intervalEnd i n hp
      let last := S.intervalEnd i (n + 1) h
      let B := S.consecutiveBandData hf prev last (by dsimp [prev, last, intervalEnd]; omega)
      obtain ⟨c, hc, hcx⟩ := ih hp
      obtain ⟨d, hd, hdx⟩ := (S.data (S.point last)).exists_fullSmoothStep hf (hs (S.point last))
      let e := B.smoothBodyEquiv hf
      let a := (c.retarget e).append d
      let b := a.castLength (show 1 + (n + 1) = (n + 1) + 1 by omega)
      refine ⟨b, ?_, ?_⟩
      · change (a.castLength _).indices = _
        rw [FullSmoothHandleChain.castLength_indices]
        exact ((c.retarget e).append_indices d).trans
          (congrArg₂ List.append ((c.retarget_indices e).trans hc) hd)
      · intro x
        change (a.castLength _).sourceMap x = _
        rw [FullSmoothHandleChain.castLength_sourceMap]
        have he := (c.retarget_sourceMap e x).trans (congrArg e.body (hcx x))
        exact ((c.retarget e).append_sourceMap d x).trans
          ((congrArg d.sourceMap he).trans (hdx _))

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SurgeryWindows
