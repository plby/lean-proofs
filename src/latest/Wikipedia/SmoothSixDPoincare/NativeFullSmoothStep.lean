import Wikipedia.SmoothSixDPoincare.FullSmoothHandleChain
import Wikipedia.SmoothSixDPoincare.NativeZeroIndexSmoothBody
import Wikipedia.SmoothSixDPoincare.NativeTopIndexSmoothBody
import Wikipedia.SmoothSixDPoincare.NativeZeroIndexSphereDiffeomorph

/-!
# Every native Morse step has a full smooth-chain realization

There is no interior-index restriction. The zero and top indices use the
constructed disk birth and disk cap; all other indices use the corrected
native framed realization. The exact index and original old-sublevel map
are retained in every case.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
def zeroIndexSmoothDisk (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 0) :
    SmoothBoundaryDisk 𝓘(ℝ, RegularLevel.Model E) d.chart.PositiveCoordinates where
  space := d.zeroIndexDiskBody hindex hf
  bodyCoordinates := Homeomorph.refl _
  boundaryCoordinates := (d.zeroIndexBornCoordinates hindex).symm
  boundary_point _ := rfl
  boundarySphere n hn := by
    let _ : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1) := ⟨hn⟩
    let _ := RegularLevel.chartedSpace hf d.upper_regular
    exact ⟨(d.zeroIndexBornDiffeomorph hindex hf n).symm.trans
      (SphereCoordinates.standardParametrization d.chart.PositiveCoordinates n).symm⟩

open Classical in
theorem exists_fullSmoothStep (hd : d.HasSmoothExterior hf) :
    ∃ c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (Module.finrank ℝ E)
        (d.lowerSmoothBody hf) (d.upperSmoothBody hf) 1,
      c.indices = [Module.finrank ℝ d.chart.NegativeCoordinates] ∧
      ∀ x : (d.lowerSmoothBody hf).body,
        c.sourceMap x = d.attachmentHomeomorph ⟨x.val, Or.inl x.property⟩ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  have hsplit := d.chart.finrank_negative_add_positive
  by_cases hzero : Module.finrank ℝ d.chart.NegativeCoordinates = 0
  · have hpos : Module.finrank ℝ d.chart.PositiveCoordinates = Module.finrank ℝ E := by omega
    let c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (Module.finrank ℝ E)
        (d.lowerSmoothBody hf) (d.upperSmoothBody hf) 1 :=
      .birth (d.zeroIndexSmoothDisk hf hzero) hpos (d.zeroIndexSmoothBodyEquiv hzero hf hd)
        (.nil (SmoothBoundaryBodyEquiv.refl (d.upperSmoothBody hf).inclusion))
    refine ⟨c, ?_, ?_⟩
    · change [0] = [Module.finrank ℝ d.chart.NegativeCoordinates]
      rw [hzero]
    · intro x
      exact d.zeroIndexSublevelHomeomorph_old hf.continuous hzero x
  by_cases htop : Module.finrank ℝ d.chart.NegativeCoordinates = Module.finrank ℝ E
  · let c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (Module.finrank ℝ E)
        (d.lowerSmoothBody hf) (d.upperSmoothBody hf) 1 :=
      .cap d.surgery.attachingSphere d.attaching_isClosedEmbedding
        (d.topIndex_attaching_isOpen htop) htop (d.topIndexSmoothBodyEquiv htop hf hd)
        (.nil (SmoothBoundaryBodyEquiv.refl (d.upperSmoothBody hf).inclusion))
    refine ⟨c, rfl, ?_⟩
    intro x
    exact d.topIndexCapBodyRealization_old htop hf x
  let m := Module.finrank ℝ d.chart.NegativeCoordinates - 1
  let n := Module.finrank ℝ d.chart.PositiveCoordinates - 1
  let _ : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1) :=
    ⟨by dsimp [m]; omega⟩
  let _ : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1) :=
    ⟨by dsimp [n]; omega⟩
  obtain ⟨P⟩ := d.nonempty_framedSmoothBoundaryData hf m n
  let c : FullSmoothHandleChain 𝓘(ℝ, RegularLevel.Model E) (Module.finrank ℝ E)
      (d.lowerSmoothBody hf) (d.upperSmoothBody hf) 1 :=
    .interior (d.attachingSmoothFace hf m) P hsplit (d.beltSmoothBodyEquiv hf m n P hd)
      (.nil (SmoothBoundaryBodyEquiv.refl (d.upperSmoothBody hf).inclusion))
  refine ⟨c, rfl, ?_⟩
  intro x
  exact d.beltFramedBodyRealization_old hf m x

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
