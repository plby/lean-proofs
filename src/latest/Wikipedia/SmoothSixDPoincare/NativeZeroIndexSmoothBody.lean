import Wikipedia.SmoothSixDPoincare.NativeZeroIndexBoundary
import Wikipedia.SmoothSixDPoincare.ZeroIndexOpenComponents
import Wikipedia.SmoothSixDPoincare.NativeOpenSurgeryExterior
import Wikipedia.SmoothSixDPoincare.NativeSmoothBoundaryBodies
import Wikipedia.SmoothSixDPoincare.SmoothBoundaryBodySum

/-!
# The native disk birth as an exact smooth-boundary body equivalence

The born boundary inherits its smooth atlas as an open component of the
actual upper level. Its disk inclusion uses the actual belt coordinates.
The retained boundary map is the constructed smooth common-exterior map.
Thus the disjoint-sum realization has a native smooth boundary restriction.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)
  (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 0)

open Classical in
def zeroIndexBornOpen : TopologicalSpace.Opens d.UpperLevel := by
  let _ : Subsingleton d.chart.NegativeCoordinates := Module.finrank_zero_iff.mp hindex
  exact d.surgery.bornOpen

open Classical in
def zeroIndexBornCoordinates :
    PuncturedHandle.UnitSphere d.chart.PositiveCoordinates ≃ₜ d.zeroIndexBornOpen hindex := by
  let _ : Subsingleton d.chart.NegativeCoordinates := Module.finrank_zero_iff.mp hindex
  exact d.surgery.bornCoordinates

open Classical in
theorem zeroIndexBornCoordinates_symm (y : d.zeroIndexBornOpen hindex) :
    d.surgery.beltSphere ((d.zeroIndexBornCoordinates hindex).symm y) = y.val := by
  let _ : Subsingleton d.chart.NegativeCoordinates := Module.finrank_zero_iff.mp hindex
  exact d.surgery.bornCoordinates_symm_coe y

open Classical in
def zeroIndexDiskInclusion :
    C(d.zeroIndexBornOpen hindex, MorseHandle.UnitDisk d.chart.PositiveCoordinates) :=
  ⟨fun y => ⟨((d.zeroIndexBornCoordinates hindex).symm y).val,
      sphere_subset_closedBall ((d.zeroIndexBornCoordinates hindex).symm y).property⟩,
    (continuous_subtype_val.comp (d.zeroIndexBornCoordinates hindex).symm.continuous).subtype_mk _⟩

open Classical in
theorem zeroIndexDiskInclusion_isClosedEmbedding :
    IsClosedEmbedding (d.zeroIndexDiskInclusion hindex) := by
  let _ : CompactSpace (d.zeroIndexBornOpen hindex) :=
    (d.zeroIndexBornCoordinates hindex).compactSpace
  apply (d.zeroIndexDiskInclusion hindex).continuous.isClosedEmbedding
  intro x y h
  apply (d.zeroIndexBornCoordinates hindex).symm.injective
  exact Subtype.ext (congrArg (fun u : MorseHandle.UnitDisk d.chart.PositiveCoordinates => u.val) h)

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
def zeroIndexDiskBody : SmoothBoundaryBody 𝓘(ℝ, RegularLevel.Model E) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ := RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace (d.zeroIndexBornOpen hindex) :=
    (d.zeroIndexBornCoordinates hindex).compactSpace
  exact SmoothBoundaryBody.ofEmbedding (d.zeroIndexDiskInclusion hindex)
    (d.zeroIndexDiskInclusion_isClosedEmbedding hindex)

variable (hd : d.HasSmoothExterior hf)

open Classical in
def zeroIndexBoundaryDiffeomorph :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
      (d.LowerLevel ⊕ d.zeroIndexBornOpen hindex) d.UpperLevel ∞ := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : Subsingleton d.chart.NegativeCoordinates := Module.finrank_zero_iff.mp hindex
  let e := d.surgery.zeroIndexOldDiffeomorph.trans (d.openExteriorDiffeomorph hf hd)
  exact (e.sumCongr (Diffeomorph.refl 𝓘(ℝ, RegularLevel.Model E) d.surgery.bornOpen ∞)).trans
    d.surgery.zeroIndexPartitionDiffeomorph

omit [T2Space M] [CompactSpace M] in
open Classical in
theorem zeroIndexBoundaryDiffeomorph_old (x : d.LowerLevel) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    d.zeroIndexBoundaryDiffeomorph hindex hf hd (Sum.inl x) =
      d.zeroIndexBoundaryHomeomorph hindex (Sum.inl x) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : Subsingleton d.chart.NegativeCoordinates := Module.finrank_zero_iff.mp hindex
  exact d.surgery.zeroIndexOldCoordinates_exterior x

omit [T2Space M] [CompactSpace M] in
open Classical in
theorem zeroIndexBoundaryDiffeomorph_born (y : d.zeroIndexBornOpen hindex) :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    d.zeroIndexBoundaryDiffeomorph hindex hf hd (Sum.inr y) = y.val := rfl

open Classical in
def zeroIndexSmoothBodyEquiv : SmoothBoundaryBody.Equiv
    ((d.lowerSmoothBody hf).sum (d.zeroIndexDiskBody hindex hf)) (d.upperSmoothBody hf) := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  refine {
    body := d.zeroIndexSublevelHomeomorph hf.continuous hindex
    boundary := d.zeroIndexBoundaryDiffeomorph hindex hf hd
    boundary_point := ?_ }
  intro x
  cases x with
  | inl x =>
      apply Subtype.ext
      exact (d.zeroIndexBoundaryHomeomorph_old_body hf.continuous hindex x).symm.trans
        (congrArg (fun y : d.UpperLevel => y.val)
          (d.zeroIndexBoundaryDiffeomorph_old hindex hf hd x)).symm
  | inr y =>
      apply Subtype.ext
      let v := (d.zeroIndexBornCoordinates hindex).symm y
      have h := (d.zeroIndexBoundaryHomeomorph_disk_body hf.continuous hindex v).symm
      rw [d.zeroIndexBoundaryHomeomorph_belt] at h
      exact h.trans (congrArg (fun z : d.UpperLevel => z.val)
        (d.zeroIndexBornCoordinates_symm hindex y))

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
