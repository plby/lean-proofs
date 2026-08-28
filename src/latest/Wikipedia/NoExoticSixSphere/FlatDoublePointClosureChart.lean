import Wikipedia.NoExoticSixSphere.FlatDoublePointClosure

/-!
# Transferring the actual zero-curve chart to the actual double-point closure

Recovery is continuous on the original closure subtype and reconstructs
every source pair exactly. On the zero-chart source, the converse inclusion
has been proved by an actual limiting argument. These facts construct a
local chart on the closure with its unchanged subtype topology.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff

namespace NoExoticSixSphere.FlatDoubleCurve

open SymmetricDifference

variable {U F : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

variable (h : U × ℝ → F) (hh : ContDiff ℝ ∞ h)
  (d : OpenPartialHomeomorph {q : (U × ℝ) × ℝ // dividedDifference h q = 0} ℝ)
  (hd : ∀ q, d q = q.val.2) (r₀ : closure (doublePoints h))

def closureChartInverse (s : ℝ) : closure (doublePoints h) := by
  classical
  exact if hs : s ∈ d.target then
    ⟨pair (d.symm s).val, pair_mem_closure_of_zero_chart h hh d hd (d.map_target hs)⟩
  else r₀

omit [FiniteDimensional ℝ U] in
theorem closureChartInverse_val {s : ℝ} (hs : s ∈ d.target) :
    (closureChartInverse h hh d hd r₀ s).val = pair (d.symm s).val := by
  simp only [closureChartInverse, dif_pos hs]

theorem closedRecover_closureChartInverse {s : ℝ} (hs : s ∈ d.target) :
    closedRecover h hh (closureChartInverse h hh d hd r₀ s) = d.symm s := by
  apply Subtype.ext
  change recover (closureChartInverse h hh d hd r₀ s).val = (d.symm s).val
  rw [closureChartInverse_val h hh d hd r₀ hs, recover_pair]

def closureChart : OpenPartialHomeomorph (closure (doublePoints h)) ℝ where
  toFun r := d (closedRecover h hh r)
  invFun := closureChartInverse h hh d hd r₀
  source := closedRecover h hh ⁻¹' d.source
  target := d.target
  map_source' _ hr := d.map_source hr
  map_target' s hs := by
    change closedRecover h hh (closureChartInverse h hh d hd r₀ s) ∈ d.source
    rw [closedRecover_closureChartInverse h hh d hd r₀ hs]
    exact d.map_target hs
  left_inv' r hr := by
    apply Subtype.ext
    rw [closureChartInverse_val h hh d hd r₀ (d.map_source hr), d.left_inv hr]
    exact pair_closedRecover h hh r
  right_inv' s hs := by
    rw [closedRecover_closureChartInverse h hh d hd r₀ hs]
    exact d.right_inv hs
  open_source := d.open_source.preimage (continuous_closedRecover h hh)
  open_target := d.open_target
  continuousOn_toFun := d.continuousOn.comp
    (continuous_closedRecover h hh).continuousOn (fun _ hr ↦ hr)
  continuousOn_invFun := by
    apply IsInducing.subtypeVal.continuousOn_iff.mpr
    apply (continuous_pair.comp_continuousOn
      (continuous_subtype_val.comp_continuousOn d.symm.continuousOn)).congr
    intro s hs
    exact closureChartInverse_val h hh d hd r₀ hs

theorem closureChart_apply (r : closure (doublePoints h)) :
    closureChart h hh d hd r₀ r = (r.val.1.2 - r.val.2.2) / 2 :=
  hd (closedRecover h hh r)

theorem closureChart_source :
    (closureChart h hh d hd r₀).source = closedRecover h hh ⁻¹' d.source := rfl

theorem closureChart_target : (closureChart h hh d hd r₀).target = d.target := rfl

theorem closureChart_inverse_smooth
    (hsmooth : ContDiffOn ℝ ∞ (fun s ↦ (d.symm s).val) d.target) :
    ContDiffOn ℝ ∞ (fun s ↦ ((closureChart h hh d hd r₀).symm s).val)
      (closureChart h hh d hd r₀).target := by
  apply (contDiff_pair.comp_contDiffOn hsmooth).congr
  intro s hs
  exact closureChartInverse_val h hh d hd r₀ hs

end NoExoticSixSphere.FlatDoubleCurve
