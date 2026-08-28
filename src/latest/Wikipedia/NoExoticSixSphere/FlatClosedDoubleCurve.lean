import Wikipedia.NoExoticSixSphere.FlatDoublePointSymmetry

/-!
# A genuine local closed double-curve chart at a nondegenerate flat singularity

For the actual map `(u,z) ↦ (u,h(u,z))`, a zero of its vertical derivative
with bijective derivative has a local closed ordered double curve. Its
coordinate is signed half-separation, its ambient parametrization is smooth,
and swapping the two source points negates the coordinate.

This theorem does not yet construct flat coordinates for an arbitrary
generic family or compute the local frame parity.
-/

noncomputable section

open Set Function
open scoped ContDiff

namespace NoExoticSixSphere.FlatDoubleCurve

open SymmetricDifference

variable {U F : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_closed_double_curve_chart (h : U × ℝ → F) (hh : ContDiff ℝ ∞ h)
    (p : U × ℝ) (hz : vertical h p = 0)
    (hb : Bijective (fderiv ℝ (vertical h) p)) :
    ∃ hc : pair (p, 0) ∈ closure (doublePoints h),
    ∃ c : OpenPartialHomeomorph (closure (doublePoints h)) ℝ,
      (⟨pair (p, 0), hc⟩ : closure (doublePoints h)) ∈ c.source ∧
      c ⟨pair (p, 0), hc⟩ = 0 ∧
      (∀ r, c r = (r.val.1.2 - r.val.2.2) / 2) ∧
      (∀ r ∈ c.source, swapClosure h r ∈ c.source) ∧
      (∀ r, c (swapClosure h r) = -c r) ∧
      ContDiffOn ℝ ∞ (fun s ↦ (c.symm s).val) c.target := by
  have hzΦ : dividedDifference h (p, 0) = 0 :=
    (dividedDifference_zero h p.1 p.2).trans hz
  have hbΦ : Bijective (fderiv ℝ (fun q : U × ℝ ↦ dividedDifference h (q, 0)) p) := by
    rw [fderiv_zero_slice]
    exact hb
  obtain ⟨d, hdp, hd, hreflect, hsmooth⟩ := ImplicitCurve.exists_symmetric_zero_chart
    (dividedDifference h) (contDiff_dividedDifference h hh) p hzΦ hbΦ
    (fun q s ↦ dividedDifference_even h q.1 q.2 s)
  let q₀ : {q : (U × ℝ) × ℝ // dividedDifference h q = 0} := ⟨(p, 0), hzΦ⟩
  have hc : pair (p, 0) ∈ closure (doublePoints h) :=
    pair_mem_closure_of_zero_chart h hh d hd hdp
  let r₀ : closure (doublePoints h) := ⟨pair (p, 0), hc⟩
  let c := closureChart h hh d hd r₀
  have hr : closedRecover h hh r₀ = q₀ := Subtype.ext (recover_pair (p, 0))
  have hsource : r₀ ∈ c.source := by
    change closedRecover h hh r₀ ∈ d.source
    rw [hr]
    exact hdp
  refine ⟨hc, c, hsource, ?_, closureChart_apply h hh d hd r₀,
    ?_, closureChart_swap h hh d hd r₀, closureChart_inverse_smooth h hh d hd r₀ hsmooth⟩
  · rw [closureChart_apply]
    simp [pair]
  · intro r hr
    exact closureChart_source_swap h hh d hd r₀ hreflect hr

end NoExoticSixSphere.FlatDoubleCurve
