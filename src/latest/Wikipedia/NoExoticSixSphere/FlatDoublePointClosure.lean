import Wikipedia.NoExoticSixSphere.FlatDoublePointCoordinates

/-!
# Every point of the regular zero-curve chart is an actual double-point limit

Away from zero separation the divided-difference equation gives genuine
distinct same-image points. At zero separation the actual inverse chart
is approached through nonzero real parameters. Its continuity places the
diagonal point in the closure, without postulating a compactification.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Topology

namespace NoExoticSixSphere.FlatDoubleCurve

open SymmetricDifference

variable {U F : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem pair_mem_closure_of_zero_chart (h : U × ℝ → F) (hh : ContDiff ℝ ∞ h)
    (d : OpenPartialHomeomorph {q : (U × ℝ) × ℝ // dividedDifference h q = 0} ℝ)
    (hd : ∀ q, d q = q.val.2)
    {q : {q : (U × ℝ) × ℝ // dividedDifference h q = 0}} (hq : q ∈ d.source) :
    pair q.val ∈ closure (doublePoints h) := by
  by_cases hs : q.val.2 = 0
  · have hdq : d q = 0 := (hd q).trans hs
    have htarget : (0 : ℝ) ∈ d.target := hdq ▸ d.map_source hq
    have hinv : d.symm 0 = q := by
      rw [← hdq]
      exact d.left_inv hq
    have hc : ContinuousAt (fun s : ℝ ↦ pair (d.symm s).val) 0 :=
      continuous_pair.continuousAt.comp
        (continuous_subtype_val.continuousAt.comp
          (d.symm.continuousOn.continuousAt (d.open_target.mem_nhds htarget)))
    have hlim : Tendsto (fun s : ℝ ↦ pair (d.symm s).val) (𝓝[≠] 0) (𝓝 (pair q.val)) := by
      simpa only [hinv] using hc.tendsto.mono_left nhdsWithin_le_nhds
    apply mem_closure_of_tendsto hlim
    have hT : ∀ᶠ s in 𝓝[≠] (0 : ℝ), s ∈ d.target :=
      mem_nhdsWithin_of_mem_nhds (d.open_target.mem_nhds htarget)
    have hne : ∀ᶠ s in 𝓝[≠] (0 : ℝ), s ≠ 0 := self_mem_nhdsWithin
    filter_upwards [hT, hne] with s hsT hsne
    apply (pair_mem_doublePoints_iff h hh (d.symm s).val).mpr
    have hparam : (d.symm s).val.2 = s := (hd (d.symm s)).symm.trans (d.right_inv hsT)
    exact ⟨hparam.symm ▸ hsne, (d.symm s).property⟩
  · exact subset_closure ((pair_mem_doublePoints_iff h hh q.val).mpr ⟨hs, q.property⟩)

end NoExoticSixSphere.FlatDoubleCurve
