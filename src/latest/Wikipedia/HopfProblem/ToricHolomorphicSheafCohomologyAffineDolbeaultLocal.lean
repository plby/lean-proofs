import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyAffineDolbeaultSections
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDbarLocalOne

/-!
# Actual local primitives in the affine Dolbeault sequence

Closed smooth coefficient pairs have the proved local `(0,1)` primitive.
An arbitrary top coefficient is cut off without any closedness claim and
integrated by the actual partial Cauchy--Green operator. Both constructions
produce genuine sections on explicitly retained smaller open neighborhoods.
-/

noncomputable section

open Set TopologicalSpace Filter Metric
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault

open PeriodTorusLineBundleClassification PeriodTorusLineBundleClassificationCousin

/-- The actual top derivative vanishes exactly when the actual coefficients
satisfy the mixed-coordinate closedness equation on their domain. -/
theorem closed_of_topSection_zero (U : Opens (ℂ × ℂ)) (s : PairSection U)
    (hs : topSection U s = 0) :
    ∀ q ∈ U, dbarFirst (smoothExtend U s.2) q = dbarSecond (smoothExtend U s.1) q := by
  intro q hq
  exact sub_eq_zero.mp (congrArg (fun t : SmoothSection U => t ⟨q, hq⟩) hs)

/-- A genuine closed form section admits a genuine local smooth primitive. -/
theorem exists_local_primitive (U : Opens (ℂ × ℂ)) (x : ℂ × ℂ) (hx : x ∈ U)
    (s : PairSection U) (hs : topSection U s = 0) :
    ∃ (V : Opens (ℂ × ℂ)) (hVU : V ≤ U), x ∈ V ∧
      ∃ t : SmoothSection V, differentialSection V t = pairRestriction hVU s := by
  obtain ⟨u, hu, hfirst, hsecond⟩ := DbarLocalOne.exists_smooth_primitive_germ
    U.isOpen (smoothExtend_contDiffOn U s.1) (smoothExtend_contDiffOn U s.2)
    (closed_of_topSection_zero U s hs) hx
  have hnear : ∀ᶠ q in 𝓝 x, q ∈ U ∧
      dbarFirst u q = smoothExtend U s.1 q ∧
      dbarSecond u q = smoothExtend U s.2 q :=
    Filter.Eventually.and (U.isOpen.mem_nhds hx) (hfirst.and hsecond)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let V : Opens (ℂ × ℂ) := ⟨ball x r, isOpen_ball⟩
  have hVU : V ≤ U := fun _ hq => (hball hq).1
  let t := sectionOfSmooth V u hu.contDiffOn
  refine ⟨V, hVU, mem_ball_self hr, t, ?_⟩
  apply Prod.ext
  · apply ContMDiffMap.ext
    intro q
    change dbarFirst (smoothExtend V t) q = s.1 ⟨q, hVU q.property⟩
    rw [dbarFirst_congr (smoothExtend_sectionOfSmooth_germ V u hu.contDiffOn q q.property)]
    exact ((hball q.property).2.1).trans (smoothExtend_apply U s.1 q (hVU q.property))
  · apply ContMDiffMap.ext
    intro q
    change dbarSecond (smoothExtend V t) q = s.2 ⟨q, hVU q.property⟩
    rw [dbarSecond_congr (smoothExtend_sectionOfSmooth_germ V u hu.contDiffOn q q.property)]
    exact ((hball q.property).2.2).trans (smoothExtend_apply U s.2 q (hVU q.property))

/-- A cutoff and the genuine one-coordinate Cauchy--Green integral solve
the second partial derivative locally, with no closedness assumption. -/
theorem exists_smooth_second_primitive_germ {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    {g : ℂ × ℂ → ℂ} (hg : ContDiffOn ℝ ∞ g U) {x : ℂ × ℂ} (hx : x ∈ U) :
    ∃ u : ℂ × ℂ → ℂ, ContDiff ℝ ∞ u ∧ dbarSecond u =ᶠ[𝓝 x] g := by
  obtain ⟨v, hv, hcv, he⟩ := DbarLocalOne.exists_compact_smooth_representative hU hg hx
  obtain ⟨k, hk, hvk⟩ := exists_compact_second_support hcv
  refine ⟨cauchySecond v, contDiff_cauchySecond hv hk hvk, ?_⟩
  filter_upwards [he] with q hq
  exact (dbarSecond_cauchySecond (hv.of_le (by simp)) hk hvk q).trans hq

/-- Every actual smooth top-form coefficient is the top derivative of
an actual smooth pair on a neighborhood of each point in its domain. -/
theorem exists_local_top_primitive (U : Opens (ℂ × ℂ)) (x : ℂ × ℂ) (hx : x ∈ U)
    (s : SmoothSection U) :
    ∃ (V : Opens (ℂ × ℂ)) (hVU : V ≤ U), x ∈ V ∧
      ∃ t : PairSection V, topSection V t = restriction hVU s := by
  obtain ⟨u, hu, he⟩ := exists_smooth_second_primitive_germ
    U.isOpen (smoothExtend_contDiffOn U s) hx
  have hnear : ∀ᶠ q in 𝓝 x, q ∈ U ∧ dbarSecond u q = smoothExtend U s q :=
    Filter.Eventually.and (U.isOpen.mem_nhds hx) he
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let V : Opens (ℂ × ℂ) := ⟨ball x r, isOpen_ball⟩
  have hVU : V ≤ U := fun _ hq => (hball hq).1
  let t := sectionOfSmooth V u hu.contDiffOn
  have ht : derivativeSection true V t = restriction hVU s := by
    apply ContMDiffMap.ext
    intro q
    change dbarSecond (smoothExtend V t) q = s ⟨q, hVU q.property⟩
    rw [dbarSecond_congr (smoothExtend_sectionOfSmooth_germ V u hu.contDiffOn q q.property)]
    exact ((hball q.property).2).trans (smoothExtend_apply U s q (hVU q.property))
  refine ⟨V, hVU, mem_ball_self hr, (-t, 0), ?_⟩
  change derivativeSection false V 0 - derivativeSection true V (-t) = restriction hVU s
  rw [map_zero, map_neg, zero_sub, neg_neg, ht]

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault
