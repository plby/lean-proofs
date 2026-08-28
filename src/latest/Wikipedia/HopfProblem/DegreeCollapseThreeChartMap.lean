import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Gluing three actual chart maps across two matching full germs

The piecewise map retains the entire left and right germs, including
the switching slices, and the middle germ at every interior point.
Agreement of values or derivatives alone is not used.
-/

noncomputable section

open Set Function Filter
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FieldChartGluing

variable {Z M : Type*} [TopologicalSpace Z] [Zero Z]

def threeChartMap (f₀ fₘ f₁ : (ℝ × Z) → M) (a b : ℝ) (p : ℝ × Z) : M :=
  if p.1 ≤ a then f₀ p else if b ≤ p.1 then f₁ p else fₘ p

theorem threeChartMap_left_germ (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ}
    {p : ℝ × Z} (hp : p.1 < a) :
    threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 p] f₀ := by
  filter_upwards [continuousAt_fst.eventually (eventually_lt_nhds hp)] with q hq
  simp only [threeChartMap, if_pos hq.le]

theorem threeChartMap_middle_germ (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ}
    {p : ℝ × Z} (ha : a < p.1) (hb : p.1 < b) :
    threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 p] fₘ := by
  filter_upwards [continuousAt_fst.eventually (eventually_gt_nhds ha),
    continuousAt_fst.eventually (eventually_lt_nhds hb)] with q hqa hqb
  simp only [threeChartMap, if_neg (not_le_of_gt hqa), if_neg (not_le_of_gt hqb)]

theorem threeChartMap_right_germ (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ}
    (hab : a < b) {p : ℝ × Z} (hp : b < p.1) :
    threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 p] f₁ := by
  filter_upwards [continuousAt_fst.eventually (eventually_gt_nhds hp)] with q hq
  simp only [threeChartMap, if_neg (not_le_of_gt (hab.trans hq)), if_pos hq.le]

theorem threeChartMap_left_closed_germ (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ}
    (hab : a < b) (heq : f₀ =ᶠ[𝓝 (a, (0 : Z))] fₘ)
    {s : ℝ} (hs : s ≤ a) : threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 (s, (0 : Z))] f₀ := by
  rcases hs.lt_or_eq with hs | hs
  · exact threeChartMap_left_germ f₀ fₘ f₁ hs
  · subst s
    filter_upwards [heq, continuousAt_fst.eventually (eventually_lt_nhds hab)] with p hp hpb
    by_cases hpa : p.1 ≤ a
    · simp only [threeChartMap, if_pos hpa]
    · simp only [threeChartMap, if_neg hpa, if_neg (not_le_of_gt hpb)]
      exact hp.symm

theorem threeChartMap_right_closed_germ (f₀ fₘ f₁ : (ℝ × Z) → M) {a b : ℝ}
    (hab : a < b) (heq : f₁ =ᶠ[𝓝 (b, (0 : Z))] fₘ)
    {s : ℝ} (hs : b ≤ s) : threeChartMap f₀ fₘ f₁ a b =ᶠ[𝓝 (s, (0 : Z))] f₁ := by
  rcases hs.eq_or_lt with hs | hs
  · subst s
    filter_upwards [heq, continuousAt_fst.eventually (eventually_gt_nhds hab)] with p hp hpa
    by_cases hpb : b ≤ p.1
    · simp only [threeChartMap, if_neg (not_le_of_gt hpa), if_pos hpb]
    · simp only [threeChartMap, if_neg (not_le_of_gt hpa), if_neg hpb]
      exact hp.symm
  · exact threeChartMap_right_germ f₀ fₘ f₁ hab hs

end Wikipedia.HopfProblem.DegreeCollapse.FieldChartGluing
