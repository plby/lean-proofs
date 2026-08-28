import Wikipedia.HopfProblem.DegreeCollapseWholeLevelConnectionRealization

/-!
# Two endpoints on a level exclude all other outgoing connections

Monotone height and distinct critical values force any nonconstant
connection below the upper critical value. The critical-value gap makes
that orbit cross the controlled level. Its two possible endpoints there
then exclude every other critical target by uniqueness of limits.
-/

noncomputable section

open Set Function Filter
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem no_other_connections_of_two_level_endpoints
    {M : Type*} [TopologicalSpace M] [T2Space M] (F : Flow ℝ M)
    {f : M → ℝ} (hf : Continuous f) {C : Set M} (hinj : InjOn f C)
    (p q r : C) {a : ℝ} (hpa : a < f p)
    (hgap : ∀ j : C, f j < f p → f j < a)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hends : ∀ x : {y : M // f y = a},
      Tendsto (fun t => F t x.val) atBot (𝓝 p.val) →
      Tendsto (fun t => F t x.val) atTop (𝓝 q.val) ∨
      Tendsto (fun t => F t x.val) atTop (𝓝 r.val)) :
    ∀ j : C, j ≠ p → j ≠ q → j ≠ r → ∀ x,
      ¬(Tendsto (fun t => F t x) atBot (𝓝 p.val) ∧
        Tendsto (fun t => F t x) atTop (𝓝 j.val)) := by
  intro j hjp hjq hjr x hx
  have hforwardHeight := hf.continuousAt.tendsto.comp hx.2
  have hbackwardHeight := hf.continuousAt.tendsto.comp hx.1
  have hle : f j ≤ f p := (hmono x).le_of_tendsto hforwardHeight 0 |>.trans
    ((hmono x).ge_of_tendsto hbackwardHeight 0)
  have hlt : f j < f p := lt_of_le_of_ne hle
    (fun h => hjp (Subtype.ext (hinj j.property p.property h)))
  obtain ⟨t, ht⟩ := FlowCancellation.exists_level_crossing_of_endpoint_limits
    F hf hx.1 hx.2 hpa (hgap j hlt)
  let z : {y : M // f y = a} := ⟨F t x, ht⟩
  have hzb : Tendsto (fun s => F s z.val) atBot (𝓝 p.val) :=
    (flow_time_atBot_limit_iff F t x p.val).mpr hx.1
  have hzf : Tendsto (fun s => F s z.val) atTop (𝓝 j.val) :=
    (flow_time_atTop_limit_iff F t x j.val).mpr hx.2
  rcases hends z hzb with hq | hr
  · exact hjq (Subtype.ext (tendsto_nhds_unique hzf hq))
  · exact hjr (Subtype.ext (tendsto_nhds_unique hzf hr))

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
