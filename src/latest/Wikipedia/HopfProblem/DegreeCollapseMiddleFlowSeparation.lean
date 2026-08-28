import Wikipedia.HopfProblem.DegreeCollapseMiddleNoConnections
import Wikipedia.HopfProblem.DegreeCollapseEmptyCoreConnections

/-!
# Actual intersections of native descending and ascending middle basins

An actual noncritical connection has strictly ordered endpoint heights.
Full canonical attaching sections below every middle critical value then
exclude all middle-to-middle connections. Under that geometric condition,
opposite middle basins intersect only at their common critical point.
These are statements about the original complete flow, not abstract cells.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}
  (S : AdaptedSurgeryWindows E f)

def NoMiddleConnections : Prop :=
  ∀ p q : criticalPoints E f,
    nativeMorseIndex E f p = 3 → nativeMorseIndex E f q = 3 →
    ∀ x, x ∉ criticalPoints E f →
      ¬(Tendsto (fun t => S.flow t x) atBot (𝓝 p.val) ∧
        Tendsto (fun t => S.flow t x) atTop (𝓝 q.val))

theorem connection_heights (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {p q x : M} (hx : x ∉ criticalPoints E f)
    (hp : Tendsto (fun t => S.flow t x) atBot (𝓝 p))
    (hq : Tendsto (fun t => S.flow t x) atTop (𝓝 q)) : f q < f x ∧ f x < f p := by
  obtain ⟨b, hb, a, ha, hback, hforward, hheights⟩ :=
    FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral
      S.zero S.descent S.distinct x
  have hb' : b = p := tendsto_nhds_unique hback hp
  have ha' : a = q := tendsto_nhds_unique hforward hq
  simpa only [hb', ha'] using hheights hx

theorem noMiddleConnections_of_sections
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (habove : ∀ p : criticalPoints E f, nativeMorseIndex E f p = 3 → a < f p)
    (hsection : ∀ (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 3),
      ∃ γ : C(Hemisphere.Sphere 2, {y : M // f y = a}), ∀ x, ∃ t : ℝ,
        S.flow t (nativeIndexThreeAttachingSphere S p hp x).val = (γ x).val) :
    NoMiddleConnections S := by
  intro p q hp hq x hx hlim
  obtain ⟨hqx, hxp⟩ := connection_heights S hf hx hlim.1 hlim.2
  obtain ⟨γ, hγ⟩ := hsection p hp
  exact S.no_connection_above_canonical_cut hf q p (hqx.trans hxp) hp
    (habove q hq) γ hγ x hlim

theorem critical_flow_fixed {x : M} (hx : x ∈ criticalPoints E f) (t : ℝ) :
    S.flow t x = x :=
  FlowConstruction.flow_fixed_of_zero (S.smooth.of_le (by simp)) S.flow S.integral
    (S.zero x hx) t

theorem critical_backward_limit {x : M} (hx : x ∈ criticalPoints E f) :
    Tendsto (fun t => S.flow t x) atBot (𝓝 x) := by
  simpa only [critical_flow_fixed S hx] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => x) atBot (𝓝 x))

theorem critical_forward_limit {x : M} (hx : x ∈ criticalPoints E f) :
    Tendsto (fun t => S.flow t x) atTop (𝓝 x) := by
  simpa only [critical_flow_fixed S hx] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => x) atTop (𝓝 x))

theorem middle_basin_pair_iff (hsep : NoMiddleConnections S)
    (p q : criticalPoints E f) (hp : nativeMorseIndex E f p = 3)
    (hq : nativeMorseIndex E f q = 3) (x : M) :
    (Tendsto (fun t => S.flow t x) atBot (𝓝 p.val) ∧
      Tendsto (fun t => S.flow t x) atTop (𝓝 q.val)) ↔ x = p.val ∧ p = q := by
  constructor
  · intro hlim
    by_cases hx : x ∈ criticalPoints E f
    · have hxp : x = p.val := tendsto_nhds_unique (critical_backward_limit S hx) hlim.1
      have hxq : x = q.val := tendsto_nhds_unique (critical_forward_limit S hx) hlim.2
      exact ⟨hxp, Subtype.ext (hxp.symm.trans hxq)⟩
    · exact (hsep p q hp hq x hx hlim).elim
  · rintro ⟨rfl, rfl⟩
    exact ⟨critical_backward_limit S p.property, critical_forward_limit S p.property⟩

theorem distinct_middle_basins_disjoint (hsep : NoMiddleConnections S)
    (p q : criticalPoints E f) (hp : nativeMorseIndex E f p = 3)
    (hq : nativeMorseIndex E f q = 3) (hpq : p ≠ q) :
    Disjoint {x | Tendsto (fun t => S.flow t x) atBot (𝓝 p.val)}
      {x | Tendsto (fun t => S.flow t x) atTop (𝓝 q.val)} := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hpq ((middle_basin_pair_iff S hsep p q hp hq x).mp ⟨hx, hy⟩).2

theorem same_middle_basins_inter (hsep : NoMiddleConnections S)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 3) :
    {x | Tendsto (fun t => S.flow t x) atBot (𝓝 p.val)} ∩
      {x | Tendsto (fun t => S.flow t x) atTop (𝓝 p.val)} = {p.val} := by
  ext x
  exact (middle_basin_pair_iff S hsep p p hp hp x).trans (and_iff_left rfl)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality
