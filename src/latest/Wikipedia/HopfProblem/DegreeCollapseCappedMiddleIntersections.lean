import Wikipedia.HopfProblem.DegreeCollapseNativeMiddleCapFillings

/-!
# The actual extremal caps introduce no opposite middle intersections

Adding the entire lower disk to a descending middle basin and the entire
upper disk to an ascending middle basin preserves their exact intersection.
Height monotonicity excludes all three extra cases. The controlled attaching
and belt fillings lie in these sets and avoid every middle critical point,
so their images are disjoint from every opposite capped basin.
No smoothness or homological marking of the resulting closed spheres is
asserted here; those comparisons remain separate construction steps.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M]

namespace SeparatedSystem

variable (D : SeparatedSystem E M)

def descendingCarrier (p : criticalPoints E D.function) : Set M :=
  {x | Tendsto (fun t => D.windows.flow t x) atBot (𝓝 p.val)} ∪
    {x | D.function x ≤ D.lowerCut}

def ascendingCarrier (p : criticalPoints E D.function) : Set M :=
  {x | Tendsto (fun t => D.windows.flow t x) atTop (𝓝 p.val)} ∪
    {x | D.upperCut ≤ D.function x}

theorem backward_height {p x : M}
    (h : Tendsto (fun t => D.windows.flow t x) atBot (𝓝 p)) : D.function x ≤ D.function p := by
  have hh := (FlowConstruction.antitone_flow_height D.smooth D.windows.flow D.windows.integral
    D.windows.zero D.windows.descent x).ge_of_tendsto
      (D.smooth.continuous.continuousAt.tendsto.comp h) 0
  simpa only [D.windows.flow.map_zero_apply] using hh

theorem forward_height {p x : M}
    (h : Tendsto (fun t => D.windows.flow t x) atTop (𝓝 p)) : D.function p ≤ D.function x := by
  have hh := (FlowConstruction.antitone_flow_height D.smooth D.windows.flow D.windows.integral
    D.windows.zero D.windows.descent x).le_of_tendsto
      (D.smooth.continuous.continuousAt.tendsto.comp h) 0
  simpa only [D.windows.flow.map_zero_apply] using hh

theorem carriers_pair_iff (p q : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) (hq : nativeMorseIndex E D.function q = 3)
    (x : M) : x ∈ D.descendingCarrier p ∩ D.ascendingCarrier q ↔ x = p.val ∧ p = q := by
  have hpU : D.function p < D.upperCut :=
    (D.windows.toSurgeryWindows.value_lt_upper p).trans (D.middle_between_caps p hp).2
  have hLq : D.lowerCut < D.function q :=
    (D.middle_between_caps q hq).1.trans (D.windows.toSurgeryWindows.lower_lt_value q)
  have hLp : D.lowerCut < D.function p :=
    (D.middle_between_caps p hp).1.trans (D.windows.toSurgeryWindows.lower_lt_value p)
  constructor
  · rintro ⟨hback | hlo, hforward | hhi⟩
    · exact (middle_basin_pair_iff D.windows D.separated p q hp hq x).mp ⟨hback, hforward⟩
    · have hh := D.backward_height hback
      exact (not_le_of_gt hpU (hhi.trans hh)).elim
    · have hh := D.forward_height hforward
      exact (not_le_of_gt hLq (hh.trans hlo)).elim
    · exact (not_le_of_gt (hLp.trans hpU) (hhi.trans hlo)).elim
  · intro h
    obtain ⟨hback, hforward⟩ := (middle_basin_pair_iff D.windows D.separated p q hp hq x).mpr h
    exact ⟨Or.inl hback, Or.inl hforward⟩

theorem attaching_orbit_descending (p : criticalPoints E D.function) {x : M}
    (hx : x ∈ orbitSaturation D.windows.flow (D.attachingMap p)) :
    Tendsto (fun t => D.windows.flow t x) atBot (𝓝 p.val) := by
  obtain ⟨z, t, rfl⟩ := hx
  exact (flow_time_atBot_limit_iff D.windows.flow t (D.attachingMap p z) p.val).mpr
    ((D.windows.attaching_basin_iff D.smooth p _).mpr ⟨z, rfl⟩)

theorem belt_orbit_ascending (p : criticalPoints E D.function) {x : M}
    (hx : x ∈ orbitSaturation D.windows.flow (D.beltMap p)) :
    Tendsto (fun t => D.windows.flow t x) atTop (𝓝 p.val) := by
  obtain ⟨z, t, rfl⟩ := hx
  exact (flow_time_atTop_limit_iff D.windows.flow t (D.beltMap p z) p.val).mpr
    ((D.windows.belt_basin_iff D.smooth p _).mpr ⟨z, rfl⟩)

theorem orbit_noncritical {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (γ : C(sphere (0 : V) 1, M)) (hγ : ∀ z, γ z ∉ criticalPoints E D.function)
    {x : M} (hx : x ∈ orbitSaturation D.windows.flow γ) : x ∉ criticalPoints E D.function := by
  intro hcrit
  obtain ⟨z, t, ht⟩ := hx
  have he := congrArg (fun y => D.windows.flow (-t) y) ht
  rw [← D.windows.flow.map_add, neg_add_cancel, D.windows.flow.map_zero_apply,
    critical_flow_fixed D.windows hcrit] at he
  apply hγ z
  rw [he]
  exact hcrit

theorem attaching_cap_disjoint (p q : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) (hq : nativeMorseIndex E D.function q = 3)
    (K : C(closedBall (0 : (D.windows.data p).chart.NegativeCoordinates) 1, M))
    (hK : ∀ z, K z ∈ orbitSaturation D.windows.flow (D.attachingMap p) ∪
      {x | D.function x ≤ D.lowerCut}) :
    Disjoint (range K) (D.ascendingCarrier q) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨z, rfl⟩ hx
  have hdesc : K z ∈ D.descendingCarrier p := by
    rcases hK z with ho | hc
    · exact Or.inl (D.attaching_orbit_descending p ho)
    · exact Or.inr hc
  obtain ⟨he, hpq⟩ := (D.carriers_pair_iff p q hp hq (K z)).mp ⟨hdesc, hx⟩
  rcases hK z with ho | hc
  · have hn := D.orbit_noncritical (D.attachingMap p)
      (fun u => (D.windows.data p).lower_regular _ ((D.windows.data p).surgery.attachingSphere u).property) ho
    apply hn
    rw [he]
    exact p.property
  · have hbelow := (D.middle_between_caps p hp).1.trans (D.windows.toSurgeryWindows.lower_lt_value p)
    change D.function (K z) ≤ D.lowerCut at hc
    rw [he] at hc
    exact not_le_of_gt hbelow hc

theorem belt_cap_disjoint (p q : criticalPoints E D.function)
    (hp : nativeMorseIndex E D.function p = 3) (hq : nativeMorseIndex E D.function q = 3)
    (K : C(closedBall (0 : (D.windows.data p).chart.PositiveCoordinates) 1, M))
    (hK : ∀ z, K z ∈ orbitSaturation D.windows.flow (D.beltMap p) ∪
      {x | D.upperCut ≤ D.function x}) :
    Disjoint (D.descendingCarrier q) (range K) := by
  apply Set.disjoint_left.mpr
  rintro x hx ⟨z, rfl⟩
  have hasc : K z ∈ D.ascendingCarrier p := by
    rcases hK z with ho | hc
    · exact Or.inl (D.belt_orbit_ascending p ho)
    · exact Or.inr hc
  obtain ⟨he, hqp⟩ := (D.carriers_pair_iff q p hq hp (K z)).mp ⟨hx, hasc⟩
  have he' : K z = p.val := he.trans (congrArg Subtype.val hqp)
  rcases hK z with ho | hc
  · have hn := D.orbit_noncritical (D.beltMap p)
      (fun u => (D.windows.data p).upper_regular _ ((D.windows.data p).surgery.beltSphere u).property) ho
    apply hn
    rw [he']
    exact p.property
  · have habove := (D.windows.toSurgeryWindows.value_lt_upper p).trans (D.middle_between_caps p hp).2
    change D.upperCut ≤ D.function (K z) at hc
    rw [he'] at hc
    exact not_le_of_gt habove hc

end SeparatedSystem
end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality
