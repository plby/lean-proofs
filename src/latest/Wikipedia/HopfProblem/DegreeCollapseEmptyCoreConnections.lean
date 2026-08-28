import Wikipedia.HopfProblem.DegreeCollapseIndexInversionConnectionRemoval

/-!
# Empty core sections and all nonincreasing critical-index pairs

An index-zero upper point has an empty attaching sphere; a full-index
lower point has an empty belt sphere. Every supposed connection would
cross that original core level, which is impossible. These two boundary
cases complete the dimension-based connection-removal theorem for all
nonincreasing pairs, including the extrema.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem unitSphere_isEmpty_of_finrank_zero {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] (hA : Module.finrank ℝ A = 0) :
    IsEmpty (PuncturedHandle.UnitSphere A) := by
  let _ : Subsingleton A := (Module.finrank_eq_zero_iff_of_free ℝ A).mp hA
  refine ⟨fun v => ?_⟩
  have hh := mem_sphere_zero_iff_norm.mp v.property
  rw [Subsingleton.elim (v : A) 0, norm_zero] at hh
  norm_num at hh

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.no_connection_of_upper_index_zero
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hpq : f p < f q)
    (hqzero : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 0) :
    ∀ x, ¬(Tendsto (fun t => S.flow t x) atBot (𝓝 q.val) ∧
      Tendsto (fun t => S.flow t x) atTop (𝓝 p.val)) := by
  let _ := unitSphere_isEmpty_of_finrank_zero hqzero
  rintro x ⟨hxq, hxp⟩
  obtain ⟨t, ht⟩ := FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
    hxq hxp (S.toSurgeryWindows.lower_lt_value q)
    ((S.toSurgeryWindows.value_lt_upper p).trans (S.separated p q hpq))
  let y : (S.data q).LowerLevel := ⟨S.flow t x, ht⟩
  have hlim : Tendsto (fun s => S.flow s (y : M)) atBot (𝓝 q.val) :=
    (flow_time_atBot_limit_iff S.flow t x q.val).mpr hxq
  obtain ⟨v, -⟩ := (S.attaching_basin_iff hf q y).mp hlim
  exact isEmptyElim v

theorem AdaptedSurgeryWindows.no_connection_of_lower_positive_zero
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hpq : f p < f q)
    (hpzero : Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 0) :
    ∀ x, ¬(Tendsto (fun t => S.flow t x) atBot (𝓝 q.val) ∧
      Tendsto (fun t => S.flow t x) atTop (𝓝 p.val)) := by
  let _ := unitSphere_isEmpty_of_finrank_zero hpzero
  rintro x ⟨hxq, hxp⟩
  obtain ⟨t, ht⟩ := FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous
    hxq hxp ((S.separated p q hpq).trans (S.toSurgeryWindows.lower_lt_value q))
    (S.toSurgeryWindows.value_lt_upper p)
  let y : (S.data p).UpperLevel := ⟨S.flow t x, ht⟩
  have hlim : Tendsto (fun s => S.flow s (y : M)) atTop (𝓝 p.val) :=
    (flow_time_atTop_limit_iff S.flow t x p.val).mpr hxp
  obtain ⟨v, -⟩ := (S.belt_basin_iff hf p y).mp hlim
  exact isEmptyElim v

theorem AdaptedSurgeryWindows.remove_connections_of_nonincreasing_indices
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hle : Module.finrank ℝ (S.data q).chart.NegativeCoordinates ≤
      Module.finrank ℝ (S.data p).chart.NegativeCoordinates) :
    ∃ (V : (z : M) → TangentSpace 𝓘(ℝ, E) z) (G : Flow ℝ M),
      ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
        (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∀ z, IsMIntegralCurve (fun t => G t z) V) ∧
      (∀ z ∈ criticalPoints E f, V z = 0) ∧
      (∀ z, z ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f z (V z) < 0) ∧
      (∀ z ∈ criticalPoints E f, ∀ᶠ y in 𝓝 z, V y = S.field y) ∧
      ∀ z, ¬(Tendsto (fun t => G t z) atBot (𝓝 q.val) ∧
        Tendsto (fun t => G t z) atTop (𝓝 p.val)) := by
  by_cases hqzero : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 0
  · exact ⟨S.field, S.flow, S.smooth, S.integral, S.zero, S.descent,
      fun _ _ => Eventually.of_forall (fun _ => rfl),
      S.no_connection_of_upper_index_zero hf p q hpq hqzero⟩
  by_cases hpzero : Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 0
  · exact ⟨S.field, S.flow, S.smooth, S.integral, S.zero, S.descent,
      fun _ _ => Eventually.of_forall (fun _ => rfl),
      S.no_connection_of_lower_positive_zero hf p q hpq hpzero⟩
  exact S.remove_connections_of_index_le hf p q hpq hconsecutive
    (Module.finrank ℝ (S.data q).chart.NegativeCoordinates - 1)
    (Module.finrank ℝ (S.data p).chart.PositiveCoordinates - 1) (by omega) (by omega) hle

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
