import Wikipedia.HopfProblem.DegreeCollapseNativeBasinConnectionCancellation
import Wikipedia.HopfProblem.DegreeCollapseDenseMinimumBasins

/-!
# A unique zero/one connection cancels with the supplied native field

At index zero the actual forward basin is open. The identity map into that
basin is therefore a full-dimensional transverse sheet; a constant map at
the connection supplies the other basin sheet. The proved native unique-orbit
cancellation theorem now applies without a fresh surgery flow or supplied
transversality data.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}
  {V : (x : M) → TangentSpace 𝓘(ℝ, E) x}

theorem isOpen_forward_basin_of_native_index_zero {p : M}
    (c : SignedMorseChart (E := E) f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hmodel : ∀ᶠ y in 𝓝 p, V y = c.descentField y)
    (hindex : Module.finrank ℝ c.NegativeCoordinates = 0) :
    IsOpen {x : M | Tendsto (fun t => F t x) atTop (𝓝 p)} := by
  let : Subsingleton c.NegativeCoordinates :=
    (Module.finrank_eq_zero_iff_of_free ℝ c.NegativeCoordinates).mp hindex
  obtain ⟨r, hr, -, hbasin⟩ := exists_descending_morse_basin_block c hf
    (hV.of_le (by simp)) F hF hzero hdesc hmodel
  have hnear : ∀ᶠ y in 𝓝 p, Tendsto (fun t => F t y) atTop (𝓝 p) := by
    filter_upwards [morse_coordinate_neighborhood c hr hr] with y hy
    exact ((hbasin y hy.1 hy.2.1 hy.2.2).1).mpr (Subsingleton.elim _ _)
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨t, ht⟩ := (hx.eventually (eventually_eventually_nhds.mpr hnear)).exists
  have hc : Continuous (fun y => F t y) := F.continuous continuous_const continuous_id
  filter_upwards [hc.continuousAt.tendsto.eventually ht] with y hy
  exact (flow_time_atTop_limit_iff F t y p).mp hy

open Classical in
theorem cancel_unique_zero_one_connection {p q z : M}
    (cp : SignedMorseChart (E := E) f p) (cq : SignedMorseChart (E := E) f q)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hindexp : nativeMorseIndex E f p = 0) (hindexq : nativeMorseIndex E f q = 1)
    (hV : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (F : Flow ℝ M) (hF : ∀ x, IsMIntegralCurve (fun t => F t x) V)
    (hzero : ∀ x ∈ criticalPoints E f, V x = 0)
    (hdesc : ∀ x, x ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f x (V x) < 0)
    (hinj : InjOn f (criticalPoints E f))
    (hpc : p ∈ criticalPoints E f) (hqc : q ∈ criticalPoints E f) (hpq : f p < f q)
    {l u : ℝ} (hl : l < f p) (hu : f q < u)
    (hpair : ∀ x ∈ criticalPoints E f, f x ∈ Icc l u → x = p ∨ x = q)
    (hp : Tendsto (fun t => F t z) atTop (𝓝 p))
    (hq : Tendsto (fun t => F t z) atBot (𝓝 q))
    (hunique : ∀ x, Tendsto (fun t => F t x) atBot (𝓝 q) →
      Tendsto (fun t => F t x) atTop (𝓝 p) → ∃ t, F t z = x)
    (heqp : ∀ᶠ x in 𝓝 p, V x = cp.descentField x)
    (heqq : ∀ᶠ x in 𝓝 q, V x = cq.descentField x) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      (criticalPoints E g).ncard + 2 = (criticalPoints E f).ncard ∧
      (∀ x, x ∈ criticalPoints E g ↔ x ∈ criticalPoints E f ∧ x ≠ p ∧ x ≠ q) ∧
      ∀ x, f x ∉ Ioo l u → g =ᶠ[𝓝 x] f := by
  have hp0 : Module.finrank ℝ cp.NegativeCoordinates = 0 :=
    (nativeMorseIndex_eq_chart cp).symm.trans hindexp
  have hq1 : Module.finrank ℝ cq.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart cq).symm.trans hindexq
  have hdim : Module.finrank ℝ E = (Module.finrank ℝ E - 1) + 1 := by
    have h := cq.finrank_negative_add_positive
    omega
  have hindex : Fintype.card {i // cq.weights i = -1} =
      Fintype.card {i // cp.weights i = -1} + 1 := by
    have h : Module.finrank ℝ cq.NegativeCoordinates =
        Module.finrank ℝ cp.NegativeCoordinates + 1 := by omega
    simpa only [SignedMorseChart.NegativeCoordinates, MorseHandle.NegativeSpace,
      finrank_euclideanSpace] using h
  have hbasin : ∀ᶠ x in 𝓝 z, Tendsto (fun t => F t x) atTop (𝓝 p) :=
    (isOpen_forward_basin_of_native_index_zero cp hf hV F hF hzero hdesc heqp hp0).mem_nhds hp
  have htrans : NativeTransversality.At 𝓘(ℝ, E) 𝓘(ℝ, E) 𝓘(ℝ, E)
      (fun _ : M => z) (fun x : M => x) z z := by
    intro _ w
    refine ⟨(0, w), ?_⟩
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun _ : M => z) z 0 +
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun x : M => x) z w = w
    rw [map_zero, zero_add]
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) id z w = w
    rw [mfderiv_id]
    rfl
  exact cancel_unique_connection_of_transverse_basin_sheets cp cq hf hm hdim hindex V hV
    hzero hdesc F hF hinj hpc hqc hpq hl hu hpair hp hq hunique heqp heqq
    (S := fun _ : M => z) (T := fun x : M => x)
    mdifferentiableAt_const mdifferentiableAt_id rfl rfl
    (Eventually.of_forall (fun _ => hq)) hbasin htrans

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
