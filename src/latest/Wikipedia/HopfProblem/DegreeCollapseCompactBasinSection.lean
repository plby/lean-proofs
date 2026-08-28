import Wikipedia.HopfProblem.DegreeCollapseThreefoldMiddleFamily

/-!
# A compact full basin section forces the entire native attaching sphere to reach it

The reaching directions are open by the actual partial flow transport.
The full compact basin section makes their transported image closed.
Connectedness of the native sphere then gives all directions, rather than
only those already known to occur in the constructed section.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}
  [TopologicalSpace X] [CompactSpace X]

theorem AdaptedSurgeryWindows.attaching_sphere_reaches_of_compact_basin_section
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = n + 1)]
    [PreconnectedSpace (Hemisphere.Sphere n)]
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (α : C(X, {y : M // f y = a})) (x₀ : X)
    (hfull : ∀ y, y ∈ range α ↔ Tendsto (fun t => S.flow t y.val) atBot (𝓝 p.val)) :
    ∀ u : sphere (0 : (S.data p).chart.NegativeCoordinates) 1,
      ((S.data p).surgery.attachingSphere u).val ∈ FlowCancellation.levelBasin S.flow f a := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf (S.data p).lower_regular
  have hback (x : X) := (hfull (α x)).mp (mem_range_self x)
  have hreach (x : X) := S.backward_basin_reaches_attaching_level hf p
    (ha (α x).val (α x).property) (hback x)
  obtain ⟨t₀, ht₀⟩ := hreach x₀
  obtain ⟨D, hsource, htarget, horbit⟩ := S.exists_native_level_basin_transport hf ha
    (S.data p).lower_regular (α x₀) ⟨S.flow t₀ (α x₀).val, ht₀⟩
  have hsrc (x : X) : α x ∈ D.source := hsource.symm ▸ hreach x
  let β : X → (S.data p).LowerLevel := D ∘ α
  have hβ : Continuous β := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (D.contMDiffOn_toFun.continuousOn.continuousAt
      (D.open_source.mem_nhds (hsrc x))).comp α.continuous.continuousAt
  have hβback (x : X) : Tendsto (fun t => S.flow t (β x).val) atBot (𝓝 p.val) := by
    obtain ⟨t, ht⟩ := horbit (α x) (hsrc x)
    change Tendsto (fun t => S.flow t (D (α x)).val) atBot (𝓝 p.val)
    rw [← ht]
    exact (flow_time_atBot_limit_iff S.flow t (α x).val p.val).mpr (hback x)
  let e := (SphereCoordinates.standardParametrization
    (S.data p).chart.NegativeCoordinates n).toHomeomorph
  let A : C(Hemisphere.Sphere n, (S.data p).LowerLevel) :=
    (S.data p).surgery.attachingSphere.comp (e : C(_, _))
  let U : Set (Hemisphere.Sphere n) := A ⁻¹' D.target
  have hUeq : U = A ⁻¹' range β := by
    ext u
    constructor
    · intro hu
      have hxu : D.symm (A u) ∈ D.source := D.map_target' hu
      have hright : D (D.symm (A u)) = A u := D.right_inv' hu
      obtain ⟨t, ht⟩ := horbit (D.symm (A u)) hxu
      rw [hright] at ht
      have hAback : Tendsto (fun t => S.flow t (A u).val) atBot (𝓝 p.val) :=
        (S.attaching_basin_iff hf p (A u)).mpr ⟨e u, rfl⟩
      have hxb : Tendsto (fun t => S.flow t (D.symm (A u)).val) atBot (𝓝 p.val) := by
        rw [← ht] at hAback
        exact (flow_time_atBot_limit_iff S.flow t (D.symm (A u)).val p.val).mp hAback
      obtain ⟨x, hx⟩ := (hfull (D.symm (A u))).mpr hxb
      exact ⟨x, (congrArg D hx).trans hright⟩
    · rintro ⟨x, hx⟩
      change A u ∈ D.target
      rw [← hx]
      exact D.map_source' (hsrc x)
  have hUopen : IsOpen U := D.open_target.preimage A.continuous
  have hUclosed : IsClosed U := by
    rw [hUeq]
    exact (isCompact_range hβ).isClosed.preimage A.continuous
  have hUne : U.Nonempty := by
    obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf p (β x₀)).mp (hβback x₀)
    obtain ⟨v, hv⟩ := e.surjective u
    refine ⟨v, ?_⟩
    change A v ∈ D.target
    have heq : A v = β x₀ := by change (S.data p).surgery.attachingSphere (e v) = _; rw [hv, hu]
    rw [heq]
    exact D.map_source' (hsrc x₀)
  have hUall : U = univ := IsClopen.eq_univ ⟨hUclosed, hUopen⟩ hUne
  intro u
  obtain ⟨v, rfl⟩ := e.surjective u
  have hv : A v ∈ D.target := show v ∈ U from hUall.symm ▸ mem_univ v
  rw [htarget] at hv
  exact hv

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
