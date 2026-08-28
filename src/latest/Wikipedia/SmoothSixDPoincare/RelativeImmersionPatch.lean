import Wikipedia.SmoothSixDPoincare.MapSmoothingPatch
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction
import Wikipedia.NoExoticSixSphere.LocalInverse
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Actual compact affine patches on arbitrary finite-dimensional normed sources

Nested smooth bumps are chosen inside the preimage of a native target chart
and outside the fixed set. A compact source neighborhood lies inside the
inner unit plateau.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

open ManifoldSmoothing (MapSmoothingPatch)

variable {E G H N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]

/-- A compact affine patch around any point outside the fixed closed set. -/
theorem exists_relative_immersion_patch_at_in_open (f : C(E, N)) {C : Set E}
    (hC : IsClosed C) {x : E} (hx : x ∉ C) {O : Set N}
    (hO : IsOpen O) (hxO : f x ∈ O) :
    ∃ p : MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N),
      ∃ L : Set E, p.Compatible f ∧ IsCompact L ∧ L ∈ 𝓝 x ∧ L ⊆ p.plateau ∧
        (∀ y ∈ C, p.cutoff y = 0) ∧ p.chart.source ⊆ O := by
  classical
  let c₀ := NoExoticSixSphere.modelChartPartialDiffeomorph (I := J) (f x)
  let c := PartialChart.restrictSource c₀ hO
  have hsource : f x ∈ c.source := ⟨mem_extChartAt_source (I := J) (f x), hxO⟩
  have hU : f ⁻¹' c.source ∩ Cᶜ ∈ 𝓝 x :=
    ((c.open_source.preimage f.continuous).inter hC.isOpen_compl).mem_nhds ⟨hsource, hx⟩
  obtain ⟨χ, _, hχ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) x).mem_iff.mp hU
  have hχone : {y : E | χ y = 1} ∈ 𝓝 x := χ.eventuallyEq_one
  obtain ⟨β, _, hβ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) x).mem_iff.mp hχone
  let p : MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N) := {
    chart := c
    cutoff := β
    outer := χ
    smooth := β.contMDiff
    outer_smooth := χ.contMDiff
    compact := β.hasCompactSupport
    outer_compact := χ.hasCompactSupport
    nested := fun y hy => hβ hy }
  have hxp : x ∈ p.plateau := mem_interior_iff_mem_nhds.mpr β.eventuallyEq_one
  obtain ⟨L, hxL, hLp, hL⟩ := local_compact_nhds (isOpen_interior.mem_nhds hxp)
  refine ⟨p, L, (fun _ hy => (hχ hy).1), hL, hxL, hLp, ?_, fun _ hz => hz.2⟩
  intro y hy
  change β y = 0
  by_contra hne
  have hi : y ∈ tsupport β := subset_tsupport β hne
  have ho : y ∈ tsupport χ := subset_tsupport χ (by
    change χ y ≠ 0
    rw [hβ hi]
    exact one_ne_zero)
  exact (hχ ho).2 hy

/-- Relative immersion data without an additional target-open constraint. -/
theorem exists_relative_immersion_patch_at (f : C(E, N)) {C : Set E}
    (hC : IsClosed C) {x : E} (hx : x ∉ C) :
    ∃ p : MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N),
      ∃ L : Set E, p.Compatible f ∧ IsCompact L ∧ L ∈ 𝓝 x ∧ L ⊆ p.plateau ∧
        ∀ y ∈ C, p.cutoff y = 0 := by
  obtain ⟨p, L, hc, hL, hn, hp, hfix, _⟩ :=
    exists_relative_immersion_patch_at_in_open (J := J) f hC hx isOpen_univ (mem_univ _)
  exact ⟨p, L, hc, hL, hn, hp, hfix⟩

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
