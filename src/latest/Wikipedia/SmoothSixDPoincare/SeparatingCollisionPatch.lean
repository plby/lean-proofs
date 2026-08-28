import Wikipedia.SmoothSixDPoincare.GlobalImageAvoidance
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Smooth target-chart patches separating a prescribed source pair

A bump supported away from the fixed closed set and from the second point
has value one at the first point and zero at the second. Its support lies
over a genuine chart of the original target manifold.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

open GeneralPosition (MapAvoidancePatch)

variable {E G H N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N]

/-- Distinct source points can be separated by a compatible chart patch whenever the first
point is outside the fixed closed set. -/
theorem exists_separating_patch_in_open (f : C(E, N)) {C : Set E} (hC : IsClosed C)
    {x y : E} (hx : x ∉ C) (hxy : x ≠ y) {O : Set N}
    (hO : IsOpen O) (hxO : f x ∈ O) :
    ∃ p : MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C,
      p.Compatible f ∧ p.cutoff x = 1 ∧ p.cutoff y = 0 ∧ p.chart.source ⊆ O := by
  classical
  let c₀ := NoExoticSixSphere.modelChartPartialDiffeomorph (I := J) (f x)
  let c := PartialChart.restrictSource c₀ hO
  have hsource : f x ∈ c.source := ⟨mem_extChartAt_source (I := J) (f x), hxO⟩
  have hU : f ⁻¹' c.source ∩ (C ∪ {y})ᶜ ∈ 𝓝 x := by
    apply ((c.open_source.preimage f.continuous).inter
      ((hC.union isClosed_singleton).isOpen_compl)).mem_nhds
    exact ⟨hsource, fun h => h.elim hx (fun h => hxy h)⟩
  obtain ⟨β, -, hβ⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) x).mem_iff.mp hU
  let p : MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C := {
    chart := c
    cutoff := β
    smooth := β.contMDiff
    compact := β.hasCompactSupport
    fixed := fun z hz => image_eq_zero_of_notMem_tsupport
      (fun ht => (hβ ht).2 (Or.inl hz)) }
  refine ⟨p, (fun _ ht => (hβ ht).1), β.eq_one, ?_, fun _ hz => hz.2⟩
  exact image_eq_zero_of_notMem_tsupport (fun ht => (hβ ht).2 (Or.inr rfl))

/-- A separating patch without a target-open constraint. -/
theorem exists_separating_patch (f : C(E, N)) {C : Set E} (hC : IsClosed C)
    {x y : E} (hx : x ∉ C) (hxy : x ≠ y) :
    ∃ p : MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C,
      p.Compatible f ∧ p.cutoff x = 1 ∧ p.cutoff y = 0 := by
  obtain ⟨p, hc, hx, hy, _⟩ :=
    exists_separating_patch_in_open (J := J) f hC hx hxy isOpen_univ (mem_univ _)
  exact ⟨p, hc, hx, hy⟩

/-- Move an unfixed member using a chart contained in the prescribed open target. -/
theorem exists_separating_patch_of_not_both_fixed_in_open (f : C(E, N)) {C : Set E}
    (hC : IsClosed C) {x y : E} (hxy : x ≠ y) (hfixed : ¬ (x ∈ C ∧ y ∈ C))
    {O : Set N} (hO : IsOpen O) (hxO : x ∉ C → f x ∈ O) (hyO : y ∉ C → f y ∈ O) :
    ∃ p : MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C,
      p.Compatible f ∧ p.cutoff x ≠ p.cutoff y ∧ p.chart.source ⊆ O := by
  by_cases hx : x ∈ C
  · have hy : y ∉ C := fun hy => hfixed ⟨hx, hy⟩
    obtain ⟨p, hp, hpy, hpx, hs⟩ :=
      exists_separating_patch_in_open (J := J) f hC hy hxy.symm hO (hyO hy)
    exact ⟨p, hp, by rw [hpx, hpy]; exact zero_ne_one, hs⟩
  · obtain ⟨p, hp, hpx, hpy, hs⟩ :=
      exists_separating_patch_in_open (J := J) f hC hx hxy hO (hxO hx)
    exact ⟨p, hp, by rw [hpx, hpy]; exact one_ne_zero, hs⟩

/-- If a pair is not entirely fixed, one orientation supplies a separating patch. -/
theorem exists_separating_patch_of_not_both_fixed (f : C(E, N)) {C : Set E}
    (hC : IsClosed C) {x y : E} (hxy : x ≠ y) (hfixed : ¬ (x ∈ C ∧ y ∈ C)) :
    ∃ p : MapAvoidancePatch 𝓘(ℝ, E) J (N := N) C,
      p.Compatible f ∧ p.cutoff x ≠ p.cutoff y := by
  obtain ⟨p, hc, hne, _⟩ :=
    exists_separating_patch_of_not_both_fixed_in_open (J := J) f hC hxy hfixed
      isOpen_univ (fun _ => mem_univ _) (fun _ => mem_univ _)
  exact ⟨p, hc, hne⟩

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
