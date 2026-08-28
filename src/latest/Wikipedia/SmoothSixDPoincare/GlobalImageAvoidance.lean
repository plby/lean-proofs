import Wikipedia.SmoothSixDPoincare.FiniteImageAvoidance
import Wikipedia.NoExoticSixSphere.LocalInverse
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Relative general position for two low-dimensional smooth maps

If the source dimensions add to less than the target dimension, a map from
a compact smooth manifold can be smoothly perturbed to avoid the other
closed smooth image. The perturbation is homotopic relative to any closed
set on which the original map already avoids the obstacle.

All chart patches and perturbations are constructed. This does not assert
that the new map is an embedding, or perform Whitney cancellation.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.GeneralPosition

variable {E G H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K}
  [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

omit [FiniteDimensional ℝ G] in
/-- Outside the fixed closed set, a compact bump can be supported over a genuine target chart. -/
theorem exists_avoidance_patch_at (f : C(X, N)) {C : Set X} (hC : IsClosed C)
    {x : X} (hx : x ∉ C) :
    ∃ p : MapAvoidancePatch I J (N := N) C, p.Compatible f ∧ p.cutoff x ≠ 0 := by
  classical
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := J) (f x)
  have hsource : f x ∈ c.source := mem_extChartAt_source (I := J) (f x)
  have hU : f ⁻¹' c.source ∩ Cᶜ ∈ 𝓝 x :=
    ((c.open_source.preimage f.continuous).inter hC.isOpen_compl).mem_nhds ⟨hsource, hx⟩
  obtain ⟨φ, _, hφ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hU
  let p : MapAvoidancePatch I J (N := N) C := {
    chart := c
    cutoff := φ
    smooth := φ.contMDiff
    compact := φ.hasCompactSupport
    fixed := by
      intro y hy
      exact image_eq_zero_of_notMem_tsupport (fun ht => (hφ ht).2 hy) }
  refine ⟨p, ?_, ?_⟩
  · exact fun y hy => (hφ hy).1
  · change φ x ≠ 0
    rw [φ.eq_one]
    exact one_ne_zero

variable {E' H' Y : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y]
  [CompactSpace X] [LindelofSpace (X × Y)]

/-- Low-dimensional smooth maps can be made disjoint, relative to an already disjoint closed set. -/
theorem exists_disjoint_smooth_map_homotopicRel_of_isClosed_range
    (f : C(X, N)) (g : C(Y, N)) (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hclosed : IsClosed (range g))
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    {C : Set X} (hC : IsClosed C) (hfixed : ∀ x ∈ C, f x ∉ range g) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C ∧
      Disjoint (range f') (range g) := by
  classical
  let bad : Set X := f ⁻¹' range g
  have hbad : IsCompact bad :=
    (hclosed.preimage f.continuous).isCompact
  have hp (x : bad) :
      ∃ p : MapAvoidancePatch I J (N := N) C, p.Compatible f ∧ p.cutoff x.1 ≠ 0 :=
    exists_avoidance_patch_at f hC (fun hx => hfixed x.1 hx x.2)
  choose p hpcompatible hpactive using hp
  have hopen (x : bad) : IsOpen (Function.support (p x).cutoff) :=
    isOpen_ne_fun (p x).smooth.continuous continuous_const
  have hcover : bad ⊆ ⋃ x : bad, Function.support (p x).cutoff := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hpactive ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hbad.elim_finite_subcover (fun x : bad => Function.support (p x).cutoff)
    hopen hcover
  apply exists_avoidance_of_finite_patches (fun i : s => p i.1) f g hf hg
    (fun i => hpcompatible i.1) hdim
  intro x hx
  obtain ⟨i, hi, hix⟩ := mem_iUnion₂.mp (hs hx)
  exact ⟨⟨i, hi⟩, hix⟩

variable [CompactSpace Y] [T2Space N]

omit [LindelofSpace (X × Y)] in
/-- Low-dimensional smooth maps can be made disjoint, relative to an already disjoint closed set. -/
theorem exists_disjoint_smooth_map_homotopicRel
    (f : C(X, N)) (g : C(Y, N)) (hf : ContMDiff I J ∞ f) (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ E + Module.finrank ℝ E' < Module.finrank ℝ G)
    {C : Set X} (hC : IsClosed C) (hfixed : ∀ x ∈ C, f x ∉ range g) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C ∧
      Disjoint (range f') (range g) :=
  exists_disjoint_smooth_map_homotopicRel_of_isClosed_range f g hf hg
    (isCompact_range g.continuous).isClosed hdim hC hfixed

end Wikipedia.SmoothSixDPoincare.GeneralPosition
