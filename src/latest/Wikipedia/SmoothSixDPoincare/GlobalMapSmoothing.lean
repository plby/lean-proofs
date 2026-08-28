import Wikipedia.SmoothSixDPoincare.FiniteMapSmoothing
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction
import Wikipedia.NoExoticSixSphere.LocalInverse
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Relative smooth representatives of continuous manifold-valued maps

All target charts and nested cutoffs are constructed from the original
continuous map. Compactness gives a finite plateau cover. The resulting
globally smooth map is homotopic relative to any closed set near which
the original map is already smooth. Source boundaries and corners are allowed.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldSmoothing

variable {E G H K X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

/-- Every source point admits compatible nested cutoffs with a unit plateau about that point. -/
theorem exists_smoothing_patch_at_in_open (f : C(X, N)) (x : X)
    {O : Set N} (hO : IsOpen O) (hxO : f x ∈ O) :
    ∃ p : MapSmoothingPatch I J (X := X) (N := N),
      p.Compatible f ∧ x ∈ p.plateau ∧ p.chart.source ⊆ O := by
  classical
  let c₀ := NoExoticSixSphere.modelChartPartialDiffeomorph (I := J) (f x)
  let c := PartialChart.restrictSource c₀ hO
  have hsource : f x ∈ c.source := ⟨mem_extChartAt_source (I := J) (f x), hxO⟩
  have hU : f ⁻¹' c.source ∈ 𝓝 x :=
    (c.open_source.preimage f.continuous).mem_nhds hsource
  obtain ⟨χ, _, hχ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hU
  have hχone : {y : X | χ y = 1} ∈ 𝓝 x := χ.eventuallyEq_one
  obtain ⟨β, _, hβ⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hχone
  let p : MapSmoothingPatch I J (X := X) (N := N) := {
    chart := c
    cutoff := β
    outer := χ
    smooth := β.contMDiff
    outer_smooth := χ.contMDiff
    compact := β.hasCompactSupport
    outer_compact := χ.hasCompactSupport
    nested := fun y hy => hβ hy }
  refine ⟨p, hχ, ?_, fun _ hx => hx.2⟩
  change x ∈ interior {y : X | β y = 1}
  exact mem_interior_iff_mem_nhds.mpr β.eventuallyEq_one

/-- Compatible local smoothing data without an additional target-open constraint. -/
theorem exists_smoothing_patch_at (f : C(X, N)) (x : X) :
    ∃ p : MapSmoothingPatch I J (X := X) (N := N), p.Compatible f ∧ x ∈ p.plateau := by
  obtain ⟨p, hc, hp, _⟩ :=
    exists_smoothing_patch_at_in_open (I := I) (J := J) f x isOpen_univ (mem_univ _)
  exact ⟨p, hc, hp⟩

variable [CompactSpace X]

/-- A continuous map into a boundaryless manifold has a smooth representative relative to `C`. -/
theorem exists_smooth_map_homotopicRel (f : C(X, N))
    {C U : Set X} (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hfU : ContMDiffOn I J ∞ f U) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C := by
  classical
  have hp (x : X) :
      ∃ p : MapSmoothingPatch I J (X := X) (N := N), p.Compatible f ∧ x ∈ p.plateau :=
    exists_smoothing_patch_at f x
  choose p hpcompatible hpplateau using hp
  have hopen (x : X) : IsOpen (p x).plateau := isOpen_interior
  have hcover : (univ : Set X) ⊆ ⋃ x, (p x).plateau := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hpplateau x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (p x).plateau)
    hopen hcover
  apply exists_smoothing_of_finite_patches (fun i : s => p i.1) f (fun i => hpcompatible i.1)
    hC hU hCU hfU
  intro x
  obtain ⟨i, hi, hix⟩ := mem_iUnion₂.mp (hs (mem_univ x))
  exact ⟨⟨i, hi⟩, hix⟩

/-- In particular every continuous map from a compact smooth source is homotopic to a smooth map. -/
theorem exists_smooth_map_homotopic (f : C(X, N)) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.Homotopic f' := by
  obtain ⟨f', hf', ⟨H⟩⟩ := exists_smooth_map_homotopicRel (I := I) (J := J) f
    isClosed_empty isOpen_empty (Subset.refl ∅) contMDiffOn_empty
  exact ⟨f', hf', ⟨H.toHomotopy⟩⟩

end Wikipedia.SmoothSixDPoincare.ManifoldSmoothing
