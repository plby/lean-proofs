import Wikipedia.SmoothSixDPoincare.GlobalMapSmoothing
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# Relative smoothing with avoidance on a compact part of the source

Restrict each target chart to the prescribed open set before constructing
the smoothing patches. The existing finite smoothing induction retains
all chart compatibility conditions, hence retains avoidance on the compact
set covered by those patches. Values on the prescribed closed set remain
fixed by an actual relative homotopy.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeAvoidingSmoothing

open ManifoldSmoothing

variable {E G H H' X N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [T2Space X]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

theorem exists_patch_in_open (f : C(X, N)) {V : Set N} (hV : IsOpen V)
    (x : X) (hx : f x ∈ V) :
    ∃ p : MapSmoothingPatch I J (X := X) (N := N),
      p.Compatible f ∧ x ∈ p.plateau ∧ p.chart.source ⊆ V := by
  classical
  let c := PartialChart.restrictSource
    (NoExoticSixSphere.modelChartPartialDiffeomorph (I := J) (f x)) hV
  have hsource : f x ∈ c.source := ⟨mem_extChartAt_source (I := J) (f x), hx⟩
  have hU : f ⁻¹' c.source ∈ 𝓝 x := (c.open_source.preimage f.continuous).mem_nhds hsource
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
  refine ⟨p, hχ, ?_, ?_⟩
  · change x ∈ interior {y : X | β y = 1}
    exact mem_interior_iff_mem_nhds.mpr β.eventuallyEq_one
  · exact inter_subset_right

theorem plateau_subset_outer (p : MapSmoothingPatch I J (X := X) (N := N)) :
    p.plateau ⊆ tsupport p.outer := by
  intro x hx
  apply p.inner_support_subset_outer
  apply subset_tsupport p.cutoff
  change p.cutoff x ≠ 0
  rw [interior_subset (s := {y | p.cutoff y = 1}) hx]
  exact one_ne_zero

variable [SigmaCompactSpace X]

theorem exists_smooth_avoiding_on_compact (f : C(X, N))
    {K C U : Set X} (hK : IsCompact K) (hC : IsClosed C) (hU : IsOpen U) (hCU : C ⊆ U)
    (hfU : ContMDiffOn I J ∞ f U) (hfK : ContMDiffOn I J ∞ f Kᶜ)
    {V : Set N} (hV : IsOpen V) (hfV : MapsTo f K V) :
    ∃ f' : C(X, N), ContMDiff I J ∞ f' ∧ f.HomotopicRel f' C ∧ MapsTo f' K V := by
  classical
  have hp (x : K) := exists_patch_in_open (I := I) (J := J) f hV x.val (hfV x.property)
  choose p hcompatible hplateau hsource using hp
  have hcover : K ⊆ ⋃ x : K, (p x).plateau := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hplateau ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun x : K => (p x).plateau)
    (fun _ => isOpen_interior) hcover
  obtain ⟨f', hc, hhom, hsm⟩ := exists_finite_patch_smoothing
    (fun i : s => p i.1) f (fun i => hcompatible i.1) hC hU hCU hfU Finset.univ
  refine ⟨f', ?_, hhom, ?_⟩
  · intro x
    apply hsm x
    by_cases hx : x ∈ K
    · obtain ⟨i, his, hxi⟩ := mem_iUnion₂.mp (hs hx)
      exact Or.inr ⟨⟨i, his⟩, Finset.mem_univ _, hxi⟩
    · exact Or.inl ((hfK x hx).contMDiffAt (hK.isClosed.isOpen_compl.mem_nhds hx))
  · intro x hx
    obtain ⟨i, his, hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact hsource i (hc ⟨i, his⟩ (plateau_subset_outer (p i) hxi))

end Wikipedia.HopfProblem.DegreeCollapse.RelativeAvoidingSmoothing
