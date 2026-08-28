import Wikipedia.HopfProblem.DegreeCollapseCriticalWindowCrossing

/-!
# One relative native isotopy prepares the whole original finite family

The finite disjoint source sum has exactly the union of the original
images. Applying native avoidance to that compact smooth map prepares all
members together with one actual supported isotopy and one protected set.
No initial avoidance from the crossed sheet is required.
-/

noncomputable section

open Set Function Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

variable {ι D Z G H H' K X Y N : Type} [Finite ι]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
  {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

theorem exists_whole_family_avoidance (a : ι → X → N) (ha : ∀ j, ContMDiff I J ∞ (a j))
    {g : Y → N} (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G)
    {C : Set N} (hC : IsClosed C) (haC : ∀ j, Disjoint (range (a j)) C) :
    ∃ (e : Diffeomorph J J N N ∞) (K : Set N),
      IsCompact K ∧ K ⊆ Cᶜ ∧ Nonempty (SupportedRelativeIsotopy e K C) ∧
      ∀ j, Disjoint (range (e ∘ a j)) (range g) := by
  obtain ⟨n, b, hb, hbrange⟩ := exists_sheetSumMap_for_finite_family a ha
  have hbC : Disjoint (range b) C := by
    apply Set.disjoint_left.mpr
    intro z hz hzC
    rw [hbrange] at hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz
    exact Set.disjoint_left.mp (haC j) hj hzC
  obtain ⟨e, K, hK, hKC, hIso, hdisj⟩ :=
    exists_supported_ambient_disjoint_fixing_closed hb hg hdim hC hbC
  refine ⟨e, K, hK, hKC, hIso, ?_⟩
  intro j
  apply Set.disjoint_left.mpr
  intro z hz hzg
  obtain ⟨x, hx⟩ := hz
  have hx' : a j x ∈ range b := by
    rw [hbrange]
    exact mem_iUnion.mpr ⟨j, mem_range_self x⟩
  obtain ⟨w, hw⟩ := hx'
  apply Set.disjoint_left.mp hdisj _ hzg
  refine ⟨w, ?_⟩
  change e (b w) = z
  rw [hw]
  exact hx

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
