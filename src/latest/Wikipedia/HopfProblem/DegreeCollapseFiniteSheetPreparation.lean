import Wikipedia.HopfProblem.DegreeCollapseRelativeAmbientAvoidance

/-!
# Prepare one member of a finite disjoint family without changing the others

The protected union is constructed from the original compact sheet images.
The whole preparation fixes each other sheet and its ambient germ at every
real time. Every time slice is injective, so the full family's pairwise
disjointness persists through the constructed motion.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

def otherSheetImages {ι X N : Type*} (a : ι → X → N) (i : ι) : Set N :=
  ⋃ j : {j : ι // j ≠ i}, range (a j.val)

theorem mem_otherSheetImages {ι X N : Type*} (a : ι → X → N) (i j : ι)
    (hji : j ≠ i) (x : X) : a j x ∈ otherSheetImages a i :=
  mem_iUnion.mpr ⟨⟨j, hji⟩, mem_range_self x⟩

theorem pairwise_disjoint_ranges_postcomp {ι X N P : Type*}
    (a : ι → X → N) (hpair : Pairwise (fun i j => Disjoint (range (a i)) (range (a j))))
    {e : N → P} (he : Injective e) :
    Pairwise (fun i j => Disjoint (range (e ∘ a i)) (range (e ∘ a j))) := by
  intro i j hij
  rw [range_comp, range_comp]
  exact (Set.disjoint_image_iff he).mpr (hpair hij)

section Germ

variable {G K N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace K] {J : ModelWithCorners ℝ G K}
  [TopologicalSpace N] [ChartedSpace K N] [T2Space N]

theorem supported_ambient_isotopy_fixed_germ
    {e : Diffeomorph J J N N ∞} {C T : Set N}
    (A : SupportedRelativeIsotopy e C T) (hC : IsCompact C) {x : N} (hx : x ∉ C)
    (t : ℝ) : (fun z => A.family (t, z)) =ᶠ[𝓝 x] id := by
  filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hx] with z hz
  exact A.fixedOutside t z hz

end Germ

variable {ι D Z G H H' K X Y N : Type*} [Finite ι]
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
  {J : ModelWithCorners ℝ G K} [I.Boundaryless] [I'.Boundaryless] [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X] [T2Space X]
  [TopologicalSpace Y] [ChartedSpace H' Y] [IsManifold I' ∞ Y] [CompactSpace Y]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

theorem exists_finite_sheet_preparation (a : ι → X → N) (ha : ∀ j, ContMDiff I J ∞ (a j))
    (hpair : Pairwise (fun j k => Disjoint (range (a j)) (range (a k))))
    {g : Y → N} (hg : ContMDiff I' J ∞ g)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) (i : ι) :
    ∃ (e : Diffeomorph J J N N ∞) (C : Set N),
      IsCompact C ∧ C ⊆ (otherSheetImages a i)ᶜ ∧
      ∃ A : SupportedRelativeIsotopy e C (otherSheetImages a i),
        Disjoint (range (e ∘ a i)) (range g) ∧
        (∀ t j, j ≠ i → ∀ x, A.family (t, a j x) = a j x) ∧
        (∀ t j, j ≠ i → ∀ x, (fun z => A.family (t, z)) =ᶠ[𝓝 (a j x)] id) ∧
        ∀ t, Pairwise (fun j k =>
          Disjoint (range ((fun z => A.family (t, z)) ∘ a j))
            (range ((fun z => A.family (t, z)) ∘ a k))) := by
  have hclosed : IsClosed (otherSheetImages a i) :=
    isClosed_iUnion_of_finite (fun j : {j : ι // j ≠ i} =>
      (isCompact_range (ha j.val).continuous).isClosed)
  have hdisj : Disjoint (range (a i)) (otherSheetImages a i) := by
    apply Set.disjoint_left.mpr
    intro z hz hother
    obtain ⟨j, hj⟩ := mem_iUnion.mp hother
    exact Set.disjoint_left.mp (hpair j.property.symm) hz hj
  obtain ⟨e, C, hC, hCU, ⟨A⟩, hnew⟩ :=
    exists_supported_ambient_disjoint_fixing_closed (ha i) hg hdim hclosed hdisj
  refine ⟨e, C, hC, hCU, A, hnew, ?_, ?_, ?_⟩
  · intro t j hji x
    exact A.fixedOn t (a j x) (mem_otherSheetImages a i j hji x)
  · intro t j hji x
    exact supported_ambient_isotopy_fixed_germ A hC
      (fun hx => hCU hx (mem_otherSheetImages a i j hji x)) t
  · intro t
    obtain ⟨d, hd⟩ := A.slices t
    have heq : (fun z => A.family (t, z)) = d := funext (fun z => (hd z).symm)
    rw [heq]
    exact pairwise_disjoint_ranges_postcomp a hpair d.injective

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
