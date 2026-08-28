import Wikipedia.NoExoticSixSphere.ManifoldParityBallSystem

/-!
# The actual compact parameter cylinder with its singular balls removed

The complement uses the original topology on time times the three-sphere.
It contains no intrinsic singularity. Its ambient topological frontier is
exactly the two original endpoint spheres together with the actual linking
spheres. No manifold-with-boundary atlas or global parity formula is asserted
by these topological statements.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily.ParityBallSystem

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {g : ℝ → Sphere 3 → M} (P : ParityBallSystem g)

def puncturedCylinder : Set (ℝ × Sphere 3) :=
  (Icc (0 : ℝ) 1 ×ˢ (univ : Set (Sphere 3))) \ P.openHoles

theorem isCompact_puncturedCylinder : IsCompact P.puncturedCylinder :=
  (isCompact_Icc.prod isCompact_univ).diff P.isOpen_openHoles

theorem injective_mfderiv_on_puncturedCylinder (q : ℝ × Sphere 3)
    (hq : q ∈ P.puncturedCylinder) : Injective (mfderiv (𝓡 3) (𝓡 6) (g q.1) q.2) := by
  by_contra hsing
  exact hq.2 (P.singular_subset_openHoles hsing)

theorem interior_puncturedCylinder : interior P.puncturedCylinder =
    (Ioo (0 : ℝ) 1 ×ˢ (univ : Set (Sphere 3))) \ P.closedHoles := by
  rw [puncturedCylinder, sdiff_eq, interior_inter, interior_prod_eq, interior_Icc,
    interior_univ, interior_compl, P.closure_openHoles]
  rfl

theorem frontier_puncturedCylinder : frontier P.puncturedCylinder =
    ({0, 1} : Set ℝ) ×ˢ (univ : Set (Sphere 3)) ∪ P.linkingBoundary := by
  have htime : (Icc (0 : ℝ) 1 ×ˢ (univ : Set (Sphere 3))) \
      (Ioo (0 : ℝ) 1 ×ˢ (univ : Set (Sphere 3))) =
      ({0, 1} : Set ℝ) ×ˢ (univ : Set (Sphere 3)) := by
    rw [← frontier_Icc zero_le_one, ← frontier_prod_univ_eq,
      (isClosed_Icc.prod isClosed_univ).frontier_eq,
      interior_prod_eq, interior_Icc, interior_univ]
  rw [P.isCompact_puncturedCylinder.isClosed.frontier_eq, P.interior_puncturedCylinder,
    puncturedCylinder, ← htime, ← P.closedHoles_sdiff_openHoles]
  ext q
  have hCI : q ∈ P.closedHoles → q ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set (Sphere 3)) :=
    fun hq ↦ P.closedHoles_subset_interiorTime hq
  have hIA : q ∈ Ioo (0 : ℝ) 1 ×ˢ (univ : Set (Sphere 3)) →
      q ∈ Icc (0 : ℝ) 1 ×ˢ (univ : Set (Sphere 3)) :=
    fun hq ↦ ⟨⟨hq.1.1.le, hq.1.2.le⟩, hq.2⟩
  have hUC : q ∈ P.openHoles → q ∈ P.closedHoles :=
    fun hq ↦ P.openHoles_subset_closedHoles hq
  simp only [mem_sdiff, mem_union]
  tauto

theorem linkingBoundary_subset_puncturedCylinder :
    P.linkingBoundary ⊆ P.puncturedCylinder := by
  rw [← P.closedHoles_sdiff_openHoles]
  intro q hq
  have ht := P.closedHoles_subset_interiorTime hq.1
  exact ⟨⟨⟨ht.1.1.le, ht.1.2.le⟩, ht.2⟩, hq.2⟩

theorem endpoint_mem_puncturedCylinder (t : ℝ) (ht : t = 0 ∨ t = 1) (x : Sphere 3) :
    (t, x) ∈ P.puncturedCylinder := by
  apply P.isCompact_puncturedCylinder.isClosed.frontier_subset
  rw [P.frontier_puncturedCylinder]
  exact Or.inl ⟨ht, mem_univ x⟩

theorem endpoint_disjoint_linkingBoundary :
    Disjoint (({0, 1} : Set ℝ) ×ˢ (univ : Set (Sphere 3))) P.linkingBoundary := by
  apply disjoint_left.mpr
  intro q hq hlink
  rw [← P.closedHoles_sdiff_openHoles] at hlink
  have ht := (P.closedHoles_subset_interiorTime hlink.1).1
  rcases hq.1 with hzero | hone
  · exact (ne_of_gt ht.1) hzero
  · exact (ne_of_lt ht.2) hone

end NoExoticSixSphere.SphereFamily.ParityBallSystem
