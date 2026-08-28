import Wikipedia.NoExoticSixSphere.ManifoldSpherePunctureCover
import Wikipedia.NoExoticSixSphere.OpenDisjointUnion

/-!
# Actual component decompositions of the global and one-point overlaps

Each neighborhood contains exactly its own removed point. In a one-point
comparison overlap, the selected component remains punctured and every other
component is the original whole neighborhood. The component maps are the
literal inclusions, not an assigned coordinate action.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily.ParityBallSystem

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {g : ℝ → Sphere 3 → M} (P : ParityBallSystem g)

theorem coverPiece_inter_punctures (i : BoundaryIndex g) :
    P.coverPiece i ∩ spherePunctures g = {spherePuncture g i} := by
  ext y
  constructor
  · rintro ⟨hy, hp⟩
    rw [← range_spherePuncture] at hp
    obtain ⟨j, rfl⟩ := hp
    have he : j = i := by
      by_contra hne
      exact disjoint_left.mp (P.pairwise_disjoint_coverPiece hne)
        (P.spherePuncture_mem_coverPiece j) hy
    subst j
    rfl
  · rintro rfl
    refine ⟨P.spherePuncture_mem_coverPiece i, ?_⟩
    rw [← range_spherePuncture]
    exact ⟨i, rfl⟩

def puncturedPiece (i : BoundaryIndex g) : Set (Sphere 4) :=
  sphereRegularSet g ∩ P.coverPiece i

def singlePiece (i j : BoundaryIndex g) : Set (Sphere 4) :=
  singlePunctureRegularSet g i ∩ P.coverPiece j

theorem puncturedPiece_eq_sdiff (i : BoundaryIndex g) :
    P.puncturedPiece i = P.coverPiece i \ {spherePuncture g i} := by
  ext y
  have h : y ∈ P.coverPiece i ∩ spherePunctures g ↔ y = spherePuncture g i := by
    rw [P.coverPiece_inter_punctures]
    rfl
  change (y ∈ P.coverPiece i ∧ y ∈ spherePunctures g ↔ y = spherePuncture g i) at h
  change (y ∉ spherePunctures g ∧ y ∈ P.coverPiece i) ↔
    y ∈ P.coverPiece i ∧ y ≠ spherePuncture g i
  tauto

theorem singlePiece_same (i : BoundaryIndex g) : P.singlePiece i i = P.puncturedPiece i := by
  rw [P.puncturedPiece_eq_sdiff]
  ext y
  exact and_comm

theorem singlePiece_other (i j : BoundaryIndex g) (hne : i ≠ j) :
    P.singlePiece i j = P.coverPiece j := by
  ext y
  constructor
  · exact fun hy ↦ hy.2
  · intro hy
    refine ⟨?_, hy⟩
    intro he
    exact disjoint_left.mp (P.pairwise_disjoint_coverPiece hne)
      (P.spherePuncture_mem_coverPiece i) (he ▸ hy)

theorem isOpen_puncturedPiece (i : BoundaryIndex g) : IsOpen (P.puncturedPiece i) :=
  P.isOpen_sphereRegularSet.inter (P.isOpen_coverPiece i)

theorem isOpen_singlePiece (i j : BoundaryIndex g) : IsOpen (P.singlePiece i j) :=
  (isOpen_singlePunctureRegularSet g i).inter (P.isOpen_coverPiece j)

def overlapHomeomorph : (Σ i, P.puncturedPiece i) ≃ₜ
    (sphereRegularSet g ∩ P.coverRegion : Set (Sphere 4)) :=
  OpenDisjointUnion.intersectionHomeomorph P.coverPiece (sphereRegularSet g)
    P.isOpen_sphereRegularSet P.isOpen_coverPiece P.pairwise_disjoint_coverPiece

def singleOverlapHomeomorph (i : BoundaryIndex g) : (Σ j, P.singlePiece i j) ≃ₜ
    (singlePunctureRegularSet g i ∩ P.coverRegion : Set (Sphere 4)) :=
  OpenDisjointUnion.intersectionHomeomorph P.coverPiece (singlePunctureRegularSet g i)
    (isOpen_singlePunctureRegularSet g i) P.isOpen_coverPiece P.pairwise_disjoint_coverPiece

def overlapComponentMap (i j : BoundaryIndex g) : C(P.puncturedPiece j, P.singlePiece i j) :=
  ContinuousMap.inclusion (inter_subset_inter_left _ (sphereRegular_subset_single g i))

theorem overlapComponentMap_self (i : BoundaryIndex g) :
    P.overlapComponentMap i i =
      (Homeomorph.setCongr (P.singlePiece_same i).symm :
        C(P.puncturedPiece i, P.singlePiece i i)) := rfl

end NoExoticSixSphere.SphereFamily.ParityBallSystem
