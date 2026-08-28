import Wikipedia.NoExoticSixSphere.FourDiskPuncturedBallHomotopy
import Wikipedia.NoExoticSixSphere.OpenDisjointUnion

/-!
# The actual finite-puncture cover of four-dimensional Euclidean space

The complement of the original closed-disk singular set and the union of
the original open balls cover the entire Euclidean space. Their overlap
is the actual disjoint union of punctured chart balls. In each one-point
comparison only its own component remains punctured.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourDisk

open GLOrthonormalization DiskDoublePoints

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]

abbrev singularComplementSet (g : Vector 4 → M) : Set (Vector 4) := (singularSet g)ᶜ

abbrev singleComplementSet (g : Vector 4 → M) (x : singularSet g) : Set (Vector 4) := {x.val}ᶜ

theorem isOpen_singleComplementSet (g : Vector 4 → M) (x : singularSet g) :
    IsOpen (singleComplementSet g x) := isClosed_singleton.isOpen_compl

theorem singularComplement_subset_single (g : Vector 4 → M) (x : singularSet g) :
    singularComplementSet g ⊆ singleComplementSet g x :=
  fun _ hy he ↦ hy (he.symm ▸ x.property)

def complementToSingle (g : Vector 4 → M) (x : singularSet g) :
    C(SingularComplement g, singleComplementSet g x) :=
  ContinuousMap.inclusion (singularComplement_subset_single g x)

namespace ParityBallSystem

variable {g : Vector 4 → M} (P : ParityBallSystem g)

include P in
theorem isOpen_singularComplementSet : IsOpen (singularComplementSet g) :=
  P.finite_singular.isClosed.isOpen_compl

theorem pairwise_disjoint_openRegion : Pairwise (fun x y ↦
    Disjoint (P.ball x).openRegion (P.ball y).openRegion) := by
  intro x y hxy
  exact (P.pairwise_disjoint hxy).mono (P.ball x).openRegion_subset_closedRegion
    (P.ball y).openRegion_subset_closedRegion

theorem singular_complement_cover : singularComplementSet g ∪ P.openHoles = univ := by
  apply eq_univ_of_forall
  intro y
  by_cases hy : y ∈ singularSet g
  · exact Or.inr (P.singular_subset_openHoles hy)
  · exact Or.inl hy

theorem single_complement_cover (x : singularSet g) :
    singleComplementSet g x ∪ P.openHoles = univ := by
  apply eq_univ_of_forall
  intro y
  by_cases hy : y = x.val
  · subst y
    exact Or.inr (P.singular_subset_openHoles x.property)
  · exact Or.inl hy

theorem openRegion_inter_singular (x : singularSet g) :
    (P.ball x).openRegion ∩ singularSet g = {x.val} := by
  ext y
  constructor
  · intro hy
    have hm : y ∈ (P.ball x).closedRegion ∩
        {z | ¬ Injective (mfderiv (𝓡 4) (𝓡 7) g z)} :=
      ⟨(P.ball x).openRegion_subset_closedRegion hy.1, hy.2.2⟩
    rwa [(P.ball x).closedRegion_inter_singular] at hm
  · rintro rfl
    exact ⟨(P.ball x).center_mem_openRegion, x.property⟩

def puncturedPiece (x : singularSet g) : Set (Vector 4) :=
  singularComplementSet g ∩ (P.ball x).openRegion

def singlePiece (x y : singularSet g) : Set (Vector 4) :=
  singleComplementSet g x ∩ (P.ball y).openRegion

theorem puncturedPiece_eq_region (x : singularSet g) :
    P.puncturedPiece x = (P.ball x).puncturedOpenRegion := by
  ext y
  have h : y ∈ (P.ball x).openRegion ∩ singularSet g ↔ y = x.val := by
    rw [P.openRegion_inter_singular]
    rfl
  change (y ∈ (P.ball x).openRegion ∧ y ∈ singularSet g ↔ y = x.val) at h
  change (y ∉ singularSet g ∧ y ∈ (P.ball x).openRegion) ↔
    y ∈ (P.ball x).openRegion ∧ y ≠ x.val
  tauto

theorem singlePiece_same (x : singularSet g) : P.singlePiece x x = P.puncturedPiece x := by
  rw [P.puncturedPiece_eq_region]
  ext y
  exact and_comm

theorem singlePiece_other (x y : singularSet g) (hne : x ≠ y) :
    P.singlePiece x y = (P.ball y).openRegion := by
  ext z
  constructor
  · exact fun hz ↦ hz.2
  · intro hz
    refine ⟨?_, hz⟩
    intro he
    exact disjoint_left.mp (P.pairwise_disjoint_openRegion hne)
      (P.ball x).center_mem_openRegion (he ▸ hz)

def openHolesHomeomorph : (Σ x, (P.ball x).openRegion) ≃ₜ P.openHoles :=
  OpenDisjointUnion.homeomorph (fun x ↦ (P.ball x).openRegion)
    (fun x ↦ (P.ball x).isOpen_openRegion) P.pairwise_disjoint_openRegion

def overlapHomeomorph : (Σ x, P.puncturedPiece x) ≃ₜ
    (singularComplementSet g ∩ P.openHoles : Set (Vector 4)) :=
  OpenDisjointUnion.intersectionHomeomorph (fun x ↦ (P.ball x).openRegion)
    (singularComplementSet g) P.isOpen_singularComplementSet
    (fun x ↦ (P.ball x).isOpen_openRegion) P.pairwise_disjoint_openRegion

def singleOverlapHomeomorph (x : singularSet g) : (Σ y, P.singlePiece x y) ≃ₜ
    (singleComplementSet g x ∩ P.openHoles : Set (Vector 4)) :=
  OpenDisjointUnion.intersectionHomeomorph (fun y ↦ (P.ball y).openRegion)
    (singleComplementSet g x) (isOpen_singleComplementSet g x)
    (fun y ↦ (P.ball y).isOpen_openRegion) P.pairwise_disjoint_openRegion

def globalToSingleIntersection (x : singularSet g) :
    C((singularComplementSet g ∩ P.openHoles : Set (Vector 4)),
      (singleComplementSet g x ∩ P.openHoles : Set (Vector 4))) :=
  ContinuousMap.inclusion (inter_subset_inter_left _ (singularComplement_subset_single g x))

def overlapComponentMap (x y : singularSet g) : C(P.puncturedPiece y, P.singlePiece x y) :=
  ContinuousMap.inclusion (inter_subset_inter_left _ (singularComplement_subset_single g x))

theorem overlapComponentMap_self (x : singularSet g) :
    P.overlapComponentMap x x =
      (Homeomorph.setCongr (P.singlePiece_same x).symm :
        C(P.puncturedPiece x, P.singlePiece x x)) := rfl

def pieceSphereEquiv (x : singularSet g) : P.puncturedPiece x ≃ₕ Sphere 3 :=
  (Homeomorph.setCongr (P.puncturedPiece_eq_region x)).toHomotopyEquiv.trans
    (P.ball x).puncturedSphereEquiv

theorem pieceSphereEquiv_symm_apply (x : singularSet g) (s : Sphere 3) :
    ((P.pieceSphereEquiv x).symm s).val = (P.ball x).chart ((1 / 2 : ℝ) • s.val) := rfl

end ParityBallSystem
end NoExoticSixSphere.GenericFourDisk
