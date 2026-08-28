import Wikipedia.NoExoticSixSphere.FourAnnulusPunctureCover

/-!
# Original one-point comparisons for the annulus overlap

Forgetting the origin and all but one singular point gives the actual
one-point complement. Together with the retained ball union it covers
all of four-dimensional Euclidean space. Only the selected overlap
component is punctured; every other component is its original open ball.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourAnnulus

open GLOrthonormalization AnnulusDoublePoints

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]

abbrev singleComplementSet (g : Vector 4 → M) (x : singularSet g) : Set (Vector 4) := {x.val}ᶜ

theorem isOpen_singleComplementSet (g : Vector 4 → M) (x : singularSet g) :
    IsOpen (singleComplementSet g x) := isClosed_singleton.isOpen_compl

theorem singularComplement_subset_single (g : Vector 4 → M) (x : singularSet g) :
    singularComplementSet g ⊆ singleComplementSet g x :=
  fun _ hy he ↦ hy.2 (he.symm ▸ x.property)

def complementToSingle (g : Vector 4 → M) (x : singularSet g) :
    C(SingularComplement g, singleComplementSet g x) :=
  ContinuousMap.inclusion (singularComplement_subset_single g x)

namespace ParityBallSystem

variable {g : Vector 4 → M} (P : ParityBallSystem g)

theorem single_complement_cover (x : singularSet g) :
    singleComplementSet g x ∪ P.openHoles = univ := by
  apply eq_univ_of_forall
  intro y
  by_cases hy : y = x.val
  · subst y
    exact Or.inr (P.singular_subset_openHoles x.property)
  · exact Or.inl hy

def singlePiece (x y : singularSet g) : Set (Vector 4) :=
  singleComplementSet g x ∩ (P.ball y).openRegion

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

end ParityBallSystem
end NoExoticSixSphere.GenericFourAnnulus
