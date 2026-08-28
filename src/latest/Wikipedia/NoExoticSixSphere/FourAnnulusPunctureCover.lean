import Wikipedia.NoExoticSixSphere.FourAnnulusPuncturedRetraction
import Wikipedia.NoExoticSixSphere.FourDiskPuncturedBall
import Wikipedia.NoExoticSixSphere.OpenDisjointUnion

/-!
# The original singularity-ball cover of nonzero four-dimensional space

The actual singular complement and the original open balls cover the
complement of the origin. Flat and nested subtype coordinates are related
by explicit homeomorphisms that retain the literal vectors. The original
overlap is a disjoint union of the actual punctured chart balls.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.GenericFourAnnulus

open GLOrthonormalization AnnulusDoublePoints SphereAnnulus

abbrev NonzeroAmbient := {y : Vector 4 // y ≠ 0}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]

def complementInNonzero (g : Vector 4 → M) : C(SingularComplement g, NonzeroAmbient) where
  toFun y := ⟨y.val, y.property.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def nonzeroComplementSet (g : Vector 4 → M) : Set NonzeroAmbient :=
  {y | y.val ∉ singularSet g}

def complementHomeomorph (g : Vector 4 → M) :
    SingularComplement g ≃ₜ nonzeroComplementSet g where
  toFun y := ⟨complementInNonzero g y, y.property.2⟩
  invFun y := ⟨y.val.val, y.val.property, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (complementInNonzero g).continuous.subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

namespace ParityBallSystem

variable {g : Vector 4 → M} (P : ParityBallSystem g)

include P in
theorem isOpen_singularComplementSet : IsOpen (singularComplementSet g) :=
  isClosed_singleton.isOpen_compl.inter P.finite_singular.isClosed.isOpen_compl

theorem openHoles_nonzero {y : Vector 4} (hy : y ∈ P.openHoles) : y ≠ 0 :=
  SphereAnnulus.ne_zero ⟨y, openDomain_subset_domain 3
    (P.closedHoles_subset_interior (P.openHoles_subset_closedHoles hy))⟩

def nonzeroHoles : Set NonzeroAmbient := {y | y.val ∈ P.openHoles}

include P in
theorem isOpen_nonzeroComplementSet : IsOpen (nonzeroComplementSet g) :=
  P.finite_singular.isClosed.isOpen_compl.preimage continuous_subtype_val

theorem isOpen_nonzeroHoles : IsOpen P.nonzeroHoles :=
  P.isOpen_openHoles.preimage continuous_subtype_val

theorem nonzero_complement_cover : nonzeroComplementSet g ∪ P.nonzeroHoles = univ := by
  apply eq_univ_of_forall
  intro y
  by_cases hy : y.val ∈ singularSet g
  · exact Or.inr (P.singular_subset_openHoles hy)
  · exact Or.inl hy

def nonzeroOverlapHomeomorph :
    (singularComplementSet g ∩ P.openHoles : Set (Vector 4)) ≃ₜ
      (nonzeroComplementSet g ∩ P.nonzeroHoles : Set NonzeroAmbient) where
  toFun y := ⟨⟨y.val, y.property.1.1⟩, y.property.1.2, y.property.2⟩
  invFun y := ⟨y.val.val, ⟨y.val.property, y.property.1⟩, y.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem nonzeroOverlap_comparison :
    (ContinuousMap.inclusion
      (inter_subset_left : nonzeroComplementSet g ∩ P.nonzeroHoles ⊆ nonzeroComplementSet g)).comp
        (P.nonzeroOverlapHomeomorph : C(_, _)) =
      (complementHomeomorph g : C(_, _)).comp
        (ContinuousMap.inclusion (inter_subset_left :
          singularComplementSet g ∩ P.openHoles ⊆ singularComplementSet g)) := by
  apply ContinuousMap.ext
  intro y
  rfl

theorem pairwise_disjoint_openRegion : Pairwise (fun x y ↦
    Disjoint (P.ball x).openRegion (P.ball y).openRegion) := by
  intro x y hxy
  exact (P.pairwise_disjoint hxy).mono (P.ball x).openRegion_subset_closedRegion
    (P.ball y).openRegion_subset_closedRegion

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

theorem puncturedPiece_eq_region (x : singularSet g) :
    P.puncturedPiece x = (P.ball x).puncturedOpenRegion := by
  ext y
  have h : y ∈ (P.ball x).openRegion ∩ singularSet g ↔ y = x.val := by
    rw [P.openRegion_inter_singular]
    rfl
  have hn : y ∈ (P.ball x).openRegion → y ≠ 0 :=
    fun hy ↦ P.openHoles_nonzero (mem_iUnion.mpr ⟨x, hy⟩)
  change (y ∈ (P.ball x).openRegion ∧ y ∈ singularSet g ↔ y = x.val) at h
  change ((y ≠ 0 ∧ y ∉ singularSet g) ∧ y ∈ (P.ball x).openRegion) ↔
    y ∈ (P.ball x).openRegion ∧ y ≠ x.val
  tauto

def openHolesHomeomorph : (Σ x, (P.ball x).openRegion) ≃ₜ P.openHoles :=
  OpenDisjointUnion.homeomorph (fun x ↦ (P.ball x).openRegion)
    (fun x ↦ (P.ball x).isOpen_openRegion) P.pairwise_disjoint_openRegion

def overlapHomeomorph : (Σ x, P.puncturedPiece x) ≃ₜ
    (singularComplementSet g ∩ P.openHoles : Set (Vector 4)) :=
  OpenDisjointUnion.intersectionHomeomorph (fun x ↦ (P.ball x).openRegion)
    (singularComplementSet g) P.isOpen_singularComplementSet
    (fun x ↦ (P.ball x).isOpen_openRegion) P.pairwise_disjoint_openRegion

def pieceSphereEquiv (x : singularSet g) : P.puncturedPiece x ≃ₕ Sphere 3 :=
  (Homeomorph.setCongr (P.puncturedPiece_eq_region x)).toHomotopyEquiv.trans
    (P.ball x).puncturedSphereEquiv

theorem pieceSphereEquiv_symm_apply (x : singularSet g) (q : Sphere 3) :
    ((P.pieceSphereEquiv x).symm q).val = (P.ball x).chart ((1 / 2 : ℝ) • q.val) := rfl

end ParityBallSystem
end NoExoticSixSphere.GenericFourAnnulus
