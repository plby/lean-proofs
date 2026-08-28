import Wikipedia.HopfProblem.DegreeCollapseDiskHomotopyExtension
import Wikipedia.HopfProblem.OrbitPairHomotopyExtensionPushout
import Wikipedia.NoExoticSixSphere.EuclideanLocalHomology

/-!
# Homotopy extension and homology for the actual normed characteristic disk

The disk-cylinder retraction works for any finite-dimensional normed
space, including the max-norm coordinate space used by the James cells.
Radial homotopy equivalences compare its boundary sphere with the Euclidean
sphere. Only homology vanishing is transported, not an unproved isometry.
-/

noncomputable section

open CategoryTheory Set Metric Topology
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology OrbitPair
open Wikipedia.SmoothSixDPoincare

namespace NoExoticSixSphere.NormedDiskHomology

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

def puncturedHomeomorph (e : E ≃L[ℝ] F) : PuncturedRadial.Space E ≃ₜ PuncturedRadial.Space F :=
  e.toHomeomorph.subtype (fun x ↦ by
    change x ≠ 0 ↔ e x ≠ 0
    constructor
    · intro hx he
      exact hx (e.injective (he.trans (map_zero e).symm))
    · intro hx he
      exact hx (he ▸ map_zero e))

def sphereHomotopyEquiv (e : E ≃L[ℝ] F) :
    ContinuousMap.HomotopyEquiv (sphere (0 : E) 1) (sphere (0 : F) 1) :=
  ((PuncturedRadial.sphereHomotopyEquiv (N := E) 1 zero_lt_one).trans
    (puncturedHomeomorph e).toHomotopyEquiv).trans
      (PuncturedRadial.sphereHomotopyEquiv (N := F) 1 zero_lt_one).symm

theorem finiteSphere_homology_subsingleton (m d : ℕ) (hm : 2 ≤ m)
    (hd : d ≠ 0) (hdm : d + 1 ≠ m) :
    Subsingleton (SingularHomology (sphere (0 : Fin m → ℝ) 1) d) := by
  let : Subsingleton (SingularHomology (sphere (0 : EuclideanSpace ℝ (Fin m)) 1) d) := by
    have he : m = (m - 2) + 2 := (Nat.sub_add_cancel hm).symm
    rw [he]
    exact SphereHomology.unitSphere_homology_subsingleton (m - 2) d hd (by omega)
  exact (homotopyEquivHomologyEquiv
    (sphereHomotopyEquiv (EuclideanSpace.equiv (Fin m) ℝ).symm) d).injective.subsingleton

abbrev Disk (E : Type) [NormedAddCommGroup E] := closedBall (0 : E) 1

def boundary (E : Type) [NormedAddCommGroup E] : Set (Disk E) :=
  {x | x.val ∈ sphere (0 : E) 1}

def boundaryHomeomorph (E : Type) [NormedAddCommGroup E] :
    sphere (0 : E) 1 ≃ₜ boundary E where
  toFun x := ⟨⟨x.val, sphere_subset_closedBall x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def sphereInclusion (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    TopCat.of (sphere (0 : E) 1) ⟶ TopCat.of (Disk E) :=
  TopCat.ofHom (DegreeCollapse.DiskCylinder.boundaryToDisk (E := E))

def boundaryInclusion (E : Type) [NormedAddCommGroup E] :
    TopCat.of (boundary E) ⟶ TopCat.of (Disk E) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem sphere_hasHomotopyExtension (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    HomotopyExtension.HasHomotopyExtension (sphereInclusion E) := by
  intro Z f G h0
  exact DegreeCollapse.DiskCylinder.exists_disk_homotopy_extension f G h0

theorem boundary_hasHomotopyExtension (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    HomotopyExtension.HasHomotopyExtension (boundaryInclusion E) := by
  have he : boundaryInclusion E =
      (TopCat.isoOfHomeo (boundaryHomeomorph E)).inv ≫ sphereInclusion E := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl
  rw [he]
  exact HomotopyExtension.comp _ _ (HomotopyExtension.of_isIso _)
    (sphere_hasHomotopyExtension E)

theorem disk_homology_subsingleton (m d : ℕ) (hd : d ≠ 0) :
    Subsingleton (SingularHomology (Disk (Fin m → ℝ)) d) := by
  let : ContractibleSpace (Disk (Fin m → ℝ)) :=
    (convex_closedBall (0 : Fin m → ℝ) 1).contractibleSpace
      ⟨0, mem_closedBall_self zero_le_one⟩
  exact contractible_homology_subsingleton _ d hd

theorem boundary_homology_subsingleton (m d : ℕ) (hm : 2 ≤ m)
    (hd : d ≠ 0) (hdm : d + 1 ≠ m) :
    Subsingleton (SingularHomology (boundary (Fin m → ℝ)) d) := by
  let := finiteSphere_homology_subsingleton m d hm hd hdm
  exact (homeomorphHomologyEquiv (boundaryHomeomorph (Fin m → ℝ)) d).symm.injective.subsingleton

end NoExoticSixSphere.NormedDiskHomology
