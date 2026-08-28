import Wikipedia.NoExoticSixSphere.PartialFrameMayerVietoris

/-!
# The actual center fiber and its patch homology map

The center section of a column chart is the original column reconstruction.
Its homology map is the inverse of the patch retraction, so the second
summand of the reduced Mayer–Vietoris map is the actual south fiber inclusion.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ColumnBundle

open GLOrthonormalization
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {n r : ℕ} (v : UnitSphere (Vector (r + 1)))
  (c : UnitSphere (Vector (n + 1)))

theorem fromCoordinates_center (a : Space n r) :
    fromCoordinates v c (c, a) = ColumnFiber.reconstruct v c a := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  change localRotationOperator c.val c.val ((ColumnFiber.reconstruct v c a).val x) = _
  rw [localRotationOperator_self]
  rfl

theorem reconstruct_mem_patch (a : Space n r) :
    ColumnFiber.reconstruct v c a ∈ Patch v c := by
  change column v (ColumnFiber.reconstruct v c a) ∈ baseSet c
  have he : column v (ColumnFiber.reconstruct v c a) = c :=
    Subtype.ext (ColumnFiber.reconstruct_column v c a)
  rw [he]
  exact center_mem_baseSet v c

def centerSection : C(Space n r, Patch v c) :=
  ⟨fun a ↦ ⟨ColumnFiber.reconstruct v c a, reconstruct_mem_patch v c a⟩,
    (ColumnFiber.continuous_reconstruct v c (fun a ↦ a) continuous_id).subtype_mk _⟩

theorem patchFiber_centerSection :
    (patchFiber v c).comp (centerSection v c) = ContinuousMap.id _ := by
  apply ContinuousMap.ext
  intro a
  change (toCoordinates v c (ColumnFiber.reconstruct v c a)).2 = a
  rw [← fromCoordinates_center, toCoordinates_fromCoordinates]

theorem inclusion_centerSection :
    (subtypeInclusion (Patch v c)).comp (centerSection v c) =
      ColumnFiber.reconstructionMap v c := rfl

theorem centerSection_homology (k : ℕ) (b : SingularHomology (Space n r) k) :
    singularHomologyMap (centerSection v c) k b =
      (homotopyEquivHomologyEquiv (patchHomotopyEquiv v c) k).symm b := by
  apply (homotopyEquivHomologyEquiv (patchHomotopyEquiv v c) k).injective
  rw [LinearEquiv.apply_symm_apply]
  change singularHomologyMap (patchFiber v c) k
    (singularHomologyMap (centerSection v c) k b) = b
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, patchFiber_centerSection,
    singularHomologyMap_id]
  rfl

end NoExoticSixSphere.Stiefel.ColumnBundle

namespace NoExoticSixSphere.Stiefel.ColumnHomology

open GLOrthonormalization ColumnBundle
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

theorem reducedRightMap_south {r : ℕ} (n : ℕ) (v : UnitSphere (Vector (r + 1)))
    (k : ℕ) (b : SingularHomology (Space (n + 1) r) k) :
    reducedRightMap n v k (0, b) =
      singularHomologyMap (ColumnFiber.reconstructionMap v
        (antipode (spherePole (n + 1)))) k b := by
  change rightHomologyMap (North n v) (South n v) k
    ((northEquiv n v k).symm 0, (southEquiv n v k).symm b) = _
  rw [map_zero, rightHomologyMap_apply, map_zero, zero_add]
  change singularHomologyMap (subtypeInclusion (South n v)) k
    ((homotopyEquivHomologyEquiv
      (patchHomotopyEquiv v (antipode (spherePole (n + 1)))) k).symm b) = _
  rw [← centerSection_homology, ← LinearMap.comp_apply, ← singularHomologyMap_comp,
    inclusion_centerSection]

end NoExoticSixSphere.Stiefel.ColumnHomology
