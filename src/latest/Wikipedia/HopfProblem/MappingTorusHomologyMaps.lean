import Wikipedia.HopfProblem.MappingTorusHomologyHomotopies
import Wikipedia.HopfProblem.MappingTorusHomologyAlgebra
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy
import Wikipedia.HopfProblem.SingularMayerVietoris

/-!
# Actual inclusion maps in the mapping-torus Mayer–Vietoris sequence

The integral singular homology groups here are Mathlib's actual homology
objects. The interval charts and homotopies identify the two intersection
inclusions with the identity fold and the fold twisted by the given
homeomorphism. Consequently the actual signed Mayer–Vietoris map is
`(a,b) ↦ (a+b, -(a+f_*b))`, and its next map is the fibre inclusion
applied to `a+b`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.MappingTorusHomology

open SingularMayerVietoris PeriodTorusHigherHomology
open MappingTorus MappingTorus.HomologyCover

variable {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)

/-- The actual integral homology map of the given homeomorphism. -/
abbrev monodromyHomologyMap (n : ℕ) : SingularHomology X n →ₗ[ℤ] SingularHomology X n :=
  singularHomologyMap (f : C(X, X)) n

/-- The actual homeomorphism gives the corresponding homology automorphism. -/
def monodromyHomologyEquiv (n : ℕ) : SingularHomology X n ≃ₗ[ℤ] SingularHomology X n :=
  homeomorphHomologyEquiv f n

@[simp] theorem monodromyHomologyEquiv_toLinearMap (n : ℕ) :
    (monodromyHomologyEquiv f n).toLinearMap = monodromyHomologyMap f n := rfl

/-- The actual inclusion of the time-zero fibre induces this homomorphism. -/
abbrev fibreHomologyMap (n : ℕ) :
    SingularHomology X n →ₗ[ℤ] SingularHomology (Torus f) n :=
  singularHomologyMap (fibreInclusion f) n

/-- The concrete endpoint homotopy identifies a fibre class with its monodromy. -/
theorem fibreHomologyMap_comp_monodromy (n : ℕ) :
    (fibreHomologyMap f n).comp (monodromyHomologyMap f n) = fibreHomologyMap f n := by
  rw [← singularHomologyMap_comp]
  exact (homotopy_homologyMap (fibreMonodromyHomotopy f) n).symm

/-- Actual homology coordinates on the two open members. -/
def arcHomologyEquiv (n : ℕ) :
    (SingularHomology (U f) n × SingularHomology (V f) n) ≃ₗ[ℤ]
      (SingularHomology X n × SingularHomology X n) :=
  ((homotopyEquivHomologyEquiv (homotopyEquivU f) n).toAddEquiv.prodCongr
    (homotopyEquivHomologyEquiv (homotopyEquivV f) n).toAddEquiv).toIntLinearEquiv

@[simp] theorem arcHomologyEquiv_apply (n : ℕ)
    (a : SingularHomology (U f) n × SingularHomology (V f) n) :
    arcHomologyEquiv f n a =
      (homotopyEquivHomologyEquiv (homotopyEquivU f) n a.1,
        homotopyEquivHomologyEquiv (homotopyEquivV f) n a.2) := rfl

/-- Actual intersection homology, with lower and upper component coordinates in this order. -/
def intersectionHomologyEquiv (n : ℕ) :
    SingularHomology (U f ∩ V f : Set (Torus f)) n ≃ₗ[ℤ]
      (SingularHomology X n × SingularHomology X n) :=
  (homotopyEquivHomologyEquiv (intersectionHomotopyEquiv f) n).trans
    (sumHomologyEquiv X X n)

@[simp] theorem intersectionHomologyEquiv_apply (n : ℕ)
    (a : SingularHomology (U f ∩ V f : Set (Torus f)) n) :
    intersectionHomologyEquiv f n a = sumHomologyEquiv X X n
      (singularHomologyMap (intersectionHomotopyEquiv f).toFun n a) := rfl

theorem inclusionU_homology (n : ℕ) :
    singularHomologyMap (inclusionU f) n =
      (fibreHomologyMap f n).comp
        (homotopyEquivHomologyEquiv (homotopyEquivU f) n).toLinearMap := by
  rw [homotopy_homologyMap (inclusionUHomotopy f) n, singularHomologyMap_comp]
  rfl

theorem inclusionV_homology (n : ℕ) :
    singularHomologyMap (inclusionV f) n =
      (fibreHomologyMap f n).comp
        (homotopyEquivHomologyEquiv (homotopyEquivV f) n).toLinearMap := by
  rw [homotopy_homologyMap (inclusionVHomotopy f) n, singularHomologyMap_comp]
  rfl

/-- Both intersection components map by the identity in the first open chart. -/
theorem intersectionToU_homology (n : ℕ)
    (a : SingularHomology (U f ∩ V f : Set (Torus f)) n) :
    homotopyEquivHomologyEquiv (homotopyEquivU f) n
        (singularHomologyMap (intersectionToU f) n a) =
      (intersectionHomologyEquiv f n a).1 + (intersectionHomologyEquiv f n a).2 := by
  change singularHomologyMap (homotopyEquivU f).toFun n
    (singularHomologyMap (intersectionToU f) n a) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    intersectionToU_fold, singularHomologyMap_comp]
  simp only [LinearMap.comp_apply, intersectionHomologyEquiv_apply]
  exact sumHomologyEquiv_fold (X := X) n
    (singularHomologyMap (intersectionHomotopyEquiv f).toFun n a)

/-- The upper component contributes the actual monodromy in the second open chart. -/
theorem intersectionToV_homology (n : ℕ)
    (a : SingularHomology (U f ∩ V f : Set (Torus f)) n) :
    homotopyEquivHomologyEquiv (homotopyEquivV f) n
        (singularHomologyMap (intersectionToV f) n a) =
      (intersectionHomologyEquiv f n a).1 +
        monodromyHomologyMap f n (intersectionHomologyEquiv f n a).2 := by
  change singularHomologyMap (homotopyEquivV f).toFun n
    (singularHomologyMap (intersectionToV f) n a) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    intersectionToV_twistedFold, singularHomologyMap_comp]
  simp only [LinearMap.comp_apply, intersectionHomologyEquiv_apply]
  have h := sumHomologyEquiv_sumElim (ContinuousMap.id X) (f : C(X, X)) n
    (singularHomologyMap (intersectionHomotopyEquiv f).toFun n a)
  simpa only [singularHomologyMap_id, LinearMap.id_apply] using h

/-- The actual first Mayer–Vietoris map is the signed two-arc matrix. -/
theorem leftHomologyMap_coordinates (n : ℕ)
    (a : SingularHomology (U f ∩ V f : Set (Torus f)) n) :
    arcHomologyEquiv f n (leftHomologyMap (U f) (V f) n a) =
      Algebra.twoArcMap (monodromyHomologyMap f n) (intersectionHomologyEquiv f n a) := by
  rw [leftHomologyMap_apply]
  change
    (homotopyEquivHomologyEquiv (homotopyEquivU f) n
      (singularHomologyMap (intersectionToU f) n a),
      homotopyEquivHomologyEquiv (homotopyEquivV f) n
        (-singularHomologyMap (intersectionToV f) n a)) = _
  rw [map_neg, intersectionToU_homology, intersectionToV_homology]
  rfl

/-- The actual second Mayer–Vietoris map is the fibre inclusion on the sum of coordinates. -/
theorem rightHomologyMap_coordinates (n : ℕ)
    (a : SingularHomology (U f) n × SingularHomology (V f) n) :
    rightHomologyMap (U f) (V f) n a =
      fibreHomologyMap f n ((arcHomologyEquiv f n a).1 + (arcHomologyEquiv f n a).2) := by
  rw [rightHomologyMap_apply]
  change singularHomologyMap (inclusionU f) n a.1 +
    singularHomologyMap (inclusionV f) n a.2 = _
  rw [inclusionU_homology, inclusionV_homology]
  exact (map_add (fibreHomologyMap f n) _ _).symm

end Wikipedia.HopfProblem.MappingTorusHomology
