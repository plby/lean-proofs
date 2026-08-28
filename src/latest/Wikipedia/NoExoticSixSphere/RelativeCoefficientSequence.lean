import Wikipedia.NoExoticSixSphere.RelativeCoefficientExactness
import Wikipedia.HopfProblem.SphereHomologyCoefficientsChains
import Wikipedia.HopfProblem.SphereHomologyCoefficientsAlgebra

/-!
# The actual coefficient sequence for relative singular homology

Multiplication by `p` and the native coefficient reduction give a short
exact sequence of the original relative complexes. Its homology sequence
identifies the exact kernel of reduction and its Bockstein obstruction.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris SphereHomologyCoefficients

namespace NoExoticSixSphere.RelativeCoefficients

variable {X : Type} [TopologicalSpace X]

/-- Homology of the original relative complex with coefficients `ℤ/p`. -/
abbrev ModHomology (p : ℕ) (U : Set X) (n : ℕ) : ModuleCat.{0} ℤ :=
  (complex (ModuleCat.of ℤ (ZMod p)) U).homology n

/-- Native coefficient reduction on the original relative complexes. -/
abbrev reduction (p : ℕ) (U : Set X) :
    RelativeSingularHomology.complex U ⟶ complex (ModuleCat.of ℤ (ZMod p)) U :=
  change (reductionCoefficient p) U

theorem change_multiplication (p : ℕ) (U : Set X) :
    change ((p : ℤ) • 𝟙 (ModuleCat.of ℤ ℤ)) U =
      (p : ℤ) • 𝟙 (RelativeSingularHomology.complex U) := by
  change (functor U).map ((p : ℤ) • 𝟙 (ModuleCat.of ℤ ℤ)) =
    (p : ℤ) • 𝟙 ((functor U).obj (ModuleCat.of ℤ ℤ))
  rw [CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_id]

/-- The native relative coefficient sequence, with its literal maps. -/
def coefficientSequence (p : ℕ) (U : Set X) :
    ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  (SphereHomologyCoefficients.coefficientSequence p).map (functor U)

theorem coefficientSequence_f (p : ℕ) (U : Set X) :
    (coefficientSequence p U).f = (p : ℤ) • 𝟙 (RelativeSingularHomology.complex U) :=
  change_multiplication p U

theorem coefficientSequence_g (p : ℕ) (U : Set X) :
    (coefficientSequence p U).g = reduction p U := rfl

theorem coefficientSequence_shortExact (p : ℕ) (hp : p ≠ 0) (U : Set X) :
    (coefficientSequence p U).ShortExact :=
  functor_shortExact _ U (SphereHomologyCoefficients.coefficientSequence_shortExact p hp)

/-- The original coefficient reduction on actual relative homology. -/
abbrev reductionMap (p : ℕ) (U : Set X) (n : ℕ) :
    RelativeSingularHomology.Homology U n →ₗ[ℤ] ModHomology p U n :=
  homologyLinearMap (reduction p U) n

theorem multiplication_homology (p : ℕ) (U : Set X) (n : ℕ) :
    homologyLinearMap (coefficientSequence p U).f n =
      (p : ℤ) • (LinearMap.id : RelativeSingularHomology.Homology U n →ₗ[ℤ]
        RelativeSingularHomology.Homology U n) := by
  rw [coefficientSequence_f]
  change ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).map
    ((p : ℤ) • 𝟙 (RelativeSingularHomology.complex U))).hom = _
  rw [CategoryTheory.Functor.map_zsmul, CategoryTheory.Functor.map_id]
  rfl

/-- The connecting map of the proved relative coefficient sequence. -/
def bockstein (p : ℕ) (hp : p ≠ 0) (U : Set X) (n : ℕ) :
    ModHomology p U (n + 1) →ₗ[ℤ] RelativeSingularHomology.Homology U n :=
  connectingMap (coefficientSequence_shortExact p hp U) n

theorem reductionMap_ker (p : ℕ) (hp : p ≠ 0) (U : Set X) (n : ℕ) :
    LinearMap.ker (reductionMap p U n) =
      scalarImage p (RelativeSingularHomology.Homology U n) := by
  have h := exact_at_middleHomology (coefficientSequence_shortExact p hp U) n
  rw [multiplication_homology] at h
  exact h.symm

theorem bockstein_range (p : ℕ) (hp : p ≠ 0) (U : Set X) (n : ℕ) :
    LinearMap.range (bockstein p hp U n) =
      LinearMap.ker ((p : ℤ) • (LinearMap.id : RelativeSingularHomology.Homology U n →ₗ[ℤ]
        RelativeSingularHomology.Homology U n)) := by
  have h := exact_at_leftHomology (coefficientSequence_shortExact p hp U) n
  rw [multiplication_homology] at h
  exact h

theorem reductionMap_range (p : ℕ) (hp : p ≠ 0) (U : Set X) (n : ℕ) :
    LinearMap.range (reductionMap p U (n + 1)) = LinearMap.ker (bockstein p hp U n) :=
  exact_at_rightHomology (coefficientSequence_shortExact p hp U) n

/-- Vanishing of the preceding integral relative group makes actual reduction surjective. -/
theorem reductionMap_surjective_of_subsingleton (p : ℕ) (hp : p ≠ 0) (U : Set X) (n : ℕ)
    [Subsingleton (RelativeSingularHomology.Homology U n)] :
    Function.Surjective (reductionMap p U (n + 1)) := by
  have hb : bockstein p hp U n = 0 := Subsingleton.elim _ _
  apply LinearMap.range_eq_top.mp
  rw [reductionMap_range p hp U n, hb, LinearMap.ker_zero]

/-- Coefficient reduction in degree zero is always surjective. -/
theorem reductionMap_zero_surjective (p : ℕ) (hp : p ≠ 0) (U : Set X) :
    Function.Surjective (reductionMap p U 0) :=
  homologyLinearMap_second_zero_surjective (coefficientSequence_shortExact p hp U)

end NoExoticSixSphere.RelativeCoefficients
