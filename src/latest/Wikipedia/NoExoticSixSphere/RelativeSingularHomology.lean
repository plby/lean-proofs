import Wikipedia.HopfProblem.SingularMayerVietorisSequence
import Wikipedia.HopfProblem.SingularMayerVietorisSmallChainsInclusions
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Relative singular homology of an actual pair

The relative complex of `(X, U)` is the cokernel of the actual singular-chain
map of the subtype inclusion. Its degreewise quotient map is surjective,
with kernel exactly the chains supported in `U`. The long exact sequence
below is the homology sequence of this proved short exact sequence of chain
complexes; relative homology is not the quotient of absolute homology groups.

This is infrastructure for local homology and duality. It does not assert
Poincaré duality or nondegeneracy of the geometric intersection pairing.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.RelativeSingularHomology

variable {X : Type} [TopologicalSpace X]

/-- The actual chain map of the subspace inclusion. -/
abbrev inclusion (U : Set X) : singularComplex U ⟶ singularComplex X :=
  singularChainMap (subtypeInclusion U)

instance inclusion_mono (U : Set X) : Mono (inclusion U) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  exact (ModuleCat.mono_iff_injective _).mpr (subtypeInclusion_chain_injective U n)

/-- The actual relative singular-chain complex, with integral coefficients. -/
abbrev complex (U : Set X) : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  cokernel (inclusion U)

/-- Projection from ambient chains to relative chains. -/
def projection (U : Set X) : singularComplex X ⟶ complex U :=
  cokernel.π (inclusion U)

@[simp]
theorem inclusion_projection (U : Set X) : inclusion U ≫ projection U = 0 :=
  cokernel.condition (inclusion U)

/-- The singular-chain sequence of the actual pair. -/
def sequence (U : Set X) : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk (inclusion U) (projection U) (inclusion_projection U)

/-- Short exactness follows from injectivity of the actual inclusion on chains. -/
theorem sequence_shortExact (U : Set X) : (sequence U).ShortExact where
  exact := ShortComplex.exact_cokernel (inclusion U)
  mono_f := inclusion_mono U
  epi_g := inferInstanceAs (Epi (cokernel.π (inclusion U)))

/-- The actual quotient map in each degree. -/
abbrev quotientMap (U : Set X) (n : ℕ) : Chains X n →ₗ[ℤ] (complex U).X n :=
  ((projection U).f n).hom

theorem quotientMap_surjective (U : Set X) (n : ℕ) :
    Function.Surjective (quotientMap U n) := by
  have := (sequence_shortExact U).epi_g
  exact (ModuleCat.epi_iff_surjective _).mp
    (inferInstanceAs (Epi ((sequence U).g.f n)))

/-- A chain becomes zero relatively precisely when it is supported in the subspace. -/
theorem quotientMap_ker (U : Set X) (n : ℕ) :
    LinearMap.ker (quotientMap U n) = supportedChainSubmodule U n := by
  have h := (sequence_shortExact U).exact.map
    (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n)
  exact h.moduleCat_range_eq_ker.symm.trans (subtypeInclusion_chain_range U n)

theorem quotientMap_eq_zero_iff (U : Set X) (n : ℕ) (c : Chains X n) :
    quotientMap U n c = 0 ↔ c ∈ supportedChainSubmodule U n := by
  change c ∈ LinearMap.ker (quotientMap U n) ↔ _
  rw [quotientMap_ker]

/-- The relative boundary is induced by the original singular boundary. -/
theorem boundary_quotientMap (U : Set X) (i j : ℕ) (c : Chains X i) :
    ((complex U).d i j).hom (quotientMap U i c) =
      quotientMap U j (((singularComplex X).d i j).hom c) :=
  congrArg (fun f => ModuleCat.Hom.hom f c) ((projection U).comm i j)

/-- Relative cycles are precisely chains whose boundary is supported in `U`. -/
theorem relativeCycle_iff (U : Set X) (i j : ℕ) (c : Chains X i) :
    ((complex U).d i j).hom (quotientMap U i c) = 0 ↔
      ((singularComplex X).d i j).hom c ∈ supportedChainSubmodule U j := by
  rw [boundary_quotientMap, quotientMap_eq_zero_iff]

/-- Homology of the genuine relative chain complex. -/
abbrev Homology (U : Set X) (n : ℕ) := (complex U).homology n

/-- The actual map from absolute to relative homology. -/
abbrev toRelative (U : Set X) (n : ℕ) : SingularHomology X n →ₗ[ℤ] Homology U n :=
  homologyLinearMap (projection U) n

/-- The connecting homomorphism to homology of the actual subspace. -/
def connecting (U : Set X) (n : ℕ) : Homology U (n + 1) →ₗ[ℤ] SingularHomology U n :=
  connectingMap (sequence_shortExact U) n

theorem exact_at_subspace (U : Set X) (n : ℕ) :
    LinearMap.range (connecting U n) =
      LinearMap.ker (singularHomologyMap (subtypeInclusion U) n) :=
  exact_at_leftHomology (sequence_shortExact U) n

theorem exact_at_ambient (U : Set X) (n : ℕ) :
    LinearMap.range (singularHomologyMap (subtypeInclusion U) n) =
      LinearMap.ker (toRelative U n) :=
  exact_at_middleHomology (sequence_shortExact U) n

theorem exact_at_relative (U : Set X) (n : ℕ) :
    LinearMap.range (toRelative U (n + 1)) = LinearMap.ker (connecting U n) :=
  exact_at_rightHomology (sequence_shortExact U) n

theorem toRelative_zero_surjective (U : Set X) : Function.Surjective (toRelative U 0) :=
  homologyLinearMap_second_zero_surjective (sequence_shortExact U)

end NoExoticSixSphere.RelativeSingularHomology
