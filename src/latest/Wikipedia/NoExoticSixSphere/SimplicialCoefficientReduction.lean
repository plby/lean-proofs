import Wikipedia.NoExoticSixSphere.SimplicialCoefficientChains
import Wikipedia.HopfProblem.SphereHomologyCoefficientsChains

/-!
# Native finite-cyclic coefficient reduction for simplicial chain maps

The coefficient short exact sequence and its naturality transfer an actual
integral quasi-isomorphism to the same simplicial map with finite-cyclic
coefficients. This applies to small-simplex subcomplexes, not only to
singular sets of whole topological spaces.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SphereHomologyCoefficients

namespace NoExoticSixSphere.SimplicialCoefficients

abbrev coefficientSequence (p : ℕ) (X : SSet.{0}) :
    ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  (SphereHomologyCoefficients.coefficientSequence p).map (coefficientFunctor X)

theorem coefficientSequence_shortExact (p : ℕ) (hp : p ≠ 0) (X : SSet.{0}) :
    (coefficientSequence p X).ShortExact :=
  coefficientFunctor_shortExact X _ (SphereHomologyCoefficients.coefficientSequence_shortExact p hp)

/-- The original simplicial map gives a map of the actual coefficient short exact sequences. -/
def coefficientSequenceMap (p : ℕ) {X Y : SSet.{0}} (f : X ⟶ Y) :
    coefficientSequence p X ⟶ coefficientSequence p Y where
  τ₁ := (chains (ModuleCat.of ℤ ℤ)).map f
  τ₂ := (chains (ModuleCat.of ℤ ℤ)).map f
  τ₃ := (chains (ModuleCat.of ℤ (ZMod p))).map f
  comm₁₂ := ((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map
    (SphereHomologyCoefficients.coefficientSequence p).f).naturality f
  comm₂₃ := ((SSet.chainComplexFunctor (ModuleCat.{0} ℤ)).map
    (SphereHomologyCoefficients.coefficientSequence p).g).naturality f

/-- An integral quasi-isomorphism induces a quasi-isomorphism on the native finite coefficients. -/
theorem map_mod_quasiIso_of_integral (p : ℕ) (hp : p ≠ 0) {X Y : SSet.{0}} (f : X ⟶ Y)
    (h : QuasiIso ((chains (ModuleCat.of ℤ ℤ)).map f)) :
    QuasiIso ((chains (ModuleCat.of ℤ (ZMod p))).map f) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (coefficientSequenceMap p f)
    (coefficientSequence_shortExact p hp X) (coefficientSequence_shortExact p hp Y) h h

end NoExoticSixSphere.SimplicialCoefficients
