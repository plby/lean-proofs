import Wikipedia.NoExoticSixSphere.RelativeModTwoCapCochainExact

/-!
# Original maps of pairs act on relative mod-two cochains

Pullback is literal precomposition by the actual integral relative chain
map. Its absolute restriction agrees with pullback of the original
absolute cochain, through the original quotient projection square.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem FirstHurewicz

namespace NoExoticSixSphere.RelativeModTwoCochains

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable {U : Set X} {V : Set Y}

/-- Pullback by the original map of pairs. -/
def pullbackMap (f : C(X, Y)) (hf : Set.MapsTo f U V) : complex V ⟶ complex U :=
  ModTwoDualComplex.map (RelativeCoefficients.mapChain (ModuleCat.of ℤ ℤ) f hf)

abbrev pullback (f : C(X, Y)) (hf : Set.MapsTo f U V) (p : ℕ) :
    Cochain V p →ₗ[ℤ] Cochain U p := ((pullbackMap f hf).f p).hom

theorem pullback_apply (f : C(X, Y)) (hf : Set.MapsTo f U V) (p : ℕ)
    (α : Cochain V p) (c : (RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) U).X p) :
    pullback f hf p α c =
      α (((RelativeCoefficients.mapChain (ModuleCat.of ℤ ℤ) f hf).f p).hom c) := rfl

/-- The actual pair projection square gives the absolute pullback formula. -/
theorem toAbsolute_pullback (f : C(X, Y)) (hf : Set.MapsTo f U V) (p : ℕ)
    (α : Cochain V p) :
    toAbsolute U p (pullback f hf p α) =
      ModTwoCapProduct.pullback f p (toAbsolute V p α) := by
  apply AddMonoidHom.ext
  intro c
  have he := congrArg (fun g => (g.f p).hom c)
    (RelativeCoefficients.projection_mapChain (ModuleCat.of ℤ ℤ) f hf)
  exact congrArg α he

/-- Pullback on the genuine relative cohomology objects. -/
abbrev cohomologyPullback (f : C(X, Y)) (hf : Set.MapsTo f U V) (p : ℕ) :
    Cohomology V p →ₗ[ℤ] Cohomology U p :=
  (HomologicalComplex.homologyMap (pullbackMap f hf) p).hom

theorem cohomologyPullback_cocycleClass (f : C(X, Y)) (hf : Set.MapsTo f U V) (p : ℕ)
    (α : Cocycle V p) :
    cohomologyPullback f hf p (SingularCohomologyFree.cocycleClass (complex V) p α) =
      SingularCohomologyFree.cocycleClass (complex U) p
        (SingularCohomologyFree.mapCocycles (pullbackMap f hf) p α) :=
  SingularCohomologyFree.homologyMap_cocycleClass (pullbackMap f hf) p α

end NoExoticSixSphere.RelativeModTwoCochains
