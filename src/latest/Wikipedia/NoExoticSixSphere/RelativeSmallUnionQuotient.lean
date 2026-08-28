import Wikipedia.NoExoticSixSphere.SingularSmallUnionEquivalence
import Wikipedia.NoExoticSixSphere.RelativeSubcomplexComparison

/-!
# The actual small-relative quotient computes the open-union relative group

The original small-to-union map and the ambient identity give a map of
short exact pair sequences. Its first map is a quasi-isomorphism by the
constructed subdivision comparison. Therefore the actual quotient map is
a quasi-isomorphism, with its original projection formula retained.
-/

noncomputable section

open CategoryTheory Limits

namespace NoExoticSixSphere.RelativeCoefficients

open SimplicialCoefficients SingularSubcomplex

variable {X : Type} [TopologicalSpace X] (R : ModuleCat.{0} ℤ) (U V : Set X)

abbrev smallRelativeComplex : ChainComplex (ModuleCat.{0} ℤ) ℕ :=
  SubcomplexRelative.complex R (support U ⊔ support V)

abbrev smallRelativeProjection : (singular X).chainComplex R ⟶ smallRelativeComplex R U V :=
  SubcomplexRelative.projection R (support U ⊔ support V)

abbrev smallPairSequence : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  ShortComplex.mk ((chains R).map (smallInclusion U V)) (smallRelativeProjection R U V)
    (cokernel.condition _)

theorem smallPairSequence_shortExact : (smallPairSequence R U V).ShortExact where
  exact := ShortComplex.exact_cokernel ((chains R).map (smallInclusion U V))
  mono_f := inferInstanceAs (Mono ((chains R).map (smallInclusion U V)))
  epi_g := inferInstanceAs (Epi (smallRelativeProjection R U V))

theorem smallToUnion_chain_square :
    (chains R).map (smallInclusion U V) ≫ 𝟙 ((singular X).chainComplex R) =
      (chains R).map (smallToUnion U V) ≫
        (chains R).map (SingularSubcomplex.inclusion (U ∪ V)) := by
  rw [Category.comp_id, ← Functor.map_comp, smallToUnion_inclusion]

/-- The original quotient map induced by inclusion of small simplices in the open union. -/
def smallToUnionQuotient : smallRelativeComplex R U V ⟶ complex R (U ∪ V) :=
  cokernel.map ((chains R).map (smallInclusion U V)) (inclusion R (U ∪ V))
    ((chains R).map (smallToUnion U V)) (𝟙 ((singular X).chainComplex R))
    (smallToUnion_chain_square R U V)

@[reassoc]
theorem projection_smallToUnionQuotient :
    smallRelativeProjection R U V ≫ smallToUnionQuotient R U V = projection R (U ∪ V) :=
  (cokernel.π_desc _ _ _).trans (Category.id_comp _)

/-- The actual map of pair sequences retains the ambient identity. -/
def smallToUnionSequenceMap : smallPairSequence R U V ⟶ sequence R (U ∪ V) where
  τ₁ := (chains R).map (smallToUnion U V)
  τ₂ := 𝟙 ((singular X).chainComplex R)
  τ₃ := smallToUnionQuotient R U V
  comm₁₂ := (smallToUnion_chain_square R U V).symm
  comm₂₃ := by
    change 𝟙 ((singular X).chainComplex R) ≫ projection R (U ∪ V) =
      smallRelativeProjection R U V ≫ smallToUnionQuotient R U V
    exact (Category.id_comp _).trans (projection_smallToUnionQuotient R U V).symm

/-- Native finite-cyclic relative homology of the open union is computed by actual small chains. -/
theorem smallToUnionQuotient_mod_quasiIso (p : ℕ) (hp : p ≠ 0)
    (hU : IsOpen U) (hV : IsOpen V) :
    QuasiIso (smallToUnionQuotient (ModuleCat.of ℤ (ZMod p)) U V) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃
    (smallToUnionSequenceMap (ModuleCat.of ℤ (ZMod p)) U V)
    (smallPairSequence_shortExact (ModuleCat.of ℤ (ZMod p)) U V)
    (sequence_shortExact (ModuleCat.of ℤ (ZMod p)) (U ∪ V))
    (smallToUnion_mod_quasiIso U V p hp hU hV)
    (inferInstanceAs (QuasiIso (𝟙 ((singular X).chainComplex (ModuleCat.of ℤ (ZMod p))))))

end NoExoticSixSphere.RelativeCoefficients
