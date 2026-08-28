import Wikipedia.NoExoticSixSphere.SmallRelativeIntegralSplitting
import Wikipedia.NoExoticSixSphere.ModTwoDualQuasiIso

/-!
# Original small-relative comparison on integral chains and mod-two cochains

The genuine integral small-chain comparison for two open subsets and the
ambient identity give the relative quasi-isomorphism. The actual relative
and small-relative terms are proved free, so its original mod-two dual is
also a quasi-isomorphism.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.RelativeCoefficients

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- Native integral small-relative chains compute the relative group of the open union. -/
theorem smallToUnionQuotient_integral_quasiIso (hU : IsOpen U) (hV : IsOpen V) :
    QuasiIso (smallToUnionQuotient (ModuleCat.of ℤ ℤ) U V) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃
    (smallToUnionSequenceMap (ModuleCat.of ℤ ℤ) U V)
    (smallPairSequence_shortExact (ModuleCat.of ℤ ℤ) U V)
    (sequence_shortExact (ModuleCat.of ℤ ℤ) (U ∪ V))
    (SingularSubcomplex.smallToUnion_integral_quasiIso U V hU hV)
    (inferInstanceAs (QuasiIso (𝟙 ((SingularSubcomplex.singular X).chainComplex
      (ModuleCat.of ℤ ℤ)))))

/-- The original contravariant mod-two comparison retains the genuine quotient map. -/
theorem smallToUnionQuotient_dual_quasiIso (hU : IsOpen U) (hV : IsOpen V) :
    QuasiIso (ModTwoDualComplex.map (smallToUnionQuotient (ModuleCat.of ℤ ℤ) U V)) := by
  let (n : ℕ) : Projective ((smallRelativeComplex (ModuleCat.of ℤ ℤ) U V).X n) := by
    let : Module.Free ℤ ((smallRelativeComplex (ModuleCat.of ℤ ℤ) U V).X n) :=
      SmallRelativeIntegral.chains_free U V n
    exact ModuleCat.projective_of_categoryTheory_projective _
  let (n : ℕ) : Projective ((complex (ModuleCat.of ℤ ℤ) (U ∪ V)).X n) := by
    let : Module.Free ℤ ((complex (ModuleCat.of ℤ ℤ) (U ∪ V)).X n) :=
      RelativeSingularHomology.chains_free (U ∪ V) n
    exact ModuleCat.projective_of_categoryTheory_projective _
  let := smallToUnionQuotient_integral_quasiIso U V hU hV
  exact ModTwoDualComplex.map_quasiIso_of_projective
    (smallToUnionQuotient (ModuleCat.of ℤ ℤ) U V)

end NoExoticSixSphere.RelativeCoefficients
