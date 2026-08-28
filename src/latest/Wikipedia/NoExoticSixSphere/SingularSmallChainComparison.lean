import Wikipedia.NoExoticSixSphere.SingularSmallSubcomplex
import Wikipedia.NoExoticSixSphere.SimplicialCoefficientReduction
import Wikipedia.NoExoticSixSphere.RelativeSmallChainComparison

/-!
# Comparison with the proved subdivision equivalence

The integral chains of the actual small-simplex subcomplex and the earlier
supported-chain complex are colimits of the same actual inclusion diagram.
Their canonical isomorphism commutes with the ambient inclusion. Hence
the already constructed subdivision proves the native small inclusion is
a quasi-isomorphism, also after native finite-cyclic coefficient reduction.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem FirstHurewicz

namespace NoExoticSixSphere.SingularSubcomplex

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- The native pushout expressed with the original integral intersection maps. -/
theorem integralSmallSquare :
    IsPushout (SingularMayerVietoris.intersectionToLeft U V)
      (SingularMayerVietoris.intersectionToRight U V)
      ((SimplicialCoefficients.chains (ModuleCat.of ℤ ℤ)).map (toSmallLeft U V))
      ((SimplicialCoefficients.chains (ModuleCat.of ℤ ℤ)).map (toSmallRight U V)) :=
  smallChainSquare U V (ModuleCat.of ℤ ℤ)

/-- The canonical comparison between the two actual small-chain constructions. -/
def integralSmallIso : (Small U V).chainComplex (ModuleCat.of ℤ ℤ) ≅
    SingularMayerVietoris.smallComplex U V :=
  (integralSmallSquare U V).isColimit.coconePointUniqueUpToIso
    (RelativeSingularHomology.smallChainSquare_isPushout U V).isColimit

@[reassoc]
theorem toSmallLeft_integralSmallIso :
    (SimplicialCoefficients.chains (ModuleCat.of ℤ ℤ)).map (toSmallLeft U V) ≫
        (integralSmallIso U V).hom = SingularMayerVietoris.toSmallLeft U V :=
  (integralSmallSquare U V).isColimit.comp_coconePointUniqueUpToIso_hom
    (RelativeSingularHomology.smallChainSquare_isPushout U V).isColimit WalkingSpan.left

@[reassoc]
theorem toSmallRight_integralSmallIso :
    (SimplicialCoefficients.chains (ModuleCat.of ℤ ℤ)).map (toSmallRight U V) ≫
        (integralSmallIso U V).hom = SingularMayerVietoris.toSmallRight U V :=
  (integralSmallSquare U V).isColimit.comp_coconePointUniqueUpToIso_hom
    (RelativeSingularHomology.smallChainSquare_isPushout U V).isColimit WalkingSpan.right

/-- The canonical comparison retains the original ambient inclusion, not just homology ranks. -/
theorem integralSmallIso_inclusion :
    (integralSmallIso U V).hom ≫ SingularMayerVietoris.smallInclusion U V =
      (SimplicialCoefficients.chains (ModuleCat.of ℤ ℤ)).map (smallInclusion U V) := by
  apply (integralSmallSquare U V).hom_ext
  · rw [toSmallLeft_integralSmallIso_assoc, SingularMayerVietoris.toSmallLeft_inclusion]
    exact (chainToSmallLeft_inclusion U V (ModuleCat.of ℤ ℤ)).symm
  · rw [toSmallRight_integralSmallIso_assoc, SingularMayerVietoris.toSmallRight_inclusion]
    exact (chainToSmallRight_inclusion U V (ModuleCat.of ℤ ℤ)).symm

/-- Actual subdivision proves the integral native small-chain inclusion is a quasi-isomorphism. -/
theorem smallInclusion_integral_quasiIso (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    QuasiIso ((SimplicialCoefficients.chains (ModuleCat.of ℤ ℤ)).map (smallInclusion U V)) := by
  have := SingularMayerVietoris.smallInclusion_quasiIso U V hU hV hcover
  rw [← integralSmallIso_inclusion]
  infer_instance

/-- The same original inclusion is a quasi-isomorphism with native finite-cyclic coefficients. -/
theorem smallInclusion_mod_quasiIso (p : ℕ) (hp : p ≠ 0) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) :
    QuasiIso ((SimplicialCoefficients.chains (ModuleCat.of ℤ (ZMod p))).map (smallInclusion U V)) :=
  SimplicialCoefficients.map_mod_quasiIso_of_integral p hp (smallInclusion U V)
    (smallInclusion_integral_quasiIso U V hU hV hcover)

end NoExoticSixSphere.SingularSubcomplex
