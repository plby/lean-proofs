import Wikipedia.NoExoticSixSphere.SupportedEvaluationLocalization
import Wikipedia.NoExoticSixSphere.PointSupportedCohomologyMarking
import Wikipedia.NoExoticSixSphere.ManifoldFundamentalClass
import Wikipedia.NoExoticSixSphere.SphereCompactificationChart
import Wikipedia.HopfProblem.SphereHomologyCoefficientsSphere

/-!
# Unit evaluation of every nonzero point class on the original three-sphere

The actual mod-two sphere fundamental class is the constructed global
manifold class, since both are the unique nonzero top class. Native
coefficient change and localization give the original local fundamental
class at every point. Hence every nonzero singleton-supported top
cohomology class evaluates to one on the original integral sphere class.
Finite-support additivity gives the cardinality when all components are
nonzero; proving that transversality supplies those components is separate.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SphereHomology

namespace NoExoticSixSphere.SpherePointEvaluation

local notation "V" => EuclideanSpace ℝ (Fin 3)

local instance modelDimension : Fact (Module.finrank ℝ V = (0 + 2) + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The constructed global manifold class is the original reduced sphere top class. -/
theorem fundamentalClass_eq_standard :
    ManifoldFundamentalClass.fundamentalClass (E := V) 0 (Sphere 3) =
      unitSphereModTopClass 2 2 := by
  let : Nonempty (Sphere 3) := ⟨spherePole 3⟩
  let F := unitSphereModHomologyTopEquiv 2 (by decide) 2
  have hn : F (ManifoldFundamentalClass.fundamentalClass (E := V) 0 (Sphere 3)) ≠ 0 := by
    intro he
    exact ManifoldFundamentalClass.fundamentalClass_ne_zero (E := V) 0 (Sphere 3)
      (F.injective (he.trans F.map_zero.symm))
  apply F.injective
  rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide)
    (F (ManifoldFundamentalClass.fundamentalClass (E := V) 0 (Sphere 3))) with h | h
  · exact (hn h).elim
  · exact h.trans (unitSphereModHomologyTopEquiv_topClass 2 (by decide) 2).symm

/-- The original integral sphere class localizes to the actual mod-two local fundamental class. -/
theorem integralTopClass_local_reduction (x : Sphere 3) :
    RelativeCoefficients.reductionMap 2 ({x}ᶜ : Set (Sphere 3)) 3
        (SupportedRelativeHomology.fromAbsolute (ModuleCat.of ℤ ℤ) {x} 3 (unitSphereTopClass 2)) =
      ModTwoLocalClass.manifoldClass (E := V) 0 x :=
  (SupportedRelativeHomology.fromAbsolute_reduction 2 ({x} : Set (Sphere 3)) 3
    (unitSphereTopClass 2)).symm.trans
      ((congrArg (SupportedRelativeHomology.fromAbsolute (ModuleCat.of ℤ (ZMod 2)) {x} 3)
        fundamentalClass_eq_standard.symm).trans
          (ManifoldFundamentalClass.localize_fundamentalClass (E := V) 0 (Sphere 3) x))

/-- Any nonzero original point-supported top class contributes exactly one. -/
theorem singleton_value_eq_one (x : Sphere 3)
    (a : SupportedModTwoCohomology.Cohomology ({x} : Set (Sphere 3)) 3) (ha : a ≠ 0) :
    SupportedModTwoCohomology.value {x} 3 (unitSphereTopClass 2) a = 1 :=
  (SupportedModTwoCohomology.value_eq_relative {x} 3 (unitSphereTopClass 2) a).trans
    (PointSupportedCohomology.evaluation_eq_one_of_reduction_eq_localClass
      (E := V) 0 x a ha _ (integralTopClass_local_reduction x))

/-- Finite support evaluates to its cardinality when every actual point component is nonzero. -/
theorem finite_value_eq_card_of_nonzero (s : Finset (Sphere 3))
    (a : SupportedModTwoCohomology.Cohomology (s : Set (Sphere 3)) 3)
    (ha : ∀ x ∈ s, SupportedModTwoCohomology.pointPieces s 3 a x ≠ 0) :
    SupportedModTwoCohomology.value (s : Set (Sphere 3)) 3 (unitSphereTopClass 2) a =
      (s.card : ZMod 2) :=
  SupportedModTwoCohomology.value_eq_card_of_point_values_one s 3 (unitSphereTopClass 2) a
    (fun x hx => singleton_value_eq_one x _ (ha x hx))

end NoExoticSixSphere.SpherePointEvaluation
