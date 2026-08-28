import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportRegular
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportPeriod
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportPaths

/-!
# Period normalization and flatness for the actual regular family

The proved regular covering discharges the generic covering hypothesis.
The literal fibre markings agree with the original complex periods and
remain constant along projections of actual upstairs paths.
-/

noncomputable section

open UpperHalfPlane

namespace Wikipedia.HopfProblem.TrianglePeriodFamily

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology

variable (P : HolomorphicPeriodMap ℂ ℍ)
  (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
  (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂)

/-- The actual regular-fibre marking agrees with the source's positive period columns. -/
theorem regularFibreSingularH2Equiv_inducedHomology_period (b : TriangleRegularPoint)
    (a : SingularHomology (P.point b.val).Torus 2) :
    regularFibreSingularH2Equiv P h₁ h₂ b
      (singularHomologyMap
        ((regularData P h₁ h₂).fibreHomeomorph (regularCovering P h₁ h₂) b :
          C(((regularData P h₁ h₂).periods.point b).Torus,
            (regularData P h₁ h₂).projection ⁻¹' {(regularData P h₁ h₂).baseQuotient b})) 2 a) =
      periodTorusH2ExteriorEquiv (P.point b.val) a :=
  (regularData P h₁ h₂).fibreSingularH2Equiv_inducedHomology_period
    (regularCovering P h₁ h₂) b a

/-- The cubic marking agrees with the actual threefold positive period products. -/
theorem regularFibreSingularH3Equiv_inducedHomology_period (b : TriangleRegularPoint)
    (a : SingularHomology (P.point b.val).Torus 3) :
    regularFibreSingularH3Equiv P h₁ h₂ b
      (singularHomologyMap
        ((regularData P h₁ h₂).fibreHomeomorph (regularCovering P h₁ h₂) b :
          C(((regularData P h₁ h₂).periods.point b).Torus,
            (regularData P h₁ h₂).projection ⁻¹' {(regularData P h₁ h₂).baseQuotient b})) 3 a) =
      periodTorusH3ExteriorEquiv (P.point b.val) a :=
  (regularData P h₁ h₂).fibreSingularH3Equiv_inducedHomology_period
    (regularCovering P h₁ h₂) b a

/-- Along an actual projected upstairs path, the second-homology marking is constant. -/
theorem regularTransport_singularH2_projectedPath {b c : TriangleRegularPoint}
    (δ : Path.Homotopic.Quotient b c)
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 2) :
    regularFibreSingularH2Equiv P h₁ h₂ c
      (regularHomologyTransportDegree P h₁ h₂ 2
        (δ.map ⟨triangleRegularProject, triangleRegularProject_covering.continuous⟩) a) =
      regularFibreSingularH2Equiv P h₁ h₂ b a :=
  (regularData P h₁ h₂).transport_singularH2_projectedPath (regularCovering P h₁ h₂) δ a

/-- The corresponding genuine flatness statement in third singular homology. -/
theorem regularTransport_singularH3_projectedPath {b c : TriangleRegularPoint}
    (δ : Path.Homotopic.Quotient b c)
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 3) :
    regularFibreSingularH3Equiv P h₁ h₂ c
      (regularHomologyTransportDegree P h₁ h₂ 3
        (δ.map ⟨triangleRegularProject, triangleRegularProject_covering.continuous⟩) a) =
      regularFibreSingularH3Equiv P h₁ h₂ b a :=
  (regularData P h₁ h₂).transport_singularH3_projectedPath (regularCovering P h₁ h₂) δ a

theorem regularFibreSingularH2_free (b : TriangleRegularPoint) :
    Module.Free ℤ (SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 2) :=
  (regularData P h₁ h₂).fibreSingularH2_free (regularCovering P h₁ h₂) b

theorem regularFibreSingularH3_free (b : TriangleRegularPoint) :
    Module.Free ℤ (SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 3) :=
  (regularData P h₁ h₂).fibreSingularH3_free (regularCovering P h₁ h₂) b

theorem regularFibreSingularH2_finite (b : TriangleRegularPoint) :
    Module.Finite ℤ (SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 2) :=
  (regularData P h₁ h₂).fibreSingularH2_finite (regularCovering P h₁ h₂) b

theorem regularFibreSingularH3_finite (b : TriangleRegularPoint) :
    Module.Finite ℤ (SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 3) :=
  (regularData P h₁ h₂).fibreSingularH3_finite (regularCovering P h₁ h₂) b

theorem regularFibreSingularH2_finrank (b : TriangleRegularPoint) :
    Module.finrank ℤ
      (SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 2) = 6 :=
  (regularData P h₁ h₂).fibreSingularH2_finrank (regularCovering P h₁ h₂) b

theorem regularFibreSingularH3_finrank (b : TriangleRegularPoint) :
    Module.finrank ℤ
      (SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 3) = 4 :=
  (regularData P h₁ h₂).fibreSingularH3_finrank (regularCovering P h₁ h₂) b

end Wikipedia.HopfProblem.TrianglePeriodFamily
