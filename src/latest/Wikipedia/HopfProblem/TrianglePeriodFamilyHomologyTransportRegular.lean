import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportMonodromy
import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportRegular

/-!
# Higher singular-homology transport of the actual regular family

The constructed regular covering discharges the covering hypothesis in the
general transport theorems. The markings identify the literal singular homology
of each family fibre with the integral exterior powers of its period lattice.
The chosen deck-realizing loops do not claim to be geometric meridians.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped Matrix MatrixGroups

namespace Wikipedia.HopfProblem.TrianglePeriodFamily

open FirstHurewicz SpecialPeriods
open SingularMayerVietoris PeriodTorusHigherHomology PeriodTorusHigherHomologyExterior

variable (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂)

/-- The actual degree-two homology of a regular fibre in its exterior marking. -/
def regularFibreSingularH2Equiv (b : TriangleRegularPoint) :
    SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 2 ≃ₗ[ℤ]
      latticeExterior 2 :=
  (regularData P h₁ h₂).fibreSingularH2Equiv (regularCovering P h₁ h₂) b

/-- The actual degree-three homology of a regular fibre in its exterior marking. -/
def regularFibreSingularH3Equiv (b : TriangleRegularPoint) :
    SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 3 ≃ₗ[ℤ]
      latticeExterior 3 :=
  (regularData P h₁ h₂).fibreSingularH3Equiv (regularCovering P h₁ h₂) b

/-- Actual singular-homology transport between regular family fibres in every degree. -/
def regularHomologyTransportDegree (n : ℕ) {x y : TriangleRegularQuotient}
    (γ : Path.Homotopic.Quotient x y) :
    SingularHomology (RegularFibre P h₁ h₂ x) n ≃ₗ[ℤ]
      SingularHomology (RegularFibre P h₁ h₂ y) n :=
  (regularData P h₁ h₂).homologyTransportDegree (regularCovering P h₁ h₂) n γ

@[simp] theorem regularHomologyTransportDegree_toLinearMap (n : ℕ)
    {x y : TriangleRegularQuotient} (γ : Path.Homotopic.Quotient x y) :
    (regularHomologyTransportDegree P h₁ h₂ n γ).toLinearMap =
      singularHomologyMap (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ x, RegularFibre P h₁ h₂ y)) n := rfl

@[simp] theorem regularHomologyTransportDegree_apply (n : ℕ)
    {x y : TriangleRegularQuotient} (γ : Path.Homotopic.Quotient x y)
    (a : SingularHomology (RegularFibre P h₁ h₂ x) n) :
    regularHomologyTransportDegree P h₁ h₂ n γ a =
      singularHomologyMap (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ x, RegularFibre P h₁ h₂ y)) n a := rfl

@[simp] theorem regularHomologyTransportDegree_refl (n : ℕ) (x : TriangleRegularQuotient) :
    regularHomologyTransportDegree P h₁ h₂ n (Path.Homotopic.Quotient.refl x) =
      LinearEquiv.refl ℤ (SingularHomology (RegularFibre P h₁ h₂ x) n) :=
  (regularData P h₁ h₂).homologyTransportDegree_refl (regularCovering P h₁ h₂) n x

theorem regularHomologyTransportDegree_trans (n : ℕ)
    {x y z : TriangleRegularQuotient}
    (γ : Path.Homotopic.Quotient x y) (δ : Path.Homotopic.Quotient y z) :
    regularHomologyTransportDegree P h₁ h₂ n (γ.trans δ) =
      (regularHomologyTransportDegree P h₁ h₂ n γ).trans
        (regularHomologyTransportDegree P h₁ h₂ n δ) :=
  (regularData P h₁ h₂).homologyTransportDegree_trans (regularCovering P h₁ h₂) n γ δ

@[simp] theorem regularHomologyTransportDegree_trans_apply (n : ℕ)
    {x y z : TriangleRegularQuotient}
    (γ : Path.Homotopic.Quotient x y) (δ : Path.Homotopic.Quotient y z)
    (a : SingularHomology (RegularFibre P h₁ h₂ x) n) :
    regularHomologyTransportDegree P h₁ h₂ n (γ.trans δ) a =
      regularHomologyTransportDegree P h₁ h₂ n δ
        (regularHomologyTransportDegree P h₁ h₂ n γ a) :=
  (regularData P h₁ h₂).homologyTransportDegree_trans_apply
    (regularCovering P h₁ h₂) n γ δ a

@[simp] theorem regularHomologyTransportDegree_symm (n : ℕ)
    {x y : TriangleRegularQuotient} (γ : Path.Homotopic.Quotient x y) :
    regularHomologyTransportDegree P h₁ h₂ n γ.symm =
      (regularHomologyTransportDegree P h₁ h₂ n γ).symm :=
  (regularData P h₁ h₂).homologyTransportDegree_symm (regularCovering P h₁ h₂) n γ

theorem regularHomologyTransportDegree_homotopy (n : ℕ)
    {x y : TriangleRegularQuotient} {γ δ : Path x y} (h : γ.Homotopic δ) :
    regularHomologyTransportDegree P h₁ h₂ n (Path.Homotopic.Quotient.mk γ) =
      regularHomologyTransportDegree P h₁ h₂ n (Path.Homotopic.Quotient.mk δ) :=
  (regularData P h₁ h₂).homologyTransportDegree_homotopy (regularCovering P h₁ h₂) n h

theorem regularHomologyTransportDegree_eq_of_lift_endpoint_eq (n : ℕ)
    {x y : TriangleRegularQuotient} {γ δ : Path.Homotopic.Quotient x y}
    (b : triangleRegularProject ⁻¹' {x})
    (he : triangleRegularProject_covering.isCoveringMap.monodromy γ b =
      triangleRegularProject_covering.isCoveringMap.monodromy δ b) :
    regularHomologyTransportDegree P h₁ h₂ n γ =
      regularHomologyTransportDegree P h₁ h₂ n δ :=
  (regularData P h₁ h₂).homologyTransportDegree_eq_of_lift_endpoint_eq
    (regularCovering P h₁ h₂) n b he

/-- The actual regular-loop representation on the literal fibre homology in every degree. -/
def regularHomologyMonodromyDegreeHom (n : ℕ) (b : TriangleRegularPoint) :
    FundamentalGroup TriangleRegularQuotient (triangleRegularProject b) →*
      (SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) n ≃ₗ[ℤ]
        SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) n) :=
  (regularData P h₁ h₂).homologyMonodromyDegreeHom (regularCovering P h₁ h₂) n b

@[simp] theorem regularHomologyMonodromyDegreeHom_apply (n : ℕ) (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b)) :
    regularHomologyMonodromyDegreeHom P h₁ h₂ n b γ =
      regularHomologyTransportDegree P h₁ h₂ n γ := rfl

@[simp] theorem regularHomologyMonodromyDegreeHom_apply_class (n : ℕ)
    (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) n) :
    regularHomologyMonodromyDegreeHom P h₁ h₂ n b γ a =
      singularHomologyMap (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) n a := rfl

/-- Every actual regular-base loop acts by the exterior power of its lattice action. -/
theorem regularTransport_singularH2 (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 2) :
    regularFibreSingularH2Equiv P h₁ h₂ b
      (singularHomologyMap (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) 2 a) =
      exteriorPower.map 2 (regularLatticeTransportHom P h₁ h₂ b γ : LatticeMatrix).mulVecLin
        (regularFibreSingularH2Equiv P h₁ h₂ b a) :=
  (regularData P h₁ h₂).transport_singularH2 (regularCovering P h₁ h₂) b γ a

theorem regularTransport_singularH2_conjugate (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b)) :
    (regularFibreSingularH2Equiv P h₁ h₂ b).toLinearMap.comp
      ((singularHomologyMap (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) 2).comp
        (regularFibreSingularH2Equiv P h₁ h₂ b).symm.toLinearMap) =
      exteriorPower.map 2 (regularLatticeTransportHom P h₁ h₂ b γ : LatticeMatrix).mulVecLin :=
  (regularData P h₁ h₂).transport_singularH2_conjugate
    (regularCovering P h₁ h₂) b γ

/-- An actual inverse lifted endpoint gives the positive deck action. -/
theorem regularTransport_singularH2_of_inverse_endpoint (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (g : TriangleGroup)
    (hγ : (triangleRegularProject_covering.isCoveringMap.monodromy γ ⟨b, rfl⟩ :
      TriangleRegularPoint) = g⁻¹ • b)
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 2) :
    regularFibreSingularH2Equiv P h₁ h₂ b
      (singularHomologyMap (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) 2 a) =
      exteriorPower.map 2 (triangleDualRepresentation g : LatticeMatrix).mulVecLin
        (regularFibreSingularH2Equiv P h₁ h₂ b a) :=
  (regularData P h₁ h₂).transport_singularH2_of_inverse_endpoint
    (regularCovering P h₁ h₂) b γ g hγ a

/-- An actual positive lifted endpoint gives the inverse deck action. -/
theorem regularTransport_singularH2_of_endpoint (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (g : TriangleGroup)
    (hγ : (triangleRegularProject_covering.isCoveringMap.monodromy γ ⟨b, rfl⟩ :
      TriangleRegularPoint) = g • b)
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 2) :
    regularFibreSingularH2Equiv P h₁ h₂ b
      (singularHomologyMap (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) 2 a) =
      exteriorPower.map 2 (triangleDualRepresentation g⁻¹ : LatticeMatrix).mulVecLin
        (regularFibreSingularH2Equiv P h₁ h₂ b a) :=
  (regularData P h₁ h₂).transport_singularH2_of_endpoint
    (regularCovering P h₁ h₂) b γ g hγ a

/-- A supplied upstairs path gives its actual higher-homology action without a
further lifted-endpoint hypothesis. -/
theorem regularProjectedLoop_transport_singularH2 (b : TriangleRegularPoint)
    (g : TriangleGroup) (δ : Path b (g⁻¹ • b))
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 2) :
    regularFibreSingularH2Equiv P h₁ h₂ b
      (singularHomologyMap
        (regularPathTransport P h₁ h₂ (regularProjectedLoop P h₁ h₂ b g δ) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) 2 a) =
      exteriorPower.map 2 (triangleDualRepresentation g : LatticeMatrix).mulVecLin
        (regularFibreSingularH2Equiv P h₁ h₂ b a) :=
  (regularData P h₁ h₂).projectedLoop_transport_singularH2
    (regularCovering P h₁ h₂) b g δ a

/-- The chosen actual deck-realizing loop gives every dual-representation
exterior action, without a supplied path or endpoint hypothesis. -/
theorem regularDeckLoop_transport_singularH2 (b : TriangleRegularPoint) (g : TriangleGroup)
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 2) :
    regularFibreSingularH2Equiv P h₁ h₂ b
      (singularHomologyMap (regularPathTransport P h₁ h₂ (regularDeckLoop P h₁ h₂ b g) :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) 2 a) =
      exteriorPower.map 2 (triangleDualRepresentation g : LatticeMatrix).mulVecLin
        (regularFibreSingularH2Equiv P h₁ h₂ b a) :=
  regularProjectedLoop_transport_singularH2 P h₁ h₂ b g
    (PathConnectedSpace.somePath b (g⁻¹ • b)) a

/-- Every actual regular-base loop acts by the exterior power of its lattice action. -/
theorem regularTransport_singularH3 (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 3) :
    regularFibreSingularH3Equiv P h₁ h₂ b
      (singularHomologyMap (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) 3 a) =
      exteriorPower.map 3 (regularLatticeTransportHom P h₁ h₂ b γ : LatticeMatrix).mulVecLin
        (regularFibreSingularH3Equiv P h₁ h₂ b a) :=
  (regularData P h₁ h₂).transport_singularH3 (regularCovering P h₁ h₂) b γ a

theorem regularTransport_singularH3_conjugate (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b)) :
    (regularFibreSingularH3Equiv P h₁ h₂ b).toLinearMap.comp
      ((singularHomologyMap (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) 3).comp
        (regularFibreSingularH3Equiv P h₁ h₂ b).symm.toLinearMap) =
      exteriorPower.map 3 (regularLatticeTransportHom P h₁ h₂ b γ : LatticeMatrix).mulVecLin :=
  (regularData P h₁ h₂).transport_singularH3_conjugate
    (regularCovering P h₁ h₂) b γ

/-- An actual inverse lifted endpoint gives the positive deck action. -/
theorem regularTransport_singularH3_of_inverse_endpoint (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (g : TriangleGroup)
    (hγ : (triangleRegularProject_covering.isCoveringMap.monodromy γ ⟨b, rfl⟩ :
      TriangleRegularPoint) = g⁻¹ • b)
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 3) :
    regularFibreSingularH3Equiv P h₁ h₂ b
      (singularHomologyMap (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) 3 a) =
      exteriorPower.map 3 (triangleDualRepresentation g : LatticeMatrix).mulVecLin
        (regularFibreSingularH3Equiv P h₁ h₂ b a) :=
  (regularData P h₁ h₂).transport_singularH3_of_inverse_endpoint
    (regularCovering P h₁ h₂) b γ g hγ a

/-- An actual positive lifted endpoint gives the inverse deck action. -/
theorem regularTransport_singularH3_of_endpoint (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (g : TriangleGroup)
    (hγ : (triangleRegularProject_covering.isCoveringMap.monodromy γ ⟨b, rfl⟩ :
      TriangleRegularPoint) = g • b)
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 3) :
    regularFibreSingularH3Equiv P h₁ h₂ b
      (singularHomologyMap (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) 3 a) =
      exteriorPower.map 3 (triangleDualRepresentation g⁻¹ : LatticeMatrix).mulVecLin
        (regularFibreSingularH3Equiv P h₁ h₂ b a) :=
  (regularData P h₁ h₂).transport_singularH3_of_endpoint
    (regularCovering P h₁ h₂) b γ g hγ a

/-- A supplied upstairs path gives its actual higher-homology action without a
further lifted-endpoint hypothesis. -/
theorem regularProjectedLoop_transport_singularH3 (b : TriangleRegularPoint)
    (g : TriangleGroup) (δ : Path b (g⁻¹ • b))
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 3) :
    regularFibreSingularH3Equiv P h₁ h₂ b
      (singularHomologyMap
        (regularPathTransport P h₁ h₂ (regularProjectedLoop P h₁ h₂ b g δ) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) 3 a) =
      exteriorPower.map 3 (triangleDualRepresentation g : LatticeMatrix).mulVecLin
        (regularFibreSingularH3Equiv P h₁ h₂ b a) :=
  (regularData P h₁ h₂).projectedLoop_transport_singularH3
    (regularCovering P h₁ h₂) b g δ a

/-- The chosen actual deck-realizing loop gives every dual-representation
exterior action, without a supplied path or endpoint hypothesis. -/
theorem regularDeckLoop_transport_singularH3 (b : TriangleRegularPoint) (g : TriangleGroup)
    (a : SingularHomology (RegularFibre P h₁ h₂ (triangleRegularProject b)) 3) :
    regularFibreSingularH3Equiv P h₁ h₂ b
      (singularHomologyMap (regularPathTransport P h₁ h₂ (regularDeckLoop P h₁ h₂ b g) :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) 3 a) =
      exteriorPower.map 3 (triangleDualRepresentation g : LatticeMatrix).mulVecLin
        (regularFibreSingularH3Equiv P h₁ h₂ b a) :=
  regularProjectedLoop_transport_singularH3 P h₁ h₂ b g
    (PathConnectedSpace.somePath b (g⁻¹ • b)) a

end Wikipedia.HopfProblem.TrianglePeriodFamily

