import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportMonodromy
import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportHomology
import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportLoops

/-!
# Actual singular-homology transport on the regular triangle family

The actual regular triangle covering discharges every covering hypothesis
in the general flat-transport construction. The resulting maps act between
the literal fibres of the descended family, and their actual singular
first-homology maps have the proved integral column matrices.

Specified inverse-generator lifted endpoints give `A₁`, `A₂`, and `M₀`.
The constructed deck-realizing loops give the same matrices without an
extra endpoint hypothesis; no geometric-meridian claim is made for those
arbitrarily chosen upstairs paths.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped Matrix MatrixGroups

namespace Wikipedia.HopfProblem.TrianglePeriodFamily

open FirstHurewicz SpecialPeriods

variable (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂)

/-- The literal fibre of the constructed regular family projection. -/
abbrev RegularFibre (x : TriangleRegularQuotient) : Type :=
  (regularData P h₁ h₂).projection ⁻¹' {x}

/-- Actual fibre transport along a relative homotopy class of regular-base paths. -/
def regularTransport {x y : TriangleRegularQuotient} (γ : Path.Homotopic.Quotient x y) :
    RegularFibre P h₁ h₂ x ≃ₜ RegularFibre P h₁ h₂ y :=
  (regularData P h₁ h₂).transport (regularCovering P h₁ h₂) γ

/-- Actual fibre transport along a path in the actual regular quotient. -/
def regularPathTransport {x y : TriangleRegularQuotient} (γ : Path x y) :
    RegularFibre P h₁ h₂ x ≃ₜ RegularFibre P h₁ h₂ y :=
  (regularData P h₁ h₂).pathTransport (regularCovering P h₁ h₂) γ

@[simp] theorem regularTransport_refl (x : TriangleRegularQuotient) :
    regularTransport P h₁ h₂ (Path.Homotopic.Quotient.refl x) = Homeomorph.refl _ :=
  (regularData P h₁ h₂).transport_refl (regularCovering P h₁ h₂) x

theorem regularTransport_trans {x y z : TriangleRegularQuotient}
    (γ : Path.Homotopic.Quotient x y) (δ : Path.Homotopic.Quotient y z) :
    regularTransport P h₁ h₂ (γ.trans δ) =
      (regularTransport P h₁ h₂ γ).trans (regularTransport P h₁ h₂ δ) :=
  (regularData P h₁ h₂).transport_trans (regularCovering P h₁ h₂) γ δ

@[simp] theorem regularTransport_symm {x y : TriangleRegularQuotient}
    (γ : Path.Homotopic.Quotient x y) :
    regularTransport P h₁ h₂ γ.symm = (regularTransport P h₁ h₂ γ).symm :=
  (regularData P h₁ h₂).transport_symm (regularCovering P h₁ h₂) γ

theorem regularPathTransport_eq_of_homotopic {x y : TriangleRegularQuotient}
    {γ δ : Path x y} (h : γ.Homotopic δ) :
    regularPathTransport P h₁ h₂ γ = regularPathTransport P h₁ h₂ δ :=
  (regularData P h₁ h₂).pathTransport_eq_of_homotopic (regularCovering P h₁ h₂) h

@[simp] theorem regularPathTransport_refl (x : TriangleRegularQuotient) :
    regularPathTransport P h₁ h₂ (Path.refl x) = Homeomorph.refl _ :=
  (regularData P h₁ h₂).pathTransport_refl (regularCovering P h₁ h₂) x

theorem regularPathTransport_trans {x y z : TriangleRegularQuotient}
    (γ : Path x y) (δ : Path y z) :
    regularPathTransport P h₁ h₂ (γ.trans δ) =
      (regularPathTransport P h₁ h₂ γ).trans (regularPathTransport P h₁ h₂ δ) :=
  (regularData P h₁ h₂).pathTransport_trans (regularCovering P h₁ h₂) γ δ

@[simp] theorem regularPathTransport_symm {x y : TriangleRegularQuotient} (γ : Path x y) :
    regularPathTransport P h₁ h₂ γ.symm = (regularPathTransport P h₁ h₂ γ).symm :=
  (regularData P h₁ h₂).pathTransport_symm (regularCovering P h₁ h₂) γ

/-- The actual integral singular first homology of a regular fibre, in
the proved ordered complex period-column marking. -/
def regularFibreSingularH1Equiv (b : TriangleRegularPoint) :
    SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b)) ≃ₗ[ℤ] Lattice :=
  (regularData P h₁ h₂).fibreSingularH1Equiv (regularCovering P h₁ h₂) b

/-- The genuine singular-homology equivalence induced by regular fibre transport. -/
def regularHomologyTransport {x y : TriangleRegularQuotient}
    (γ : Path.Homotopic.Quotient x y) :
    SingularH1 (RegularFibre P h₁ h₂ x) ≃ₗ[ℤ] SingularH1 (RegularFibre P h₁ h₂ y) :=
  (regularData P h₁ h₂).homologyTransport (regularCovering P h₁ h₂) γ

@[simp] theorem regularHomologyTransport_apply {x y : TriangleRegularQuotient}
    (γ : Path.Homotopic.Quotient x y) (a : SingularH1 (RegularFibre P h₁ h₂ x)) :
    regularHomologyTransport P h₁ h₂ γ a =
      inducedHomology (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ x, RegularFibre P h₁ h₂ y)) a := rfl

/-- A representation on the actual integral singular homology of the
literal regular fibre, before changing to any lattice coordinates. -/
def regularHomologyMonodromyHom (b : TriangleRegularPoint) :
    FundamentalGroup TriangleRegularQuotient (triangleRegularProject b) →*
      (SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b)) ≃ₗ[ℤ]
        SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :=
  (regularData P h₁ h₂).homologyMonodromyHom (regularCovering P h₁ h₂) b

@[simp] theorem regularHomologyMonodromyHom_apply_class (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :
    regularHomologyMonodromyHom P h₁ h₂ b γ a =
      inducedHomology (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) a := rfl

/-- The actual singular-homology map of every regular-base loop is its
integral covering-monodromy matrix in the proved fibre marking. -/
theorem regularTransport_singularH1 (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :
    regularFibreSingularH1Equiv P h₁ h₂ b
      (inducedHomology (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) a) =
      (regularLatticeTransportHom P h₁ h₂ b γ : LatticeMatrix) *ᵥ
        regularFibreSingularH1Equiv P h₁ h₂ b a :=
  (regularData P h₁ h₂).transport_singularH1 (regularCovering P h₁ h₂) b γ a

theorem regularTransport_singularH1_conjugate (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b)) :
    (regularFibreSingularH1Equiv P h₁ h₂ b).toLinearMap.comp
      ((inducedHomology (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b)))).comp
        (regularFibreSingularH1Equiv P h₁ h₂ b).symm.toLinearMap) =
      Matrix.toLin' (regularLatticeTransportHom P h₁ h₂ b γ : LatticeMatrix) :=
  (regularData P h₁ h₂).transport_singularH1_conjugate (regularCovering P h₁ h₂) b γ

theorem regularHomologyMonodromyHom_marked (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :
    regularFibreSingularH1Equiv P h₁ h₂ b (regularHomologyMonodromyHom P h₁ h₂ b γ a) =
      (regularLatticeTransportHom P h₁ h₂ b γ : LatticeMatrix) *ᵥ
        regularFibreSingularH1Equiv P h₁ h₂ b a :=
  regularTransport_singularH1 P h₁ h₂ b γ a

/-- The lifted-endpoint criterion applies to any supplied actual loop,
including a geometric meridian once its indicated lift is verified. -/
theorem regularTransport_singularH1_of_inverse_endpoint (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (g : TriangleGroup)
    (hγ : (triangleRegularProject_covering.isCoveringMap.monodromy γ ⟨b, rfl⟩ :
      TriangleRegularPoint) = g⁻¹ • b)
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :
    regularFibreSingularH1Equiv P h₁ h₂ b
      (inducedHomology (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) a) =
      (triangleDualRepresentation g : LatticeMatrix) *ᵥ
        regularFibreSingularH1Equiv P h₁ h₂ b a :=
  (regularData P h₁ h₂).transport_singularH1_of_inverse_endpoint
    (regularCovering P h₁ h₂) b γ g hγ a

theorem regularTransport_singularH1_generator₁ (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (hγ : (triangleRegularProject_covering.isCoveringMap.monodromy γ ⟨b, rfl⟩ :
      TriangleRegularPoint) = triangleGenerator₁⁻¹ • b)
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :
    regularFibreSingularH1Equiv P h₁ h₂ b
      (inducedHomology (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) a) =
      A₁ *ᵥ regularFibreSingularH1Equiv P h₁ h₂ b a := by
  rw [regularTransport_singularH1, regularLatticeTransportHom_generator₁ P h₁ h₂ b γ hγ]

theorem regularTransport_singularH1_generator₂ (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (hγ : (triangleRegularProject_covering.isCoveringMap.monodromy γ ⟨b, rfl⟩ :
      TriangleRegularPoint) = triangleGenerator₂⁻¹ • b)
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :
    regularFibreSingularH1Equiv P h₁ h₂ b
      (inducedHomology (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) a) =
      A₂ *ᵥ regularFibreSingularH1Equiv P h₁ h₂ b a := by
  rw [regularTransport_singularH1, regularLatticeTransportHom_generator₂ P h₁ h₂ b γ hγ]

theorem regularTransport_singularH1_cusp (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (hγ : (triangleRegularProject_covering.isCoveringMap.monodromy γ ⟨b, rfl⟩ :
      TriangleRegularPoint) = triangleCuspGenerator⁻¹ • b)
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :
    regularFibreSingularH1Equiv P h₁ h₂ b
      (inducedHomology (regularTransport P h₁ h₂ γ :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) a) =
      M₀ *ᵥ regularFibreSingularH1Equiv P h₁ h₂ b a := by
  rw [regularTransport_singularH1, regularLatticeTransportHom_cusp P h₁ h₂ b γ hγ]

/-- A specified upstairs path gives its actual singular-homology map;
the covering theorem proves its endpoint, rather than requiring it as input. -/
theorem regularProjectedLoop_transport_singularH1 (b : TriangleRegularPoint)
    (g : TriangleGroup) (δ : Path b (g⁻¹ • b))
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :
    regularFibreSingularH1Equiv P h₁ h₂ b
      (inducedHomology
        (regularPathTransport P h₁ h₂ (regularProjectedLoop P h₁ h₂ b g δ) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) a) =
      (triangleDualRepresentation g : LatticeMatrix) *ᵥ
        regularFibreSingularH1Equiv P h₁ h₂ b a :=
  (regularData P h₁ h₂).projectedLoop_transport_singularH1 (regularCovering P h₁ h₂) b g δ a

/-- The chosen actual deck-realizing loops compute every matrix in the
dual representation on the actual fibre singular homology. -/
theorem regularDeckLoop_transport_singularH1 (b : TriangleRegularPoint) (g : TriangleGroup)
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :
    regularFibreSingularH1Equiv P h₁ h₂ b
      (inducedHomology (regularPathTransport P h₁ h₂ (regularDeckLoop P h₁ h₂ b g) :
        C(RegularFibre P h₁ h₂ (triangleRegularProject b),
          RegularFibre P h₁ h₂ (triangleRegularProject b))) a) =
      (triangleDualRepresentation g : LatticeMatrix) *ᵥ
        regularFibreSingularH1Equiv P h₁ h₂ b a :=
  regularProjectedLoop_transport_singularH1 P h₁ h₂ b g
    (PathConnectedSpace.somePath b (g⁻¹ • b)) a

theorem regularDeckLoop_generator₁_singularH1 (b : TriangleRegularPoint)
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :
    regularFibreSingularH1Equiv P h₁ h₂ b
      (inducedHomology
        (regularPathTransport P h₁ h₂ (regularDeckLoop P h₁ h₂ b triangleGenerator₁) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) a) =
      A₁ *ᵥ regularFibreSingularH1Equiv P h₁ h₂ b a := by
  rw [regularDeckLoop_transport_singularH1, triangleDualRepresentation_generator₁_matrix]

theorem regularDeckLoop_generator₂_singularH1 (b : TriangleRegularPoint)
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :
    regularFibreSingularH1Equiv P h₁ h₂ b
      (inducedHomology
        (regularPathTransport P h₁ h₂ (regularDeckLoop P h₁ h₂ b triangleGenerator₂) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) a) =
      A₂ *ᵥ regularFibreSingularH1Equiv P h₁ h₂ b a := by
  rw [regularDeckLoop_transport_singularH1, triangleDualRepresentation_generator₂_matrix]

theorem regularDeckLoop_cusp_singularH1 (b : TriangleRegularPoint)
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :
    regularFibreSingularH1Equiv P h₁ h₂ b
      (inducedHomology
        (regularPathTransport P h₁ h₂ (regularDeckLoop P h₁ h₂ b triangleCuspGenerator) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) a) =
      M₀ *ᵥ regularFibreSingularH1Equiv P h₁ h₂ b a := by
  rw [regularDeckLoop_transport_singularH1, triangleDualRepresentation_cusp_matrix]

end Wikipedia.HopfProblem.TrianglePeriodFamily
