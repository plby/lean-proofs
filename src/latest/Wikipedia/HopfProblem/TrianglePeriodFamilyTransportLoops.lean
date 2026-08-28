import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportRepresentation

/-!
# Actual regular-base loops realizing the integral triangle representation

Projecting a path in the actual regular triangle domain from `b` to
`g⁻¹ • b` gives a based loop whose lifted endpoint is verified by unique
path lifting. Its integral transport is the dual representation of `g`.
Path connectedness constructs such a loop for every group element, so
the actual transport representation has exactly the prescribed image.

These chosen paths realize deck elements; no winding or meridian claim
is made for an arbitrary choice of path. The endpoint criteria also
apply to any supplied geometric meridians with the specified lifts.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped Matrix MatrixGroups

namespace Wikipedia.HopfProblem.TrianglePeriodFamily

open SpecialPeriods

variable (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂)

/-- The integral representation of the actual regular base's fundamental
group, constructed from its genuine quotient-covering monodromy. -/
def regularLatticeTransportHom (b : TriangleRegularPoint) :
    FundamentalGroup TriangleRegularQuotient (triangleRegularProject b) →* SL(4, ℤ) :=
  (regularData P h₁ h₂).latticeTransportHom (regularCovering P h₁ h₂) b

/-- Project an actual specified path to an inverse deck translate. -/
def regularProjectedLoop (b : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b)) :
    Path (triangleRegularProject b) (triangleRegularProject b) :=
  (regularData P h₁ h₂).projectedLoop (regularCovering P h₁ h₂) b g δ

@[simp] theorem regularProjectedLoop_apply (b : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b)) (t : unitInterval) :
    regularProjectedLoop P h₁ h₂ b g δ t = triangleRegularProject (δ t) := rfl

/-- The actual covering's path-lifting theorem verifies the projected loop's endpoint. -/
theorem regularProjectedLoop_monodromy (b : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b)) :
    triangleRegularProject_covering.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (regularProjectedLoop P h₁ h₂ b g δ)) ⟨b, rfl⟩ =
        ⟨g⁻¹ • b, triangleRegularProject_covering.map_smul g⁻¹⟩ :=
  (regularData P h₁ h₂).projectedLoop_monodromy (regularCovering P h₁ h₂) b g δ

/-- The transport of the specified projected loop is the literal dual
matrix representation of the indicated element, with its inverse convention exposed. -/
theorem regularLatticeTransportHom_projectedLoop (b : TriangleRegularPoint)
    (g : TriangleGroup) (δ : Path b (g⁻¹ • b)) :
    regularLatticeTransportHom P h₁ h₂ b
      (Path.Homotopic.Quotient.mk (regularProjectedLoop P h₁ h₂ b g δ)) =
        triangleDualRepresentation g :=
  (regularData P h₁ h₂).latticeTransportHom_projectedLoop (regularCovering P h₁ h₂) b g δ

theorem regularProjectedLoop_generator₁_matrix (b : TriangleRegularPoint)
    (δ : Path b (triangleGenerator₁⁻¹ • b)) :
    (regularLatticeTransportHom P h₁ h₂ b
      (Path.Homotopic.Quotient.mk
        (regularProjectedLoop P h₁ h₂ b triangleGenerator₁ δ)) : LatticeMatrix) = A₁ := by
  rw [regularLatticeTransportHom_projectedLoop, triangleDualRepresentation_generator₁_matrix]

theorem regularProjectedLoop_generator₂_matrix (b : TriangleRegularPoint)
    (δ : Path b (triangleGenerator₂⁻¹ • b)) :
    (regularLatticeTransportHom P h₁ h₂ b
      (Path.Homotopic.Quotient.mk
        (regularProjectedLoop P h₁ h₂ b triangleGenerator₂ δ)) : LatticeMatrix) = A₂ := by
  rw [regularLatticeTransportHom_projectedLoop, triangleDualRepresentation_generator₂_matrix]

theorem regularProjectedLoop_cusp_matrix (b : TriangleRegularPoint)
    (δ : Path b (triangleCuspGenerator⁻¹ • b)) :
    (regularLatticeTransportHom P h₁ h₂ b
      (Path.Homotopic.Quotient.mk
        (regularProjectedLoop P h₁ h₂ b triangleCuspGenerator δ)) : LatticeMatrix) = M₀ := by
  rw [regularLatticeTransportHom_projectedLoop, triangleDualRepresentation_cusp_matrix]

/-- Path connectedness of the actual regular triangle domain supplies
an actual based loop realizing each deck element. This choice is not
asserted to have any specified geometric winding. -/
def regularDeckLoop (b : TriangleRegularPoint) (g : TriangleGroup) :
    Path (triangleRegularProject b) (triangleRegularProject b) :=
  regularProjectedLoop P h₁ h₂ b g (PathConnectedSpace.somePath b (g⁻¹ • b))

theorem regularDeckLoop_monodromy (b : TriangleRegularPoint) (g : TriangleGroup) :
    triangleRegularProject_covering.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (regularDeckLoop P h₁ h₂ b g)) ⟨b, rfl⟩ =
        ⟨g⁻¹ • b, triangleRegularProject_covering.map_smul g⁻¹⟩ :=
  regularProjectedLoop_monodromy P h₁ h₂ b g (PathConnectedSpace.somePath b (g⁻¹ • b))

@[simp] theorem regularLatticeTransportHom_deckLoop (b : TriangleRegularPoint)
    (g : TriangleGroup) :
    regularLatticeTransportHom P h₁ h₂ b
      (Path.Homotopic.Quotient.mk (regularDeckLoop P h₁ h₂ b g)) =
        triangleDualRepresentation g :=
  regularLatticeTransportHom_projectedLoop P h₁ h₂ b g
    (PathConnectedSpace.somePath b (g⁻¹ • b))

@[simp] theorem regularDeckLoop_generator₁_matrix (b : TriangleRegularPoint) :
    (regularLatticeTransportHom P h₁ h₂ b
      (Path.Homotopic.Quotient.mk
        (regularDeckLoop P h₁ h₂ b triangleGenerator₁)) : LatticeMatrix) = A₁ := by
  rw [regularLatticeTransportHom_deckLoop, triangleDualRepresentation_generator₁_matrix]

@[simp] theorem regularDeckLoop_generator₂_matrix (b : TriangleRegularPoint) :
    (regularLatticeTransportHom P h₁ h₂ b
      (Path.Homotopic.Quotient.mk
        (regularDeckLoop P h₁ h₂ b triangleGenerator₂)) : LatticeMatrix) = A₂ := by
  rw [regularLatticeTransportHom_deckLoop, triangleDualRepresentation_generator₂_matrix]

@[simp] theorem regularDeckLoop_cusp_matrix (b : TriangleRegularPoint) :
    (regularLatticeTransportHom P h₁ h₂ b
      (Path.Homotopic.Quotient.mk
        (regularDeckLoop P h₁ h₂ b triangleCuspGenerator)) : LatticeMatrix) = M₀ := by
  rw [regularLatticeTransportHom_deckLoop, triangleDualRepresentation_cusp_matrix]

/-- Specified lifts of any supplied actual loops determine their integral
transport; this criterion applies in particular to supplied meridians. -/
theorem regularLatticeTransportHom_eq_of_inverse_endpoint (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (g : TriangleGroup)
    (hγ : (triangleRegularProject_covering.isCoveringMap.monodromy γ ⟨b, rfl⟩ :
      TriangleRegularPoint) = g⁻¹ • b) :
    regularLatticeTransportHom P h₁ h₂ b γ = triangleDualRepresentation g :=
  (regularData P h₁ h₂).latticeTransportHom_eq_of_inverse_endpoint
    (regularCovering P h₁ h₂) b γ g hγ

theorem regularLatticeTransportHom_generator₁ (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (hγ : (triangleRegularProject_covering.isCoveringMap.monodromy γ ⟨b, rfl⟩ :
      TriangleRegularPoint) = triangleGenerator₁⁻¹ • b) :
    (regularLatticeTransportHom P h₁ h₂ b γ : LatticeMatrix) = A₁ := by
  rw [regularLatticeTransportHom_eq_of_inverse_endpoint P h₁ h₂ b γ triangleGenerator₁ hγ,
    triangleDualRepresentation_generator₁_matrix]

theorem regularLatticeTransportHom_generator₂ (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (hγ : (triangleRegularProject_covering.isCoveringMap.monodromy γ ⟨b, rfl⟩ :
      TriangleRegularPoint) = triangleGenerator₂⁻¹ • b) :
    (regularLatticeTransportHom P h₁ h₂ b γ : LatticeMatrix) = A₂ := by
  rw [regularLatticeTransportHom_eq_of_inverse_endpoint P h₁ h₂ b γ triangleGenerator₂ hγ,
    triangleDualRepresentation_generator₂_matrix]

theorem regularLatticeTransportHom_cusp (b : TriangleRegularPoint)
    (γ : FundamentalGroup TriangleRegularQuotient (triangleRegularProject b))
    (hγ : (triangleRegularProject_covering.isCoveringMap.monodromy γ ⟨b, rfl⟩ :
      TriangleRegularPoint) = triangleCuspGenerator⁻¹ • b) :
    (regularLatticeTransportHom P h₁ h₂ b γ : LatticeMatrix) = M₀ := by
  rw [regularLatticeTransportHom_eq_of_inverse_endpoint P h₁ h₂ b γ triangleCuspGenerator hγ,
    triangleDualRepresentation_cusp_matrix]

/-- The actual regular-base representation has precisely the dual
representation's image; the reverse inclusion uses the constructed loops. -/
theorem regularLatticeTransportHom_range (b : TriangleRegularPoint) :
    (regularLatticeTransportHom P h₁ h₂ b).range = triangleDualRepresentation.range := by
  ext A
  constructor
  · rintro ⟨γ, rfl⟩
    exact ⟨(regularData P h₁ h₂).deckTransportHom (regularCovering P h₁ h₂) b γ, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨Path.Homotopic.Quotient.mk (regularDeckLoop P h₁ h₂ b g),
      regularLatticeTransportHom_deckLoop P h₁ h₂ b g⟩

end Wikipedia.HopfProblem.TrianglePeriodFamily
