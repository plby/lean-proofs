import Wikipedia.HopfProblem.TrianglePeriodFamilyTransportRegular

/-!
# Projecting specified local meridian lifts

These constructions depend only on the actual regular triangle covering,
not on a period map.  The later elliptic and cusp files provide explicit
local paths, whose coordinate formulas certify that their projections are
meridians.  This file records projection, unique lifting, and the change of
orientation.  No arbitrary path is asserted to be a meridian.

The endpoint convention is literal: a positive meridian lifts to the
inverse clockwise deck generator.  Its ordinary fibre transport therefore
has the matrix of the clockwise generator.  Reversing the meridian
reverses ordinary transport, as required by the source's inverse-transport
convention for clockwise meridians.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped Matrix MatrixGroups

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open FirstHurewicz SpecialPeriods

/-- Projection of a specified path to an inverse deck translate.  The
construction itself is independent of the varying torus family. -/
def projectLift (b : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b)) :
    Path (triangleRegularProject b) (triangleRegularProject b) :=
  (δ.map triangleRegularProject_covering.continuous).cast rfl
    (triangleRegularProject_covering.map_smul g⁻¹).symm

@[simp] theorem projectLift_apply (b : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b)) (t : unitInterval) :
    projectLift b g δ t = triangleRegularProject (δ t) := rfl

/-- Unique path lifting recovers the entire specified path. -/
theorem projectLift_liftPath (b : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b)) :
    triangleRegularProject_covering.isCoveringMap.liftPath (projectLift b g δ) b
      (projectLift b g δ).source = δ.toContinuousMap := by
  apply ContinuousMap.coe_injective
  exact ((triangleRegularProject_covering.isCoveringMap.eq_liftPath_iff _).mpr
    ⟨δ.continuous, rfl, δ.source⟩).symm

/-- The endpoint of the actual covering lift is proved, not supplied as
additional monodromy data. -/
theorem projectLift_monodromy (b : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b)) :
    triangleRegularProject_covering.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (projectLift b g δ)) ⟨b, rfl⟩ =
        ⟨g⁻¹ • b, triangleRegularProject_covering.map_smul g⁻¹⟩ := by
  apply triangleRegularProject_covering.isCoveringMap.monodromy_eq_of_map_eq
    (Path.Homotopic.Quotient.mk δ)
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

/-- Reverse the specified lift and translate its starting point back to
the original point.  Its endpoint is now the clockwise deck translate. -/
def reverseLift (b : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b)) : Path b ((g⁻¹)⁻¹ • b) :=
  (δ.symm.map (continuous_const_smul g)).cast (by simp) (by simp)

@[simp] theorem reverseLift_apply (b : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b)) (t : unitInterval) :
    reverseLift b g δ t = g • δ (unitInterval.symm t) := rfl

/-- The translated reverse lift projects to the literal reversed loop. -/
theorem projectLift_reverseLift (b : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b)) :
    projectLift b g⁻¹ (reverseLift b g δ) = (projectLift b g δ).symm := by
  ext t
  exact triangleRegularProject_covering.map_smul g

/-- The translated reverse path is the entire actual lift of the
clockwise loop from the original starting point. -/
theorem projectLift_symm_liftPath (b : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b)) :
    triangleRegularProject_covering.isCoveringMap.liftPath (projectLift b g δ).symm b
      (projectLift b g δ).symm.source = (reverseLift b g δ).toContinuousMap := by
  simpa only [projectLift_reverseLift] using
    projectLift_liftPath b g⁻¹ (reverseLift b g δ)

/-- The reversed loop has the clockwise generator as its genuine lifted
endpoint in the original starting sheet. -/
theorem projectLift_symm_monodromy (b : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b)) :
    (triangleRegularProject_covering.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (projectLift b g δ).symm) ⟨b, rfl⟩ :
        TriangleRegularPoint) = g • b := by
  rw [← projectLift_reverseLift]
  simpa only [inv_inv] using congrArg Subtype.val
    (projectLift_monodromy b g⁻¹ (reverseLift b g δ))

variable (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (Triangle.generatorTwoSL • z) = (P.point z).step₂)

/-- The family-independent projected loop is the literal loop used by
the already constructed flat transport. -/
theorem projectLift_eq_regularProjectedLoop (b : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b)) :
    projectLift b g δ = regularProjectedLoop P h₁ h₂ b g δ := rfl

theorem projectLift_latticeTransport (b : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b)) :
    regularLatticeTransportHom P h₁ h₂ b
      (Path.Homotopic.Quotient.mk (projectLift b g δ)) = triangleDualRepresentation g :=
  regularLatticeTransportHom_projectedLoop P h₁ h₂ b g δ

/-- Ordinary transport around the reversed, clockwise loop is the inverse
of the indicated dual matrix. -/
theorem projectLift_symm_latticeTransport (b : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b)) :
    regularLatticeTransportHom P h₁ h₂ b
      (Path.Homotopic.Quotient.mk (projectLift b g δ).symm) =
        (triangleDualRepresentation g)⁻¹ := by
  rw [← projectLift_reverseLift, projectLift_latticeTransport, map_inv]

/-- Inverting clockwise transport gives exactly the source's
inverse-transport matrix, without changing the orientation label. -/
theorem projectLift_symm_inverseTransport (b : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b)) :
    (regularLatticeTransportHom P h₁ h₂ b
      (Path.Homotopic.Quotient.mk (projectLift b g δ).symm))⁻¹ =
        triangleDualRepresentation g := by
  rw [projectLift_symm_latticeTransport, inv_inv]

/-- The actual first singular homology map, in the proved ordered period
column marking, for the specified positive local lift. -/
theorem projectLift_singularH1 (b : TriangleRegularPoint) (g : TriangleGroup)
    (δ : Path b (g⁻¹ • b))
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :
    regularFibreSingularH1Equiv P h₁ h₂ b
      (inducedHomology
        (regularPathTransport P h₁ h₂ (projectLift b g δ) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) a) =
      (triangleDualRepresentation g : LatticeMatrix) *ᵥ
        regularFibreSingularH1Equiv P h₁ h₂ b a :=
  regularProjectedLoop_transport_singularH1 P h₁ h₂ b g δ a

/-- Inverse transport along the clockwise loop acts on actual singular
homology by the source's matrix.  The inverse is the inverse of the
constructed fibre homeomorphism, not a convention imposed on a symbol. -/
theorem projectLift_symm_inverseTransport_singularH1
    (b : TriangleRegularPoint) (g : TriangleGroup) (δ : Path b (g⁻¹ • b))
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :
    regularFibreSingularH1Equiv P h₁ h₂ b
      (inducedHomology
        ((regularPathTransport P h₁ h₂ (projectLift b g δ).symm).symm :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) a) =
      (triangleDualRepresentation g : LatticeMatrix) *ᵥ
        regularFibreSingularH1Equiv P h₁ h₂ b a := by
  rw [regularPathTransport_symm, Homeomorph.symm_symm]
  exact projectLift_singularH1 P h₁ h₂ b g δ a

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
