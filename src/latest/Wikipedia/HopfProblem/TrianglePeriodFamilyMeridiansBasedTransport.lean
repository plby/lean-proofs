import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansTransport

/-!
# Clockwise geometric meridians in one common marked fibre

The local circles with their actual tails give three meridians based at
one arbitrary regular point.  Their clockwise reversals have exactly the
source's matrices under inverse transport on the literal fibre singular
homology.  No fundamental-group generating or product relation is assumed
for the chosen tails.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped Matrix MatrixGroups

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open FirstHurewicz SpecialPeriods SpecialPeriods.Triangle

/-- The clockwise elliptic meridian with its actual based tail. -/
def basedEllipticCWMeridian (b : TriangleRegularPoint) (j : Elliptic.Kind)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Path (triangleRegularProject b) (triangleRegularProject b) :=
  (basedEllipticCCWMeridian b j r hr hr1).symm

/-- The clockwise cusp meridian with its actual based tail. -/
def basedCuspCWMeridian (b : TriangleRegularPoint) (Y : ℝ)
    (hY : width ≤ Y) (z : horodisc Y) :
    Path (triangleRegularProject b) (triangleRegularProject b) :=
  (basedCuspCCWMeridian b Y hY z).symm

theorem basedEllipticCWMeridian_monodromy (b : TriangleRegularPoint) (j : Elliptic.Kind)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (triangleRegularProject_covering.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (basedEllipticCWMeridian b j r hr hr1))
      ⟨b, rfl⟩ : TriangleRegularPoint) = ellipticGenerator j • b :=
  projectLift_symm_monodromy b (ellipticGenerator j)
    (rebaseLift b (ellipticBasePoint j r hr hr1) (ellipticGenerator j)
      (PathConnectedSpace.somePath b _) (ellipticCCWLift j r hr hr1))

theorem basedCuspCWMeridian_monodromy (b : TriangleRegularPoint) (Y : ℝ)
    (hY : width ≤ Y) (z : horodisc Y) :
    (triangleRegularProject_covering.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk (basedCuspCWMeridian b Y hY z))
      ⟨b, rfl⟩ : TriangleRegularPoint) = triangleCuspGenerator • b :=
  projectLift_symm_monodromy b triangleCuspGenerator
    (rebaseLift b (cuspBasePoint Y hY z) triangleCuspGenerator
      (PathConnectedSpace.somePath b _) (cuspCCWLift Y hY z))

variable (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (generatorTwoSL • z) = (P.point z).step₂)

/-- The two clockwise elliptic meridians give `A₁` and `A₂` in the
inverse-transport convention at one common base point. -/
theorem basedEllipticCWMeridian_inverseTransport_matrix (b : TriangleRegularPoint)
    (j : Elliptic.Kind) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (((regularLatticeTransportHom P h₁ h₂ b
      (Path.Homotopic.Quotient.mk (basedEllipticCWMeridian b j r hr hr1)))⁻¹ : SL(4, ℤ)) :
        LatticeMatrix) = j.matrix := by
  change (((regularLatticeTransportHom P h₁ h₂ b
    (Path.Homotopic.Quotient.mk (basedEllipticCCWMeridian b j r hr hr1))⁻¹)⁻¹ : SL(4, ℤ)) :
      LatticeMatrix) = _
  rw [map_inv, inv_inv, basedEllipticCCWMeridian_matrix]

/-- The clockwise cusp meridian gives `M₀` in that same base marking. -/
theorem basedCuspCWMeridian_inverseTransport_matrix (b : TriangleRegularPoint)
    (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    (((regularLatticeTransportHom P h₁ h₂ b
      (Path.Homotopic.Quotient.mk (basedCuspCWMeridian b Y hY z)))⁻¹ : SL(4, ℤ)) :
        LatticeMatrix) = M₀ := by
  change (((regularLatticeTransportHom P h₁ h₂ b
    (Path.Homotopic.Quotient.mk (basedCuspCCWMeridian b Y hY z))⁻¹)⁻¹ : SL(4, ℤ)) :
      LatticeMatrix) = _
  rw [map_inv, inv_inv, basedCuspCCWMeridian_matrix]

theorem basedEllipticCCWMeridian_singularH1 (b : TriangleRegularPoint) (j : Elliptic.Kind)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :
    regularFibreSingularH1Equiv P h₁ h₂ b
      (inducedHomology
        (regularPathTransport P h₁ h₂ (basedEllipticCCWMeridian b j r hr hr1) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) a) =
      j.matrix *ᵥ regularFibreSingularH1Equiv P h₁ h₂ b a := by
  have h := regularTransport_singularH1 P h₁ h₂ b
    (Path.Homotopic.Quotient.mk (basedEllipticCCWMeridian b j r hr hr1)) a
  rw [basedEllipticCCWMeridian_matrix] at h
  exact h

theorem basedCuspCCWMeridian_singularH1 (b : TriangleRegularPoint) (Y : ℝ)
    (hY : width ≤ Y) (z : horodisc Y)
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :
    regularFibreSingularH1Equiv P h₁ h₂ b
      (inducedHomology
        (regularPathTransport P h₁ h₂ (basedCuspCCWMeridian b Y hY z) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) a) =
      M₀ *ᵥ regularFibreSingularH1Equiv P h₁ h₂ b a := by
  have h := regularTransport_singularH1 P h₁ h₂ b
    (Path.Homotopic.Quotient.mk (basedCuspCCWMeridian b Y hY z)) a
  rw [basedCuspCCWMeridian_matrix] at h
  exact h

/-- Source-convention monodromy on the literal common fibre homology. -/
theorem basedEllipticCWMeridian_inverseTransport_singularH1 (b : TriangleRegularPoint)
    (j : Elliptic.Kind) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :
    regularFibreSingularH1Equiv P h₁ h₂ b
      (inducedHomology
        ((regularPathTransport P h₁ h₂ (basedEllipticCWMeridian b j r hr hr1)).symm :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) a) =
      j.matrix *ᵥ regularFibreSingularH1Equiv P h₁ h₂ b a := by
  change regularFibreSingularH1Equiv P h₁ h₂ b
    (inducedHomology ((regularPathTransport P h₁ h₂
      (basedEllipticCCWMeridian b j r hr hr1).symm).symm : C(_, _)) a) = _
  rw [regularPathTransport_symm, Homeomorph.symm_symm]
  exact basedEllipticCCWMeridian_singularH1 P h₁ h₂ b j r hr hr1 a

/-- The cusp source-convention monodromy on that same literal fibre. -/
theorem basedCuspCWMeridian_inverseTransport_singularH1 (b : TriangleRegularPoint)
    (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y)
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject b))) :
    regularFibreSingularH1Equiv P h₁ h₂ b
      (inducedHomology
        ((regularPathTransport P h₁ h₂ (basedCuspCWMeridian b Y hY z)).symm :
          C(RegularFibre P h₁ h₂ (triangleRegularProject b),
            RegularFibre P h₁ h₂ (triangleRegularProject b))) a) =
      M₀ *ᵥ regularFibreSingularH1Equiv P h₁ h₂ b a := by
  change regularFibreSingularH1Equiv P h₁ h₂ b
    (inducedHomology ((regularPathTransport P h₁ h₂
      (basedCuspCCWMeridian b Y hY z).symm).symm : C(_, _)) a) = _
  rw [regularPathTransport_symm, Homeomorph.symm_symm]
  exact basedCuspCCWMeridian_singularH1 P h₁ h₂ b Y hY z a

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
