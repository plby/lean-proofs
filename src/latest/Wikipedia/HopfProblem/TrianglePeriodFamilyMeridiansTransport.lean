import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansLoops

/-!
# Actual homology monodromy of the geometric meridians

The local circles and their lifts have already been constructed in the
actual regular triangle quotient.  The theorems here apply the proved
flat transport to those loops, without a supplied lift-endpoint
hypothesis.  Counterclockwise forward transport gives `A₁`, `A₂`, and
`M₀`.  Clockwise inverse transport gives the same matrices, exactly as in
Convention 3.17 and Proposition 3.19 of the source.

The statements concern the literal integral singular homology of the
actual varying-family fibres, expressed in the proved period-column
marking.  The final statements move the geometric meridians to one common
regular base point by the actual outgoing and returning tails.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped Matrix MatrixGroups

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open FirstHurewicz SpecialPeriods SpecialPeriods.Triangle

private theorem elliptic_dual_matrix (j : Elliptic.Kind) :
    (triangleDualRepresentation (ellipticGenerator j) : LatticeMatrix) = j.matrix := by
  cases j
  · exact triangleDualRepresentation_generator₁_matrix
  · exact triangleDualRepresentation_generator₂_matrix

variable (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (generatorTwoSL • z) = (P.point z).step₂)

theorem ellipticCCWMeridian_latticeTransport (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    regularLatticeTransportHom P h₁ h₂ (ellipticBasePoint j r hr hr1)
      (Path.Homotopic.Quotient.mk (ellipticCCWMeridian j r hr hr1)) =
        triangleDualRepresentation (ellipticGenerator j) :=
  projectLift_latticeTransport P h₁ h₂ _ _ _

/-- The genuine positive order-three/four meridian has matrix `A₁`/`A₂`. -/
theorem ellipticCCWMeridian_matrix (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    (regularLatticeTransportHom P h₁ h₂ (ellipticBasePoint j r hr hr1)
      (Path.Homotopic.Quotient.mk (ellipticCCWMeridian j r hr hr1)) : LatticeMatrix) =
        j.matrix := by
  rw [ellipticCCWMeridian_latticeTransport, elliptic_dual_matrix]

/-- Clockwise forward transport is the inverse dual matrix. -/
theorem ellipticCWMeridian_forwardTransport (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    regularLatticeTransportHom P h₁ h₂ (ellipticBasePoint j r hr hr1)
      (Path.Homotopic.Quotient.mk (ellipticCWMeridian j r hr hr1)) =
        (triangleDualRepresentation (ellipticGenerator j))⁻¹ :=
  projectLift_symm_latticeTransport P h₁ h₂ _ _ _

/-- The actual clockwise loop has the source's matrix in its explicitly
declared inverse-transport convention. -/
theorem ellipticCWMeridian_inverseTransport_matrix (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    (((regularLatticeTransportHom P h₁ h₂ (ellipticBasePoint j r hr hr1)
      (Path.Homotopic.Quotient.mk (ellipticCWMeridian j r hr hr1)))⁻¹ : SL(4, ℤ)) :
        LatticeMatrix) =
        j.matrix := by
  rw [ellipticCWMeridian_forwardTransport, inv_inv, elliptic_dual_matrix]

theorem ellipticCCWMeridian_singularH1 (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1)
    (a : SingularH1 (RegularFibre P h₁ h₂
      (triangleRegularProject (ellipticBasePoint j r hr hr1)))) :
    regularFibreSingularH1Equiv P h₁ h₂ (ellipticBasePoint j r hr hr1)
      (inducedHomology
        (regularPathTransport P h₁ h₂ (ellipticCCWMeridian j r hr hr1) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject (ellipticBasePoint j r hr hr1)),
            RegularFibre P h₁ h₂ (triangleRegularProject (ellipticBasePoint j r hr hr1)))) a) =
      j.matrix *ᵥ regularFibreSingularH1Equiv P h₁ h₂ (ellipticBasePoint j r hr hr1) a := by
  have h := projectLift_singularH1 P h₁ h₂ (ellipticBasePoint j r hr hr1)
    (ellipticGenerator j) (ellipticCCWLift j r hr hr1) a
  rw [elliptic_dual_matrix] at h
  exact h

/-- On actual singular homology, the inverse of the constructed
clockwise fibre homeomorphism acts by the source's `A₁`/`A₂`. -/
theorem ellipticCWMeridian_inverseTransport_singularH1 (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1)
    (a : SingularH1 (RegularFibre P h₁ h₂
      (triangleRegularProject (ellipticBasePoint j r hr hr1)))) :
    regularFibreSingularH1Equiv P h₁ h₂ (ellipticBasePoint j r hr hr1)
      (inducedHomology
        ((regularPathTransport P h₁ h₂ (ellipticCWMeridian j r hr hr1)).symm :
          C(RegularFibre P h₁ h₂ (triangleRegularProject (ellipticBasePoint j r hr hr1)),
            RegularFibre P h₁ h₂ (triangleRegularProject (ellipticBasePoint j r hr hr1)))) a) =
      j.matrix *ᵥ regularFibreSingularH1Equiv P h₁ h₂ (ellipticBasePoint j r hr hr1) a := by
  have h := projectLift_symm_inverseTransport_singularH1 P h₁ h₂
    (ellipticBasePoint j r hr hr1) (ellipticGenerator j) (ellipticCCWLift j r hr hr1) a
  rw [elliptic_dual_matrix] at h
  exact h

theorem cuspCCWMeridian_latticeTransport (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    regularLatticeTransportHom P h₁ h₂ (cuspBasePoint Y hY z)
      (Path.Homotopic.Quotient.mk (cuspCCWMeridian Y hY z)) =
        triangleDualRepresentation triangleCuspGenerator :=
  projectLift_latticeTransport P h₁ h₂ _ _ _

/-- The genuine positive cusp meridian has matrix `M₀`. -/
theorem cuspCCWMeridian_matrix (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    (regularLatticeTransportHom P h₁ h₂ (cuspBasePoint Y hY z)
      (Path.Homotopic.Quotient.mk (cuspCCWMeridian Y hY z)) : LatticeMatrix) = M₀ := by
  rw [cuspCCWMeridian_latticeTransport, triangleDualRepresentation_cusp_matrix]

theorem cuspCWMeridian_forwardTransport (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    regularLatticeTransportHom P h₁ h₂ (cuspBasePoint Y hY z)
      (Path.Homotopic.Quotient.mk (cuspCWMeridian Y hY z)) =
        (triangleDualRepresentation triangleCuspGenerator)⁻¹ :=
  projectLift_symm_latticeTransport P h₁ h₂ _ _ _

/-- Clockwise inverse transport around the actual cusp circle is `M₀`. -/
theorem cuspCWMeridian_inverseTransport_matrix (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    (((regularLatticeTransportHom P h₁ h₂ (cuspBasePoint Y hY z)
      (Path.Homotopic.Quotient.mk (cuspCWMeridian Y hY z)))⁻¹ : SL(4, ℤ)) :
        LatticeMatrix) = M₀ := by
  rw [cuspCWMeridian_forwardTransport, inv_inv, triangleDualRepresentation_cusp_matrix]

theorem cuspCCWMeridian_singularH1 (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y)
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject (cuspBasePoint Y hY z)))) :
    regularFibreSingularH1Equiv P h₁ h₂ (cuspBasePoint Y hY z)
      (inducedHomology
        (regularPathTransport P h₁ h₂ (cuspCCWMeridian Y hY z) :
          C(RegularFibre P h₁ h₂ (triangleRegularProject (cuspBasePoint Y hY z)),
            RegularFibre P h₁ h₂ (triangleRegularProject (cuspBasePoint Y hY z)))) a) =
      M₀ *ᵥ regularFibreSingularH1Equiv P h₁ h₂ (cuspBasePoint Y hY z) a := by
  have h := projectLift_singularH1 P h₁ h₂ (cuspBasePoint Y hY z)
    triangleCuspGenerator (cuspCCWLift Y hY z) a
  rw [triangleDualRepresentation_cusp_matrix] at h
  exact h

/-- The inverse of the actual clockwise cusp-transport homeomorphism
acts on the fibre's actual singular homology by `M₀`. -/
theorem cuspCWMeridian_inverseTransport_singularH1 (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y)
    (a : SingularH1 (RegularFibre P h₁ h₂ (triangleRegularProject (cuspBasePoint Y hY z)))) :
    regularFibreSingularH1Equiv P h₁ h₂ (cuspBasePoint Y hY z)
      (inducedHomology
        ((regularPathTransport P h₁ h₂ (cuspCWMeridian Y hY z)).symm :
          C(RegularFibre P h₁ h₂ (triangleRegularProject (cuspBasePoint Y hY z)),
            RegularFibre P h₁ h₂ (triangleRegularProject (cuspBasePoint Y hY z)))) a) =
      M₀ *ᵥ regularFibreSingularH1Equiv P h₁ h₂ (cuspBasePoint Y hY z) a := by
  have h := projectLift_symm_inverseTransport_singularH1 P h₁ h₂
    (cuspBasePoint Y hY z) triangleCuspGenerator (cuspCCWLift Y hY z) a
  rw [triangleDualRepresentation_cusp_matrix] at h
  exact h

/-- Both positive elliptic meridians have their indicated matrix in one
common base fibre, after attaching the proved outgoing and return tails. -/
theorem basedEllipticCCWMeridian_matrix (b : TriangleRegularPoint) (j : Elliptic.Kind)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (regularLatticeTransportHom P h₁ h₂ b
      (Path.Homotopic.Quotient.mk (basedEllipticCCWMeridian b j r hr hr1)) : LatticeMatrix) =
        j.matrix := by
  change (regularLatticeTransportHom P h₁ h₂ b
    (Path.Homotopic.Quotient.mk (basedLoop b _ _ _)) : LatticeMatrix) = _
  rw [basedLoop_latticeTransport, elliptic_dual_matrix]

/-- The positive cusp meridian is marked by `M₀` in that same base fibre. -/
theorem basedCuspCCWMeridian_matrix (b : TriangleRegularPoint) (Y : ℝ)
    (hY : width ≤ Y) (z : horodisc Y) :
    (regularLatticeTransportHom P h₁ h₂ b
      (Path.Homotopic.Quotient.mk (basedCuspCCWMeridian b Y hY z)) : LatticeMatrix) = M₀ := by
  change (regularLatticeTransportHom P h₁ h₂ b
    (Path.Homotopic.Quotient.mk (basedLoop b _ _ _)) : LatticeMatrix) = _
  rw [basedLoop_latticeTransport, triangleDualRepresentation_cusp_matrix]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
