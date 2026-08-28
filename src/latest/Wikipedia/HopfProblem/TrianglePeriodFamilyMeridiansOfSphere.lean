import Wikipedia.HopfProblem.SpecialPeriodsConstruction
import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansBasedTransport

/-!
# Geometric meridian monodromy for the constructed period family

The period map here is the one constructed from the normalized
biholomorphism of the actual compact triangle quotient with the sphere.
Its generator equations are proved by that construction, not additional
inputs to the monodromy theorems.

The loops are the existing, period-independent geometric meridians.
Counterclockwise forward transport and clockwise inverse transport act
on the literal integral singular homology of the constructed fibres by
`A₁`, `A₂`, and `M₀`, in the proved period-column marking.  The final
formulas use the existing tails to put all three meridians at one common
regular base point, with both orientations on that same fibre homology.

The only geometric input is the normalized sphere biholomorphism and
its three marked values.  Its existence is not asserted in this module.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint Matrix MatrixGroups

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians.OfSphere

open FirstHurewicz SpecialPeriods SpecialPeriods.Triangle

attribute [local instance] triangleCompactifiedChartedSpace

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))
  (h₀ : π (triangleOpenInclusion triangleOrbitCenterOne) = ((0 : ℂ) : RiemannSphere))
  (h₁ : π (triangleOpenInclusion triangleOrbitCenterTwo) = ((1 : ℂ) : RiemannSphere))

local notation "P" => Construction.periodMapOfSphere π hπ h₀ h₁
local notation "hgen₁" => Construction.periodMapOfSphere_generator₁ π hπ h₀ h₁
local notation "hgen₂" => Construction.periodMapOfSphere_generator₂ π hπ h₀ h₁

/-- The literal fibre of the regular family built from the constructed
period map and its proved generator equations. -/
abbrev Fibre (x : TriangleRegularQuotient) : Type :=
  RegularFibre P hgen₁ hgen₂ x

/-- Actual transport in the constructed regular family along a path. -/
abbrev pathTransport {x y : TriangleRegularQuotient} (γ : Path x y) :
    Fibre π hπ h₀ h₁ x ≃ₜ Fibre π hπ h₀ h₁ y :=
  regularPathTransport P hgen₁ hgen₂ γ

/-- The proved period-column marking of actual integral singular homology. -/
abbrev fibreSingularH1Equiv (b : TriangleRegularPoint) :
    SingularH1 (Fibre π hπ h₀ h₁ (triangleRegularProject b)) ≃ₗ[ℤ] Lattice :=
  regularFibreSingularH1Equiv P hgen₁ hgen₂ b

/-- Integral lattice transport for the constructed regular family. -/
abbrev latticeTransportHom (b : TriangleRegularPoint) :
    FundamentalGroup TriangleRegularQuotient (triangleRegularProject b) →* SL(4, ℤ) :=
  regularLatticeTransportHom P hgen₁ hgen₂ b

/-- The actual positive elliptic meridian has matrix `A₁` or `A₂`. -/
theorem ellipticCCWMeridian_matrix (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    (latticeTransportHom π hπ h₀ h₁ (ellipticBasePoint j r hr hr1)
      (Path.Homotopic.Quotient.mk (ellipticCCWMeridian j r hr hr1)) : LatticeMatrix) =
        j.matrix :=
  Meridians.ellipticCCWMeridian_matrix P hgen₁ hgen₂ j r hr hr1

/-- The actual clockwise elliptic meridian has the source's matrix
when inverse transport is used, as in the source's convention. -/
theorem ellipticCWMeridian_inverseTransport_matrix (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    (((latticeTransportHom π hπ h₀ h₁ (ellipticBasePoint j r hr hr1)
      (Path.Homotopic.Quotient.mk (ellipticCWMeridian j r hr hr1)))⁻¹ : SL(4, ℤ)) :
        LatticeMatrix) = j.matrix :=
  Meridians.ellipticCWMeridian_inverseTransport_matrix P hgen₁ hgen₂ j r hr hr1

/-- The positive elliptic meridian acts on the actual fibre's singular
homology by `A₁` or `A₂`, not merely on an abstract lattice. -/
theorem ellipticCCWMeridian_singularH1 (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1)
    (a : SingularH1 (Fibre π hπ h₀ h₁
      (triangleRegularProject (ellipticBasePoint j r hr hr1)))) :
    fibreSingularH1Equiv π hπ h₀ h₁ (ellipticBasePoint j r hr hr1)
      (inducedHomology
        (pathTransport π hπ h₀ h₁ (ellipticCCWMeridian j r hr hr1) :
          C(Fibre π hπ h₀ h₁ (triangleRegularProject (ellipticBasePoint j r hr hr1)),
            Fibre π hπ h₀ h₁ (triangleRegularProject (ellipticBasePoint j r hr hr1)))) a) =
      j.matrix *ᵥ fibreSingularH1Equiv π hπ h₀ h₁ (ellipticBasePoint j r hr hr1) a :=
  Meridians.ellipticCCWMeridian_singularH1 P hgen₁ hgen₂ j r hr hr1 a

/-- The inverse of actual clockwise elliptic fibre transport acts on
integral singular homology by the source's `A₁` or `A₂`. -/
theorem ellipticCWMeridian_inverseTransport_singularH1 (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1)
    (a : SingularH1 (Fibre π hπ h₀ h₁
      (triangleRegularProject (ellipticBasePoint j r hr hr1)))) :
    fibreSingularH1Equiv π hπ h₀ h₁ (ellipticBasePoint j r hr hr1)
      (inducedHomology
        ((pathTransport π hπ h₀ h₁ (ellipticCWMeridian j r hr hr1)).symm :
          C(Fibre π hπ h₀ h₁ (triangleRegularProject (ellipticBasePoint j r hr hr1)),
            Fibre π hπ h₀ h₁ (triangleRegularProject (ellipticBasePoint j r hr hr1)))) a) =
      j.matrix *ᵥ fibreSingularH1Equiv π hπ h₀ h₁ (ellipticBasePoint j r hr hr1) a :=
  Meridians.ellipticCWMeridian_inverseTransport_singularH1 P hgen₁ hgen₂ j r hr hr1 a

/-- The actual positive cusp meridian has matrix `M₀`. -/
theorem cuspCCWMeridian_matrix (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    (latticeTransportHom π hπ h₀ h₁ (cuspBasePoint Y hY z)
      (Path.Homotopic.Quotient.mk (cuspCCWMeridian Y hY z)) : LatticeMatrix) = M₀ :=
  Meridians.cuspCCWMeridian_matrix P hgen₁ hgen₂ Y hY z

/-- The actual clockwise cusp meridian has matrix `M₀` in the source's
inverse-transport convention. -/
theorem cuspCWMeridian_inverseTransport_matrix (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y) :
    (((latticeTransportHom π hπ h₀ h₁ (cuspBasePoint Y hY z)
      (Path.Homotopic.Quotient.mk (cuspCWMeridian Y hY z)))⁻¹ : SL(4, ℤ)) :
        LatticeMatrix) = M₀ :=
  Meridians.cuspCWMeridian_inverseTransport_matrix P hgen₁ hgen₂ Y hY z

/-- The positive cusp meridian acts on actual integral singular homology
by the explicit cusp matrix `M₀`. -/
theorem cuspCCWMeridian_singularH1 (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y)
    (a : SingularH1 (Fibre π hπ h₀ h₁ (triangleRegularProject (cuspBasePoint Y hY z)))) :
    fibreSingularH1Equiv π hπ h₀ h₁ (cuspBasePoint Y hY z)
      (inducedHomology
        (pathTransport π hπ h₀ h₁ (cuspCCWMeridian Y hY z) :
          C(Fibre π hπ h₀ h₁ (triangleRegularProject (cuspBasePoint Y hY z)),
            Fibre π hπ h₀ h₁ (triangleRegularProject (cuspBasePoint Y hY z)))) a) =
      M₀ *ᵥ fibreSingularH1Equiv π hπ h₀ h₁ (cuspBasePoint Y hY z) a :=
  Meridians.cuspCCWMeridian_singularH1 P hgen₁ hgen₂ Y hY z a

/-- The inverse of actual clockwise cusp fibre transport acts on the
actual integral singular homology by the source's `M₀`. -/
theorem cuspCWMeridian_inverseTransport_singularH1 (Y : ℝ) (hY : width ≤ Y)
    (z : horodisc Y)
    (a : SingularH1 (Fibre π hπ h₀ h₁ (triangleRegularProject (cuspBasePoint Y hY z)))) :
    fibreSingularH1Equiv π hπ h₀ h₁ (cuspBasePoint Y hY z)
      (inducedHomology
        ((pathTransport π hπ h₀ h₁ (cuspCWMeridian Y hY z)).symm :
          C(Fibre π hπ h₀ h₁ (triangleRegularProject (cuspBasePoint Y hY z)),
            Fibre π hπ h₀ h₁ (triangleRegularProject (cuspBasePoint Y hY z)))) a) =
      M₀ *ᵥ fibreSingularH1Equiv π hπ h₀ h₁ (cuspBasePoint Y hY z) a :=
  Meridians.cuspCWMeridian_inverseTransport_singularH1 P hgen₁ hgen₂ Y hY z a

/-- Attaching the existing outgoing and return tails gives the same
elliptic matrices in any one fixed regular base fibre. -/
theorem basedEllipticCCWMeridian_matrix (b : TriangleRegularPoint) (j : Elliptic.Kind)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (latticeTransportHom π hπ h₀ h₁ b
      (Path.Homotopic.Quotient.mk (basedEllipticCCWMeridian b j r hr hr1)) : LatticeMatrix) =
        j.matrix :=
  Meridians.basedEllipticCCWMeridian_matrix P hgen₁ hgen₂ b j r hr hr1

/-- The cusp meridian has matrix `M₀` in that same common base fibre. -/
theorem basedCuspCCWMeridian_matrix (b : TriangleRegularPoint) (Y : ℝ)
    (hY : width ≤ Y) (z : horodisc Y) :
    (latticeTransportHom π hπ h₀ h₁ b
      (Path.Homotopic.Quotient.mk (basedCuspCCWMeridian b Y hY z)) : LatticeMatrix) = M₀ :=
  Meridians.basedCuspCCWMeridian_matrix P hgen₁ hgen₂ b Y hY z

/-- The actual clockwise elliptic meridians give the source matrices
in one common base fibre under inverse transport. -/
theorem basedEllipticCWMeridian_inverseTransport_matrix (b : TriangleRegularPoint)
    (j : Elliptic.Kind) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    (((latticeTransportHom π hπ h₀ h₁ b
      (Path.Homotopic.Quotient.mk (basedEllipticCWMeridian b j r hr hr1)))⁻¹ : SL(4, ℤ)) :
        LatticeMatrix) = j.matrix :=
  Meridians.basedEllipticCWMeridian_inverseTransport_matrix P hgen₁ hgen₂ b j r hr hr1

/-- The actual clockwise cusp meridian gives `M₀` in that same marking
under inverse transport. -/
theorem basedCuspCWMeridian_inverseTransport_matrix (b : TriangleRegularPoint)
    (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y) :
    (((latticeTransportHom π hπ h₀ h₁ b
      (Path.Homotopic.Quotient.mk (basedCuspCWMeridian b Y hY z)))⁻¹ : SL(4, ℤ)) :
        LatticeMatrix) = M₀ :=
  Meridians.basedCuspCWMeridian_inverseTransport_matrix P hgen₁ hgen₂ b Y hY z

/-- The positive elliptic meridians act by `A₁` and `A₂` on the
singular homology of one common constructed regular fibre. -/
theorem basedEllipticCCWMeridian_singularH1 (b : TriangleRegularPoint) (j : Elliptic.Kind)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (a : SingularH1 (Fibre π hπ h₀ h₁ (triangleRegularProject b))) :
    fibreSingularH1Equiv π hπ h₀ h₁ b
      (inducedHomology
        (pathTransport π hπ h₀ h₁ (basedEllipticCCWMeridian b j r hr hr1) :
          C(Fibre π hπ h₀ h₁ (triangleRegularProject b),
            Fibre π hπ h₀ h₁ (triangleRegularProject b))) a) =
      j.matrix *ᵥ fibreSingularH1Equiv π hπ h₀ h₁ b a :=
  Meridians.basedEllipticCCWMeridian_singularH1 P hgen₁ hgen₂ b j r hr hr1 a

/-- The positive cusp meridian acts by `M₀` on that same singular homology. -/
theorem basedCuspCCWMeridian_singularH1 (b : TriangleRegularPoint) (Y : ℝ)
    (hY : width ≤ Y) (z : horodisc Y)
    (a : SingularH1 (Fibre π hπ h₀ h₁ (triangleRegularProject b))) :
    fibreSingularH1Equiv π hπ h₀ h₁ b
      (inducedHomology
        (pathTransport π hπ h₀ h₁ (basedCuspCCWMeridian b Y hY z) :
          C(Fibre π hπ h₀ h₁ (triangleRegularProject b),
            Fibre π hπ h₀ h₁ (triangleRegularProject b))) a) =
      M₀ *ᵥ fibreSingularH1Equiv π hπ h₀ h₁ b a :=
  Meridians.basedCuspCCWMeridian_singularH1 P hgen₁ hgen₂ b Y hY z a

/-- The source's clockwise inverse-transport convention gives `A₁`
and `A₂` on the actual singular homology of one common regular fibre. -/
theorem basedEllipticCWMeridian_inverseTransport_singularH1 (b : TriangleRegularPoint)
    (j : Elliptic.Kind) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (a : SingularH1 (Fibre π hπ h₀ h₁ (triangleRegularProject b))) :
    fibreSingularH1Equiv π hπ h₀ h₁ b
      (inducedHomology
        ((pathTransport π hπ h₀ h₁ (basedEllipticCWMeridian b j r hr hr1)).symm :
          C(Fibre π hπ h₀ h₁ (triangleRegularProject b),
            Fibre π hπ h₀ h₁ (triangleRegularProject b))) a) =
      j.matrix *ᵥ fibreSingularH1Equiv π hπ h₀ h₁ b a :=
  Meridians.basedEllipticCWMeridian_inverseTransport_singularH1 P hgen₁ hgen₂
    b j r hr hr1 a

/-- The source's clockwise cusp matrix `M₀` acts on that same actual
fibre homology under inverse transport. -/
theorem basedCuspCWMeridian_inverseTransport_singularH1 (b : TriangleRegularPoint)
    (Y : ℝ) (hY : width ≤ Y) (z : horodisc Y)
    (a : SingularH1 (Fibre π hπ h₀ h₁ (triangleRegularProject b))) :
    fibreSingularH1Equiv π hπ h₀ h₁ b
      (inducedHomology
        ((pathTransport π hπ h₀ h₁ (basedCuspCWMeridian b Y hY z)).symm :
          C(Fibre π hπ h₀ h₁ (triangleRegularProject b),
            Fibre π hπ h₀ h₁ (triangleRegularProject b))) a) =
      M₀ *ᵥ fibreSingularH1Equiv π hπ h₀ h₁ b a :=
  Meridians.basedCuspCWMeridian_inverseTransport_singularH1 P hgen₁ hgen₂ b Y hY z a

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians.OfSphere
