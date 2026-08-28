import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticNative
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticGamma
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticProduct
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticCapProduct
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionEllipticBasic

/-!
# Full product coordinates on the original elliptic fillings

The primitive main twist gives an explicit homeomorphism from the entire
original elliptic filling to the original open unit disc times its actual
central surface.  Its second coordinate is exactly the existing radial
retraction.  On the actual overlap boundary, this product is the previously
proved central-surface/circle product, with its circle sent to the specified
root-radius circle in the disc.

The disc coordinate is fixed by the native real-time vertical flow.  These
are exact topological formulas on the original spaces.  They do not assert
smoothness of the product coordinates or identify either factor with a ball.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticFullProduct

open Elliptic SpecialPeriods EllipticModel EllipticNative EllipticGamma
open ThreefoldOverlapMappingTorus
open ThreefoldOverlapMappingTorus.Elliptic (affine_pow_order)

variable {j : Kind} (D : Elliptic.Equivariant.Data j)

/-- The native normalized coordinate has the exact sector type used by the product model. -/
theorem normalizedGamma_sector (j : Kind) (x : RealTorus₄) :
    normalizedGamma j (flatTorusAffine j j.twist x) = normalizedGamma j x + sector j.order :=
  normalizedGamma_flatTorusAffine j x

/-- The full native filling is an explicit product with its actual central surface. -/
def fillingProductHomeomorph :
    D.Space j.twist (mainTwist_admissible j) ≃ₜ
      Disc × Surface j D.centralPeriod j.twist (mainTwist_admissible j) :=
  (capHomeomorph D j.twist (mainTwist_admissible j)).trans
    ((capProductHomeomorph j.order (flatTorusAffine j j.twist)
      (affine_pow_order j j.twist j.matrix_fixes_twist)
      (normalizedGamma j) (normalizedGamma_sector j)).trans
        ((Homeomorph.refl Disc).prodCongr
          (fibreSurfaceHomeomorph j D.centralPeriod j.twist (mainTwist_admissible j))))

/-- The forward formula on every original quotient representative. -/
@[simp] theorem fillingProductHomeomorph_quotient (s : Disc) (x : RealTorus₄) :
    fillingProductHomeomorph D (D.quotient j.twist (mainTwist_admissible j) (s, x)) =
      (rotate (normalizedGamma j x) s,
        surfaceProjection j D.centralPeriod j.twist (mainTwist_admissible j)
          (flatTorusPeriodHomeomorph D.centralPeriod.val x)) := by
  unfold fillingProductHomeomorph
  rw [Homeomorph.trans_apply, Homeomorph.trans_apply, capHomeomorph_quotient,
    capProductHomeomorph_project]
  change (rotate (normalizedGamma j x) s,
    fibreSurfaceHomeomorph j D.centralPeriod j.twist (mainTwist_admissible j)
      (fibreProject j.order (flatTorusAffine j j.twist)
        (affine_pow_order j j.twist j.matrix_fixes_twist) x)) = _
  rw [fibreSurfaceHomeomorph_project]

/-- The inverse needs no choice of a circle argument and returns the original representative. -/
theorem fillingProductHomeomorph_symm_surfaceProjection (s : Disc) (x : RealTorus₄) :
    (fillingProductHomeomorph D).symm
      (s, surfaceProjection j D.centralPeriod j.twist (mainTwist_admissible j)
        (flatTorusPeriodHomeomorph D.centralPeriod.val x)) =
      D.quotient j.twist (mainTwist_admissible j) (rotate (-normalizedGamma j x) s, x) := by
  apply (fillingProductHomeomorph D).injective
  rw [Homeomorph.apply_symm_apply, fillingProductHomeomorph_quotient, rotate_rotate_neg]

/-- The product preserves the literal root radius on every original representative. -/
theorem fillingProductHomeomorph_quotient_norm (s : Disc) (x : RealTorus₄) :
    ‖((fillingProductHomeomorph D
      (D.quotient j.twist (mainTwist_admissible j) (s, x))).1 : ℂ)‖ = ‖(s : ℂ)‖ := by
  rw [fillingProductHomeomorph_quotient, rotate_norm]

/-- On the whole native filling the original radial retraction forgets only the disc coordinate. -/
theorem fillingSurfaceRetraction_quotient (v : Lattice) (hv : AdmissibleTwist j v)
    (s : Disc) (x : RealTorus₄) :
    D.fillingSurfaceRetraction v hv (D.quotient v hv (s, x)) =
      surfaceProjection j D.centralPeriod v hv
        (flatTorusPeriodHomeomorph D.centralPeriod.val x) := by
  obtain ⟨u, rfl⟩ := standardLattice.mkQ_surjective x
  rw [flatTorusPeriodHomeomorph_mkQ]
  apply D.centralFibreInclusion_injective v hv
  rw [ThreefoldOverlapMappingTorus.Elliptic.centralInclusion_surfaceRetraction,
    D.fillingRadial_quotient, discRadial_one,
    D.centralFibreInclusion_surfaceProjection, D.centralInclusion_flatProjection]
  rfl

/-- The second product coordinate is the literal existing filling retraction. -/
theorem fillingProductHomeomorph_snd (y : D.Space j.twist (mainTwist_admissible j)) :
    (fillingProductHomeomorph D y).2 =
      D.fillingSurfaceRetraction j.twist (mainTwist_admissible j) y := by
  obtain ⟨⟨s, x⟩, rfl⟩ := D.quotient_surjective j.twist (mainTwist_admissible j) y
  rw [fillingProductHomeomorph_quotient, fillingSurfaceRetraction_quotient]

/-- Equality of the actual continuous maps, not only of induced homology maps. -/
theorem fillingProductHomeomorph_snd_comp :
    (ContinuousMap.snd : C(Disc × Surface j D.centralPeriod j.twist
      (mainTwist_admissible j), Surface j D.centralPeriod j.twist (mainTwist_admissible j))).comp
        (fillingProductHomeomorph D : C(_, _)) =
      D.fillingSurfaceRetraction j.twist (mainTwist_admissible j) := by
  ext y
  exact fillingProductHomeomorph_snd D y

/-- Every real time of the original vertical flow fixes the full product's disc coordinate. -/
theorem fillingProductHomeomorph_fst_flow_real (t : ℝ)
    (y : D.Space j.twist (mainTwist_admissible j)) :
    (fillingProductHomeomorph D
      (Threefold.VerticalAction.Elliptic.flow D j.twist (mainTwist_admissible j)
        (t : ℂ) y)).1 = (fillingProductHomeomorph D y).1 := by
  obtain ⟨⟨s, x⟩, rfl⟩ := D.quotient_surjective j.twist (mainTwist_admissible j) y
  rw [Threefold.VerticalAction.Elliptic.flow_quotient]
  change (fillingProductHomeomorph D (D.quotient j.twist (mainTwist_admissible j)
    (s, x + standardLattice.mkQ ((D.periods.periodEquiv s).symm
      (Threefold.VerticalAction.Period.vector (t : ℂ)))))).1 = _
  rw [fillingProductHomeomorph_quotient, fillingProductHomeomorph_quotient]
  exact congrArg (fun c => rotate c s) (normalizedGamma_periodFlow_real D.periods j t (s, x))

section SpecialBoundary

open Elliptic.HigherHomology
open SpecialPeriods.EllipticFilling
open ThreefoldOverlapMappingTorus.Elliptic
open TrianglePeriodFamily.GammaZero
open TrianglePeriodFamily.Boundary.EllipticCapProduct

/-- The primitive twist coordinate in the boundary model is the literal normalized γ circle. -/
theorem normalizedGamma_eq_split_fst (j : Kind) (x : RealTorus₄) :
    normalizedGamma j x = (splitFlatTorusHomeomorph j x).1 := by
  obtain ⟨u, rfl⟩ := standardLattice.mkQ_surjective x
  rw [normalizedGamma_apply, fibreGamma_mkQ, splitFlatTorusHomeomorph_mkQ]
  change j.twist 0 • (u 0 : AddCircle (1 : ℝ)) =
    (((j.twist 0 : ℝ) * u 0 : ℝ) : AddCircle (1 : ℝ))
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]

/-- Multiplication by the actual circle phase adds the literal positive root angle. -/
theorem rotate_root (n : ℕ) (r : ℝ) (a : Radius n r) (c t : AddCircle (1 : ℝ)) :
    rotate c (root n r a t) = root n r a (c + t) := by
  apply Subtype.ext
  change (phase c : ℂ) * ((a : ℝ) • (phase t : ℂ)) =
    (a : ℝ) • (phase (c + t) : ℂ)
  rw [phase_add, _root_.Circle.coe_mul, Complex.real_smul, Complex.real_smul]
  ring

/-- The boundary's full-filling codomain retains the exact original quotient point. -/
theorem specialBoundaryToFullFilling_mk (j : Kind) (t : ℝ) (x : RealTorus₄) :
    specialBoundaryToFullFilling j
      (MappingTorus.mk (flatTorusAffine j j.twist) (t, x)) =
      (specialLocalData j).quotient j.twist (mainTwist_admissible j)
        (root j.order (Threefold.specialBaseCover.radius (some j)) (specialRootRadius j)
          ((t / j.order : ℝ) : AddCircle (1 : ℝ)), x) :=
  specialBoundaryInclusion_mk j t x

/-- The full product of the original special-period elliptic filling. -/
def specialFillingProductHomeomorph (j : Kind) :
    SpecialFullFilling j ≃ₜ Disc × BoundaryCentralSurface j :=
  fillingProductHomeomorph (specialLocalData j)

/-- Exact compatibility with the original boundary product, including its native angle. -/
theorem specialFillingProductHomeomorph_boundary (j : Kind) (q : SpecialBoundary j) :
    specialFillingProductHomeomorph j (specialBoundaryToFullFilling j q) =
      (root j.order (Threefold.specialBaseCover.radius (some j)) (specialRootRadius j)
        (boundaryProductHomeomorph j q).2, (boundaryProductHomeomorph j q).1) := by
  obtain ⟨⟨t, x⟩, rfl⟩ := MappingTorus.mk_surjective (flatTorusAffine j j.twist) q
  rw [specialBoundaryToFullFilling_mk]
  change fillingProductHomeomorph (specialLocalData j) _ = _
  rw [fillingProductHomeomorph_quotient, normalizedGamma_eq_split_fst, rotate_root,
    boundaryProductHomeomorph_mk, specialBoundaryToCentral_mk]

/-- The boundary disc coordinate is precisely its specified root radius times
the phase of the previously defined native boundary circle coordinate. -/
theorem specialFillingProductHomeomorph_boundary_disc_val (j : Kind) (q : SpecialBoundary j) :
    ((specialFillingProductHomeomorph j (specialBoundaryToFullFilling j q)).1 : ℂ) =
      ((specialRootRadius j : ℝ) : ℂ) * (phase (boundaryCircleCoordinate j q) : ℂ) := by
  rw [specialFillingProductHomeomorph_boundary]
  exact Complex.real_smul

end SpecialBoundary

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticFullProduct
