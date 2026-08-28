import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyCore

/-!
# The native elliptic boundary gauge interpolation is an isotopy

Every slice is the literal translation by the difference of the original
real logarithmic gauge and the actual linear gauge.  Its negative-time
inverse is explicit.  Composing with the original regular-family boundary
map gives exactly the already proved gauge interpolation, not just another
homotopy or an equality of homology maps.
-/

noncomputable section

open scoped ContinuousMap Matrix

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy

open Elliptic MappingTorus
open TrianglePeriodFamily.Boundary
open TrianglePeriodFamily.Boundary.EllipticGaugeLinearization
open ThreefoldOverlapMappingTorus.Elliptic

/-- The full real discrepancy, retaining the native logarithm and every original period column. -/
def correction (j : Kind) (τ : ℝ) : C(ℝ, RealCoordinates) :=
  linearGauge j j.twist - nativeGaugeRealLift j τ

@[simp] theorem correction_apply (j : Kind) (τ t : ℝ) :
    correction j τ t = linearGauge j j.twist t - nativeGaugeRealLift j τ t := rfl

/-- The affine errors cancel as actual real vectors. -/
theorem correction_forward (j : Kind) (τ t : ℝ) :
    flatLinear j (correction j τ (t + 1)) = correction j τ t := by
  rw [correction_apply, map_sub, linearGauge_forward j j.twist j.matrix_fixes_twist,
    nativeGaugeRealLift_forward, correction_apply]
  abel

/-- The original linear monodromy has its genuine finite order on the real vector space. -/
theorem flatLinear_iterate_order (j : Kind) (x : RealCoordinates) :
    (flatLinear j : RealCoordinates → RealCoordinates)^[j.order] x = x := by
  have hz : Elliptic.realCast (0 : Lattice) = (0 : RealCoordinates) := by
    ext i
    change ((0 : ℤ) : ℝ) = 0
    exact Int.cast_zero
  have h : flatAffine j (0 : Lattice) = (flatLinear j : RealCoordinates → RealCoordinates) := by
    funext y
    simp only [flatAffine, hz, smul_zero, add_zero]
  simpa only [h, hz, add_zero] using
    flatAffine_iterate_order j (0 : Lattice) (by simp) x

/-- Iterating the homogeneous recurrence does not introduce an integral error. -/
theorem homogeneous_iterate (j : Kind) (h : ℝ → RealCoordinates)
    (hh : ∀ t, flatLinear j (h (t + 1)) = h t) (n : ℕ) (t : ℝ) :
    (flatLinear j : RealCoordinates → RealCoordinates)^[n] (h (t + n)) = h t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, Function.iterate_succ_apply, ← add_assoc, hh]
    exact ih

/-- The angular correction is genuinely periodic with the original elliptic order. -/
theorem correction_periodic (j : Kind) (τ : ℝ) :
    Function.Periodic (correction j τ) (j.order : ℝ) := by
  intro t
  have h := homogeneous_iterate j (correction j τ) (correction_forward j τ) j.order t
  rw [flatLinear_iterate_order] at h
  exact h

/-- The literal real-parameter boundary action on the original special mapping torus. -/
def nativeBoundaryTranslation (j : Kind) (τ s : ℝ) : C(SpecialBoundary j, SpecialBoundary j) :=
  boundaryTranslation j j.twist (correction j τ) (correction_forward j τ) s

@[simp] theorem nativeBoundaryTranslation_mk (j : Kind) (τ s t : ℝ) (x : RealTorus₄) :
    nativeBoundaryTranslation j τ s (mk (flatTorusAffine j j.twist) (t, x)) =
      mk (flatTorusAffine j j.twist) (t, x + standardLattice.mkQ (s • correction j τ t)) := rfl

/-- Every parameter gives a genuine homeomorphism with the negative-parameter inverse. -/
def nativeBoundaryHomeomorph (j : Kind) (τ s : ℝ) : SpecialBoundary j ≃ₜ SpecialBoundary j :=
  boundaryHomeomorph j j.twist (correction j τ) (correction_forward j τ) s

@[simp] theorem nativeBoundaryHomeomorph_apply (j : Kind) (τ s : ℝ) (x : SpecialBoundary j) :
    nativeBoundaryHomeomorph j τ s x = nativeBoundaryTranslation j τ s x := rfl

@[simp] theorem nativeBoundaryHomeomorph_symm_apply (j : Kind) (τ s : ℝ)
    (x : SpecialBoundary j) :
    (nativeBoundaryHomeomorph j τ s).symm x = nativeBoundaryTranslation j τ (-s) x := rfl

theorem nativeBoundaryTranslation_joint_continuous (j : Kind) (τ : ℝ) :
    Continuous (fun p : ℝ × SpecialBoundary j => nativeBoundaryTranslation j τ p.1 p.2) :=
  boundaryTranslation_joint_continuous j j.twist (correction j τ) (correction_forward j τ)

@[simp] theorem nativeBoundaryTranslation_zero (j : Kind) (τ : ℝ) (x : SpecialBoundary j) :
    nativeBoundaryTranslation j τ 0 x = x :=
  boundaryTranslation_zero j j.twist (correction j τ) (correction_forward j τ) x

theorem nativeBoundaryTranslation_add (j : Kind) (τ s r : ℝ) (x : SpecialBoundary j) :
    nativeBoundaryTranslation j τ (s + r) x =
      nativeBoundaryTranslation j τ s (nativeBoundaryTranslation j τ r x) :=
  boundaryTranslation_add j j.twist (correction j τ) (correction_forward j τ) s r x

theorem nativeBoundaryTranslation_base (j : Kind) (τ s : ℝ) (x : SpecialBoundary j) :
    base (flatTorusAffine j j.twist) (nativeBoundaryTranslation j τ s x) =
      base (flatTorusAffine j j.twist) x :=
  boundaryTranslation_base j j.twist (correction j τ) (correction_forward j τ) s x

/-- A jointly continuous isotopy from the identity, with the explicit slice inverses above. -/
def nativeBoundaryIsotopy (j : Kind) (τ : ℝ) :
    (ContinuousMap.id (SpecialBoundary j)).Homotopy (nativeBoundaryTranslation j τ 1) where
  toFun p := nativeBoundaryTranslation j τ p.1 p.2
  continuous_toFun := (nativeBoundaryTranslation_joint_continuous j τ).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  map_zero_left x := nativeBoundaryTranslation_zero j τ x
  map_one_left _ := rfl

@[simp] theorem nativeBoundaryIsotopy_apply (j : Kind) (τ : ℝ)
    (s : unitInterval) (x : SpecialBoundary j) :
    nativeBoundaryIsotopy j τ (s, x) = nativeBoundaryHomeomorph j τ s x := rfl

/-- The original interpolation equals postcomposition with this actual boundary isotopy. -/
theorem nativeGaugeInterpolation_eq (j : Kind) (τ : ℝ) (s : unitInterval)
    (x : SpecialBoundary j) :
    nativeRegularBoundaryMap j τ (nativeBoundaryTranslation j τ s x) =
      nativeRegularBoundaryGaugeLinearizationHomotopy j τ (s, x) := by
  obtain ⟨⟨t, u⟩, rfl⟩ := mk_surjective (flatTorusAffine j j.twist) x
  rw [nativeBoundaryTranslation_mk, nativeRegularBoundaryMap_realLift,
    nativeRegularBoundaryGaugeLinearizationHomotopy_mk, add_assoc, ← map_add]
  apply congrArg (fun z : RealCoordinates =>
    (TrianglePeriodFamily.regularData SpecialPeriods.specialPeriodMap
      SpecialPeriods.specialPeriodMap_generator₁
      SpecialPeriods.specialPeriodMap_generator₂).quotient
      (nativeShiftedBase j τ t, u + standardLattice.mkQ z))
  ext i
  simp only [correction_apply, linearGauge_apply, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- At time one the exact native boundary map becomes the exact linear-gauge map. -/
theorem nativeRegularBoundaryMap_comp_one (j : Kind) (τ : ℝ) :
    (nativeRegularBoundaryMap j τ).comp (nativeBoundaryTranslation j τ 1) =
      linearRegularBoundaryMap j τ := by
  ext x
  have h := nativeGaugeInterpolation_eq j τ (1 : unitInterval) x
  exact h.trans ((nativeRegularBoundaryGaugeLinearizationHomotopy j τ).apply_one x)

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
