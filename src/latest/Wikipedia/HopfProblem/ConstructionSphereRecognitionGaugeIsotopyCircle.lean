import Wikipedia.HopfProblem.ConstructionSphereRecognitionGaugeIsotopyNative
import Wikipedia.HopfProblem.ThreefoldHomologyDeltaSweepFlat
import Wikipedia.HopfProblem.CuspBoundaryGammaZeroMappingTorus

/-!
# The original delta circle commutes with the native boundary isotopy

The fourth real period column is fixed by both original elliptic matrices.
Its genuine circle translation therefore descends to the original affine
mapping torus, leaving real time and the base-circle map unchanged.  The
resulting continuous circle action commutes pointwise with the literal
native gauge correction at every real isotopy parameter.
-/

noncomputable section

open scoped ContinuousMap Matrix

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy

open Elliptic MappingTorus
open TrianglePeriodFamily.Boundary
open ThreefoldOverlapMappingTorus.Elliptic
open SpecialPeriods.Threefold.Homology.DeltaSweep

local notation "Circle" => AddCircle (1 : ℝ)

/-- The unchanged fourth period column is fixed by each original real matrix. -/
theorem flatLinear_delta_real (j : Kind) :
    flatLinear j (Pi.basisFun ℝ (Fin 4) 3) = Pi.basisFun ℝ (Fin 4) 3 := by
  cases j <;> ext i <;> fin_cases i <;>
    simp [flatLinear, Kind.matrix, A₁, A₂, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Pi.basisFun_apply]

/-- The actual affine monodromy commutes with the original positive delta circle. -/
theorem flatTorusAffine_add_deltaCircle (j : Kind) (v : Lattice)
    (x : RealTorus₄) (d : Circle) :
    flatTorusAffine j v (x + deltaCircle d) =
      flatTorusAffine j v x + deltaCircle d := by
  obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective d
  rw [deltaCircle_real_apply, flatTorusAffine_add_mkQ, map_smul,
    flatLinear_delta_real]

/-- Literal delta translation on the original special affine mapping torus. -/
def boundaryDeltaTranslation (j : Kind) (d : Circle) :
    C(SpecialBoundary j, SpecialBoundary j) :=
  CuspBoundaryGammaZero.mappingTorusMap
    (flatTorusAffine j j.twist) (flatTorusAffine j j.twist)
    ⟨fun x => x + deltaCircle d, continuous_id.add continuous_const⟩
    (fun x => (flatTorusAffine_add_deltaCircle j j.twist x d).symm)

/-- Every cylinder representative retains its exact time and original fibre coordinates. -/
@[simp] theorem boundaryDeltaTranslation_mk (j : Kind) (d : Circle)
    (t : ℝ) (x : RealTorus₄) :
    boundaryDeltaTranslation j d (mk (flatTorusAffine j j.twist) (t, x)) =
      mk (flatTorusAffine j j.twist) (t, x + deltaCircle d) := rfl

/-- The actual base-circle projection is fixed pointwise. -/
theorem boundaryDeltaTranslation_base (j : Kind) (d : Circle) (x : SpecialBoundary j) :
    base (flatTorusAffine j j.twist) (boundaryDeltaTranslation j d x) =
      base (flatTorusAffine j j.twist) x := by
  obtain ⟨⟨t, u⟩, rfl⟩ := mk_surjective (flatTorusAffine j j.twist) x
  rfl

@[simp] theorem boundaryDeltaTranslation_zero (j : Kind) (x : SpecialBoundary j) :
    boundaryDeltaTranslation j 0 x = x := by
  obtain ⟨⟨t, u⟩, rfl⟩ := mk_surjective (flatTorusAffine j j.twist) x
  simp only [boundaryDeltaTranslation_mk, deltaCircle_zero, add_zero]

/-- Circle addition gives composition of the literal boundary translations. -/
theorem boundaryDeltaTranslation_add (j : Kind) (d e : Circle) (x : SpecialBoundary j) :
    boundaryDeltaTranslation j (d + e) x =
      boundaryDeltaTranslation j d (boundaryDeltaTranslation j e x) := by
  obtain ⟨⟨t, u⟩, rfl⟩ := mk_surjective (flatTorusAffine j j.twist) x
  simp only [boundaryDeltaTranslation_mk, deltaCircle_add]
  apply congrArg (fun y : RealTorus₄ => mk (flatTorusAffine j j.twist) (t, y))
  abel

/-- Joint continuity is proved through the original open cylinder quotient. -/
theorem boundaryDeltaTranslation_joint_continuous (j : Kind) :
    Continuous (fun p : Circle × SpecialBoundary j =>
      boundaryDeltaTranslation j p.1 p.2) := by
  apply (IsOpenQuotientMap.id.prodMap
    (Cylinder.projection_isOpenQuotientMap
      (flatTorusAffine j j.twist))).continuous_comp_iff.mp
  change Continuous (fun p : Circle × (ℝ × RealTorus₄) =>
    mk (flatTorusAffine j j.twist) (p.2.1, p.2.2 + deltaCircle p.1))
  exact (mk_continuous _).comp ((continuous_fst.comp continuous_snd).prodMk
    ((continuous_snd.comp continuous_snd).add (deltaCircle.continuous.comp continuous_fst)))

/-- The actual circle action, without installing an unrelated global instance. -/
@[instance_reducible] def boundaryDeltaAction (j : Kind) :
    AddAction Circle (SpecialBoundary j) where
  vadd d x := boundaryDeltaTranslation j d x
  zero_vadd := boundaryDeltaTranslation_zero j
  add_vadd := boundaryDeltaTranslation_add j

/-- The bundled action is jointly continuous in the unchanged quotient topology. -/
theorem boundaryDeltaAction_continuous (j : Kind) :
    let := boundaryDeltaAction j
    ContinuousVAdd Circle (SpecialBoundary j) := by
  let := boundaryDeltaAction j
  exact ⟨boundaryDeltaTranslation_joint_continuous j⟩

/-- Every circle element acts by a genuine homeomorphism with the negative-element inverse. -/
def boundaryDeltaHomeomorph (j : Kind) (d : Circle) :
    SpecialBoundary j ≃ₜ SpecialBoundary j where
  toFun := boundaryDeltaTranslation j d
  invFun := boundaryDeltaTranslation j (-d)
  left_inv x := by
    rw [← boundaryDeltaTranslation_add, neg_add_cancel, boundaryDeltaTranslation_zero]
  right_inv x := by
    rw [← boundaryDeltaTranslation_add, add_neg_cancel, boundaryDeltaTranslation_zero]
  continuous_toFun := (boundaryDeltaTranslation j d).continuous
  continuous_invFun := (boundaryDeltaTranslation j (-d)).continuous

@[simp] theorem boundaryDeltaHomeomorph_apply (j : Kind) (d : Circle)
    (x : SpecialBoundary j) :
    boundaryDeltaHomeomorph j d x = boundaryDeltaTranslation j d x := rfl

@[simp] theorem boundaryDeltaHomeomorph_symm_apply (j : Kind) (d : Circle)
    (x : SpecialBoundary j) :
    (boundaryDeltaHomeomorph j d).symm x = boundaryDeltaTranslation j (-d) x := rfl

/-- Any genuine homogeneous boundary translation commutes with the original delta circle. -/
theorem boundaryTranslation_delta (j : Kind) (h : C(ℝ, RealCoordinates))
    (hh : ∀ t, flatLinear j (h (t + 1)) = h t) (s : ℝ) (d : Circle)
    (x : SpecialBoundary j) :
    boundaryTranslation j j.twist h hh s (boundaryDeltaTranslation j d x) =
      boundaryDeltaTranslation j d (boundaryTranslation j j.twist h hh s x) := by
  obtain ⟨⟨t, u⟩, rfl⟩ := mk_surjective (flatTorusAffine j j.twist) x
  simp only [boundaryDeltaTranslation_mk, boundaryTranslation_mk]
  apply congrArg (fun y : RealTorus₄ => mk (flatTorusAffine j j.twist) (t, y))
  abel

/-- The actual native gauge isotopy is delta-equivariant at every real parameter. -/
theorem nativeBoundaryTranslation_delta (j : Kind) (τ s : ℝ) (d : Circle)
    (x : SpecialBoundary j) :
    nativeBoundaryTranslation j τ s (boundaryDeltaTranslation j d x) =
      boundaryDeltaTranslation j d (nativeBoundaryTranslation j τ s x) :=
  boundaryTranslation_delta j (correction j τ) (correction_forward j τ) s d x

/-- The same exact commutation for the native homeomorphism slices. -/
theorem nativeBoundaryHomeomorph_delta (j : Kind) (τ s : ℝ) (d : Circle)
    (x : SpecialBoundary j) :
    nativeBoundaryHomeomorph j τ s (boundaryDeltaTranslation j d x) =
      boundaryDeltaTranslation j d (nativeBoundaryHomeomorph j τ s x) :=
  nativeBoundaryTranslation_delta j τ s d x

/-- The original unit-interval isotopy retains that same circle action pointwise. -/
theorem nativeBoundaryIsotopy_delta (j : Kind) (τ : ℝ) (s : unitInterval) (d : Circle)
    (x : SpecialBoundary j) :
    nativeBoundaryIsotopy j τ (s, boundaryDeltaTranslation j d x) =
      boundaryDeltaTranslation j d (nativeBoundaryIsotopy j τ (s, x)) :=
  nativeBoundaryTranslation_delta j τ s d x

end Wikipedia.HopfProblem.ConstructionSphereRecognition.GaugeIsotopy
