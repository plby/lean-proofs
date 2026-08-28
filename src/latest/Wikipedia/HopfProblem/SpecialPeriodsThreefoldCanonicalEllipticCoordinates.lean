import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalEllipticCompatibility
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackLocal
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPatchCharts

/-!
# Exact local volume factors on the actual elliptic patches

Canonical pullback multiplies local volume by the determinant of the
genuine chart derivative; its inverse uses the inverse determinant.
For the actual glued chart coming from the same native elliptic chart,
the derivative is identity and the two local volume frames agree exactly.
Both the small piece and the full-filling parametrization retain their
original atlases throughout.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Elliptic

open Wikipedia.HopfProblem.Elliptic EllipticFilling TrianglePeriodFamily.Canonical

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] specialFullFillingChartedSpace specialEllipticPieceChartedSpace
  Threefold.chartedSpace

local instance fullCoordinateManifold (j : Kind) :
    IsManifold IF ω (SpecialFullFilling j) := (specialFullFilling_construction j).2.2.1

local instance pieceCoordinateManifold (j : Kind) :
    IsManifold IF ω (SpecialEllipticPiece j) := specialEllipticPiece_isManifold j

local instance globalCoordinateManifold : IsManifold IF ω Threefold.Space :=
  Threefold.space_isManifold

/-- Determinant of the actual native-to-global coordinate expression. -/
def patchJacobian (j : Kind) (i : atlas Model (SpecialEllipticPiece j))
    (k : atlas Model Threefold.Space) (x : SpecialEllipticPiece j) : ℂ :=
  Pullback.chartDeterminant (EllipticGeometry.inclusion j) i k x

theorem patchJacobian_eq_fderiv (j : Kind) (i : atlas Model (SpecialEllipticPiece j))
    (k : atlas Model Threefold.Space) (x : SpecialEllipticPiece j) :
    patchJacobian j i k x = LinearMap.det
      (fderiv ℂ (k.val ∘ EllipticGeometry.inclusion j ∘ i.val.symm) (i.val x)).toLinearMap :=
  rfl

theorem patchJacobian_ne_zero (j : Kind) (i : atlas Model (SpecialEllipticPiece j))
    (k : atlas Model Threefold.Space) {x : SpecialEllipticPiece j}
    (hi : x ∈ i.val.source) (hk : EllipticGeometry.inclusion j x ∈ k.val.source) :
    patchJacobian j i k x ≠ 0 :=
  Pullback.chartDeterminant_ne_zero (EllipticGeometry.inclusion j) i k hi hk
    (EllipticGeometry.inclusion_isLocalDiffeomorph j x)

/-- The chart representation is pullback by the actual coordinate derivative. -/
theorem patchPullback_inCoordinates (j : Kind)
    (i : atlas Model (SpecialEllipticPiece j)) (k : atlas Model Threefold.Space)
    {x : SpecialEllipticPiece j} (hi : x ∈ i.val.source)
    (hk : EllipticGeometry.inclusion j x ∈ k.val.source)
    (v : Threefold.Canonical.bundle.Fiber (EllipticGeometry.inclusion j x)) :
    inCoordinates j i x (patchPullback j x v) =
      (Threefold.Canonical.inCoordinates k
        (EllipticGeometry.inclusion j x) v).compContinuousLinearMap
          (fderiv ℂ (k.val ∘ EllipticGeometry.inclusion j ∘ i.val.symm) (i.val x)) :=
  Pullback.inCoordinates_pullbackEquiv (EllipticGeometry.inclusion_isLocalDiffeomorph j)
    i k hi hk v

theorem patchPullback_localCoefficient (j : Kind)
    (i : atlas Model (SpecialEllipticPiece j)) (k : atlas Model Threefold.Space)
    {x : SpecialEllipticPiece j} (hi : x ∈ i.val.source)
    (hk : EllipticGeometry.inclusion j x ∈ k.val.source)
    (v : Threefold.Canonical.bundle.Fiber (EllipticGeometry.inclusion j x)) :
    ((bundle j).localTriv i ⟨x, patchPullback j x v⟩).2 =
      patchJacobian j i k x *
        (Threefold.Canonical.bundle.localTriv k ⟨EllipticGeometry.inclusion j x, v⟩).2 :=
  Pullback.pullbackEquiv_localCoefficient (EllipticGeometry.inclusion_isLocalDiffeomorph j)
    i k hi hk v

theorem patchPullback_symm_localCoefficient (j : Kind)
    (i : atlas Model (SpecialEllipticPiece j)) (k : atlas Model Threefold.Space)
    {x : SpecialEllipticPiece j} (hi : x ∈ i.val.source)
    (hk : EllipticGeometry.inclusion j x ∈ k.val.source) (v : (bundle j).Fiber x) :
    (Threefold.Canonical.bundle.localTriv k
      ⟨EllipticGeometry.inclusion j x, (patchPullback j x).symm v⟩).2 =
        (patchJacobian j i k x)⁻¹ * ((bundle j).localTriv i ⟨x, v⟩).2 :=
  Pullback.pullbackEquiv_symm_localCoefficient
    (EllipticGeometry.inclusion_isLocalDiffeomorph j) i k hi hk v

/-- Pullback of a genuine global local volume frame has the actual Jacobian factor. -/
theorem patchPullback_atlas_localFrame (j : Kind)
    (i : atlas Model (SpecialEllipticPiece j)) (k : atlas Model Threefold.Space)
    {x : SpecialEllipticPiece j} (hi : x ∈ i.val.source)
    (hk : EllipticGeometry.inclusion j x ∈ k.val.source) :
    patchPullback j x
        (Atlas.localFrame Threefold.Space k ⟨EllipticGeometry.inclusion j x, hk⟩) =
      patchJacobian j i k x • Atlas.localFrame (SpecialEllipticPiece j) i ⟨x, hi⟩ := by
  apply (coordinateEquiv j i hi).injective
  rw [map_smul]
  change Atlas.inCoordinates (SpecialEllipticPiece j) i x
      (Pullback.pullbackEquiv (EllipticGeometry.inclusion_isLocalDiffeomorph j) x _) =
    patchJacobian j i k x • Atlas.inCoordinates (SpecialEllipticPiece j) i x
      (Atlas.localFrame (SpecialEllipticPiece j) i ⟨x, hi⟩)
  rw [Pullback.inCoordinates_pullbackEquiv
    (EllipticGeometry.inclusion_isLocalDiffeomorph j) i k hi hk,
    Atlas.localFrame_inCoordinates Threefold.Space k ⟨EllipticGeometry.inclusion j x, hk⟩,
    Atlas.localFrame_inCoordinates (SpecialEllipticPiece j) i ⟨x, hi⟩, volume_pullback]
  rfl

/-- The inverse fibre comparison has the inverse actual Jacobian factor on local volumes. -/
theorem patchPullback_symm_atlas_localFrame (j : Kind)
    (i : atlas Model (SpecialEllipticPiece j)) (k : atlas Model Threefold.Space)
    {x : SpecialEllipticPiece j} (hi : x ∈ i.val.source)
    (hk : EllipticGeometry.inclusion j x ∈ k.val.source) :
    (patchPullback j x).symm (Atlas.localFrame (SpecialEllipticPiece j) i ⟨x, hi⟩) =
      (patchJacobian j i k x)⁻¹ •
        Atlas.localFrame Threefold.Space k ⟨EllipticGeometry.inclusion j x, hk⟩ := by
  apply (patchPullback j x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, map_smul,
    patchPullback_atlas_localFrame j i k hi hk, smul_smul,
    inv_mul_cancel₀ (patchJacobian_ne_zero j i k hi hk), one_smul]

/-- In the actual matching glued chart, the proved coordinate Jacobian is one. -/
theorem patchJacobian_native (j : Kind) (a x : SpecialEllipticPiece j)
    (hx : x ∈ (chartAt Model a).source) :
    patchJacobian j (achart Model a)
      (Threefold.Canonical.patchChart (some (some j)) a) x = 1 :=
  Threefold.Canonical.patchChart_inclusion_det (some (some j)) a
    ((chartAt Model a).map_source hx)

/-- The native elliptic volume frame is the exact pullback of its matching
global glued volume frame, with no unspecified scalar multiplier. -/
theorem patchPullback_native_localFrame (j : Kind) (a x : SpecialEllipticPiece j)
    (hx : x ∈ (chartAt Model a).source) :
    patchPullback j x (Threefold.Canonical.patchLocalFrame (some (some j)) a x hx) =
      localFrame j a ⟨x, hx⟩ := by
  have hk := Threefold.Canonical.inclusion_mem_patchChart_source (some (some j)) a x hx
  have h := patchPullback_atlas_localFrame j (achart Model a)
    (Threefold.Canonical.patchChart (some (some j)) a) hx hk
  rw [patchJacobian_native j a x hx, one_smul] at h
  exact h

theorem patchPullback_symm_native_localFrame (j : Kind) (a x : SpecialEllipticPiece j)
    (hx : x ∈ (chartAt Model a).source) :
    (patchPullback j x).symm (localFrame j a ⟨x, hx⟩) =
      Threefold.Canonical.patchLocalFrame (some (some j)) a x hx := by
  apply (patchPullback j x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, patchPullback_native_localFrame j a x hx]

/-- The actual full-filling coordinate Jacobian on its genuine source. -/
def fullPatchJacobian (j : Kind) (i : atlas Model (SpecialFullFilling j))
    (k : atlas Model Threefold.Space) (x : SpecialFullFilling j) : ℂ :=
  Pullback.chartDeterminant (EllipticGeometry.fullParametrization j) i k x

theorem fullPatchJacobian_eq_fderiv (j : Kind) (i : atlas Model (SpecialFullFilling j))
    (k : atlas Model Threefold.Space) (x : SpecialFullFilling j) :
    fullPatchJacobian j i k x = LinearMap.det
      (fderiv ℂ (k.val ∘ EllipticGeometry.fullParametrization j ∘ i.val.symm)
        (i.val x)).toLinearMap := rfl

theorem fullPatchJacobian_ne_zero (j : Kind) (i : atlas Model (SpecialFullFilling j))
    (k : atlas Model Threefold.Space) {x : SpecialFullFilling j}
    (hx : x ∈ (EllipticGeometry.fullParametrization j).source)
    (hi : x ∈ i.val.source) (hk : EllipticGeometry.fullParametrization j x ∈ k.val.source) :
    fullPatchJacobian j i k x ≠ 0 :=
  Pullback.chartDeterminant_ne_zero (EllipticGeometry.fullParametrization j) i k hi hk
    (EllipticGeometry.fullParametrization_isLocalDiffeomorphAt j hx)

theorem fullPatchPullback_inCoordinates (j : Kind)
    (i : atlas Model (SpecialFullFilling j)) (k : atlas Model Threefold.Space)
    {x : SpecialFullFilling j} (hx : x ∈ (EllipticGeometry.fullParametrization j).source)
    (hi : x ∈ i.val.source) (hk : EllipticGeometry.fullParametrization j x ∈ k.val.source)
    (v : Threefold.Canonical.bundle.Fiber (EllipticGeometry.fullParametrization j x)) :
    fullInCoordinates j i x (fullPatchPullback j x hx v) =
      (Threefold.Canonical.inCoordinates k
        (EllipticGeometry.fullParametrization j x) v).compContinuousLinearMap
          (fderiv ℂ (k.val ∘ EllipticGeometry.fullParametrization j ∘ i.val.symm) (i.val x)) :=
  Pullback.inCoordinates_pullbackLinear (EllipticGeometry.fullParametrization j) i k hi hk
    (IsLocalDiffeomorphAt.mdifferentiableAt
      (EllipticGeometry.fullParametrization_isLocalDiffeomorphAt j hx) (by simp)) v

theorem fullPatchPullback_localCoefficient (j : Kind)
    (i : atlas Model (SpecialFullFilling j)) (k : atlas Model Threefold.Space)
    {x : SpecialFullFilling j} (hx : x ∈ (EllipticGeometry.fullParametrization j).source)
    (hi : x ∈ i.val.source) (hk : EllipticGeometry.fullParametrization j x ∈ k.val.source)
    (v : Threefold.Canonical.bundle.Fiber (EllipticGeometry.fullParametrization j x)) :
    ((fullBundle j).localTriv i ⟨x, fullPatchPullback j x hx v⟩).2 =
      fullPatchJacobian j i k x *
        (Threefold.Canonical.bundle.localTriv k
          ⟨EllipticGeometry.fullParametrization j x, v⟩).2 :=
  Pullback.pullbackLinear_localCoefficient (EllipticGeometry.fullParametrization j) i k hi hk
    (IsLocalDiffeomorphAt.mdifferentiableAt
      (EllipticGeometry.fullParametrization_isLocalDiffeomorphAt j hx) (by simp)) v

theorem fullPatchPullback_symm_localCoefficient (j : Kind)
    (i : atlas Model (SpecialFullFilling j)) (k : atlas Model Threefold.Space)
    {x : SpecialFullFilling j} (hx : x ∈ (EllipticGeometry.fullParametrization j).source)
    (hi : x ∈ i.val.source) (hk : EllipticGeometry.fullParametrization j x ∈ k.val.source)
    (v : (fullBundle j).Fiber x) :
    (Threefold.Canonical.bundle.localTriv k
      ⟨EllipticGeometry.fullParametrization j x, (fullPatchPullback j x hx).symm v⟩).2 =
        (fullPatchJacobian j i k x)⁻¹ * ((fullBundle j).localTriv i ⟨x, v⟩).2 := by
  have h := fullPatchPullback_localCoefficient j i k hx hi hk
    ((fullPatchPullback j x hx).symm v)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  calc
    _ = (fullPatchJacobian j i k x)⁻¹ * (fullPatchJacobian j i k x *
        (Threefold.Canonical.bundle.localTriv k
          ⟨EllipticGeometry.fullParametrization j x, (fullPatchPullback j x hx).symm v⟩).2) := by
      rw [← mul_assoc, inv_mul_cancel₀ (fullPatchJacobian_ne_zero j i k hx hi hk), one_mul]
    _ = _ := congrArg (fun c : ℂ => (fullPatchJacobian j i k x)⁻¹ * c) h.symm

theorem fullPatchPullback_atlas_localFrame (j : Kind)
    (i : atlas Model (SpecialFullFilling j)) (k : atlas Model Threefold.Space)
    {x : SpecialFullFilling j} (hx : x ∈ (EllipticGeometry.fullParametrization j).source)
    (hi : x ∈ i.val.source) (hk : EllipticGeometry.fullParametrization j x ∈ k.val.source) :
    fullPatchPullback j x hx
        (Atlas.localFrame Threefold.Space k ⟨EllipticGeometry.fullParametrization j x, hk⟩) =
      fullPatchJacobian j i k x • Atlas.localFrame (SpecialFullFilling j) i ⟨x, hi⟩ := by
  apply (fullCoordinateEquiv j i hi).injective
  rw [map_smul]
  change Atlas.inCoordinates (SpecialFullFilling j) i x
      (Pullback.pullbackLinear (EllipticGeometry.fullParametrization j) x _) =
    fullPatchJacobian j i k x • Atlas.inCoordinates (SpecialFullFilling j) i x
      (Atlas.localFrame (SpecialFullFilling j) i ⟨x, hi⟩)
  rw [Pullback.inCoordinates_pullbackLinear (EllipticGeometry.fullParametrization j) i k hi hk
    (IsLocalDiffeomorphAt.mdifferentiableAt
      (EllipticGeometry.fullParametrization_isLocalDiffeomorphAt j hx) (by simp)),
    Atlas.localFrame_inCoordinates Threefold.Space k
      ⟨EllipticGeometry.fullParametrization j x, hk⟩,
    Atlas.localFrame_inCoordinates (SpecialFullFilling j) i ⟨x, hi⟩, volume_pullback]
  rfl

theorem fullPatchPullback_symm_atlas_localFrame (j : Kind)
    (i : atlas Model (SpecialFullFilling j)) (k : atlas Model Threefold.Space)
    {x : SpecialFullFilling j} (hx : x ∈ (EllipticGeometry.fullParametrization j).source)
    (hi : x ∈ i.val.source) (hk : EllipticGeometry.fullParametrization j x ∈ k.val.source) :
    (fullPatchPullback j x hx).symm (Atlas.localFrame (SpecialFullFilling j) i ⟨x, hi⟩) =
      (fullPatchJacobian j i k x)⁻¹ •
        Atlas.localFrame Threefold.Space k ⟨EllipticGeometry.fullParametrization j x, hk⟩ := by
  apply (fullPatchPullback j x hx).injective
  rw [ContinuousLinearEquiv.apply_symm_apply, map_smul,
    fullPatchPullback_atlas_localFrame j i k hx hi hk, smul_smul,
    inv_mul_cancel₀ (fullPatchJacobian_ne_zero j i k hx hi hk), one_smul]

/-- The original full-filling local volume is exactly the pullback of
its matching global frame, throughout the actual selected small piece. -/
theorem fullPatchPullback_native_localFrame (j : Kind) (a x : SpecialEllipticPiece j)
    (hx : x ∈ (chartAt Model a).source) :
    fullPatchPullback j x.val (piece_mem_fullParametrization_source j x)
        (Threefold.Canonical.patchLocalFrame (some (some j)) a x hx) =
      fullLocalFrame j a.val ⟨x.val, pieceInclusion_mem_chart_source j a x hx⟩ := by
  apply (restriction j x).injective
  exact (restriction_fullPatchPullback j x
    (Threefold.Canonical.patchLocalFrame (some (some j)) a x hx)).trans
      ((patchPullback_native_localFrame j a x hx).trans
        (restriction_native_localFrame j a x hx).symm)

theorem fullPatchPullback_symm_native_localFrame (j : Kind) (a x : SpecialEllipticPiece j)
    (hx : x ∈ (chartAt Model a).source) :
    (fullPatchPullback j x.val (piece_mem_fullParametrization_source j x)).symm
        (fullLocalFrame j a.val ⟨x.val, pieceInclusion_mem_chart_source j a x hx⟩) =
      Threefold.Canonical.patchLocalFrame (some (some j)) a x hx := by
  apply (fullPatchPullback j x.val (piece_mem_fullParametrization_source j x)).injective
  exact ((fullPatchPullback j x.val (piece_mem_fullParametrization_source j x)).apply_symm_apply
    (fullLocalFrame j a.val ⟨x.val, pieceInclusion_mem_chart_source j a x hx⟩)).trans
      (fullPatchPullback_native_localFrame j a x hx).symm

/-- The actual full-filling coordinate Jacobian in the matching global
patch chart equals one; this follows from the exact native volume comparison. -/
theorem fullPatchJacobian_native (j : Kind) (a x : SpecialEllipticPiece j)
    (hx : x ∈ (chartAt Model a).source) :
    fullPatchJacobian j (achart Model a.val)
      (Threefold.Canonical.patchChart (some (some j)) a) x.val = 1 := by
  have hi := pieceInclusion_mem_chart_source j a x hx
  have hk : EllipticGeometry.fullParametrization j x.val ∈
      (Threefold.Canonical.patchChart (some (some j)) a).val.source := by
    rw [EllipticGeometry.fullParametrization_apply]
    exact Threefold.Canonical.inclusion_mem_patchChart_source (some (some j)) a x hx
  have h := fullPatchPullback_atlas_localFrame j (achart Model a.val)
    (Threefold.Canonical.patchChart (some (some j)) a)
    (piece_mem_fullParametrization_source j x) hi hk
  have hframe : Atlas.localFrame Threefold.Space
      (Threefold.Canonical.patchChart (some (some j)) a)
      ⟨EllipticGeometry.fullParametrization j x.val, hk⟩ =
        Threefold.Canonical.patchLocalFrame (some (some j)) a x hx := by
    unfold Threefold.Canonical.patchLocalFrame
    congr 1
    apply Subtype.ext
    exact EllipticGeometry.fullParametrization_apply j x
  rw [hframe, fullPatchPullback_native_localFrame] at h
  apply smul_left_injective ℂ (fullLocalFrame_ne_zero j a.val ⟨x.val, hi⟩)
  simpa only [one_smul, fullLocalFrame] using h.symm

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Elliptic
