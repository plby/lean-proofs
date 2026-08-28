import Wikipedia.HopfProblem.EllipticHigherHomologyCoverIndicesCore
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.ZMod.QuotientGroup

/-!
# The actual period-cover image in top homology

The genuine finite period cover acts on the top integral homology
coordinate by the actual fibre-homology norm after the circle boundary.
The boundary is onto and the top norm multiplies by the order.  Thus
the image has exactly that index and its actual cokernel is the cyclic
residue module, both in coordinates and in the native surface homology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology

/-- The actual top-degree covering map is the top fibre norm after
the actual circle-boundary map on the split period torus. -/
theorem surfacePeriodCoverH4Coordinates_eq_norm (j : Kind) (p : FixedPeriod j) :
    surfacePeriodCoverH4Coordinates j p =
      (fibreHomologyNormThreeCoordinate j).comp (surfacePeriodCoverCircleBoundary j p 3) := by
  ext a
  change mappingTorusH4Equiv j
    (surfaceMappingTorusHomologyEquiv j p 4
      (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 4 a)) =
    torusH3Coordinates (fibreHomologyNorm j 3 (surfacePeriodCoverCircleBoundary j p 3 a))
  rw [mappingTorusH4Equiv_boundary, surfacePeriodCover_wangBoundary]

/-- In the positive top coordinate the multiplier is the actual finite
covering order. -/
theorem surfacePeriodCoverH4Coordinates_apply (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology p.val.Torus 4) :
    surfacePeriodCoverH4Coordinates j p a =
      (j.order : ℤ) * torusH3Coordinates (surfacePeriodCoverCircleBoundary j p 3 a) := by
  rw [surfacePeriodCoverH4Coordinates_eq_norm, LinearMap.comp_apply,
    fibreHomologyNormThreeCoordinate_apply]

/-- Every multiple of the order occurs, since the circle boundary is
surjective; no smaller image is merely assumed. -/
theorem surfacePeriodCoverH4Coordinates_range (j : Kind) (p : FixedPeriod j) :
    LinearMap.range (surfacePeriodCoverH4Coordinates j p) =
      Submodule.span ℤ {(j.order : ℤ)} := by
  rw [surfacePeriodCoverH4Coordinates_eq_norm,
    LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (surfacePeriodCoverCircleBoundary_surjective j p 3)),
    fibreHomologyNormThreeCoordinate_range]

theorem surfacePeriodCoverH4Coordinates_range_iff (j : Kind) (p : FixedPeriod j) (z : ℤ) :
    z ∈ LinearMap.range (surfacePeriodCoverH4Coordinates j p) ↔ (j.order : ℤ) ∣ z := by
  rw [surfacePeriodCoverH4Coordinates_range, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa [smul_eq_mul, mul_comm] using ha.symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa [smul_eq_mul, mul_comm] using ha.symm⟩

/-- The image of the actual top covering map has index three or four,
according to the actual elliptic order. -/
theorem surfacePeriodCoverH4Coordinates_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (surfacePeriodCoverH4Coordinates j p)).toAddSubgroup.index = j.order := by
  rw [surfacePeriodCoverH4Coordinates_range, int_span_singleton_index]
  simp

theorem surfacePeriodCoverH4Coordinates_range_finiteIndex (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (surfacePeriodCoverH4Coordinates j p)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [surfacePeriodCoverH4Coordinates_range_index]
  exact j.order_pos.ne'

private def topCoverResidue (d : ℕ) : ℤ →ₗ[ℤ] ZMod d :=
  (Int.castAddHom (ZMod d)).toIntLinearMap

private theorem topCoverResidue_surjective (d : ℕ) :
    Function.Surjective (topCoverResidue d) := by
  intro z
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  exact ⟨k, rfl⟩

private theorem topCoverResidue_ker (d : ℕ) :
    LinearMap.ker (topCoverResidue d) = Submodule.span ℤ {(d : ℤ)} := by
  ext z
  rw [LinearMap.mem_ker]
  change (z : ZMod d) = 0 ↔ z ∈ Submodule.span ℤ {(d : ℤ)}
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa [smul_eq_mul, mul_comm] using ha.symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa [smul_eq_mul, mul_comm] using ha.symm⟩

/-- The actual coordinate cokernel is reduction modulo the finite
covering order. -/
def surfacePeriodCoverH4CoordinatesCokernelEquivZMod (j : Kind) (p : FixedPeriod j) :
    (ℤ ⧸ LinearMap.range (surfacePeriodCoverH4Coordinates j p)) ≃ₗ[ℤ] ZMod j.order :=
  (Submodule.quotEquivOfEq _ _
    ((surfacePeriodCoverH4Coordinates_range j p).trans (topCoverResidue_ker j.order).symm)).trans
      ((topCoverResidue j.order).quotKerEquivOfSurjective (topCoverResidue_surjective j.order))

@[simp] theorem surfacePeriodCoverH4CoordinatesCokernelEquivZMod_apply_mk
    (j : Kind) (p : FixedPeriod j) (z : ℤ) :
    surfacePeriodCoverH4CoordinatesCokernelEquivZMod j p (Submodule.Quotient.mk z) =
      (z : ZMod j.order) := rfl

@[simp] theorem surfacePeriodCoverH4CoordinatesCokernelEquivZMod_symm_apply_intCast
    (j : Kind) (p : FixedPeriod j) (z : ℤ) :
    (surfacePeriodCoverH4CoordinatesCokernelEquivZMod j p).symm (z : ZMod j.order) =
      Submodule.Quotient.mk z := by
  apply (surfacePeriodCoverH4CoordinatesCokernelEquivZMod j p).injective
  rw [LinearEquiv.apply_symm_apply, surfacePeriodCoverH4CoordinatesCokernelEquivZMod_apply_mk]

/-- The quotient of the native actual surface homology by the image of
the genuine period cover is the same cyclic residue module. -/
def surfacePeriodCoverH4CokernelEquivZMod (j : Kind) (p : FixedPeriod j) :
    (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 4 ⧸
      LinearMap.range (singularHomologyMap
        (periodCover j p j.twist (mainTwist_admissible j)) 4)) ≃ₗ[ℤ] ZMod j.order :=
  (coverCokernelCoordinatesEquiv
    (singularHomologyMap (periodCover j p j.twist (mainTwist_admissible j)) 4)
    (surfaceH4Equiv j p)).trans (surfacePeriodCoverH4CoordinatesCokernelEquivZMod j p)

@[simp] theorem surfacePeriodCoverH4CokernelEquivZMod_apply_mk
    (j : Kind) (p : FixedPeriod j)
    (a : SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 4) :
    surfacePeriodCoverH4CokernelEquivZMod j p (Submodule.Quotient.mk a) =
      (surfaceH4Equiv j p a : ZMod j.order) := rfl

@[simp] theorem surfacePeriodCoverH4CokernelEquivZMod_symm_apply_intCast
    (j : Kind) (p : FixedPeriod j) (z : ℤ) :
    (surfacePeriodCoverH4CokernelEquivZMod j p).symm (z : ZMod j.order) =
      Submodule.Quotient.mk ((surfaceH4Equiv j p).symm z) := by
  apply (surfacePeriodCoverH4CokernelEquivZMod j p).injective
  rw [LinearEquiv.apply_symm_apply, surfacePeriodCoverH4CokernelEquivZMod_apply_mk,
    LinearEquiv.apply_symm_apply]

/-- The same exact index is computed in native actual singular homology,
not merely in an abstract replacement lattice. -/
theorem surfacePeriodCover_h4_range_index (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (singularHomologyMap
      (periodCover j p j.twist (mainTwist_admissible j)) 4)).toAddSubgroup.index = j.order := by
  change Nat.card (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) 4 ⧸
    LinearMap.range (singularHomologyMap
      (periodCover j p j.twist (mainTwist_admissible j)) 4)) = j.order
  calc
    _ = Nat.card (ZMod j.order) :=
      Nat.card_congr (surfacePeriodCoverH4CokernelEquivZMod j p).toEquiv
    _ = j.order := Nat.card_zmod j.order

theorem surfacePeriodCover_h4_range_finiteIndex (j : Kind) (p : FixedPeriod j) :
    (LinearMap.range (singularHomologyMap
      (periodCover j p j.twist (mainTwist_admissible j)) 4)).toAddSubgroup.FiniteIndex := by
  refine ⟨?_⟩
  rw [surfacePeriodCover_h4_range_index]
  exact j.order_pos.ne'

end Wikipedia.HopfProblem.Elliptic.HigherHomology
