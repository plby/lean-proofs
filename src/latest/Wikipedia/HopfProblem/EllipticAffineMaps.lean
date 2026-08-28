import Wikipedia.HopfProblem.EllipticPeriodCoordinates
import Wikipedia.HopfProblem.EllipticArithmetic
import Wikipedia.HopfProblem.EllipticLinearMonodromy

/-!
# Holomorphic affine maps on the elliptic period tori

Translations and the fixed-period monodromy act on the actual quotient
complex tori.  The resulting affine biholomorphisms lift to the real
coordinate maps used in the exact freeness criterion.
-/

noncomputable section

open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic

/-- Translation on a period torus is a genuine biholomorphism. -/
def torusTranslation (p : PeriodDomain) (a : p.Torus) :
    Diffeomorph (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ ComplexPlane₂) p.Torus p.Torus ω where
  toFun x := x + a
  invFun x := x - a
  left_inv x := add_sub_cancel_right x a
  right_inv x := sub_add_cancel x a
  contMDiff_toFun := contMDiff_id.add contMDiff_const
  contMDiff_invFun := contMDiff_id.sub contMDiff_const

@[simp] theorem torusTranslation_apply (p : PeriodDomain) (a x : p.Torus) :
    torusTranslation p a x = x + a := rfl

/-- The logarithmic twist on the actual complex period torus. -/
def affineBiholomorph (j : Kind) (p : FixedPeriod j) (v : Lattice) :
    Diffeomorph (modelWithCornersSelf ℂ ComplexPlane₂)
      (modelWithCornersSelf ℂ ComplexPlane₂) p.val.Torus p.val.Torus ω :=
  (linearBiholomorph j p).trans
    (torusTranslation p.val (flatProjection p.val ((1 / (j.order : ℝ)) • realCast v)))

theorem affineBiholomorph_apply (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (x : p.val.Torus) :
    affineBiholomorph j p v x = linearBiholomorph j p x +
      flatProjection p.val ((1 / (j.order : ℝ)) • realCast v) := rfl

/-- The holomorphic affine map has exactly the prescribed real lift. -/
theorem affineBiholomorph_flatProjection (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (x : RealCoordinates) :
    affineBiholomorph j p v (flatProjection p.val x) =
      flatProjection p.val (flatAffine j v x) := by
  rw [affineBiholomorph_apply, linearBiholomorph_flatProjection, flatAffine,
    flatProjection_add]

theorem affineBiholomorph_iterate_flatProjection (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (r : ℕ) (x : RealCoordinates) :
    (affineBiholomorph j p v)^[r] (flatProjection p.val x) =
      flatProjection p.val ((flatAffine j v)^[r] x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      affineBiholomorph_flatProjection]

/-- The underlying permutation, used to construct the finite cyclic action. -/
def affinePermutation (j : Kind) (p : FixedPeriod j) (v : Lattice) :
    Equiv.Perm p.val.Torus := (affineBiholomorph j p v).toEquiv

theorem affinePermutation_pow_flatProjection (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (r : ℕ) (x : RealCoordinates) :
    (affinePermutation j p v ^ r) (flatProjection p.val x) =
      flatProjection p.val ((flatAffine j v)^[r] x) := by
  rw [Equiv.Perm.coe_pow]
  exact affineBiholomorph_iterate_flatProjection j p v r x

/-- Invariance of the integral twist makes the `m`-th power the identity. -/
theorem affinePermutation_pow_order (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) : affinePermutation j p v ^ j.order = 1 := by
  apply Equiv.ext
  intro y
  obtain ⟨x, rfl⟩ := flatProjection_surjective p.val y
  change (affinePermutation j p v ^ j.order) (flatProjection p.val x) =
    flatProjection p.val x
  rw [affinePermutation_pow_flatProjection]
  exact (flatProjection_eq_iff p.val _ _).mpr
    (flatAffine_iterate_order_congruent j v hv x)

/-- Admissible twists have no fixed points for any nonidentity power on
the actual complex torus. -/
theorem affinePermutation_pow_ne (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : AdmissibleTwist j v) (r : ℕ) (hr : 0 < r) (hrm : r < j.order)
    (y : p.val.Torus) : (affinePermutation j p v ^ r) y ≠ y := by
  obtain ⟨x, rfl⟩ := flatProjection_surjective p.val y
  rw [affinePermutation_pow_flatProjection]
  exact fun h => flatAffine_iterate_not_congruent j v hv r hr hrm x
    ((flatProjection_eq_iff p.val _ _).mp h)

/-- The source's admissibility criterion is exact for the actual torus,
not merely sufficient for the chosen twists. -/
theorem affinePermutation_free_iff (j : Kind) (p : FixedPeriod j) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) :
    (∀ r, 0 < r → r < j.order → ∀ y : p.val.Torus,
      (affinePermutation j p v ^ r) y ≠ y) ↔ AdmissibleTwist j v := by
  constructor
  · intro h
    apply (flatAffine_free_iff j v hv).mp
    intro r hr hrm x hx
    apply h r hr hrm (flatProjection p.val x)
    rw [affinePermutation_pow_flatProjection]
    exact (flatProjection_eq_iff p.val _ _).mpr hx
  · intro ha
    exact affinePermutation_pow_ne j p v ha

/-- Both twists chosen in §5 give finite free affine biholomorphisms. -/
theorem mainAffine_finite_free (j : Kind) (p : FixedPeriod j) :
    affinePermutation j p j.twist ^ j.order = 1 ∧
      ∀ r, 0 < r → r < j.order → ∀ y : p.val.Torus,
        (affinePermutation j p j.twist ^ r) y ≠ y :=
  ⟨affinePermutation_pow_order j p j.twist j.matrix_fixes_twist,
    affinePermutation_pow_ne j p j.twist (mainTwist_admissible j)⟩

end Wikipedia.HopfProblem.Elliptic
