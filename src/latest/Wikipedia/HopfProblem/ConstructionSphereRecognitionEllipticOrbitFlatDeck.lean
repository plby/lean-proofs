import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticOrbitFlat
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticOrbitFlatDeckMatrix
import Wikipedia.HopfProblem.ConstructionSphereRecognitionEllipticGamma

/-!
# The actual residual finite deck map on the delta-orbit three-torus

Forgetting precisely the original delta circle intertwines the native
four-dimensional affine elliptic action with its literal projected
affine map.  Its finite order descends from the original action.  The
retained gamma circle proves that every nonidentity iterate is free.
No further quotient is identified with a torus here.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbitFlat

open Elliptic PeriodTorusHigherHomology

local notation "Circle" => AddCircle (1 : ℝ)

/-- Exact equivariance of the literal first-three-coordinate quotient. -/
theorem dropDelta_flatTorusAffine (j : Kind) (x : RealTorus₄) :
    dropDelta (flatTorusAffine j j.twist x) = projectedAffine j (dropDelta x) := by
  obtain ⟨a, rfl⟩ := standardLattice.mkQ_surjective x
  rw [flatTorusAffine_mkQ, dropDelta_mkQ, dropDelta_mkQ,
    prefix_flatAffine, projectedAffine_coordinateProjection]

/-- The same exact equivariance for every iterate. -/
theorem dropDelta_projectedAffine_iterate (j : Kind) (r : ℕ) (x : RealTorus₄) :
    dropDelta ((flatTorusAffine j j.twist)^[r] x) =
      (projectedAffine j)^[r] (dropDelta x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        dropDelta_flatTorusAffine, ih]

/-- The native order descends through the proved surjective quotient map. -/
theorem projectedAffine_iterate_order (j : Kind) (z : DeltaBase) :
    (projectedAffine j)^[j.order] z = z := by
  obtain ⟨x, rfl⟩ := dropDelta_surjective z
  rw [← dropDelta_projectedAffine_iterate,
    flatTorusAffine_iterate_order j j.twist j.matrix_fixes_twist]

/-- The literal residual affine homeomorphism, with inverse given by its
order-minus-one iterate. -/
def deck (j : Kind) : DeltaBase ≃ₜ DeltaBase where
  toFun := projectedAffine j
  invFun := (projectedAffine j)^[j.order - 1]
  left_inv z := by
    have hm : (j.order - 1).succ = j.order := by
      have hpos := j.order_pos
      omega
    rw [← Function.iterate_succ_apply (f := projectedAffine j) (j.order - 1) z, hm]
    exact projectedAffine_iterate_order j z
  right_inv z := by
    have hm : (j.order - 1).succ = j.order := by
      have hpos := j.order_pos
      omega
    rw [← Function.iterate_succ_apply' (f := projectedAffine j) (j.order - 1) z, hm]
    exact projectedAffine_iterate_order j z
  continuous_toFun := projectedAffine_continuous j
  continuous_invFun := (projectedAffine_continuous j).iterate (j.order - 1)

@[simp] theorem deck_apply (j : Kind) (z : DeltaBase) :
    deck j z = projectedAffine j z := rfl

@[simp] theorem deck_symm_apply (j : Kind) (z : DeltaBase) :
    (deck j).symm z = (projectedAffine j)^[j.order - 1] z := rfl

theorem deck_coordinateProjection (j : Kind) (a : Fin 3 → ℝ) :
    deck j (coordinateProjection 3 a) = coordinateProjection 3 (projectedRealAffine j a) :=
  projectedAffine_coordinateProjection j a

/-- The original four-dimensional affine generator descends to this very homeomorphism. -/
theorem dropDelta_deck (j : Kind) (x : RealTorus₄) :
    dropDelta (flatTorusAffine j j.twist x) = deck j (dropDelta x) :=
  dropDelta_flatTorusAffine j x

theorem dropDelta_flatTorusAffine_iterate (j : Kind) (r : ℕ) (x : RealTorus₄) :
    dropDelta ((flatTorusAffine j j.twist)^[r] x) = (deck j)^[r] (dropDelta x) :=
  dropDelta_projectedAffine_iterate j r x

theorem deck_iterate_order (j : Kind) (z : DeltaBase) :
    (deck j)^[j.order] z = z :=
  projectedAffine_iterate_order j z

theorem deck_perm_pow_order (j : Kind) : (deck j).toEquiv ^ j.order = 1 := by
  apply Equiv.ext
  intro z
  rw [Equiv.Perm.coe_pow]
  exact deck_iterate_order j z

theorem deck_pow_apply (j : Kind) (r : ℕ) (z : DeltaBase) :
    (deck j ^ r) z = (deck j)^[r] z := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [pow_succ', Homeomorph.mul_apply, Function.iterate_succ_apply', ih]

theorem deck_pow_order (j : Kind) : deck j ^ j.order = 1 := by
  apply Homeomorph.ext
  intro z
  exact (deck_pow_apply j j.order z).trans (deck_iterate_order j z)

/-- Every iterate retains the exact signed native shift of the gamma circle. -/
theorem deck_iterate_zero_coordinate (j : Kind) (r : ℕ) (z : DeltaBase) :
    ((deck j)^[r] z) 0 =
      z 0 + (((r : ℝ) * (j.twist 0 : ℝ) / j.order : ℝ) : Circle) := by
  obtain ⟨x, rfl⟩ := dropDelta_surjective z
  rw [← dropDelta_flatTorusAffine_iterate, dropDelta_apply_zero,
    EllipticGamma.fibreGamma_flatTorusAffine_iterate, dropDelta_apply_zero]

/-- The retained first circle excludes every nonidentity finite iterate. -/
theorem deck_iterate_ne (j : Kind) (r : ℕ) (hr : 0 < r) (hrm : r < j.order)
    (z : DeltaBase) : (deck j)^[r] z ≠ z := by
  intro h
  have hc := congrFun h 0
  rw [deck_iterate_zero_coordinate] at hc
  have hshift : (((r : ℝ) * (j.twist 0 : ℝ) / j.order : ℝ) : Circle) = 0 :=
    add_left_cancel (hc.trans (add_zero _).symm)
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hshift
  have hn' : (n : ℝ) = (r : ℝ) * (j.twist 0 : ℝ) / j.order := by
    simpa only [zsmul_eq_mul, mul_one] using hn
  have hm : (j.order : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt j.order_pos)
  have hmul := (eq_div_iff hm).mp hn'
  have hint : n * (j.order : ℤ) = (r : ℤ) * j.twist 0 := by exact_mod_cast hmul
  cases j <;> norm_num [Kind.order, Kind.twist, ε, ε'] at hint hrm <;> omega

theorem deck_perm_pow_ne (j : Kind) (r : ℕ) (hr : 0 < r) (hrm : r < j.order)
    (z : DeltaBase) : ((deck j).toEquiv ^ r) z ≠ z := by
  rw [Equiv.Perm.coe_pow]
  exact deck_iterate_ne j r hr hrm z

end Wikipedia.HopfProblem.ConstructionSphereRecognition.EllipticOrbitFlat
