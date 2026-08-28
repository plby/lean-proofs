import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticFrames
import Wikipedia.HopfProblem.SpecialPeriodsTriangleRegularCentralizersTriangle

/-!
# The orientation and actual elliptic tail frames are forced

The genuine attaching-square lift relates the native elliptic generator
to the endpoint of the fixed normalized meridian.  The first cyclic
retraction of the actual triangle free product rules out reversal: its
order-three generator is not its own inverse.  Consequently the actual
tail frame centralizes the original generator and is a bounded power of
it.  These conclusions have no orientation or tail-conjugacy hypotheses.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Triangle Meridians RiemannMapping

/-- The literal free-product retraction onto the first cyclic factor. -/
def firstCyclicCharacter : TriangleGroup →* Multiplicative (ZMod 3) :=
  Monoid.Coprod.lift (MonoidHom.id _) 1

@[simp] theorem firstCyclicCharacter_generator :
    firstCyclicCharacter triangleGenerator₁ = Multiplicative.ofAdd (1 : ZMod 3) := by
  simp [firstCyclicCharacter, triangleGenerator₁]

/-- The actual order-three generator cannot be conjugated to its inverse. -/
theorem firstGenerator_not_inverse_conjugate (d : TriangleGroup) :
    triangleGenerator₁ * d ≠ d * triangleGenerator₁⁻¹ := by
  intro he
  have hm := congrArg firstCyclicCharacter he
  simp only [map_mul, map_inv, firstCyclicCharacter_generator] at hm
  rw [mul_comm (Multiplicative.ofAdd (1 : ZMod 3)) (firstCyclicCharacter d)] at hm
  have hc := mul_left_cancel hm
  have ha := congrArg (fun x : Multiplicative (ZMod 3) => x.toAdd) hc
  exact (by decide : (1 : ZMod 3) ≠ -1) ha

/-- The genuine native attaching square excludes the reversed normalized
orientation.  This is derived from its actual covering endpoints. -/
theorem normalizationReversesMeridians_false : normalizationReversesMeridians = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  apply firstGenerator_not_inverse_conjugate (nativeTailFrame .three)
  simpa [h, ellipticGenerator] using nativeTailFrame_relation_if .three

/-- The sign used in the existing slit sections is therefore nonpositive. -/
theorem normalizationOrientation_nonpos : normalizationOrientation ≤ 0 := by
  apply le_of_not_gt
  have h := normalizationReversesMeridians_false
  simpa only [normalizationReversesMeridians, decide_eq_false_iff_not] using h

/-- The actual tail frame commutes with its original elliptic generator. -/
theorem nativeTailFrame_commute (j : Elliptic.Kind) :
    Commute (ellipticGenerator j) (nativeTailFrame j) := by
  change ellipticGenerator j * nativeTailFrame j = nativeTailFrame j * ellipticGenerator j
  have h := nativeTailFrame_relation_if j
  simpa only [normalizationReversesMeridians_false, Bool.false_eq_true, if_false] using h

/-- The exact final deck frame belongs to the original cyclic stabilizer,
with a bounded integer representative; it is not an arbitrary conjugator. -/
theorem nativeTailFrame_eq_power (j : Elliptic.Kind) :
    ∃ k : ℕ, k < j.order ∧ nativeTailFrame j = ellipticGenerator j ^ k := by
  cases j
  · exact triangleGenerator₁_commute_eq_pow _ (nativeTailFrame_commute .three)
  · exact triangleGenerator₂_commute_eq_pow _ (nativeTailFrame_commute .four)

/-- The inverse frame obeys the same bounded stabilizer description. -/
theorem nativeTailFrame_inv_eq_power (j : Elliptic.Kind) :
    ∃ k : ℕ, k < j.order ∧ (nativeTailFrame j)⁻¹ = ellipticGenerator j ^ k := by
  cases j
  · exact triangleGenerator₁_commute_eq_pow _ (nativeTailFrame_commute .three).inv_right
  · exact triangleGenerator₂_commute_eq_pow _ (nativeTailFrame_commute .four).inv_right

/-- In any actual triangle action, the original generator's fixed
elements are fixed by this geometrically constructed tail frame. -/
theorem nativeTailFrame_smul_fixed {A : Type*} [MulAction TriangleGroup A]
    (j : Elliptic.Kind) (a : A) (ha : ellipticGenerator j • a = a) :
    nativeTailFrame j • a = a := by
  obtain ⟨k, hbound, hk⟩ := nativeTailFrame_eq_power j
  rw [hk]
  clear hbound hk
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_smul, ha, ih]

/-- The inverse frame also fixes the original invariant elements. -/
theorem nativeTailFrame_inv_smul_fixed {A : Type*} [MulAction TriangleGroup A]
    (j : Elliptic.Kind) (a : A) (ha : ellipticGenerator j • a = a) :
    (nativeTailFrame j)⁻¹ • a = a := by
  obtain ⟨k, hbound, hk⟩ := nativeTailFrame_inv_eq_power j
  rw [hk]
  clear hbound hk
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_smul, ha, ih]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
