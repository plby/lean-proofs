import Wikipedia.HopfProblem.EllipticDiscPower
import Wikipedia.HopfProblem.EllipticFamilies
import Wikipedia.HopfProblem.SpecialPeriodsRotations
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The fibres and ramification of the elliptic disc maps

The positive power map on the actual unit disc identifies exactly the
orbits of a primitive root rotation.  Away from the center, each fibre
has the prescribed number of points and the derivative is nonzero.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.Elliptic

open SpecialPeriods

/-- Power fibres in the actual open disc are precisely rotation orbits.
This includes the center, whose orbit is a singleton. -/
theorem discPower_eq_iff_scalar_iterate (m : ℕ) (hm : 0 < m)
    (c : ℂ) (hc : ‖c‖ = 1) (hroot : IsPrimitiveRoot c m) (z w : Disc) :
    discPower m hm z = discPower m hm w ↔
      ∃ r < m, (discScalar c hc)^[r] w = z := by
  let : NeZero m := ⟨hm.ne'⟩
  constructor
  · intro he
    have hp : (z : ℂ) ^ m = (w : ℂ) ^ m := congrArg Subtype.val he
    by_cases hw : (w : ℂ) = 0
    · have hz : (z : ℂ) = 0 := (pow_eq_zero_iff hm.ne').mp
        (by simpa only [hw, zero_pow hm.ne'] using hp)
      exact ⟨0, hm, Subtype.ext (hw.trans hz.symm)⟩
    · have hr : ((z : ℂ) / (w : ℂ)) ^ m = 1 := by
        rw [div_pow, hp, div_self (pow_ne_zero m hw)]
      obtain ⟨r, hrm, hr⟩ := hroot.eq_pow_of_pow_eq_one hr
      refine ⟨r, hrm, Subtype.ext ?_⟩
      rw [discScalar_iterate_val, hr, div_mul_cancel₀ _ hw]
  · rintro ⟨r, _, rfl⟩
    apply Subtype.ext
    change ((discScalar c hc)^[r] w : ℂ) ^ m = (w : ℂ) ^ m
    rw [discScalar_iterate_val, mul_pow, ← pow_mul, Nat.mul_comm r m,
      pow_mul, hroot.pow_eq_one, one_pow, one_mul]

theorem neg_rho_isPrimitiveRoot : IsPrimitiveRoot (-rho) 3 := by
  apply IsPrimitiveRoot.mk_of_lt _ (by decide)
  · calc
      (-rho) ^ 3 = -(rho ^ 3) := by ring
      _ = 1 := by rw [rho_cube]; norm_num
  · exact fun r hr hrm => neg_rho_pow_ne_one hr hrm

theorem discPower_three_eq_iff (z w : Disc) :
    discPower 3 (by decide) z = discPower 3 (by decide) w ↔
      ∃ r < 3, discRotateThree^[r] w = z :=
  discPower_eq_iff_scalar_iterate 3 (by decide) (-rho) (by simpa using norm_rho)
    neg_rho_isPrimitiveRoot z w

theorem discPower_four_eq_iff (z w : Disc) :
    discPower 4 (by decide) z = discPower 4 (by decide) w ↔
      ∃ r < 4, discRotateFour^[r] w = z :=
  discPower_eq_iff_scalar_iterate 4 (by decide) (-Complex.I) (by simp)
    Complex.isPrimitiveRoot_neg_I z w

/-- The equivalence specialized to the actual base rotations used by
the elliptic filling families. -/
theorem discPower_eq_iff_familyRotation (j : Kind) (z w : Disc) :
    discPower j.order j.order_pos z = discPower j.order j.order_pos w ↔
      ∃ r < j.order, (familyRotation j)^[r] w = z := by
  cases j
  · exact discPower_three_eq_iff z w
  · exact discPower_four_eq_iff z w

/-- Different rotation exponents give different points away from zero. -/
theorem discScalar_iterates_injective (m : ℕ) (c : ℂ) (hc : ‖c‖ = 1)
    (hroot : IsPrimitiveRoot c m) (w : Disc) (hw : (w : ℂ) ≠ 0) :
    Function.Injective (fun r : Fin m => (discScalar c hc)^[r.val] w) := by
  intro r s he
  apply Fin.ext
  apply hroot.pow_inj r.isLt s.isLt
  have he' := congrArg Subtype.val he
  simp only [discScalar_iterate_val] at he'
  exact mul_right_cancel₀ hw he'

/-- All points of a nonzero power fibre, with no repetitions, are given
by the finitely many rotation powers. -/
def discPowerFibreOrbitEquiv (m : ℕ) (hm : 0 < m) (c : ℂ) (hc : ‖c‖ = 1)
    (hroot : IsPrimitiveRoot c m) (w : Disc) (hw : (w : ℂ) ≠ 0) :
    Fin m ≃ (discPower m hm ⁻¹' {discPower m hm w}) :=
  Equiv.ofBijective (fun r : Fin m =>
    ⟨(discScalar c hc)^[r.val] w,
      (discPower_eq_iff_scalar_iterate m hm c hc hroot _ w).mpr ⟨r.val, r.isLt, rfl⟩⟩) (by
    constructor
    · intro r s he
      exact discScalar_iterates_injective m c hc hroot w hw (congrArg Subtype.val he)
    · rintro ⟨z, hz⟩
      obtain ⟨r, hrm, hr⟩ := (discPower_eq_iff_scalar_iterate m hm c hc hroot z w).mp hz
      exact ⟨⟨r, hrm⟩, Subtype.ext hr⟩)

theorem discPower_fibre_ncard (m : ℕ) (hm : 0 < m) (c : ℂ) (hc : ‖c‖ = 1)
    (hroot : IsPrimitiveRoot c m) (w : Disc) (hw : (w : ℂ) ≠ 0) :
    (discPower m hm ⁻¹' {w}).ncard = m := by
  obtain ⟨z, rfl⟩ := discPower_surjective m hm w
  have hz : (z : ℂ) ≠ 0 := by
    intro he
    exact hw (by simp only [discPower_coe, he, zero_pow hm.ne'])
  change Nat.card (discPower m hm ⁻¹' {discPower m hm z}) = m
  rw [Nat.card_congr (discPowerFibreOrbitEquiv m hm c hc hroot z hz).symm, Nat.card_fin]

theorem discPower_fibre_ncard_of_kind (j : Kind) (w : Disc) (hw : (w : ℂ) ≠ 0) :
    (discPower j.order j.order_pos ⁻¹' {w}).ncard = j.order := by
  cases j
  · exact discPower_fibre_ncard 3 (by decide) (-rho) (by simpa using norm_rho)
      neg_rho_isPrimitiveRoot w hw
  · exact discPower_fibre_ncard 4 (by decide) (-Complex.I) (by simp)
      Complex.isPrimitiveRoot_neg_I w hw

/-- The derivative computation is in the actual ambient complex coordinate,
which is the inherited chart on the open disc. -/
theorem complexPower_hasDerivAt (m : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => w ^ m) ((m : ℂ) * z ^ (m - 1)) z :=
  hasDerivAt_pow m z

theorem complexPower_deriv_ne_zero (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    deriv (fun w : ℂ => w ^ m) z ≠ 0 := by
  rw [(complexPower_hasDerivAt m z).deriv]
  exact mul_ne_zero (by exact_mod_cast hm.ne') (pow_ne_zero _ hz)

/-- The central branching multiplicity is exactly the power, measured
by analytic order of the actual holomorphic coordinate function. -/
theorem complexPower_order_at_zero (m : ℕ) :
    analyticOrderAt (fun z : ℂ => z ^ m) 0 = (m : ℕ∞) := by
  have h : AnalyticAt ℂ (fun z : ℂ => z ^ m) 0 := by fun_prop
  apply h.analyticOrderAt_eq_natCast.mpr
  refine ⟨fun _ => 1, analyticAt_const, one_ne_zero, ?_⟩
  exact Filter.Eventually.of_forall (fun z => by simp)

/-- Every noncentral point of every power fibre is a simple analytic root. -/
theorem complexPower_order_at_nonzero (m : ℕ) (hm : 0 < m) (z : ℂ) (hz : z ≠ 0) :
    analyticOrderAt (fun w : ℂ => w ^ m - z ^ m) z = 1 :=
  ((analyticAt_id (𝕜 := ℂ) (z := z)).pow m).analyticOrderAt_sub_eq_one_of_deriv_ne_zero
    (complexPower_deriv_ne_zero m hm z hz)

end Wikipedia.HopfProblem.Elliptic
