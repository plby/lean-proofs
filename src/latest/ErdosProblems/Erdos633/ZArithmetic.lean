import ErdosProblems.Erdos633.Arithmetic

/-!
# The unconditional nonsquare obstruction for Z

If the Z test were square, its sum with `c²` would be three times `(a+b)²`.
A descent modulo three excludes that equation without a primitivity assumption.
-/

namespace Erdos633

theorem sum_sq_ne_three_sq (u v w : ℕ) (hw : 0 < w) : u ^ 2 + v ^ 2 ≠ 3 * w ^ 2 := by
  induction w using Nat.strong_induction_on generalizing u v with
  | h w ih =>
    intro heq
    have hz : (u : ZMod 3) ^ 2 + (v : ZMod 3) ^ 2 = 0 := by
      have h' := congrArg (fun n : ℕ => (n : ZMod 3)) heq
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        show (3 : ZMod 3) = 0 by decide, zero_mul] using h'
    have hmod : ∀ x y : ZMod 3, x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0 := by decide
    obtain ⟨hu0, hv0⟩ := hmod _ _ hz
    have hu : 3 ∣ u := (ZMod.natCast_eq_zero_iff u 3).mp hu0
    have hv : 3 ∣ v := (ZMod.natCast_eq_zero_iff v 3).mp hv0
    obtain ⟨u', rfl⟩ := hu
    obtain ⟨v', rfl⟩ := hv
    have hdw2 : 3 ∣ w ^ 2 := by
      refine ⟨u' ^ 2 + v' ^ 2, ?_⟩
      nlinarith [heq]
    have hdw : 3 ∣ w := Nat.prime_three.dvd_of_dvd_pow hdw2
    obtain ⟨w', hww⟩ := hdw
    have hw' : 0 < w' := by omega
    have hlt : w' < w := by omega
    apply ih w' hlt u' v' hw'
    nlinarith [heq]

theorem oneTwenty_Z_numerator_not_isSquare (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ¬ IsSquare ((2 * a + b) * (a + 2 * b)) := by
  rintro ⟨d, hd⟩
  apply sum_sq_ne_three_sq d c (a + b) (by omega)
  nlinarith [h]

end Erdos633
