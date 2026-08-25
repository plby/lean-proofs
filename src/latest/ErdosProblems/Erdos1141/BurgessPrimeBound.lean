import ErdosProblems.Erdos1141.BurgessAmplifier
import ErdosProblems.Erdos1141.BurgessPrimeMoment

/-!
# The finite arbitrary-order Burgess inequality for prime moduli
-/

namespace Pollack17.Burgess

open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

theorem abs_qchar_le_one (x : ZMod p) : |qchar x| ≤ 1 := by
  rcases quadraticChar_isQuadratic (ZMod p) x with h | h | h <;> norm_num [qchar, h]

theorem naturalShiftSum_qchar_moment_le {V : ℕ} (hV : V < p) (r : ℕ) :
    (∑ x : ZMod p, naturalShiftSum qchar V x ^ (2 * r)) ≤
      (V : ℝ) ^ r * (r : ℝ) ^ (2 * r) * p +
        (V : ℝ) ^ (2 * r) * (Stepanov.simpleRootConstant (2 * r) : ℝ) * Real.sqrt p := by
  let S : Finset (ZMod p) := (Finset.Icc 1 V).image Nat.cast
  have hinj : Set.InjOn (Nat.cast : ℕ → ZMod p) (Finset.Icc 1 V) := by
    intro a ha b hb hab
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp hab).eq_of_lt_of_lt
      ((Finset.mem_Icc.mp ha).2.trans_lt hV) ((Finset.mem_Icc.mp hb).2.trans_lt hV)
  have hcard : S.card = V := by
    rw [Finset.card_image_of_injOn hinj]
    simp
  have hsum (x : ZMod p) : naturalShiftSum qchar V x = shiftSum S x := by
    rw [shiftSum, Finset.sum_image hinj]
    rfl
  simpa only [hsum, hcard] using shiftSum_even_moment_le S r

theorem prime_amplifier_even_power_le {M H U V : ℕ}
    (hH : 0 < H) (hU : 0 < U) (hUp : U < p) (hVp : V < p)
    (hsmall : 2 * (U * H) < p) (k : ℕ) :
    amplifierNumerator (qchar (p := p)) M H (Finset.Icc 1 U) V ^ (2 * (k + 1)) ≤
      ((H : ℝ) * U) ^ (2 * k) *
        (((H : ℝ) * (1 + Real.log U) + U) * ((U : ℝ) * (1 + Real.log U))) *
        ((V : ℝ) ^ (k + 1) * (k + 1 : ℝ) ^ (2 * (k + 1)) * p +
          (V : ℝ) ^ (2 * (k + 1)) *
            (Stepanov.simpleRootConstant (2 * (k + 1)) : ℝ) * Real.sqrt p) := by
  have hcop : ∀ u ∈ Finset.Icc 1 U, u.Coprime p := by
    intro u hu
    exact (Nat.coprime_comm.mp ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (Finset.mem_Icc.mp hu).1
        ((Finset.mem_Icc.mp hu).2.trans_lt hUp))))
  have he := naturalRatioEnergy_le (M := M) (Finset.Icc 1 U)
    (fun _ h => h) hcop hH hU hsmall
  have hm := naturalShiftSum_qchar_moment_le hVp (k + 1)
  simp only [Nat.cast_add, Nat.cast_one] at hm
  have hh := amplifierNumerator_even_power_le (qchar (p := p)) M H (Finset.Icc 1 U) V k
  simp only [Nat.card_Icc, Nat.add_sub_cancel] at hh
  refine hh.trans (mul_le_mul ?_ hm ?_ ?_)
  · exact mul_le_mul_of_nonneg_left he (by positivity)
  · exact Finset.sum_nonneg fun x _ => (even_two_mul _).pow_nonneg _
  · have hlog : 0 ≤ Real.log (U : ℝ) := Real.log_nonneg (by exact_mod_cast hU)
    positivity

end Pollack17.Burgess
