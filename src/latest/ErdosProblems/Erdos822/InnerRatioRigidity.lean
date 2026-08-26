/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.StructuredTotientFormula
import Mathlib

/-! # Rigidity of the inner rational function in the large-divisor range -/

namespace Erdos822

theorem prime_not_dvd_shifted_mul_of_lt {k r : ℕ}
    (hk : 0 < k) (hr : r.Prime) (hkr : k < r) : ¬ r ∣ shiftedTotient (k * r) := by
  have hrk : ¬ r ∣ k := Nat.not_dvd_of_pos_of_lt hk hkr
  have hφ : ¬ r ∣ Nat.totient k :=
    Nat.not_dvd_of_pos_of_lt (Nat.totient_pos.mpr hk) ((Nat.totient_le k).trans_lt hkr)
  have hpred : ¬ r ∣ r - 1 := Nat.not_dvd_of_pos_of_lt
    (Nat.sub_pos_of_lt hr.one_lt) (Nat.sub_lt hr.pos (by norm_num))
  have hφkr : Nat.totient (k * r) = Nat.totient k * (r - 1) := by
    rw [Nat.mul_comm k r, Nat.totient_mul_of_prime_of_not_dvd hr hrk]
    ring
  intro hdiv
  have hrtot : r ∣ Nat.totient (k * r) :=
    (Nat.dvd_add_iff_right (dvd_mul_left r k)).mpr hdiv
  rw [hφkr] at hrtot
  exact (hr.dvd_mul.mp hrtot).elim hφ hpred

theorem middlePrime_le_of_inner_ratio_cross_eq {k r k' r' : ℕ}
    (hk : 0 < k) (hk' : 0 < k') (hr : r.Prime) (hr' : r'.Prime)
    (hkr : k < r) (hk'r' : k' < r')
    (heq : (k * r * Nat.totient (k * r)) * shiftedTotient (k' * r') =
      (k' * r' * Nat.totient (k' * r')) * shiftedTotient (k * r)) :
    r ≤ r' := by
  by_contra hnot
  have hr'r : r' < r := by omega
  have hdiv : r ∣ (k' * r' * Nat.totient (k' * r')) * shiftedTotient (k * r) := by
    rw [← heq]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left r k) _) _
  have hnum : r ∣ k' * r' * Nat.totient (k' * r') :=
    (hr.dvd_mul.mp hdiv).resolve_right (prime_not_dvd_shifted_mul_of_lt hk hr hkr)
  have hr'k' : ¬ r' ∣ k' := Nat.not_dvd_of_pos_of_lt hk' hk'r'
  have hφ : Nat.totient (k' * r') = Nat.totient k' * (r' - 1) := by
    rw [Nat.mul_comm k' r', Nat.totient_mul_of_prime_of_not_dvd hr' hr'k']
    ring
  rw [hφ] at hnum
  rcases hr.dvd_mul.mp hnum with hleft | hright
  · rcases hr.dvd_mul.mp hleft with hdivk | hdivr
    · exact Nat.not_dvd_of_pos_of_lt hk' (hk'r'.trans hr'r) hdivk
    · exact Nat.not_dvd_of_pos_of_lt hr'.pos hr'r hdivr
  · rcases hr.dvd_mul.mp hright with hdivφ | hdivpred
    · exact Nat.not_dvd_of_pos_of_lt (Nat.totient_pos.mpr hk')
        ((Nat.totient_le k').trans_lt (hk'r'.trans hr'r)) hdivφ
    · exact Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hr'.one_lt)
        ((Nat.sub_le r' 1).trans_lt hr'r) hdivpred

theorem smallFactor_eq_of_same_prime_inner_cross_eq {k k' r : ℕ}
    (hk : 0 < k) (hk' : 0 < k') (hr : r.Prime) (hkr : k < r) (hk'r : k' < r)
    (heq : (k * r * Nat.totient (k * r)) * shiftedTotient (k' * r) =
      (k' * r * Nat.totient (k' * r)) * shiftedTotient (k * r)) : k = k' := by
  have hrk : ¬ r ∣ k := Nat.not_dvd_of_pos_of_lt hk hkr
  have hrk' : ¬ r ∣ k' := Nat.not_dvd_of_pos_of_lt hk' hk'r
  have hφ (a : ℕ) (ha : ¬ r ∣ a) : Nat.totient (a * r) = Nat.totient a * (r - 1) := by
    rw [Nat.mul_comm a r, Nat.totient_mul_of_prime_of_not_dvd hr ha]
    ring
  have heq' : k * Nat.totient k * (k' * r + Nat.totient k' * (r - 1)) =
      k' * Nat.totient k' * (k * r + Nat.totient k * (r - 1)) := by
    have hfac : 0 < r * (r - 1) := mul_pos hr.pos (Nat.sub_pos_of_lt hr.one_lt)
    apply Nat.eq_of_mul_eq_mul_left hfac
    dsimp [shiftedTotient] at heq
    rw [hφ k hrk, hφ k' hrk'] at heq
    calc
      _ = (k * r * (Nat.totient k * (r - 1))) * (k' * r + Nat.totient k' * (r - 1)) := by ring
      _ = _ := heq
      _ = _ := by ring
  letI : Fact r.Prime := ⟨hr⟩
  have hu : (Nat.totient k : ZMod r) ≠ 0 := by
    intro hzero
    exact Nat.not_dvd_of_pos_of_lt (Nat.totient_pos.mpr hk) ((Nat.totient_le k).trans_lt hkr)
      ((ZMod.natCast_eq_zero_iff (Nat.totient k) r).mp hzero)
  have hv : (Nat.totient k' : ZMod r) ≠ 0 := by
    intro hzero
    exact Nat.not_dvd_of_pos_of_lt (Nat.totient_pos.mpr hk') ((Nat.totient_le k').trans_lt hk'r)
      ((ZMod.natCast_eq_zero_iff (Nat.totient k') r).mp hzero)
  have hmod := congrArg (fun a : ℕ ↦ (a : ZMod r)) heq'
  push_cast at hmod
  have hpred : ((r - 1 : ℕ) : ZMod r) = -1 := by
    rw [Nat.cast_sub hr.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]
  simp only [ZMod.natCast_self, mul_zero, zero_add, hpred] at hmod
  have hcast : (k : ZMod r) = k' := by
    apply mul_right_cancel₀ (mul_ne_zero hu hv)
    linear_combination -hmod
  have hrem := (ZMod.natCast_eq_natCast_iff' k k' r).mp hcast
  simpa only [Nat.mod_eq_of_lt hkr, Nat.mod_eq_of_lt hk'r] using hrem

theorem factors_eq_of_inner_ratio_cross_eq {k r k' r' : ℕ}
    (hk : 0 < k) (hk' : 0 < k') (hr : r.Prime) (hr' : r'.Prime)
    (hkr : k < r) (hk'r' : k' < r')
    (heq : (k * r * Nat.totient (k * r)) * shiftedTotient (k' * r') =
      (k' * r' * Nat.totient (k' * r')) * shiftedTotient (k * r)) :
    k = k' ∧ r = r' := by
  have hrr' := middlePrime_le_of_inner_ratio_cross_eq hk hk' hr hr' hkr hk'r' heq
  have hr'r := middlePrime_le_of_inner_ratio_cross_eq hk' hk hr' hr hk'r' hkr heq.symm
  have hreq : r = r' := by omega
  subst r'
  exact ⟨smallFactor_eq_of_same_prime_inner_cross_eq hk hk' hr hkr hk'r' heq, rfl⟩

#print axioms factors_eq_of_inner_ratio_cross_eq

end Erdos822
