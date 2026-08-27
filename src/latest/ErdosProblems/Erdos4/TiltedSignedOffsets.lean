import ErdosProblems.Erdos4.TiltedFiberOffsets

/-! Short signed offsets determine a root color modulo each witness prime. -/

namespace Erdos4.Tilted

def SignedOffsetWitness (p v n U : ℕ) (o : Bool × Fin U) : Prop :=
  0 < o.2.val ∧ if o.1 then n = v + p * o.2.val else v = n + p * o.2.val

theorem exists_signed_offset {p v n Y U : ℕ} (_hp : 0 < p)
    (hvY : v ≤ Y) (hnY : n ≤ Y) (hnv : n ≠ v) (hYU : Y < p * U)
    (hmod : (n : ZMod p) = (v : ZMod p)) :
    ∃ o : Bool × Fin U, SignedOffsetWitness p v n U o := by
  have hm := (ZMod.natCast_eq_natCast_iff n v p).mp hmod
  rcases le_total v n with hvn | hnv'
  · obtain ⟨h, hh⟩ := hm.symm.dvd'
    have hform : n = v + p * h := by omega
    have hhpos : 0 < h := by
      by_contra hzero
      have : h = 0 := by omega
      simp [this] at hform
      exact hnv hform
    have hhU : h < U := by
      by_contra hnot
      have hU : U ≤ h := by omega
      have hmul := Nat.mul_le_mul_left p hU
      omega
    exact ⟨(true, ⟨h, hhU⟩), hhpos, hform⟩
  · obtain ⟨h, hh⟩ := hm.dvd'
    have hform : v = n + p * h := by omega
    have hhpos : 0 < h := by
      by_contra hzero
      have : h = 0 := by omega
      simp [this] at hform
      exact hnv hform.symm
    have hhU : h < U := by
      by_contra hnot
      have hU : U ≤ h := by omega
      have hmul := Nat.mul_le_mul_left p hU
      omega
    exact ⟨(false, ⟨h, hhU⟩), hhpos, hform⟩

theorem same_signed_witness_modEq {p q v n m U s : ℕ} (hs : s.Prime)
    (o : Bool × Fin U) (hU : U ≤ s)
    (hn : SignedOffsetWitness p v n U o) (hm : SignedOffsetWitness q v m U o)
    (hsn : s ∣ n) (hsm : s ∣ m) : p ≡ q [MOD s] := by
  have hlt : o.2.val < s := o.2.isLt.trans_le hU
  have hcop : s.Coprime o.2.val := hs.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hn.1 hlt)
  have hnm : n ≡ m [MOD s] := hsn.modEq_zero_nat.trans hsm.zero_modEq_nat
  have hmul : p * o.2.val ≡ q * o.2.val [MOD s] := by
    cases ho : o.1
    · have hpform : v = n + p * o.2.val := by simpa only [SignedOffsetWitness, ho, Bool.false_eq_true, if_false] using hn.2
      have hqform : v = m + q * o.2.val := by simpa only [SignedOffsetWitness, ho, Bool.false_eq_true, if_false] using hm.2
      have hsum : n + p * o.2.val ≡ m + q * o.2.val [MOD s] := by rw [← hpform, ← hqform]
      exact hnm.add_left_cancel hsum
    · have hpform : n = v + p * o.2.val := by simpa only [SignedOffsetWitness, ho, if_true] using hn.2
      have hqform : m = v + q * o.2.val := by simpa only [SignedOffsetWitness, ho, if_true] using hm.2
      rw [hpform, hqform] at hnm
      exact Nat.ModEq.add_left_cancel' v hnm
  exact Nat.ModEq.cancel_right_of_coprime hcop hmul

end Erdos4.Tilted
