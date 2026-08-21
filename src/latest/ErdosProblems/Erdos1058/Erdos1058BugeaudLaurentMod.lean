import ErdosProblems.Erdos1058.Erdos1058BugeaudLaurent

namespace Erdos1058.BugeaudLaurent

theorem odd_pow_two_pow_modEq_one {z T : ℕ} (hz : Odd z) :
    z ^ (2 ^ T) ≡ 1 [MOD 2 ^ T] := by
  cases T with
  | zero =>
      exact Nat.modEq_one
  | succ T =>
      have hcop : z.Coprime (2 ^ (T + 1)) :=
        (Nat.coprime_two_right.mpr hz).pow_right (T + 1)
      have h := Nat.ModEq.pow_totient hcop
      rw [Nat.totient_prime_pow Nat.prime_two (by omega : 0 < T + 1)] at h
      norm_num at h
      have h2 := h.pow 2
      have hexp : z ^ (2 ^ (T + 1)) = (z ^ (2 ^ T)) ^ 2 := by
        rw [show 2 ^ (T + 1) = 2 ^ T * 2 by simp [pow_succ, mul_comm], pow_mul]
      rw [hexp]
      simpa using h2

theorem exists_odd_exponent_inverse (b T : ℕ) (hb : Odd b) :
    ∃ c t : ℕ, b * c = 1 + 2 ^ T * t := by
  cases T with
  | zero =>
      refine ⟨1, b - 1, ?_⟩
      have hbpos : 0 < b := Odd.pos hb
      simp
      omega
  | succ T =>
      have hbCop : b.Coprime (2 ^ (T + 1)) :=
        (Nat.coprime_two_right.mpr hb).pow_right (T + 1)
      let u : (ZMod (2 ^ (T + 1)))ˣ := ZMod.unitOfCoprime b hbCop
      let c : ℕ := ((↑(u⁻¹) : ZMod (2 ^ (T + 1)))).val
      have hcCast : (c : ZMod (2 ^ (T + 1))) = ↑(u⁻¹) := by
        simp [c]
      have hbcZ : (b : ZMod (2 ^ (T + 1))) * c = 1 := by
        rw [hcCast]
        change (↑u : ZMod (2 ^ (T + 1))) * ↑(u⁻¹) = 1
        simp
      have hbcMod : b * c ≡ 1 [MOD 2 ^ (T + 1)] := by
        rw [← ZMod.natCast_eq_natCast_iff]
        simpa only [Nat.cast_mul, Nat.cast_one] using hbcZ
      have hbcPos : 1 ≤ b * c := by
        by_contra h
        have hzero : b * c = 0 := by omega
        have hmodZero : (0 : ℕ) ≡ 1 [MOD 2 ^ (T + 1)] := hzero ▸ hbcMod
        have hm : 1 < 2 ^ (T + 1) := by
          have hp : 0 < 2 ^ T := pow_pos (by norm_num) _
          rw [pow_succ]
          omega
        have heq : 0 = 1 :=
          Nat.ModEq.eq_of_lt_of_lt hmodZero (by omega) hm
        omega
      have hdvd : 2 ^ (T + 1) ∣ b * c - 1 :=
        (Nat.modEq_iff_dvd' hbcPos).mp hbcMod.symm
      obtain ⟨t, ht⟩ := hdvd
      refine ⟨c, t, ?_⟩
      omega

theorem zmod_pow_mul_exponent_inverse {z b c t T r : ℕ}
    (hz : Odd z) (hbc : b * c = 1 + 2 ^ T * t) :
    (z : ZMod (2 ^ T)) ^ (b * c * r) = (z : ZMod (2 ^ T)) ^ r := by
  have hperiodNat := odd_pow_two_pow_modEq_one (T := T) hz
  have hperiod : (z : ZMod (2 ^ T)) ^ (2 ^ T) = 1 := by
    have hcast : ((z ^ (2 ^ T) : ℕ) : ZMod (2 ^ T)) = (1 : ℕ) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).2 hperiodNat
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hcast
  rw [hbc]
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, pow_add, pow_mul, hperiod]
  simp

theorem zmod_interpolation_identity
    {p q a b c t T r s v : ℕ}
    (hp : Odd p) (hq : Odd q)
    (hbc : b * c = 1 + 2 ^ T * t)
    (hrel : (p ^ a * q ^ b) ^ 2 ≡ 1 [MOD 2 ^ T]) :
    (p ^ (2 * r) * q ^ (2 * v) : ZMod (2 ^ T)) =
      (q ^ (2 * (v + s)) * (p ^ (2 * c)) ^ (b * r + a * s) : ℕ) := by
  have hrelZ :
      (((p : ZMod (2 ^ T)) ^ a * (q : ZMod (2 ^ T)) ^ b) ^ 2) = 1 := by
    have hcast : ((((p ^ a * q ^ b) ^ 2 : ℕ) : ZMod (2 ^ T))) = (1 : ℕ) :=
      (ZMod.natCast_eq_natCast_iff _ _ _).2 hrel
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_one] using hcast
  have hpInv (w : ℕ) :
      (p : ZMod (2 ^ T)) ^ (b * c * w) = (p : ZMod (2 ^ T)) ^ w :=
    zmod_pow_mul_exponent_inverse hp hbc
  have hqInv (w : ℕ) :
      (q : ZMod (2 ^ T)) ^ (b * c * w) = (q : ZMod (2 ^ T)) ^ w :=
    zmod_pow_mul_exponent_inverse hq hbc
  have hDbr :
      ((p ^ (2 * c) : ℕ) : ZMod (2 ^ T)) ^ (b * r) =
        (p : ZMod (2 ^ T)) ^ (2 * r) := by
    simp only [Nat.cast_pow]
    calc
      ((p : ZMod (2 ^ T)) ^ (2 * c)) ^ (b * r) =
          (p : ZMod (2 ^ T)) ^ (2 * c * (b * r)) := by
            exact (pow_mul (p : ZMod (2 ^ T)) (2 * c) (b * r)).symm
      _ =
          ((p : ZMod (2 ^ T)) ^ (b * c * r)) ^ 2 := by
            rw [← pow_mul]
            congr 1
            ring
      _ = ((p : ZMod (2 ^ T)) ^ r) ^ 2 := by rw [hpInv]
      _ = (p : ZMod (2 ^ T)) ^ (2 * r) := by
        rw [← pow_mul]
        congr 1
        ring
  have hDasQ :
      ((p ^ (2 * c) : ℕ) : ZMod (2 ^ T)) ^ (a * s) *
        (q : ZMod (2 ^ T)) ^ (2 * s) = 1 := by
    have hpow := congrArg (fun z : ZMod (2 ^ T) => z ^ (c * s)) hrelZ
    simp only [one_pow, mul_pow] at hpow
    rw [← pow_mul, ← pow_mul] at hpow
    rw [← pow_mul, ← pow_mul] at hpow
    have hpExp : a * (2 * (c * s)) = 2 * c * (a * s) := by ring
    have hqExp : b * (2 * (c * s)) = 2 * (b * c * s) := by ring
    rw [hpExp, hqExp] at hpow
    have hq2 : (q : ZMod (2 ^ T)) ^ (2 * (b * c * s)) =
        (q : ZMod (2 ^ T)) ^ (2 * s) := by
      rw [show 2 * (b * c * s) = (b * c * s) * 2 by ring, pow_mul, hqInv]
      rw [show 2 * s = s * 2 by omega, pow_mul]
    rw [hq2] at hpow
    simpa only [Nat.cast_pow, ← pow_mul] using hpow
  push_cast
  simp only [Nat.cast_pow] at hDbr hDasQ
  rw [show 2 * (v + s) = 2 * v + 2 * s by ring, pow_add]
  rw [pow_add]
  rw [hDbr]
  calc
    (p : ZMod (2 ^ T)) ^ (2 * r) * (q : ZMod (2 ^ T)) ^ (2 * v) =
        ((p : ZMod (2 ^ T)) ^ (2 * r) * (q : ZMod (2 ^ T)) ^ (2 * v)) *
          (((p : ZMod (2 ^ T)) ^ (2 * c)) ^ (a * s) *
            (q : ZMod (2 ^ T)) ^ (2 * s)) := by rw [hDasQ, mul_one]
    _ = (q : ZMod (2 ^ T)) ^ (2 * v) * (q : ZMod (2 ^ T)) ^ (2 * s) *
        ((p : ZMod (2 ^ T)) ^ (2 * r) *
          ((p : ZMod (2 ^ T)) ^ (2 * c)) ^ (a * s)) := by ring

end Erdos1058.BugeaudLaurent
