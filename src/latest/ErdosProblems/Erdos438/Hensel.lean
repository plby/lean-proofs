import Mathlib

namespace Erdos587

lemma exists_square_modEq_primePower_succ
    {p k : ℕ} {a z : ℤ} (hk : 0 < k)
    (hcop : IsCoprime (2 * z) (p : ℤ))
    (h : a ≡ z ^ 2 [ZMOD ((p ^ k : ℕ) : ℤ)]) :
    ∃ z' : ℤ, IsCoprime (2 * z') (p : ℤ) ∧
      a ≡ z' ^ 2 [ZMOD ((p ^ (k + 1) : ℕ) : ℤ)] := by
  rw [Int.modEq_iff_dvd] at h
  obtain ⟨w, hw⟩ := h
  have hcop' := hcop
  obtain ⟨u, v, huv⟩ := hcop
  let t : ℤ := -u * w
  have hpk : (p : ℤ) ∣ ((p ^ k : ℕ) : ℤ) := by
    rw [Nat.cast_pow]
    exact dvd_pow_self _ (Nat.ne_of_gt hk)
  let z' : ℤ := z + (p ^ k : ℕ) * t
  refine ⟨z', ?_, ?_⟩
  · obtain ⟨d, hd⟩ := hpk
    have hz' : 2 * z' = 2 * z + (p : ℤ) * (2 * d * t) := by
      dsimp only [z']
      rw [hd]
      ring
    rw [hz']
    exact hcop'.add_mul_left_left _
  · rw [Int.modEq_iff_dvd]
    have hlin : (p : ℤ) ∣ w + 2 * z * t := by
      refine ⟨v * w, ?_⟩
      dsimp only [t]
      calc
        w + 2 * z * (-u * w) = (1 - u * (2 * z)) * w := by ring
        _ = ((p : ℤ) * v) * w := by
          rw [show 1 - u * (2 * z) = (p : ℤ) * v by linarith [huv]]
        _ = (p : ℤ) * (v * w) := by ring
    obtain ⟨c, hc⟩ := hlin
    obtain ⟨d, hd⟩ := hpk
    refine ⟨c + d * t ^ 2, ?_⟩
    have hpow : (((p ^ (k + 1) : ℕ) : ℤ)) = (p : ℤ) ^ k * (p : ℤ) := by
      push_cast
      exact pow_succ (p : ℤ) k
    rw [hpow]
    calc
      z' ^ 2 - a =
          ((p ^ k : ℕ) : ℤ) *
            (w + 2 * z * t + ((p ^ k : ℕ) : ℤ) * t ^ 2) := by
        dsimp only [z']
        rw [show a = z ^ 2 - ((p ^ k : ℕ) : ℤ) * w by linarith [hw]]
        push_cast
        ring
      _ = ((p ^ k : ℕ) : ℤ) *
            ((p : ℤ) * c + (p : ℤ) * d * t ^ 2) := by
        rw [hc, hd]
      _ = ((p : ℤ) ^ k * (p : ℤ)) * (c + d * t ^ 2) := by
        push_cast
        ring

lemma isCoprime_two_mul_of_square_modEq_odd_prime
    {p : ℕ} {a z : ℤ} (hp : p.Prime) (hodd : p ≠ 2)
    (ha : IsCoprime a (p : ℤ))
    (h : a ≡ z ^ 2 [ZMOD (p : ℤ)]) :
    IsCoprime (2 * z) (p : ℤ) := by
  rw [Int.modEq_iff_dvd] at h
  obtain ⟨w, hw⟩ := h
  have hzsq : IsCoprime (z ^ 2) (p : ℤ) := by
    rw [show z ^ 2 = a + (p : ℤ) * w by linarith [hw]]
    exact ha.add_mul_left_left w
  have hz : IsCoprime z (p : ℤ) :=
    (IsCoprime.pow_left_iff (by decide : 0 < 2)).mp hzsq
  have hpnot : ¬p ∣ 2 := by
    intro hp2
    rcases (Nat.dvd_prime Nat.prime_two).mp hp2 with hp1 | hp2eq
    · exact hp.ne_one hp1
    · exact hodd hp2eq
  have h2nat : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    exact hpnot
  exact h2nat.isCoprime.mul_left hz

lemma exists_square_modEq_primePower
    {p e : ℕ} {a z : ℤ} (he : 0 < e)
    (hcop : IsCoprime (2 * z) (p : ℤ))
    (h : a ≡ z ^ 2 [ZMOD (p : ℤ)]) :
    ∃ z' : ℤ, IsCoprime (2 * z') (p : ℤ) ∧
      a ≡ z' ^ 2 [ZMOD ((p ^ e : ℕ) : ℤ)] := by
  induction e using Nat.case_strong_induction_on with
  | hz => omega
  | hi e ih =>
      by_cases he0 : e = 0
      · subst e
        exact ⟨z, hcop, by simpa using h⟩
      · have hepos : 0 < e := Nat.pos_of_ne_zero he0
        obtain ⟨z', hz'cop, hz'⟩ := ih e le_rfl hepos
        exact exists_square_modEq_primePower_succ hepos hz'cop hz'

lemma exists_square_modEq_primePower_of_odd_prime
    {p e : ℕ} {a z : ℤ} (hp : p.Prime) (hodd : p ≠ 2) (he : 0 < e)
    (ha : IsCoprime a (p : ℤ))
    (h : a ≡ z ^ 2 [ZMOD (p : ℤ)]) :
    ∃ z' : ℤ, a ≡ z' ^ 2 [ZMOD ((p ^ e : ℕ) : ℤ)] := by
  obtain ⟨z', _hz'cop, hz'⟩ := exists_square_modEq_primePower he
    (isCoprime_two_mul_of_square_modEq_odd_prime hp hodd ha h) h
  exact ⟨z', hz'⟩

end Erdos587
