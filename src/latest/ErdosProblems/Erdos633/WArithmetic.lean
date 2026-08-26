import ErdosProblems.Erdos633.WDescentStep

/-!
# The unconditional nonsquare obstruction for W

The descent is extended to nonprimitive pairs. If `b(a+b)` were a square,
the 120-degree cosine-law relation would give two Pythagorean triples with
one doubled leg, contradicting the descent.
-/

namespace Erdos633

theorem no_coprime_doubled_leg (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b)
    (h₁ : a ^ 2 + b ^ 2 = c ^ 2) (h₂ : a ^ 2 + (2 * b) ^ 2 = d ^ 2) : False := by
  rcases Nat.mod_two_eq_zero_or_one a with heven | hodd
  · have ha2 : 2 ∣ a := Nat.dvd_of_mod_eq_zero heven
    obtain ⟨a', haa⟩ := ha2
    have ha' : 0 < a' := by omega
    have hbodd : b % 2 = 1 := Nat.odd_iff.mp (Nat.coprime_two_right.mp
      (Nat.Coprime.of_dvd_right (show 2 ∣ a from ⟨a', haa⟩) hab.symm))
    have hba' : b.Coprime a' :=
      Nat.Coprime.of_dvd_right (show a' ∣ a from ⟨2, by omega⟩) hab.symm
    rw [haa] at h₁ h₂
    have hd2 : 2 ∣ d ^ 2 := by
      refine ⟨2 * (a' ^ 2 + b ^ 2), ?_⟩
      nlinarith only [h₂]
    have hd : 2 ∣ d := Nat.prime_two.dvd_of_dvd_pow hd2
    obtain ⟨d', hdd⟩ := hd
    rw [hdd] at h₂
    apply no_primitive_doubled_leg b a' d' c ha' hba' hbodd
    · nlinarith only [h₂]
    · nlinarith only [h₁]
  · exact no_primitive_doubled_leg a b c d hb hab hodd h₁ h₂

/-- No positive pair of Pythagorean triples can have one common leg and
another leg doubled. No gcd or parity assumption is imposed. -/
theorem no_doubled_leg_pythagorean_pair (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h₁ : a ^ 2 + b ^ 2 = c ^ 2) (h₂ : a ^ 2 + (2 * b) ^ 2 = d ^ 2) : False := by
  obtain ⟨A, B, hAB, haA, hbB⟩ := Nat.exists_coprime a b
  let g := Nat.gcd a b
  change a = A * g at haA
  change b = B * g at hbB
  have hg : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have hg0 := ne_of_gt hg
  have hA : 0 < A := by
    by_contra h
    have hz : A = 0 := by omega
    simp only [hz, zero_mul] at haA
    omega
  have hB : 0 < B := by
    by_contra h
    have hz : B = 0 := by omega
    simp only [hz, zero_mul] at hbB
    omega
  have hgc : g ∣ c := by
    apply (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
    refine ⟨A ^ 2 + B ^ 2, ?_⟩
    rw [← h₁, haA, hbB]
    ring
  have hgd : g ∣ d := by
    apply (Nat.pow_dvd_pow_iff (by decide : 2 ≠ 0)).mp
    refine ⟨A ^ 2 + (2 * B) ^ 2, ?_⟩
    rw [← h₂, haA, hbB]
    ring
  obtain ⟨C, hcC⟩ := hgc
  obtain ⟨D, hdD⟩ := hgd
  apply no_coprime_doubled_leg A B C D hA hB hAB
  · apply mul_left_cancel₀ (pow_ne_zero 2 hg0)
    calc
      g ^ 2 * (A ^ 2 + B ^ 2) = a ^ 2 + b ^ 2 := by rw [haA, hbB]; ring
      _ = c ^ 2 := h₁
      _ = g ^ 2 * C ^ 2 := by rw [hcC]; ring
  · apply mul_left_cancel₀ (pow_ne_zero 2 hg0)
    calc
      g ^ 2 * (A ^ 2 + (2 * B) ^ 2) = a ^ 2 + (2 * b) ^ 2 := by rw [haA, hbB]; ring
      _ = d ^ 2 := h₂
      _ = g ^ 2 * D ^ 2 := by rw [hdD]; ring

/-- The W count obstruction holds for every positive integer 120-degree
parameter triple, including nonprimitive ones. -/
theorem oneTwenty_W_numerator_not_isSquare (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    ¬ IsSquare (b * (a + b)) := by
  rintro ⟨d, hd⟩
  have hdpos : 0 < d := by
    have hprod : 0 < b * (a + b) := by positivity
    nlinarith only [hprod, hd]
  apply no_doubled_leg_pythagorean_pair a d c (a + 2 * b) ha hdpos
  · nlinarith only [h, hd]
  · nlinarith only [hd]

end Erdos633
