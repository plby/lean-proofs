import ErdosProblems.Erdos633b.PythagoreanDescentTools

/-! Terminating descent excluding two primitive Pythagorean triples with one doubled leg. -/

namespace Erdos633b.PythagoreanDescent

structure PrimitivePair (a b : ℤ) : Prop where
  odd_first : a % 2 = 1
  positive_second : 0 < b
  coprime : IsCoprime a b
  first_square : IsSquare (a ^ 2 + b ^ 2)
  second_square : IsSquare (a ^ 2 + 4 * b ^ 2)

theorem PrimitivePair.neg_first (a b : ℤ) (h : PrimitivePair a b) : PrimitivePair (-a) b := by
  refine ⟨by have := h.odd_first; omega, h.positive_second, h.coprime.neg_left, ?_, ?_⟩
  · simpa using h.first_square
  · simpa using h.second_square

theorem PrimitivePair.sign_three (a b : ℤ) (h : PrimitivePair a b) :
    ∃ a' : ℤ, PrimitivePair a' b ∧ a' % 4 = 3 := by
  by_cases ha : a % 4 = 3
  · exact ⟨a, h, ha⟩
  · exact ⟨-a, h.neg_first a b, by have := h.odd_first; omega⟩

theorem step_at_three (a b : ℤ) (h : PrimitivePair a b) (ha : a % 4 = 3) :
    ∃ α δ : ℤ, PrimitivePair α δ ∧ δ < b := by
  obtain ⟨m, n, hm, hn, hmn, _, hnodd, heA, heB⟩ :=
    parameters a b ha h.positive_second h.coprime h.first_square
  have ha2 : IsCoprime a 2 := by
    rw [isCoprime_comm, Int.prime_two.coprime_iff_not_dvd]
    intro hd
    have hh := Int.emod_eq_zero_of_dvd hd
    have := h.odd_first
    omega
  have hs2 : IsSquare (a ^ 2 + (2 * b) ^ 2) := by
    convert h.second_square using 1; ring
  obtain ⟨k, l, hk, hl, _, hkeven, _, heA', heB'⟩ :=
    parameters a (2 * b) ha (by linarith [h.positive_second])
      (ha2.mul_right h.coprime) hs2
  obtain ⟨t, hkt⟩ := Int.dvd_of_emod_eq_zero hkeven
  have ht : 0 < t := by omega
  have hprod : n * m = l * t := by rw [hkt] at heB'; nlinarith [heB, heB']
  obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, hN, hM, hL, hT, hαδ, hβγ⟩ :=
    four_factors n m l t hn hm hl ht hmn.symm hprod
  have he : β ^ 2 * (α ^ 2 + 4 * δ ^ 2) = (α ^ 2 + δ ^ 2) * γ ^ 2 := by
    rw [hM, hN] at heA
    rw [hkt, hT, hL] at heA'
    linear_combination heA - heA'
  have hmatch := EulerDescent.reduced_cross_sign (β ^ 2) (γ ^ 2)
    (α ^ 2 + δ ^ 2) (α ^ 2 + 4 * δ ^ 2) hβγ.pow (two_sums_coprime α δ hαδ) he
  have hsq : IsSquare (α ^ 2 + δ ^ 2) ∧ IsSquare (α ^ 2 + 4 * δ ^ 2) := by
    rcases hmatch with ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact ⟨⟨β, by simpa [sq] using h1.symm⟩, ⟨γ, by simpa [sq] using h2.symm⟩⟩
    · nlinarith [sq_nonneg β, sq_nonneg α, sq_pos_of_pos hδ]
  have hαodd : α % 2 = 1 := odd_of_dvd_odd α n hnodd ⟨β, hN⟩
  have hδm : δ ≤ m := by nlinarith [hM]
  have hmb : m < b := by nlinarith [heB]
  exact ⟨α, δ, ⟨hαodd, hδ, hαδ, hsq.1, hsq.2⟩, hδm.trans_lt hmb⟩

theorem descent_step (a b : ℤ) (h : PrimitivePair a b) :
    ∃ α δ : ℤ, PrimitivePair α δ ∧ δ < b := by
  obtain ⟨a', h', ha'⟩ := h.sign_three a b
  exact step_at_three a' b h' ha'

/-- The doubled-leg obstruction, proved by a strict decrease of the positive second coordinate. -/
theorem no_primitive_pair (a b : ℤ) (h : PrimitivePair a b) : False := by
  have aux : ∀ N : ℕ, ∀ a b : ℤ, b.toNat = N → PrimitivePair a b → False := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro a b hb h
      obtain ⟨α, δ, hnew, hlt⟩ := descent_step a b h
      have hlt' : δ.toNat < N := by
        rw [← hb]
        exact (Int.toNat_lt_toNat h.positive_second).mpr hlt
      exact ih δ.toNat hlt' α δ rfl hnew
  exact aux b.toNat a b rfl h

end Erdos633b.PythagoreanDescent
