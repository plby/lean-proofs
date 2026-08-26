import ErdosProblems.Erdos941.AuxiliaryPrimes

/-! # The even squarefree case of the three-square construction -/

namespace Erdos941

theorem exists_prime_even_auxiliary {r : ℕ} (hr : 0 < r) (hro : Odd r) :
    ∃ q : ℕ, r < q ∧ q.Prime ∧ q % 8 = (if r % 4 = 1 then 1 else 5) ∧
      ((2 * r : ℕ) : ℤ) ∣ (q : ℤ) + 1 := by
  let k := if r % 4 = 1 then 1 else 5
  have hk : k.Coprime 8 := by
    dsimp [k]
    split <;> norm_num
  have h8r : (8 : ℕ).Coprime r := by
    simpa using (Nat.coprime_two_left.mpr hro).pow_left 3
  have hsub : (r - 1).Coprime r :=
    (Nat.coprime_self_sub_left hr).mpr (Nat.coprime_one_left r)
  obtain ⟨q, hqr, hqp, hq8, hqr'⟩ := exists_prime_two_congruences
    (by norm_num : 0 < (8 : ℕ)) hr h8r hk hsub r
  have hq8' : q % 8 = k := by
    change q % 8 = k % 8 at hq8
    have hk8 : k < 8 := by dsimp [k]; split <;> omega
    rwa [Nat.mod_eq_of_lt hk8] at hq8
  refine ⟨q, hqr, hqp, hq8', ?_⟩
  have hrdiv : r ∣ q + 1 := by
    refine ⟨q / r + 1, ?_⟩
    have hh := Nat.mod_add_div q r
    have hrem : q % r = (r - 1) % r := hqr'
    rw [hrem, Nat.mod_eq_of_lt (by omega : r - 1 < r)] at hh
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hqodd : q % 2 = 1 := by
    dsimp [k] at hq8'
    split at hq8' <;> omega
  have h2div : (2 : ℤ) ∣ (q : ℤ) + 1 := by
    have hh : (q : ℤ) % 2 = 1 := by exact_mod_cast hqodd
    omega
  have hc : IsCoprime (2 : ℤ) (r : ℤ) := by
    exact_mod_cast Nat.coprime_two_left.mpr hro
  have hh := hc.mul_dvd h2div (by exact_mod_cast hrdiv)
  simpa using hh

theorem neg_square_mod_auxiliary_even {r q : ℕ} [Fact q.Prime] (hro : Odd r)
    (hq8 : q % 8 = if r % 4 = 1 then 1 else 5)
    (hqr : (r : ℤ) ∣ (q : ℤ) + 1) : IsSquare (-(((2 * r : ℕ) : ℤ) : ZMod q)) := by
  have hq4 : q % 4 = 1 := by split at hq8 <;> omega
  have hq2 : q % 2 = 1 := by omega
  have hqo : Odd q := Nat.odd_iff.mpr hq2
  have hmod : (q : ℤ) % r = (-1 : ℤ) % r := by
    apply Int.modEq_iff_dvd.mpr
    rw [show -1 - (q : ℤ) = -((q : ℤ) + 1) by ring]
    exact dvd_neg.mpr hqr
  have hchi : ZMod.χ₈ q * ZMod.χ₄ r = 1 := by
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hro) with hr1 | hr3
    · have hq1 : q % 8 = 1 := by simpa only [hr1, ↓reduceIte] using hq8
      rw [ZMod.χ₄_nat_one_mod_four hr1, ZMod.χ₈_nat_eq_if_mod_eight]
      norm_num [hq2, hq1]
    · have hq5 : q % 8 = 5 := by simpa [hr3] using hq8
      rw [ZMod.χ₄_nat_three_mod_four hr3, ZMod.χ₈_nat_eq_if_mod_eight]
      norm_num [hq2, hq5]
  have hj : jacobiSym (-((2 * r : ℕ) : ℤ)) q = 1 := by
    rw [jacobiSym.neg _ hqo, ZMod.χ₄_nat_one_mod_four hq4, one_mul, Nat.cast_mul,
      Nat.cast_ofNat,
      jacobiSym.mul_left, jacobiSym.at_two hqo,
      jacobiSym.quadratic_reciprocity_one_mod_four' hro hq4,
      jacobiSym.mod_left' hmod, jacobiSym.at_neg_one hro]
    exact hchi
  simpa only [Int.cast_neg] using ZMod.isSquare_of_jacobiSym_eq_one hj

theorem three_squares_squarefree_even {m : ℕ} (hm : 0 < m) (hsq : Squarefree m)
    (heven : 2 ∣ m) : ∃ X Y Z : ℤ, norm3 X Y Z = m := by
  obtain ⟨r, rfl⟩ := heven
  have hr : 0 < r := by omega
  have hro : Odd r := Nat.coprime_two_left.mp (Nat.coprime_of_squarefree_mul hsq)
  obtain ⟨q, _, hq, hq8, hqm⟩ := exists_prime_even_auxiliary hr hro
  let : Fact q.Prime := ⟨hq⟩
  have hq4 : q % 4 = 1 := by split at hq8 <;> omega
  have hqr : (r : ℤ) ∣ (q : ℤ) + 1 :=
    (by exact_mod_cast dvd_mul_left r 2 : (r : ℤ) ∣ ((2 * r : ℕ) : ℤ)).trans hqm
  obtain ⟨b, c, hc⟩ := exists_int_root_neg (neg_square_mod_auxiliary_even hro hq8 hqr)
  apply three_squares_of_ankeny_parameters hq.pos hm hsq hc
    (t := 1) (by simpa using hqm) (isCoprime_of_dvd_add_one hqm)
  intro p hp hp3
  refine ⟨prime_three_mod_four_not_dvd_aux hp hq hp3 hq4, ?_⟩
  intro hpm
  exact auxiliary_neg_square ((by exact_mod_cast hpm : (p : ℤ) ∣ (2 * r : ℕ)).trans hqm)

end Erdos941
