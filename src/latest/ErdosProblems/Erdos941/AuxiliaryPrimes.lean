import ErdosProblems.Erdos941.AnkenyLattice
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# Choosing the auxiliary primes for the three-square construction
-/

namespace Erdos941

theorem exists_prime_two_congruences {u v r s : ℕ} (hu : 0 < u) (hv : 0 < v)
    (huv : u.Coprime v) (hr : r.Coprime u) (hs : s.Coprime v) (B : ℕ) :
    ∃ q : ℕ, B < q ∧ q.Prime ∧ q ≡ r [MOD u] ∧ q ≡ s [MOD v] := by
  obtain ⟨w, hwu, hwv⟩ := Nat.chineseRemainder huv r s
  have hwu' : w.Coprime u := by
    change w.gcd u = 1
    rw [hwu.gcd_eq]
    exact hr
  have hwv' : w.Coprime v := by
    change w.gcd v = 1
    rw [hwv.gcd_eq]
    exact hs
  obtain ⟨q, hqB, hq, hqw⟩ := Nat.forall_exists_prime_gt_and_modEq B
    (Nat.mul_pos hu hv).ne' (hwu'.mul_right hwv')
  exact ⟨q, hqB, hq, ((Nat.ModEq.of_dvd (dvd_mul_right u v) hqw).trans hwu),
    ((Nat.ModEq.of_dvd (dvd_mul_left v u) hqw).trans hwv)⟩

theorem exists_prime_one_mod_four_neg_one {m : ℕ} (hm : 0 < m) (ho : Odd m) :
    ∃ q : ℕ, m < q ∧ q.Prime ∧ q % 4 = 1 ∧ (m : ℤ) ∣ (q : ℤ) + 1 := by
  have hfour : (4 : ℕ).Coprime m := by
    simpa using (Nat.coprime_two_left.mpr ho).pow_left 2
  have hsub : (m - 1).Coprime m :=
    (Nat.coprime_self_sub_left hm).mpr (Nat.coprime_one_left m)
  obtain ⟨q, hqm, hqp, hq4, hqm'⟩ := exists_prime_two_congruences
    (by norm_num : 0 < (4 : ℕ)) hm hfour (Nat.coprime_one_left 4) hsub m
  refine ⟨q, hqm, hqp, ?_, ?_⟩
  · change q % 4 = 1 % 4 at hq4
    exact hq4
  have hrem : q % m = (m - 1) % m := hqm'
  have hmod : (m - 1) % m = m - 1 := Nat.mod_eq_of_lt (by omega)
  rw [hmod] at hrem
  have hnat : m ∣ q + 1 := by
    refine ⟨q / m + 1, ?_⟩
    have hh := Nat.mod_add_div q m
    rw [hrem] at hh
    rw [Nat.mul_add, Nat.mul_one]
    omega
  exact_mod_cast hnat

theorem neg_square_mod_auxiliary_one {m q : ℕ} [Fact q.Prime]
    (hm4 : m % 4 = 1) (hq4 : q % 4 = 1) (hqm : (m : ℤ) ∣ (q : ℤ) + 1) :
    IsSquare (-((m : ℤ) : ZMod q)) := by
  have hmo : Odd m := Nat.odd_iff.mpr (by omega)
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have hmod : (q : ℤ) % m = (-1 : ℤ) % m := by
    apply Int.modEq_iff_dvd.mpr
    rw [show -1 - (q : ℤ) = -((q : ℤ) + 1) by ring]
    exact dvd_neg.mpr hqm
  have hj : jacobiSym (-(m : ℤ)) q = 1 := by
    rw [jacobiSym.neg _ hqo, ZMod.χ₄_nat_one_mod_four hq4, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four' hmo hq4,
      jacobiSym.mod_left' hmod, jacobiSym.at_neg_one hmo,
      ZMod.χ₄_nat_one_mod_four hm4]
  simpa only [Int.cast_neg] using ZMod.isSquare_of_jacobiSym_eq_one hj

theorem exists_int_root_neg {m q : ℕ} [Fact q.Prime]
    (h : IsSquare (-((m : ℤ) : ZMod q))) : ∃ b c : ℤ, (q : ℤ) * c = b ^ 2 + m := by
  obtain ⟨r, hr⟩ := h
  have hb : ((r.cast : ℤ) : ZMod q) ^ 2 + (m : ZMod q) = 0 := by
    rw [ZMod.intCast_zmod_cast, pow_two]
    have hh : r * r = -(m : ZMod q) := by
      simpa only [Int.cast_natCast] using hr.symm
    rw [hh]
    ring
  have hd : (q : ℤ) ∣ (r.cast : ℤ) ^ 2 + m := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
    simpa only [Int.cast_add, Int.cast_pow, Int.cast_natCast] using hb
  obtain ⟨c, hc⟩ := hd
  exact ⟨r.cast, c, hc.symm⟩

theorem prime_three_mod_four_not_dvd_aux {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hp3 : p % 4 = 3) (hq1 : q % 4 = 1) : ¬ p ∣ q := by
  intro hd
  rcases (Nat.dvd_prime hq).mp hd with h | h
  · exact hp.ne_one h
  · omega

theorem isCoprime_of_dvd_add_one {m q : ℤ} (h : m ∣ q + 1) :
    IsCoprime m q := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d, -1, ?_⟩
  linear_combination -hd

theorem auxiliary_neg_square {p q : ℕ} (h : (p : ℤ) ∣ (q : ℤ) + 1) :
    IsSquare (-(q : ZMod p)) := by
  have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) + 1) p).mpr h
  push_cast at hh
  refine ⟨1, ?_⟩
  linear_combination -hh

theorem three_squares_squarefree_one_mod_four {m : ℕ} (hm : 0 < m)
    (hsq : Squarefree m) (hm4 : m % 4 = 1) :
    ∃ X Y Z : ℤ, norm3 X Y Z = m := by
  have hmo : Odd m := Nat.odd_iff.mpr (by omega)
  obtain ⟨q, _, hq, hq4, hqm⟩ := exists_prime_one_mod_four_neg_one hm hmo
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨b, c, hc⟩ := exists_int_root_neg (neg_square_mod_auxiliary_one hm4 hq4 hqm)
  apply three_squares_of_ankeny_parameters hq.pos hm hsq hc
    (t := 1) (by simpa using hqm) (isCoprime_of_dvd_add_one hqm)
  intro p hp hp3
  refine ⟨prime_three_mod_four_not_dvd_aux hp hq hp3 hq4, ?_⟩
  intro hpm
  exact auxiliary_neg_square ((by exact_mod_cast hpm : (p : ℤ) ∣ m).trans hqm)

theorem exists_prime_one_mod_four_neg_two {m : ℕ} (hm : 2 ≤ m) (ho : Odd m) :
    ∃ q : ℕ, m < q ∧ q.Prime ∧ q % 4 = 1 ∧ (m : ℤ) ∣ (q : ℤ) + 2 := by
  have htwo := Nat.coprime_two_left.mpr ho
  have hfour : (4 : ℕ).Coprime m := by simpa using htwo.pow_left 2
  have hsub : (m - 2).Coprime m := (Nat.coprime_self_sub_left hm).mpr htwo
  obtain ⟨q, hqm, hqp, hq4, hqm'⟩ := exists_prime_two_congruences
    (by norm_num : 0 < (4 : ℕ)) (by omega : 0 < m) hfour
    (Nat.coprime_one_left 4) hsub m
  refine ⟨q, hqm, hqp, ?_, ?_⟩
  · change q % 4 = 1 % 4 at hq4
    exact hq4
  have hrem : q % m = (m - 2) % m := hqm'
  rw [Nat.mod_eq_of_lt (by omega : m - 2 < m)] at hrem
  have hnat : m ∣ q + 2 := by
    refine ⟨q / m + 1, ?_⟩
    have hh := Nat.mod_add_div q m
    rw [hrem] at hh
    rw [Nat.mul_add, Nat.mul_one]
    omega
  exact_mod_cast hnat

theorem neg_square_mod_auxiliary_three {m q : ℕ} [Fact q.Prime]
    (hm8 : m % 8 = 3) (hq4 : q % 4 = 1) (hqm : (m : ℤ) ∣ (q : ℤ) + 2) :
    IsSquare (-((m : ℤ) : ZMod q)) := by
  have hm2 : m % 2 = 1 := by omega
  have hmo : Odd m := Nat.odd_iff.mpr hm2
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  have hmod : (q : ℤ) % m = (-2 : ℤ) % m := by
    apply Int.modEq_iff_dvd.mpr
    rw [show -2 - (q : ℤ) = -((q : ℤ) + 2) by ring]
    exact dvd_neg.mpr hqm
  have hj : jacobiSym (-(m : ℤ)) q = 1 := by
    rw [jacobiSym.neg _ hqo, ZMod.χ₄_nat_one_mod_four hq4, one_mul,
      jacobiSym.quadratic_reciprocity_one_mod_four' hmo hq4,
      jacobiSym.mod_left' hmod, jacobiSym.at_neg_two hmo,
      ZMod.χ₈'_nat_eq_if_mod_eight]
    simp only [hm2, hm8, reduceCtorEq, or_true, ↓reduceIte]
  simpa only [Int.cast_neg] using ZMod.isSquare_of_jacobiSym_eq_one hj

private theorem sq_add_odd_even {b m : ℤ} (hb : b % 2 = 1) (hm : m % 2 = 1) :
    (2 : ℤ) ∣ b ^ 2 + m := by
  have hb' : (2 : ℤ) ∣ b - 1 := by omega
  obtain ⟨x, hx⟩ := hb'
  have hm' : (2 : ℤ) ∣ m - 1 := by omega
  obtain ⟨y, hy⟩ := hm'
  refine ⟨2 * x ^ 2 + 2 * x + y + 1, ?_⟩
  have hbval : b = 2 * x + 1 := by omega
  have hmval : m = 2 * y + 1 := by omega
  rw [hbval, hmval]
  ring

theorem exists_int_root_neg_twice {m q : ℕ} [Fact q.Prime] (hm : Odd m) (hq : Odd q)
    (h : IsSquare (-((m : ℤ) : ZMod q))) :
    ∃ b c : ℤ, (2 * q : ℕ) * c = b ^ 2 + m := by
  obtain ⟨b, c, hc⟩ := exists_int_root_neg h
  have hm2 : (m : ℤ) % 2 = 1 := by exact_mod_cast Nat.odd_iff.mp hm
  have hq2 : (q : ℤ) % 2 = 1 := by exact_mod_cast Nat.odd_iff.mp hq
  have h2q : IsCoprime (2 : ℤ) (q : ℤ) := by
    exact_mod_cast Nat.coprime_two_left.mpr hq
  have base : ∀ B : ℤ, B % 2 = 1 → (q : ℤ) ∣ B ^ 2 + m →
      ∃ b c : ℤ, (2 * q : ℕ) * c = b ^ 2 + m := by
    intro B hB hdiv
    obtain ⟨C, hC⟩ := h2q.mul_dvd (sq_add_odd_even hB hm2) hdiv
    refine ⟨B, C, ?_⟩
    simpa using hC.symm
  by_cases hb : b % 2 = 1
  · exact base b hb ⟨c, hc.symm⟩
  · apply base (b + q) (by omega)
    refine ⟨c + 2 * b + q, ?_⟩
    linear_combination -hc

theorem three_squares_squarefree_three_mod_eight {m : ℕ} (hm : 0 < m)
    (hsq : Squarefree m) (hm8 : m % 8 = 3) :
    ∃ X Y Z : ℤ, norm3 X Y Z = m := by
  have hmo : Odd m := Nat.odd_iff.mpr (by omega)
  obtain ⟨q, _, hq, hq4, hqm⟩ := exists_prime_one_mod_four_neg_two (by omega) hmo
  let : Fact q.Prime := ⟨hq⟩
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  obtain ⟨b, c, hc⟩ := exists_int_root_neg_twice hmo hqo
    (neg_square_mod_auxiliary_three hm8 hq4 hqm)
  let t : ℤ := ((m : ℤ) + 1) / 2
  have htwo : 2 * t = (m : ℤ) + 1 := by
    have hh : (m : ℤ) % 2 = 1 := by exact_mod_cast Nat.odd_iff.mp hmo
    dsimp [t]
    omega
  obtain ⟨d, hd⟩ := hqm
  have hm2 : IsCoprime (m : ℤ) (2 : ℤ) := by
    refine ⟨-1, t, ?_⟩
    linarith
  have hmq : IsCoprime (m : ℤ) (q : ℤ) := by
    refine ⟨d * t - 1, -t, ?_⟩
    linear_combination -t * hd + htwo
  have ht : (m : ℤ) ∣ ((2 * q : ℕ) : ℤ) * t ^ 2 + 1 := by
    refine ⟨2 * d * t ^ 2 - (m : ℤ) - 2, ?_⟩
    push_cast
    linear_combination 2 * t ^ 2 * hd - (2 * t + (m : ℤ) + 1) * htwo
  apply three_squares_of_ankeny_parameters (by omega) hm hsq hc ht
    (by simpa using hm2.mul_right hmq)
  intro p hp hp3
  refine ⟨?_, ?_⟩
  · intro hdiv
    rcases hp.dvd_mul.mp hdiv with h2 | hq'
    · have := Nat.le_of_dvd (by norm_num : 0 < (2 : ℕ)) h2
      omega
    · exact prime_three_mod_four_not_dvd_aux hp hq hp3 hq4 hq'
  · intro hpm
    have hdiv : (p : ℤ) ∣ (q : ℤ) + 2 :=
      (by exact_mod_cast hpm : (p : ℤ) ∣ m).trans ⟨d, hd⟩
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd ((q : ℤ) + 2) p).mpr hdiv
    push_cast at hh
    refine ⟨2, ?_⟩
    push_cast
    linear_combination -2 * hh

end Erdos941
