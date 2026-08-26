/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.GILDivisorBounds

/-! # Smooth and rough divisibility on the GIL cofactor family -/

namespace Erdos822

open scoped BigOperators Classical
open Filter

theorem smoothPart_dvd_smoothPart_of_dvd {a b y : ℕ} (hb : b ≠ 0) (hab : a ∣ b) :
    smoothPart a y ∣ smoothPart b y := by
  have ha : a ≠ 0 := by
    intro ha
    subst a
    exact hb (by simpa using hab)
  apply (Nat.factorization_le_iff_dvd (smoothPart_ne_zero a y) (smoothPart_ne_zero b y)).mp
  rw [factorization_smoothPart, factorization_smoothPart]
  intro p
  simp only [smoothFactorization, Finsupp.filter_apply]
  split_ifs
  · exact (Nat.factorization_le_iff_dvd ha hb).mpr hab p
  · rfl

theorem roughPart_dvd_roughPart_of_dvd {a b y : ℕ} (hb : b ≠ 0) (hab : a ∣ b) :
    roughPart a y ∣ roughPart b y := by
  have ha : a ≠ 0 := by
    intro ha
    subst a
    exact hb (by simpa using hab)
  apply (Nat.factorization_le_iff_dvd (roughPart_ne_zero a y) (roughPart_ne_zero b y)).mp
  rw [factorization_roughPart, factorization_roughPart]
  intro p
  simp only [roughFactorization, Finsupp.filter_apply]
  split_ifs
  · exact (Nat.factorization_le_iff_dvd ha hb).mpr hab p
  · rfl

theorem gilCofactors_shifted_smoothPart_le {N S m : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (hy : 1 ≤ b1Cutoff N) (hm : m ∈ gilCofactors N S C) :
    smoothPart (shiftedTotient m) (b1Cutoff N) ≤ N := by
  rw [smoothPart_shiftedTotient_eq (oddRawCofactors_pos (gilCofactors_subset_oddRaw N S C hm))
    (gilCofactors_preserving hN hm)]
  exact (gilCofactors_smoothPart_le_natLog hN hy hm).trans (Nat.log_le_self 2 N)

theorem gilCofactors_divisor_le_mul_rough {N S m h : ℕ} {C : ℝ}
    (hN : 2 ≤ N) (hy : 1 ≤ b1Cutoff N) (hm : m ∈ gilCofactors N S C)
    (hh : h ∣ shiftedTotient m) : h ≤ N * roughPart h (b1Cutoff N) := by
  have hmpos := oddRawCofactors_pos (gilCofactors_subset_oddRaw N S C hm)
  have hsne : shiftedTotient m ≠ 0 := by dsimp [shiftedTotient]; omega
  have hhne : h ≠ 0 := by
    intro hh0
    subst h
    exact hsne (by simpa using hh)
  have hpart := smoothPart_dvd_smoothPart_of_dvd (y := b1Cutoff N) hsne hh
  have hle := (Nat.le_of_dvd (Nat.pos_of_ne_zero (smoothPart_ne_zero _ _)) hpart).trans
    (gilCofactors_shifted_smoothPart_le hN hy hm)
  calc
    h = smoothPart h (b1Cutoff N) * roughPart h (b1Cutoff N) := (smoothPart_mul_roughPart hhne).symm
    _ ≤ N * roughPart h (b1Cutoff N) := Nat.mul_le_mul_right _ hle

theorem eventually_gilCofactors_rough_divisors_card_le (S : ℕ) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ gilCofactors N S C,
      (roughPart (shiftedTotient m) (b1Cutoff N)).divisors.card ≤ N := by
  filter_upwards [eventually_five_pow_roughPart_primeFactors_card_le_nat] with N hN
  intro m hm
  have hmraw := gilCofactors_subset_oddRaw N S C hm
  have hmpos := oddRawCofactors_pos hmraw
  have hspos : 0 < shiftedTotient m := by dsimp [shiftedTotient]; omega
  have hsle := (shiftedTotient_le_two_mul m).trans
    (Nat.mul_le_mul_left 2 (oddRawCofactors_le_pow_twenty_eight hmraw))
  have hfive := hN (shiftedTotient m) hspos hsle
  have hsq := gilCofactors_roughDivisor_squarefree hm (dvd_refl (shiftedTotient m))
  have hsum := sum_divisors_four_pow_primeFactorsCard_eq_five_pow hsq
  have hcardNat : (roughPart (shiftedTotient m) (b1Cutoff N)).divisors.card ≤
      5 ^ (roughPart (shiftedTotient m) (b1Cutoff N)).primeFactors.card := by
    rw [← hsum]
    calc
      _ = ∑ _d ∈ (roughPart (shiftedTotient m) (b1Cutoff N)).divisors, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun d hd ↦ one_le_pow₀ (by norm_num)
  exact hcardNat.trans hfive

#print axioms eventually_gilCofactors_rough_divisors_card_le

end Erdos822
