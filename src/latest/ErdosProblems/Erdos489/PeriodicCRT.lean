import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open scoped BigOperators

/-- Compatibility of two shifted divisibility conditions: every common divisor
of the two moduli, hence their gcd, divides the distance between the shifts. -/
theorem gcd_dvd_dist_of_dvd_add_shifts
    (a b n u v : ℕ) (ha : a ∣ n + u) (hb : b ∣ n + v) :
    Nat.gcd a b ∣ Nat.dist u v := by
  have hgu : Nat.gcd a b ∣ n + u :=
    dvd_trans (Nat.gcd_dvd_left a b) ha
  have hgv : Nat.gcd a b ∣ n + v :=
    dvd_trans (Nat.gcd_dvd_right a b) hb
  rcases le_total u v with huv | hvu
  · rw [Nat.dist_eq_sub_of_le huv]
    have h := Nat.dvd_sub hgv hgu
    simpa [Nat.add_sub_add_left] using h
  · rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hvu]
    have h := Nat.dvd_sub hgu hgv
    simpa [Nat.add_sub_add_left] using h

/-- Two shifted divisibility conditions have at most `gcd a b` solutions in a
product period of length `a*b`.

This is the endpoint-free finite-period CRT capacity needed for the periodic
version of the long-gap pair charge.  No coprimality or compatibility
assumption is required for the upper bound. -/
theorem card_shifted_pair_solutions_product_period_le_gcd
    (a b u v : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ((Finset.range (a * b)).filter
      (fun n => a ∣ n + u ∧ b ∣ n + v)).card ≤ Nat.gcd a b := by
  let S : Finset ℕ := (Finset.range (a * b)).filter
    (fun n => a ∣ n + u ∧ b ∣ n + v)
  let L := Nat.lcm a b
  have hL : 0 < L := Nat.lcm_pos ha hb
  have hordered : ∀ {n m : ℕ}, n ∈ S → m ∈ S → n ≤ m →
      n / L = m / L → n = m := by
    intro n m hn hm hnm hquot
    have hna : a ∣ n + u := (Finset.mem_filter.mp hn).2.1
    have hma : a ∣ m + u := (Finset.mem_filter.mp hm).2.1
    have hnb : b ∣ n + v := (Finset.mem_filter.mp hn).2.2
    have hmb : b ∣ m + v := (Finset.mem_filter.mp hm).2.2
    have hda : a ∣ m - n := by
      have h := Nat.dvd_sub hma hna
      simpa [Nat.add_sub_add_right] using h
    have hdb : b ∣ m - n := by
      have h := Nat.dvd_sub hmb hnb
      simpa [Nat.add_sub_add_right] using h
    have hdL : L ∣ m - n := Nat.lcm_dvd hda hdb
    have hnlow : L * (n / L) ≤ n := Nat.mul_div_le n L
    have hmup : m < L * (m / L + 1) := Nat.lt_mul_div_succ m hL
    rw [← hquot, Nat.mul_add] at hmup
    have hmdecomp : n + (m - n) = m := Nat.add_sub_of_le hnm
    have hdiff : m - n < L := by omega
    have hz : m - n = 0 := Nat.eq_zero_of_dvd_of_lt hdL hdiff
    omega
  have hinj : Set.InjOn (fun n : ℕ => n / L) (S : Set ℕ) := by
    intro n hn m hm hquot
    rcases le_total n m with hnm | hmn
    · exact hordered hn hm hnm hquot
    · exact (hordered hm hn hmn hquot.symm).symm
  have hcard_image : (S.image (fun n => n / L)).card = S.card :=
    Finset.card_image_iff.mpr hinj
  have himage : S.image (fun n => n / L) ⊆ Finset.range (Nat.gcd a b) := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨n, hn, rfl⟩
    have hnlt : n < a * b := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    have hab : L * Nat.gcd a b = a * b := Nat.lcm_mul_gcd a b
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hL).2
    rw [Nat.mul_comm, hab]
    exact hnlt
  change S.card ≤ Nat.gcd a b
  rw [← hcard_image]
  simpa using Finset.card_le_card himage

/-- The same shifted-pair capacity over any whole number `k` of product
periods.  This is the form used when the global finite-sieve period contains
`a*b` as a factor. -/
theorem card_shifted_pair_solutions_mul_product_period_le
    (a b u v k : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ((Finset.range (k * (a * b))).filter
      (fun n => a ∣ n + u ∧ b ∣ n + v)).card ≤
      k * Nat.gcd a b := by
  let p := a * b
  let S : Finset ℕ := (Finset.range p).filter
    (fun n => a ∣ n + u ∧ b ∣ n + v)
  let T : Finset ℕ := (Finset.range (k * p)).filter
    (fun n => a ∣ n + u ∧ b ∣ n + v)
  have hp : 0 < p := Nat.mul_pos ha hb
  let f : ℕ → ℕ × ℕ := fun n => (n / p, n % p)
  have hinj : Set.InjOn f (T : Set ℕ) := by
    intro n hn m hm hnm
    have hq : n / p = m / p := congrArg Prod.fst hnm
    have hr : n % p = m % p := congrArg Prod.snd hnm
    calc
      n = n % p + p * (n / p) := (Nat.mod_add_div n p).symm
      _ = m % p + p * (m / p) := by rw [hq, hr]
      _ = m := Nat.mod_add_div m p
  have himage : T.image f ⊆ Finset.range k ×ˢ S := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨n, hn, rfl⟩
    have hnrange : n < k * p :=
      Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    have hna : a ∣ n + u := (Finset.mem_filter.mp hn).2.1
    have hnb : b ∣ n + v := (Finset.mem_filter.mp hn).2.2
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_range.mpr
      exact (Nat.div_lt_iff_lt_mul hp).2 hnrange
    · change n % p ∈ S
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr (Nat.mod_lt n hp)
      · constructor
        · have hmul : a ∣ p * (n / p) := by
            exact dvd_mul_of_dvd_left (by simpa [p] using dvd_mul_right a b) _
          apply (Nat.dvd_add_iff_left hmul).mpr
          have hnrepr := Nat.mod_add_div n p
          rw [← hnrepr] at hna
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hna
        · have hmul : b ∣ p * (n / p) := by
            exact dvd_mul_of_dvd_left (by simpa [p, Nat.mul_comm] using dvd_mul_right b a) _
          apply (Nat.dvd_add_iff_left hmul).mpr
          have hnrepr := Nat.mod_add_div n p
          rw [← hnrepr] at hnb
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hnb
  have hcard_image : (T.image f).card = T.card :=
    Finset.card_image_iff.mpr hinj
  have hbase : S.card ≤ Nat.gcd a b := by
    simpa [S, p] using
      card_shifted_pair_solutions_product_period_le_gcd a b u v ha hb
  change T.card ≤ k * Nat.gcd a b
  rw [← hcard_image]
  calc
    (T.image f).card ≤ (Finset.range k ×ˢ S).card := Finset.card_le_card himage
    _ = k * S.card := by simp
    _ ≤ k * Nat.gcd a b := Nat.mul_le_mul_left k hbase

/-- If the shift distance is positive and at most `D`, compatibility converts
the product-period CRT capacity into the uniform bound `k*D`. -/
theorem card_shifted_pair_solutions_mul_product_period_le_distance_bound
    (a b u v k D : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hcompat : Nat.gcd a b ∣ Nat.dist u v)
    (hdpos : 0 < Nat.dist u v) (hdD : Nat.dist u v ≤ D) :
    ((Finset.range (k * (a * b))).filter
      (fun n => a ∣ n + u ∧ b ∣ n + v)).card ≤ k * D := by
  calc
    ((Finset.range (k * (a * b))).filter
      (fun n => a ∣ n + u ∧ b ∣ n + v)).card ≤
        k * Nat.gcd a b :=
      card_shifted_pair_solutions_mul_product_period_le a b u v k ha hb
    _ ≤ k * Nat.dist u v :=
      Nat.mul_le_mul_left k (Nat.le_of_dvd hdpos hcompat)
    _ ≤ k * D := Nat.mul_le_mul_left k hdD

end Erdos489
