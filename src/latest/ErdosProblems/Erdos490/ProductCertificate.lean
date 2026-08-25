import Mathlib

namespace Erdos490

open Finset

noncomputable def primeReciprocalFactor (n : ℕ) : ℝ :=
  if n.Prime then (n : ℝ) / (n - 1) else 1

/-- A zero entry retains the integer's Euler factor. A nonzero entry must
certify compositeness by a proper divisor. Rounded products are upper bounds. -/
def roundedProductCertificate (n b : ℕ) : List ℕ → Option ℕ
  | [] => some b
  | d :: ds =>
      if d = 0 then
        roundedProductCertificate (n + 1) ((b * n + n - 2) / (n - 1)) ds
      else if 1 < d ∧ d < n ∧ d ∣ n then
        roundedProductCertificate (n + 1) b ds
      else none

lemma primeReciprocalFactor_nonneg (n : ℕ) : 0 ≤ primeReciprocalFactor n := by
  unfold primeReciprocalFactor
  split_ifs with hp
  · have hn : (1 : ℝ) < n := by exact_mod_cast hp.one_lt
    exact div_nonneg (Nat.cast_nonneg n) (by linarith)
  · norm_num

lemma primeReciprocalFactor_le {n : ℕ} (hn : 2 ≤ n) :
    primeReciprocalFactor n ≤ (n : ℝ) / (n - 1) := by
  unfold primeReciprocalFactor
  split_ifs
  · rfl
  · have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < n - 1)]
    norm_num

lemma le_rounded_product {n b : ℕ} (hn : 2 ≤ n) :
    (b : ℝ) * primeReciprocalFactor n ≤ ((b * n + n - 2) / (n - 1) : ℕ) := by
  have hd : 0 < n - 1 := by omega
  have hdiv : b * n ≤ ((b * n + n - 2) / (n - 1)) * (n - 1) := by
    have h := Nat.div_add_mod (b * n + n - 2) (n - 1)
    have hm := Nat.mod_lt (b * n + n - 2) hd
    rw [Nat.mul_comm (n - 1)] at h
    omega
  have hnR : (0 : ℝ) < (n : ℝ) - 1 := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  calc
    (b : ℝ) * primeReciprocalFactor n ≤ b * ((n : ℝ) / (n - 1)) :=
      mul_le_mul_of_nonneg_left (primeReciprocalFactor_le hn) (Nat.cast_nonneg b)
    _ ≤ ((b * n + n - 2) / (n - 1) : ℕ) := by
      rw [← mul_div_assoc, div_le_iff₀ hnR]
      have h := Nat.cast_le (α := ℝ).mpr hdiv
      push_cast [Nat.cast_sub (by omega : 1 ≤ n)] at h
      exact h

theorem roundedProductCertificate_sound {n b v : ℕ} {ds : List ℕ}
    (hn : 2 ≤ n) (h : roundedProductCertificate n b ds = some v) :
    (b : ℝ) * ∏ i ∈ Finset.range ds.length, primeReciprocalFactor (n + i) ≤ v := by
  induction ds generalizing n b v with
  | nil =>
    simp only [roundedProductCertificate, Option.some.injEq] at h
    subst v
    simp
  | cons d ds ih =>
    simp only [roundedProductCertificate] at h
    rw [List.length_cons, Finset.prod_range_succ']
    simp only [Nat.add_zero]
    have htail : 0 ≤ ∏ i ∈ Finset.range ds.length, primeReciprocalFactor (n + (i + 1)) :=
      Finset.prod_nonneg fun i _ => primeReciprocalFactor_nonneg _
    split_ifs at h with hd hcomp
    · have hi := ih (by omega : 2 ≤ n + 1) h
      have hstep := mul_le_mul_of_nonneg_right (le_rounded_product (b := b) hn) htail
      simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at hi hstep ⊢
      simpa [mul_assoc, mul_comm, mul_left_comm, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using hstep.trans hi
    · have hnp : ¬ n.Prime := by
        intro hp
        rcases (Nat.dvd_prime hp).mp hcomp.2.2 with h | h <;> omega
      simpa [primeReciprocalFactor, hnp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (by omega : 2 ≤ n + 1) h

noncomputable def reciprocalPrefix (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, primeReciprocalFactor (2 + i)

theorem certificate_prefix_step {scale : ℝ} {n b v : ℕ} {ds : List ℕ}
    (hprev : scale * reciprocalPrefix n ≤ b)
    (hcert : roundedProductCertificate (2 + n) b ds = some v) :
    scale * reciprocalPrefix (n + ds.length) ≤ v := by
  have hc := roundedProductCertificate_sound (by omega : 2 ≤ 2 + n) hcert
  unfold reciprocalPrefix at hprev ⊢
  rw [Finset.prod_range_add]
  have ht : 0 ≤ ∏ i ∈ Finset.range ds.length, primeReciprocalFactor (2 + (n + i)) :=
    Finset.prod_nonneg fun _ _ => primeReciprocalFactor_nonneg _
  calc
    _ = (scale * ∏ i ∈ Finset.range n, primeReciprocalFactor (2 + i)) *
        ∏ i ∈ Finset.range ds.length, primeReciprocalFactor (2 + (n + i)) := by ring
    _ ≤ (b : ℝ) * ∏ i ∈ Finset.range ds.length, primeReciprocalFactor (2 + (n + i)) :=
      mul_le_mul_of_nonneg_right hprev ht
    _ ≤ v := by simpa only [Nat.add_assoc] using hc

end Erdos490
