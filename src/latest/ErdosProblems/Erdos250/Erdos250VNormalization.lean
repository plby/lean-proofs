import ErdosProblems.Erdos250.Erdos250RatFrac
import ErdosProblems.Erdos250.Erdos250Arithmetic
import ErdosProblems.Erdos250.Erdos250ZV

open scoped BigOperators

namespace VNormalization

open DoublePartialFraction.OldRational
open Erdos250Arithmetic

lemma erased_range_eq_union {n k : ℕ} (hk : k ≤ n) :
    (Finset.range (n + 1)).erase k =
      Finset.range k ∪ Finset.Icc (k + 1) n := by
  ext j
  simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Icc]
  omega

lemma lower_factor {k j : ℕ} (hj : j < k) :
    (1 - root k / root j) ^ 2 =
      ((oddFactor (k - j) : ℕ) : ℚ) ^ 2 := by
  have he : (j + 1) + (k - j) = k + 1 := by omega
  have hr : root k / root j = (2 : ℚ) ^ (k - j) := by
    rw [root, root]
    calc
      (2 : ℚ) ^ (k + 1) / (2 : ℚ) ^ (j + 1) =
          ((2 : ℚ) ^ (j + 1) * (2 : ℚ) ^ (k - j)) /
            (2 : ℚ) ^ (j + 1) := by rw [← pow_add, he]
      _ = (2 : ℚ) ^ (k - j) := by field_simp
  rw [hr]
  simp only [oddFactor]
  have hp : 1 ≤ 2 ^ (k - j) := one_le_pow₀ (by omega)
  rw [Nat.cast_sub hp]
  push_cast
  ring

lemma lower_product (k : ℕ) :
    (∏ j ∈ Finset.range k, (1 - root k / root j) ^ 2) =
      (denProd k : ℚ) ^ 2 := by
  calc
    _ = ∏ j ∈ Finset.range k, (((oddFactor (k - j) : ℕ) : ℚ) ^ 2) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact lower_factor (Finset.mem_range.mp hj)
    _ = ∏ d ∈ Finset.Icc 1 k, (((oddFactor d : ℕ) : ℚ) ^ 2) := by
      simpa only using
        (ZV.prod_range_reverse_Icc (fun d ↦ (((oddFactor d : ℕ) : ℚ) ^ 2)) k)
    _ = (denProd k : ℚ) ^ 2 := by
      simp only [denProd, Nat.cast_prod, Finset.prod_pow]

lemma upper_factor {k j : ℕ} (hkj : k < j) :
    (1 - root k / root j) ^ 2 =
      (((oddFactor (j - k) : ℕ) : ℚ) ^ 2) /
        (2 : ℚ) ^ (2 * (j - k)) := by
  have he : (k + 1) + (j - k) = j + 1 := by omega
  have hpow : (2 : ℚ) ^ (j + 1) =
      (2 : ℚ) ^ (k + 1) * (2 : ℚ) ^ (j - k) := by
    rw [← pow_add, he]
  have hr : root k / root j = 1 / (2 : ℚ) ^ (j - k) := by
    rw [root, root, hpow]
    field_simp
  rw [hr]
  simp only [oddFactor]
  have hp : 1 ≤ 2 ^ (j - k) := one_le_pow₀ (by omega)
  rw [Nat.cast_sub hp]
  push_cast
  have hpow2 : (2 : ℚ) ^ (2 * (j - k)) = ((2 : ℚ) ^ (j - k)) ^ 2 := by
    rw [show 2 * (j - k) = (j - k) + (j - k) by omega, pow_add, pow_two]
  rw [hpow2]
  field_simp [pow_ne_zero]

lemma prod_Icc_sub {M : Type*} [CommMonoid M] (f : ℕ → M) (n k : ℕ)
    (hk : k ≤ n) :
    ∏ j ∈ Finset.Icc (k + 1) n, f (j - k) =
      ∏ d ∈ Finset.Icc 1 (n - k), f d := by
  apply Finset.prod_bij (fun j _hj ↦ j - k)
  · intro j hj
    simp only [Finset.mem_Icc] at hj ⊢
    omega
  · intro j₁ hj₁ j₂ hj₂ heq
    simp only [Finset.mem_Icc] at hj₁ hj₂
    omega
  · intro d hd
    simp only [Finset.mem_Icc] at hd
    refine ⟨d + k, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro j hj
    rfl

lemma sum_Icc_id (m : ℕ) :
    ∑ d ∈ Finset.Icc 1 m, d = m * (m + 1) / 2 := by
  have hs : ∑ d ∈ Finset.Icc 1 m, d = ∑ d ∈ Finset.range (m + 1), d := by
    apply Finset.sum_subset
    · intro d hd
      simp only [Finset.mem_Icc, Finset.mem_range] at hd ⊢
      omega
    · intro d hd hnot
      simp only [Finset.mem_range] at hd
      simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
      have : d = 0 := by omega
      simp [this]
  rw [hs]
  simpa [Nat.mul_comm] using (Finset.sum_range_id (n := m + 1))

lemma sum_Icc_twice (m : ℕ) :
    ∑ d ∈ Finset.Icc 1 m, 2 * d = m * (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih]
      ring

lemma upper_product {n k : ℕ} (hk : k ≤ n) :
    (∏ j ∈ Finset.Icc (k + 1) n, (1 - root k / root j) ^ 2) =
      (denProd (n - k) : ℚ) ^ 2 /
        (2 : ℚ) ^ ((n - k) * (n - k + 1)) := by
  calc
    _ = ∏ j ∈ Finset.Icc (k + 1) n,
        (((oddFactor (j - k) : ℕ) : ℚ) ^ 2 /
          (2 : ℚ) ^ (2 * (j - k))) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hj' := Finset.mem_Icc.mp hj
      exact upper_factor (by omega : k < j)
    _ = ∏ d ∈ Finset.Icc 1 (n - k),
        (((oddFactor d : ℕ) : ℚ) ^ 2 / (2 : ℚ) ^ (2 * d)) := by
      simpa only using
        (prod_Icc_sub
          (fun d ↦ (((oddFactor d : ℕ) : ℚ) ^ 2 / (2 : ℚ) ^ (2 * d))) n k hk)
    _ = (∏ d ∈ Finset.Icc 1 (n - k), (((oddFactor d : ℕ) : ℚ) ^ 2)) /
        (∏ d ∈ Finset.Icc 1 (n - k), (2 : ℚ) ^ (2 * d)) := by
      rw [Finset.prod_div_distrib]
    _ = (denProd (n - k) : ℚ) ^ 2 /
        (2 : ℚ) ^ (∑ d ∈ Finset.Icc 1 (n - k), 2 * d) := by
      congr 1
      · simp only [denProd, Nat.cast_prod, Finset.prod_pow]
      · rw [Finset.prod_pow_eq_pow_sum]
    _ = _ := by
      congr 2
      rw [sum_Icc_twice]

lemma denominator_product {n k : ℕ} (hk : k ≤ n) :
    (∏ j ∈ (Finset.range (n + 1)).erase k,
        (1 - root k / root j) ^ 2) =
      (denProd k : ℚ) ^ 2 * (denProd (n - k) : ℚ) ^ 2 /
        (2 : ℚ) ^ ((n - k) * (n - k + 1)) := by
  rw [erased_range_eq_union hk, Finset.prod_union]
  · rw [lower_product, upper_product hk]
    ring
  · exact Finset.disjoint_left.mpr fun j hj₁ hj₂ ↦ by
      simp only [Finset.mem_range] at hj₁
      simp only [Finset.mem_Icc] at hj₂
      omega

def lambda (n : ℕ) : ℚ :=
  (-1 : ℚ) ^ n * (denProd n : ℚ) /
    (2 : ℚ) ^ (n ^ 2 + 2 * n + 1)

theorem lambda_root_mul_vCoeff_eq_cCoeff {n k : ℕ} (hk : k ≤ n) :
    lambda n * root k * vCoeff n k = cCoeff n k := by
  rw [lambda, vCoeff_eq_products, ZV.numerator_prod_closed, denominator_product hk]
  simp only [cCoeff]
  push_cast
  have hdk : (denProd k : ℚ) ≠ 0 := by exact_mod_cast (ZV.denProd_pos k).ne'
  have hdnk : (denProd (n - k) : ℚ) ≠ 0 := by
    exact_mod_cast (ZV.denProd_pos (n - k)).ne'
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  have hgauss :
      (denProd n : ℚ) * (highProd k n : ℚ) =
        ((gauss2 n k : ℚ) ^ 2 * (gauss2 (n + k) k : ℚ)) *
          ((denProd k : ℚ) ^ 2 * (denProd (n - k) : ℚ) ^ 2) := by
    have h := ZV.gaussian_odd_identity hk
    field_simp [hdk, hdnk] at h
    nlinarith
  field_simp [root, hdk, hdnk, h2]
  have hsign : ((-1 : ℚ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  rw [hsign, one_mul]
  have hpower :
      root k * root k ^ n *
          (2 : ℚ) ^ ((n - k) * (n - k + 1)) *
          (2 : ℚ) ^ (k * (n - k)) =
        (2 : ℚ) ^ (n ^ 2 + 2 * n + 1) := by
    rw [root, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    have hn : n = k + (n - k) := by omega
    rw [hn]
    simp only [Nat.add_sub_cancel_left]
    ring
  calc
    (denProd n : ℚ) * root k * root k ^ n * (highProd k n : ℚ) *
          (2 : ℚ) ^ ((n - k) * (n - k + 1)) *
          (2 : ℚ) ^ (k * (n - k)) =
        ((denProd n : ℚ) * (highProd k n : ℚ)) *
          (root k * root k ^ n *
            (2 : ℚ) ^ ((n - k) * (n - k + 1)) *
            (2 : ℚ) ^ (k * (n - k))) := by ring
    _ = (((gauss2 n k : ℚ) ^ 2 * (gauss2 (n + k) k : ℚ)) *
          ((denProd k : ℚ) ^ 2 * (denProd (n - k) : ℚ) ^ 2)) *
          (root k * root k ^ n *
            (2 : ℚ) ^ ((n - k) * (n - k + 1)) *
            (2 : ℚ) ^ (k * (n - k))) := by rw [hgauss]
    _ = (2 : ℚ) ^ (n ^ 2 + 2 * n + 1) * (denProd k : ℚ) ^ 2 *
          (denProd (n - k) : ℚ) ^ 2 * (gauss2 n k : ℚ) ^ 2 *
          (gauss2 (n + k) k : ℚ) := by rw [hpower]; ring

end VNormalization
