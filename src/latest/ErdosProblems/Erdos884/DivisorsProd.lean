/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Licensed under the Apache License, Version 2.0; see LICENSE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 884.
Informal proof: Daniel Larsen, building on Terence Tao's construction.
Formal proof: Claude Fable 5, with minor guidance from R. J. Honicky.
Source: https://www.erdosproblems.com/884#post-7362
https://github.com/honicky/erdos884/tree/323e9a01306df1e094b434beaa48c018370fe258
Original Lean/Mathlib version: 4.31.0.
Original Mathlib commit: fabf563a7c95a166b8d7b6efca11c8b4dc9d911f.
The port reuses the repository's existing PNT+ Selberg sieve by Arend Mellendijk.
-/
import ErdosProblems.Erdos884.Prelude

open Function

set_option linter.mathlibStandardSet false

/-
  DivisorsProd884.lean — divisors of products of distinct primes,
  for the formalization of Larsen's disproof of Erdős problem #884.

  Exports:
    primeFactors_prodPrimes, squarefree_prodPrimes, divisors_prodPrimes,
    prodPrimes_injOn, card_divisors_prodPrimes,
    sum_inv_divisors_erase_one_le, sum_inv_divisors_le,
    prod_gcd_of_dvd_prod, card_primeFactors_eq_sum_gcd
-/

namespace Erdos884

theorem primeFactors_prodPrimes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, p).primeFactors = s :=
  Nat.primeFactors_prod hs

theorem squarefree_prodPrimes {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  refine Nat.squarefree_iff_prime_squarefree.mpr ?_
  intro p hp h_dvd
  by_cases hps : p ∈ s
  · rw [← Finset.mul_prod_erase s (fun p => p) hps,
      mul_dvd_mul_iff_left hp.ne_zero] at h_dvd
    obtain ⟨q, hq, hpq⟩ := hp.prime.exists_mem_finset_dvd h_dvd
    rw [Finset.mem_erase] at hq
    exact hq.1 ((Nat.prime_dvd_prime_iff_eq hp (hs q hq.2)).mp hpq).symm
  · obtain ⟨q, hq, hpq⟩ := hp.prime.exists_mem_finset_dvd ((dvd_mul_right p p).trans h_dvd)
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hs q hq)).mp hpq
    subst heq
    exact hps hq

theorem divisors_prodPrimes {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) :
    (∏ p ∈ B, p).divisors = B.powerset.image fun s => ∏ p ∈ s, p := by
  have hP0 : (∏ p ∈ B, p) ≠ 0 :=
    (Finset.prod_pos fun p hp => (hB p hp).pos).ne'
  ext d
  simp only [Nat.mem_divisors, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨hd, -⟩
    refine ⟨d.primeFactors, ?_, ?_⟩
    · calc d.primeFactors
          ⊆ (∏ p ∈ B, p).primeFactors := Nat.primeFactors_mono hd hP0
        _ = B := Nat.primeFactors_prod hB
    · exact Nat.prod_primeFactors_of_squarefree
        (Squarefree.squarefree_of_dvd hd (squarefree_prodPrimes hB))
  · rintro ⟨s, hs, rfl⟩
    exact ⟨Finset.prod_dvd_prod_of_subset s B (fun p => p) hs, hP0⟩

theorem prodPrimes_injOn {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) :
    Set.InjOn (fun s : Finset ℕ => ∏ p ∈ s, p) B.powerset := by
  intro s hs t ht hst
  have hs' : s ⊆ B := Finset.mem_powerset.mp (Finset.mem_coe.mp hs)
  have ht' : t ⊆ B := Finset.mem_powerset.mp (Finset.mem_coe.mp ht)
  have h1 : (∏ p ∈ s, p).primeFactors = s :=
    Nat.primeFactors_prod fun p hp => hB p (hs' hp)
  have h2 : (∏ p ∈ t, p).primeFactors = t :=
    Nat.primeFactors_prod fun p hp => hB p (ht' hp)
  have hst' : ∏ p ∈ s, p = ∏ p ∈ t, p := hst
  rw [← h1, ← h2, hst']

theorem card_divisors_prodPrimes {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) :
    (∏ p ∈ B, p).divisors.card = 2 ^ B.card := by
  rw [divisors_prodPrimes hB, Finset.card_image_of_injOn (prodPrimes_injOn hB),
    Finset.card_powerset]

/-! ### Bounding the sum of inverses of divisors -/

/-- If `0 ≤ u` and `2Ku ≤ 1` then `(1+u)^K ≤ 1 + 2Ku`. -/
lemma one_add_pow_le_aux {u : ℝ} (hu : 0 ≤ u) :
    ∀ K : ℕ, 2 * K * u ≤ 1 → (1 + u) ^ K ≤ 1 + 2 * K * u := by
  intro K
  induction K with
  | zero => intro _; norm_num
  | succ K ih =>
    intro hK1
    push_cast at hK1 ⊢
    have h2K : 2 * (K : ℝ) * u ≤ 1 := by
      have hstep : 2 * (K : ℝ) * u ≤ 2 * ((K : ℝ) + 1) * u :=
        mul_le_mul_of_nonneg_right (by linarith) hu
      linarith
    have h1u : (0 : ℝ) ≤ 1 + u := by linarith
    have hKuu : 2 * (K : ℝ) * u * u ≤ 1 * u := mul_le_mul_of_nonneg_right h2K hu
    calc (1 + u) ^ (K + 1) = (1 + u) ^ K * (1 + u) := pow_succ _ _
      _ ≤ (1 + 2 * (K : ℝ) * u) * (1 + u) := mul_le_mul_of_nonneg_right (ih h2K) h1u
      _ = 1 + 2 * (K : ℝ) * u + u + 2 * (K : ℝ) * u * u := by ring
      _ ≤ 1 + 2 * ((K : ℝ) + 1) * u := by linarith

theorem sum_inv_divisors_le {B : Finset ℕ} {x₀ : ℕ} (hB : ∀ p ∈ B, p.Prime)
    (hlow : ∀ p ∈ B, x₀ ≤ p) (hx₀ : 2 * B.card ≤ x₀) (h0 : 0 < x₀) :
    ∑ d ∈ (∏ p ∈ B, p).divisors, ((d:ℝ))⁻¹ ≤ 1 + 2 * B.card / x₀ := by
  have hx0R : (0 : ℝ) < (x₀ : ℝ) := by exact_mod_cast h0
  have hcardle : 2 * (B.card : ℝ) * ((x₀ : ℝ))⁻¹ ≤ 1 := by
    have h1 : 2 * (B.card : ℝ) ≤ (x₀ : ℝ) := by exact_mod_cast hx₀
    have h2 : 2 * (B.card : ℝ) * ((x₀ : ℝ))⁻¹ ≤ (x₀ : ℝ) * ((x₀ : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    rwa [mul_inv_cancel₀ hx0R.ne'] at h2
  rw [divisors_prodPrimes hB, Finset.sum_image (prodPrimes_injOn hB)]
  calc ∑ s ∈ B.powerset, (((∏ p ∈ s, p : ℕ) : ℝ))⁻¹
      = ∑ s ∈ B.powerset, ∏ p ∈ s, ((p : ℝ))⁻¹ := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Nat.cast_prod]
        exact (Finset.prod_inv_distrib _).symm
    _ = ∏ p ∈ B, (1 + ((p : ℝ))⁻¹) := (Finset.prod_one_add B).symm
    _ ≤ (1 + ((x₀ : ℝ))⁻¹) ^ B.card := by
        rw [← Finset.prod_const]
        refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
        have hxp : (x₀ : ℝ) ≤ (p : ℝ) := by exact_mod_cast hlow p hp
        have hinv := inv_anti₀ hx0R hxp
        linarith
    _ ≤ 1 + 2 * (B.card : ℝ) * ((x₀ : ℝ))⁻¹ :=
        one_add_pow_le_aux (by positivity) B.card hcardle
    _ = 1 + 2 * (B.card : ℝ) / (x₀ : ℝ) := by rw [div_eq_mul_inv]

theorem sum_inv_divisors_erase_one_le {B : Finset ℕ} {x₀ : ℕ} (hB : ∀ p ∈ B, p.Prime)
    (hlow : ∀ p ∈ B, x₀ ≤ p) (hx₀ : 2 * B.card ≤ x₀) (h0 : 0 < x₀) :
    ∑ d ∈ (∏ p ∈ B, p).divisors.erase 1, ((d:ℝ))⁻¹ ≤ 2 * B.card / x₀ := by
  have hP0 : (∏ p ∈ B, p) ≠ 0 :=
    (Finset.prod_pos fun p hp => (hB p hp).pos).ne'
  have h1mem : 1 ∈ (∏ p ∈ B, p).divisors := Nat.one_mem_divisors.mpr hP0
  have hsplit := Finset.add_sum_erase (∏ p ∈ B, p).divisors
    (fun d => ((d : ℝ))⁻¹) h1mem
  have hsum := sum_inv_divisors_le hB hlow hx₀ h0
  rw [← hsplit] at hsum
  norm_num at hsum
  linarith

/-! ### Divisors of products of pairwise coprime numbers -/

/-- If the members of `t` are pairwise coprime under `f`, and `a ∉ t` is such that
`Finset.cons a t` is still pairwise coprime, then `f a` is coprime to `∏ i ∈ t, f i`. -/
private lemma coprime_prod_of_pairwise_cons {ι : Type*} {f : ι → ℕ} {a : ι} {t : Finset ι}
    (ha : a ∉ t) (h : (↑(Finset.cons a t ha) : Set ι).Pairwise (Nat.Coprime on f)) :
    Nat.Coprime (f a) (∏ i ∈ t, f i) := by
  refine Nat.Coprime.prod_right fun i hi => ?_
  have hne : a ≠ i := by rintro rfl; exact ha hi
  have hma : a ∈ (↑(Finset.cons a t ha) : Set ι) := by
    rw [Finset.coe_cons]; exact Set.mem_insert _ _
  have hmi : i ∈ (↑(Finset.cons a t ha) : Set ι) := by
    rw [Finset.coe_cons]; exact Set.mem_insert_of_mem _ (Finset.mem_coe.mpr hi)
  exact h hma hmi hne

private lemma gcd_prod_eq_prod_gcd {ι : Type*} (d : ℕ) {m : ι → ℕ} (t : Finset ι) :
    (↑t : Set ι).Pairwise (Nat.Coprime on m) →
      Nat.gcd d (∏ i ∈ t, m i) = ∏ i ∈ t, Nat.gcd d (m i) := by
  induction t using Finset.cons_induction with
  | empty => intro _; simp
  | cons a t ha ih =>
    intro h
    have hsub : (↑t : Set ι) ⊆ ↑(Finset.cons a t ha) := by
      rw [Finset.coe_cons]; exact Set.subset_insert _ _
    have hcop : Nat.Coprime (m a) (∏ i ∈ t, m i) := coprime_prod_of_pairwise_cons ha h
    rw [Finset.prod_cons ha, Finset.prod_cons ha, Nat.Coprime.gcd_mul d hcop,
      ih (h.mono hsub)]

private lemma card_primeFactors_prod {ι : Type*} {f : ι → ℕ} (t : Finset ι) :
    (∀ i ∈ t, f i ≠ 0) → (↑t : Set ι).Pairwise (Nat.Coprime on f) →
      (∏ i ∈ t, f i).primeFactors.card = ∑ i ∈ t, (f i).primeFactors.card := by
  induction t using Finset.cons_induction with
  | empty => intro _ _; simp
  | cons a t ha ih =>
    intro h0 h
    have hsub : (↑t : Set ι) ⊆ ↑(Finset.cons a t ha) := by
      rw [Finset.coe_cons]; exact Set.subset_insert _ _
    have ha0 : f a ≠ 0 := h0 a (Finset.mem_cons_self a t)
    have ht0 : ∀ i ∈ t, f i ≠ 0 := fun i hi => h0 i (Finset.mem_cons_of_mem hi)
    have hprod0 : (∏ i ∈ t, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr ht0
    have hcop : Nat.Coprime (f a) (∏ i ∈ t, f i) := coprime_prod_of_pairwise_cons ha h
    rw [Finset.prod_cons ha, Finset.sum_cons ha, Nat.primeFactors_mul ha0 hprod0,
      Finset.card_union_of_disjoint hcop.disjoint_primeFactors, ih ht0 (h.mono hsub)]

theorem prod_gcd_of_dvd_prod {r : ℕ} {m : Fin r → ℕ}
    (hcop : Pairwise (Nat.Coprime on m)) {d : ℕ} (hd : d ∣ ∏ i, m i) :
    d = ∏ i, Nat.gcd d (m i) := by
  have hpw : (↑(Finset.univ : Finset (Fin r)) : Set (Fin r)).Pairwise (Nat.Coprime on m) :=
    fun i _ j _ hij => hcop hij
  calc d = Nat.gcd d (∏ i, m i) := (Nat.gcd_eq_left hd).symm
    _ = ∏ i, Nat.gcd d (m i) := gcd_prod_eq_prod_gcd d Finset.univ hpw

theorem card_primeFactors_eq_sum_gcd {r : ℕ} {m : Fin r → ℕ} (hm : ∀ i, m i ≠ 0)
    (hcop : Pairwise (Nat.Coprime on m)) {d : ℕ} (hd : d ∣ ∏ i, m i) :
    d.primeFactors.card = ∑ i, (Nat.gcd d (m i)).primeFactors.card := by
  have hg0 : ∀ i ∈ (Finset.univ : Finset (Fin r)), Nat.gcd d (m i) ≠ 0 := by
    intro i _ hzero
    exact hm i (Nat.gcd_eq_zero_iff.mp hzero).2
  have hgcop : (↑(Finset.univ : Finset (Fin r)) : Set (Fin r)).Pairwise
      (Nat.Coprime on fun i => Nat.gcd d (m i)) := by
    intro i _ j _ hij
    have h1 : (m i).Coprime (m j) := hcop hij
    exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right d (m i))
      (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right d (m j)) h1)
  conv_lhs => rw [prod_gcd_of_dvd_prod hcop hd]
  exact card_primeFactors_prod Finset.univ hg0 hgcop

end Erdos884
