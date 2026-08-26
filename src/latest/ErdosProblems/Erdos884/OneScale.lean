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
import ErdosProblems.Erdos884.PairCount

set_option linter.mathlibStandardSet false

/-!
# Erdős 884 — one-scale gap-sum bounds (Lemmas G/H/I of the blueprint)

For a window `B` of `K` primes in `(x₀, x₀+H]` with pairwise gaps `> N`, and
`m := ∏ p ∈ B, p`, we bound the gap sum of `m.divisors` by classifying the
consecutive divisor pairs `(a, b)` by `(ω a, ω b)`:

* both prime (class 1): `oneScale_primePart_le`   — bound `K/N`;
* `2 ≤ ω a = ω b` (class 2): `oneScale_sameCard_le` — bound `2K(1+log K)/N² + 2·4^K/x₀`;
* `ω a ≠ ω b` (class 3): `oneScale_diffCard_le`   — bound `2^(K+3)·K/x₀`;
* the trichotomy glue: `oneScale_gapSum_le`.

All internal helpers are prefixed `os_`.
-/

namespace Erdos884

/-! ### Generic extraction lemma for `pairSumOn` bounds -/

/-- To bound `pairSumOn A C`, it suffices to bound `∑ invGap` over an arbitrary finite set of
pairs each of which lies in `A ×ˢ A`, is increasing, and satisfies `C`. -/
lemma os_pairSumOn_le_of_forall {A : Finset ℕ} {C : ℕ → ℕ → Prop} {r : ℝ}
    (h : ∀ S : Finset (ℕ × ℕ),
      (∀ p ∈ S, p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 < p.2 ∧ C p.1 p.2) →
      ∑ p ∈ S, invGap p.1 p.2 ≤ r) :
    pairSumOn A C ≤ r := by
  have memf : ∀ {q : ℕ × ℕ → Prop} {inst : DecidablePred q} {s : Finset (ℕ × ℕ)} {x : ℕ × ℕ},
      x ∈ @Finset.filter _ q inst s ↔ x ∈ s ∧ q x := by
    intro q inst s x
    let := inst
    exact Finset.mem_filter
  unfold pairSumOn
  refine h _ fun p hp => ?_
  have hp' := memf.mp hp
  have hpq := Finset.mem_product.mp hp'.1
  exact ⟨hpq.1, hpq.2, hp'.2.1, hp'.2.2⟩

/-! ### Uniqueness of successors and predecessors among consecutive pairs -/

lemma os_consec_succ_unique {A : Finset ℕ} {a b b' : ℕ}
    (h : IsConsecutive A a b) (h' : IsConsecutive A a b') : b = b' := by
  by_contra hne
  rcases Nat.lt_or_ge b b' with hlt | hge
  · exact h'.2.2.2 b h.2.1 ⟨h.2.2.1, hlt⟩
  · have hlt : b' < b := by omega
    exact h.2.2.2 b' h'.2.1 ⟨h'.2.2.1, hlt⟩

lemma os_consec_pred_unique {A : Finset ℕ} {a a' b : ℕ}
    (h : IsConsecutive A a b) (h' : IsConsecutive A a' b) : a = a' := by
  by_contra hne
  rcases Nat.lt_or_ge a a' with hlt | hge
  · exact h.2.2.2 a' h'.1 ⟨hlt, h'.2.2.1⟩
  · have hlt : a' < a := by omega
    exact h'.2.2.2 a h.1 ⟨hlt, h.2.2.1⟩

/-! ### Divisors of `∏ p ∈ B, p` -/

lemma os_prodB_ne_zero {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) : (∏ p ∈ B, p) ≠ 0 :=
  (Finset.prod_pos fun p hp => (hB p hp).pos).ne'

lemma os_primeFactors_subset {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {d : ℕ}
    (hd : d ∈ (∏ p ∈ B, p).divisors) : d.primeFactors ⊆ B := by
  have hdvd := (Nat.mem_divisors.mp hd).1
  calc d.primeFactors ⊆ (∏ p ∈ B, p).primeFactors :=
        Nat.primeFactors_mono hdvd (os_prodB_ne_zero hB)
    _ = B := primeFactors_prodPrimes hB

lemma os_prod_primeFactors {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {d : ℕ}
    (hd : d ∈ (∏ p ∈ B, p).divisors) : ∏ p ∈ d.primeFactors, p = d :=
  Nat.prod_primeFactors_of_squarefree
    (Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd).1 (squarefree_prodPrimes hB))

lemma os_cast_eq_prod {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {d : ℕ}
    (hd : d ∈ (∏ p ∈ B, p).divisors) :
    (d:ℝ) = ∏ p ∈ d.primeFactors, (p:ℝ) := by
  conv_lhs => rw [← os_prod_primeFactors hB hd]
  push_cast
  rfl

lemma os_mem_B_of_card_one {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {d : ℕ}
    (hd : d ∈ (∏ p ∈ B, p).divisors) (h1 : d.primeFactors.card = 1) : d ∈ B := by
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
  have hpB : p ∈ B := os_primeFactors_subset hB hd (by rw [hp]; exact Finset.mem_singleton_self p)
  have hdp : d = p := by
    have h := os_prod_primeFactors hB hd
    rw [hp, Finset.prod_singleton] at h
    exact h.symm
  exact hdp ▸ hpB

lemma os_eq_one_of_card_zero {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) {d : ℕ}
    (hd : d ∈ (∏ p ∈ B, p).divisors) (h0 : d.primeFactors.card = 0) : d = 1 := by
  have hpf : d.primeFactors = ∅ := Finset.card_eq_zero.mp h0
  have h := os_prod_primeFactors hB hd
  rw [hpf, Finset.prod_empty] at h
  exact h.symm

/-! ### Class 1: consecutive pairs of primes -/

theorem oneScale_primePart_le {B : Finset ℕ} {N K : ℕ}
    (hcard : B.card = K)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) (hN : 1 ≤ N) :
    pairSumOn ((∏ p ∈ B, p).divisors)
        (fun a b => a ∈ B ∧ b ∈ B ∧ IsConsecutive ((∏ p ∈ B, p).divisors) a b)
      ≤ (K:ℝ)/N := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  refine os_pairSumOn_le_of_forall fun S hS => ?_
  have hterm : ∀ p ∈ S, invGap p.1 p.2 ≤ (N:ℝ)⁻¹ := by
    intro p hp
    obtain ⟨-, -, hlt, hpB, hqB, -⟩ := hS p hp
    refine invGap_le hNR ?_
    have hgap := hsep p.1 hpB p.2 hqB hlt
    have h1 : p.1 + N < p.2 := by omega
    have h2 : (p.1:ℝ) + N < (p.2:ℝ) := by exact_mod_cast h1
    linarith
  have hcardS : S.card ≤ K := by
    rw [← hcard]
    apply Finset.card_le_card_of_injOn (fun p => p.1)
    · intro p hp
      exact (hS p hp).2.2.2.1
    · intro p hp q hq hpq
      simp only [Finset.mem_coe] at hp hq
      obtain ⟨-, -, -, -, -, hc⟩ := hS p hp
      obtain ⟨-, -, -, -, -, hc'⟩ := hS q hq
      have h1 : p.1 = q.1 := hpq
      have h2 : p.2 = q.2 := os_consec_succ_unique (h1 ▸ hc) hc'
      exact Prod.ext h1 h2
  calc ∑ p ∈ S, invGap p.1 p.2 ≤ ∑ _p ∈ S, (N:ℝ)⁻¹ := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (N:ℝ)⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (K:ℝ) * (N:ℝ)⁻¹ := by
        have : (S.card : ℝ) ≤ (K:ℝ) := by exact_mod_cast hcardS
        gcongr
    _ = (K:ℝ)/N := by rw [div_eq_mul_inv]

/-! ### Size bounds for divisors in terms of `ω` -/

/-- Window powers are at most twice the base power: `(x₀+H)^k ≤ 2·x₀^k` when `2KH ≤ x₀`. -/
lemma os_window_pow_le {x₀ H K : ℕ} (h0 : 0 < x₀) (hKH : 2*K*H ≤ x₀) {k : ℕ} (hk : k ≤ K) :
    ((x₀:ℝ) + H) ^ k ≤ 2 * (x₀:ℝ) ^ k := by
  have hx : (0:ℝ) < x₀ := by exact_mod_cast h0
  have hu : (0:ℝ) ≤ (H:ℝ)/x₀ := by positivity
  have hbound : 2 * (k:ℝ) * ((H:ℝ)/x₀) ≤ 1 := by
    have h1 : 2 * k * H ≤ x₀ := le_trans (by
      have : 2 * k * H ≤ 2 * K * H := by
        have := Nat.mul_le_mul_right H (Nat.mul_le_mul_left 2 hk)
        omega
      exact this) hKH
    have h2 : (2 * (k:ℝ) * H) ≤ (x₀:ℝ) := by exact_mod_cast h1
    rw [show 2 * (k:ℝ) * ((H:ℝ)/x₀) = (2 * (k:ℝ) * H) / x₀ by ring, div_le_one hx]
    exact h2
  have heq : (x₀:ℝ) + H = x₀ * (1 + (H:ℝ)/x₀) := by field_simp
  have hpk : (0:ℝ) ≤ (x₀:ℝ)^k := by positivity
  calc ((x₀:ℝ) + H) ^ k = (x₀:ℝ)^k * (1 + (H:ℝ)/x₀)^k := by rw [heq, mul_pow]
    _ ≤ (x₀:ℝ)^k * (1 + 2 * (k:ℝ) * ((H:ℝ)/x₀)) :=
        mul_le_mul_of_nonneg_left (one_add_pow_le_aux hu k hbound) hpk
    _ ≤ (x₀:ℝ)^k * 2 := mul_le_mul_of_nonneg_left (by linarith) hpk
    _ = 2 * (x₀:ℝ)^k := by ring

lemma os_le_prod {B : Finset ℕ} {x₀ H : ℕ} (hB : ∀ p ∈ B, p.Prime)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H) {d : ℕ} (hd : d ∈ (∏ p ∈ B, p).divisors) :
    (x₀:ℝ) ^ d.primeFactors.card ≤ (d:ℝ) := by
  rw [os_cast_eq_prod hB hd, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
  have h := (hwin p (os_primeFactors_subset hB hd hp)).1
  exact_mod_cast h.le

lemma os_prod_le {B : Finset ℕ} {x₀ H : ℕ} (hB : ∀ p ∈ B, p.Prime)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H) {d : ℕ} (hd : d ∈ (∏ p ∈ B, p).divisors) :
    (d:ℝ) ≤ ((x₀:ℝ) + H) ^ d.primeFactors.card := by
  rw [os_cast_eq_prod hB hd, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
  have h := (hwin p (os_primeFactors_subset hB hd hp)).2
  exact_mod_cast h

/-- A divisor with strictly more prime factors is at least twice as large. -/
lemma os_double_of_omega_lt {B : Finset ℕ} {x₀ H K : ℕ} (hB : ∀ p ∈ B, p.Prime)
    (hcard : B.card = K) (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hKH : 2*K*H ≤ x₀) (hx₀ : 4 ≤ x₀)
    {d e : ℕ} (hd : d ∈ (∏ p ∈ B, p).divisors) (he : e ∈ (∏ p ∈ B, p).divisors)
    (hlt : d.primeFactors.card < e.primeFactors.card) :
    2 * (d:ℝ) ≤ (e:ℝ) := by
  have h0 : 0 < x₀ := by omega
  have hx4 : (4:ℝ) ≤ (x₀:ℝ) := by exact_mod_cast hx₀
  have hkK : d.primeFactors.card ≤ K := by
    rw [← hcard]; exact Finset.card_le_card (os_primeFactors_subset hB hd)
  have hup : (d:ℝ) ≤ 2 * (x₀:ℝ) ^ d.primeFactors.card :=
    le_trans (os_prod_le hB hwin hd) (os_window_pow_le h0 hKH hkK)
  have hlow : (x₀:ℝ) ^ (d.primeFactors.card + 1) ≤ (e:ℝ) := by
    refine le_trans ?_ (os_le_prod hB hwin he)
    exact pow_le_pow_right₀ (by linarith) hlt
  have hpow : (0:ℝ) ≤ (x₀:ℝ) ^ d.primeFactors.card := by positivity
  calc 2 * (d:ℝ) ≤ 2 * (2 * (x₀:ℝ) ^ d.primeFactors.card) := by linarith
    _ = 4 * (x₀:ℝ) ^ d.primeFactors.card := by ring
    _ ≤ (x₀:ℝ) * (x₀:ℝ) ^ d.primeFactors.card := by nlinarith
    _ = (x₀:ℝ) ^ (d.primeFactors.card + 1) := by rw [pow_succ]; ring
    _ ≤ (e:ℝ) := hlow

/-! ### Class 3: consecutive pairs with different `ω` -/

theorem oneScale_diffCard_le {B : Finset ℕ} {x₀ H K : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (hcard : B.card = K)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hKH : 2*K*H ≤ x₀) (hx₀ : 4 ≤ x₀) (hH : 1 ≤ H) :
    pairSumOn ((∏ p ∈ B, p).divisors)
        (fun a b => a.primeFactors.card ≠ b.primeFactors.card)
      ≤ (2:ℝ)^(K+3)*K/x₀ := by
  classical
  set A := (∏ p ∈ B, p).divisors with hA
  set g : ℕ → ℝ := fun b => if b = 1 then 0 else 2/(b:ℝ) with hg
  have h0 : 0 < x₀ := by omega
  have hx0R : (0:ℝ) < (x₀:ℝ) := by exact_mod_cast h0
  have hgnn : ∀ b : ℕ, 0 ≤ g b := by
    intro b
    simp only [hg]
    split <;> positivity
  -- Step B: the sum of `g` over the divisors
  have hgsum : ∑ b ∈ A, g b ≤ 4 * (K:ℝ) / x₀ := by
    have h1mem : 1 ∈ A := Nat.one_mem_divisors.mpr (os_prodB_ne_zero hprime)
    have hsplit : g 1 + ∑ b ∈ A.erase 1, g b = ∑ b ∈ A, g b :=
      Finset.add_sum_erase A g h1mem
    have hg1 : g 1 = 0 := by simp [hg]
    have herase : ∑ b ∈ A.erase 1, g b = 2 * ∑ b ∈ A.erase 1, ((b:ℝ))⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b hb => ?_
      have hb1 : b ≠ 1 := Finset.ne_of_mem_erase hb
      simp only [hg, if_neg hb1]
      rw [div_eq_mul_inv]
    have hinv : ∑ b ∈ A.erase 1, ((b:ℝ))⁻¹ ≤ 2 * (K:ℝ) / x₀ := by
      have := sum_inv_divisors_erase_one_le hprime
        (fun p hp => (hwin p hp).1.le)
        (by rw [hcard]; calc 2*K ≤ 2*K*H := by nlinarith
              _ ≤ x₀ := hKH) h0
      rw [hcard] at this
      exact this
    calc ∑ b ∈ A, g b = g 1 + ∑ b ∈ A.erase 1, g b := hsplit.symm
      _ = 2 * ∑ b ∈ A.erase 1, ((b:ℝ))⁻¹ := by rw [hg1, herase, zero_add]
      _ ≤ 2 * (2 * (K:ℝ) / x₀) := by
          have hnn : 0 ≤ ∑ b ∈ A.erase 1, ((b:ℝ))⁻¹ :=
            Finset.sum_nonneg fun b _ => by positivity
          linarith
      _ = 4 * (K:ℝ) / x₀ := by ring
  -- Step A: bound the pair sum by `card A * ∑ g`
  have hmain : pairSumOn A (fun a b => a.primeFactors.card ≠ b.primeFactors.card)
      ≤ (A.card : ℝ) * ∑ b ∈ A, g b := by
    refine os_pairSumOn_le_of_forall fun S hS => ?_
    have hterm : ∀ p ∈ S, invGap p.1 p.2 ≤ g p.2 := by
      intro p hp
      obtain ⟨ha, hb, hlt, hne⟩ := hS p hp
      have ha1 : 1 ≤ p.1 := Nat.pos_of_mem_divisors ha
      have hb1 : p.2 ≠ 1 := by omega
      have hbR : (1:ℝ) ≤ (p.2:ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hb
      have habR : (p.1:ℝ) < (p.2:ℝ) := by exact_mod_cast hlt
      have hdouble : 2 * (p.1:ℝ) ≤ (p.2:ℝ) := by
        rcases Nat.lt_or_ge p.1.primeFactors.card p.2.primeFactors.card with hω | hω
        · exact os_double_of_omega_lt hprime hcard hwin hKH hx₀ ha hb hω
        · have hω' : p.2.primeFactors.card < p.1.primeFactors.card := by omega
          have h2 := os_double_of_omega_lt hprime hcard hwin hKH hx₀ hb ha hω'
          linarith
      have hgap : (p.2:ℝ)/2 ≤ (p.2:ℝ) - p.1 := by linarith
      have hhalf : (0:ℝ) < (p.2:ℝ)/2 := by linarith
      calc invGap p.1 p.2 ≤ ((p.2:ℝ)/2)⁻¹ := inv_anti₀ hhalf hgap
        _ = 2/(p.2:ℝ) := by rw [inv_div]
        _ = g p.2 := by simp [hg, if_neg hb1]
    have hsub : S ⊆ A ×ˢ A := by
      intro p hp
      exact Finset.mem_product.mpr ⟨(hS p hp).1, (hS p hp).2.1⟩
    calc ∑ p ∈ S, invGap p.1 p.2 ≤ ∑ p ∈ S, g p.2 := Finset.sum_le_sum hterm
      _ ≤ ∑ p ∈ A ×ˢ A, g p.2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hgnn p.2
      _ = ∑ a ∈ A, ∑ b ∈ A, g b := Finset.sum_product A A (fun p => g p.2)
      _ = (A.card : ℝ) * ∑ b ∈ A, g b := by rw [Finset.sum_const, nsmul_eq_mul]
  -- assemble
  have hAcard : (A.card : ℝ) = (2:ℝ)^K := by
    rw [hA, card_divisors_prodPrimes hprime, hcard]
    push_cast
    rfl
  have hsumnn : (0:ℝ) ≤ ∑ b ∈ A, g b := Finset.sum_nonneg fun b _ => hgnn b
  calc pairSumOn A (fun a b => a.primeFactors.card ≠ b.primeFactors.card)
      ≤ (A.card : ℝ) * ∑ b ∈ A, g b := hmain
    _ = (2:ℝ)^K * ∑ b ∈ A, g b := by rw [hAcard]
    _ ≤ (2:ℝ)^K * (4 * (K:ℝ) / x₀) := by
        have : (0:ℝ) ≤ (2:ℝ)^K := by positivity
        exact mul_le_mul_of_nonneg_left hgsum this
    _ = (2:ℝ)^(K+2) * (K:ℝ) / x₀ := by rw [pow_add]; ring
    _ ≤ (2:ℝ)^(K+3)*K/x₀ := by
        have h1 : (2:ℝ)^(K+2) ≤ (2:ℝ)^(K+3) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have h2 : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
        have h3 : (0:ℝ) ≤ ((x₀:ℝ))⁻¹ := by positivity
        rw [div_eq_mul_inv, div_eq_mul_inv]
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h1 h2) h3
        exact this

/-! ### The minimum element and the gap product `D(v)` -/

/-- The minimum of a finset of naturals, defaulting to `0` on the empty set. -/
def os_min (v : Finset ℕ) : ℕ := if h : v.Nonempty then v.min' h else 0

lemma os_min_eq {v : Finset ℕ} (h : v.Nonempty) : os_min v = v.min' h := dif_pos h

lemma os_min_mem {v : Finset ℕ} (h : v.Nonempty) : os_min v ∈ v := by
  rw [os_min_eq h]; exact v.min'_mem h

lemma os_min_le {v : Finset ℕ} {p : ℕ} (hp : p ∈ v) : os_min v ≤ p := by
  rw [os_min_eq ⟨p, hp⟩]; exact v.min'_le p hp

/-- The gap product `D(v) := ∏_{p ∈ v \ {min v}} (p - min v)` as a real number. -/
noncomputable def os_D (v : Finset ℕ) : ℝ :=
  ∏ p ∈ v.erase (os_min v), ((p:ℝ) - (os_min v : ℝ))

lemma os_lt_of_mem_erase_min {v : Finset ℕ} {p : ℕ} (hp : p ∈ v.erase (os_min v)) :
    os_min v < p :=
  lt_of_le_of_ne (os_min_le (Finset.mem_of_mem_erase hp))
    (Ne.symm (Finset.ne_of_mem_erase hp))

lemma os_D_factor_ge {B : Finset ℕ} {N : ℕ}
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) {v : Finset ℕ} (hv : v ⊆ B)
    (hvne : v.Nonempty) {p : ℕ} (hp : p ∈ v.erase (os_min v)) :
    (N:ℝ) + 1 ≤ (p:ℝ) - (os_min v : ℝ) := by
  have hlt := os_lt_of_mem_erase_min hp
  have hminB : os_min v ∈ B := hv (os_min_mem hvne)
  have hpB : p ∈ B := hv (Finset.mem_of_mem_erase hp)
  have hgap := hsep _ hminB _ hpB hlt
  have h1 : os_min v + (N + 1) ≤ p := by omega
  have h2 : ((os_min v : ℕ):ℝ) + ((N:ℝ)+1) ≤ (p:ℝ) := by exact_mod_cast h1
  linarith

lemma os_D_pos {B : Finset ℕ} {N : ℕ}
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) {v : Finset ℕ} (hv : v ⊆ B)
    (hvne : v.Nonempty) : 0 < os_D v := by
  unfold os_D
  refine Finset.prod_pos fun p hp => ?_
  have h := os_D_factor_ge hsep hv hvne hp
  have hN : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  linarith

/-! ### The elementary-symmetric counting bound -/

/-- `∑_{w ⊆ S, |w| = j} ∏_{p ∈ w} f p ≤ (∑_{p ∈ S} f p)^j` for nonnegative `f`. -/
lemma os_esymm_le_pow_sum {S : Finset ℕ} {f : ℕ → ℝ} (hf : ∀ p ∈ S, 0 ≤ f p) :
    ∀ j : ℕ, ∑ w ∈ S.powerset.filter (fun w => w.card = j), ∏ p ∈ w, f p
      ≤ (∑ p ∈ S, f p) ^ j := by
  classical
  intro j
  induction j with
  | zero =>
    have h : S.powerset.filter (fun w => w.card = 0) = {∅} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.card_eq_zero,
        Finset.mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ Finset.empty_subset S, h⟩⟩
    rw [h, Finset.sum_singleton, Finset.prod_empty, pow_zero]
  | succ j ih =>
    set T := S.powerset.filter (fun w => w.card = j + 1) with hT
    set U := S ×ˢ (S.powerset.filter (fun w => w.card = j)) with hU
    have hTmem : ∀ w ∈ T, w ⊆ S ∧ w.card = j + 1 := by
      intro w hw
      have := Finset.mem_filter.mp hw
      exact ⟨Finset.mem_powerset.mp this.1, this.2⟩
    have hTne : ∀ w ∈ T, w.Nonempty := by
      intro w hw
      exact Finset.card_pos.mp (by rw [(hTmem w hw).2]; omega)
    have hstep1 : ∀ w ∈ T, ∏ p ∈ w, f p
        = f (os_min w) * ∏ p ∈ w.erase (os_min w), f p := fun w hw =>
      (Finset.mul_prod_erase w f (os_min_mem (hTne w hw))).symm
    have hinj : ∀ w ∈ T, ∀ w' ∈ T,
        (os_min w, w.erase (os_min w)) = (os_min w', w'.erase (os_min w')) → w = w' := by
      intro w hw w' hw' heq
      have h1 : os_min w = os_min w' := (Prod.mk.injEq _ _ _ _).mp heq |>.1
      have h2 : w.erase (os_min w) = w'.erase (os_min w') :=
        (Prod.mk.injEq _ _ _ _).mp heq |>.2
      calc w = insert (os_min w) (w.erase (os_min w)) :=
            (Finset.insert_erase (os_min_mem (hTne w hw))).symm
        _ = insert (os_min w') (w'.erase (os_min w')) := by rw [h2, h1]
        _ = w' := Finset.insert_erase (os_min_mem (hTne w' hw'))
    have himg : ∀ w ∈ T, (os_min w, w.erase (os_min w)) ∈ U := by
      intro w hw
      obtain ⟨hws, hwc⟩ := hTmem w hw
      refine Finset.mem_product.mpr ⟨hws (os_min_mem (hTne w hw)), ?_⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr
        (fun p hp => hws (Finset.mem_of_mem_erase hp)), ?_⟩
      rw [Finset.card_erase_of_mem (os_min_mem (hTne w hw)), hwc]
      omega
    have hsum0 : (0:ℝ) ≤ ∑ p ∈ S, f p := Finset.sum_nonneg hf
    calc ∑ w ∈ T, ∏ p ∈ w, f p
        = ∑ w ∈ T, f (os_min w) * ∏ p ∈ w.erase (os_min w), f p :=
          Finset.sum_congr rfl hstep1
      _ = ∑ x ∈ T.image (fun w => (os_min w, w.erase (os_min w))),
            f x.1 * ∏ p ∈ x.2, f p :=
          (Finset.sum_image (f := fun x : ℕ × Finset ℕ => f x.1 * ∏ p ∈ x.2, f p)
            hinj).symm
      _ ≤ ∑ x ∈ U, f x.1 * ∏ p ∈ x.2, f p := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro x hx
            obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
            exact himg w hw
          · intro x hx _
            have hx' := Finset.mem_product.mp hx
            refine mul_nonneg (hf x.1 hx'.1) (Finset.prod_nonneg fun p hp => ?_)
            exact hf p (Finset.mem_powerset.mp (Finset.mem_filter.mp hx'.2).1 hp)
      _ = (∑ p ∈ S, f p) * ∑ w ∈ S.powerset.filter (fun w => w.card = j), ∏ p ∈ w, f p := by
          rw [Finset.sum_mul_sum]
          exact Finset.sum_product _ _ _
      _ ≤ (∑ p ∈ S, f p) * (∑ p ∈ S, f p) ^ j :=
          mul_le_mul_of_nonneg_left ih hsum0
      _ = (∑ p ∈ S, f p) ^ (j + 1) := by rw [pow_succ]; ring

/-! ### Separated elements grow linearly -/

/-- In an `N`-separated set of primes, the maximum of any `n`-element subset above `p₀`
is at least `p₀ + n(N+1)`. -/
lemma os_ge_of_card_le {B : Finset ℕ} {N p₀ : ℕ}
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) (hp₀ : p₀ ∈ B) :
    ∀ n : ℕ, ∀ S : Finset ℕ, S ⊆ B → (∀ p ∈ S, p₀ < p) → n ≤ S.card →
      ∀ hS : S.Nonempty, p₀ + n * (N+1) ≤ S.max' hS := by
  intro n
  induction n with
  | zero =>
    intro S _ hall _ hS
    have := hall _ (S.max'_mem hS)
    omega
  | succ n ih =>
    intro S hSB hall hcard hS
    have hqS : S.max' hS ∈ S := S.max'_mem hS
    have hqB : S.max' hS ∈ B := hSB hqS
    rcases (S.erase (S.max' hS)).eq_empty_or_nonempty with hemp | hne
    · have hc1 : (S.erase (S.max' hS)).card = S.card - 1 :=
        Finset.card_erase_of_mem hqS
      rw [hemp] at hc1
      simp only [Finset.card_empty] at hc1
      have hn0 : n = 0 := by omega
      subst hn0
      have hgap := hsep p₀ hp₀ _ hqB (hall _ hqS)
      omega
    · have hsub : S.erase (S.max' hS) ⊆ B :=
        fun p hp => hSB (Finset.mem_of_mem_erase hp)
      have hall' : ∀ p ∈ S.erase (S.max' hS), p₀ < p :=
        fun p hp => hall p (Finset.mem_of_mem_erase hp)
      have hcard' : n ≤ (S.erase (S.max' hS)).card := by
        rw [Finset.card_erase_of_mem hqS]
        omega
      have hih := ih _ hsub hall' hcard' hne
      have hq'S : (S.erase (S.max' hS)).max' hne ∈ S.erase (S.max' hS) :=
        (S.erase (S.max' hS)).max'_mem hne
      have hq'B : (S.erase (S.max' hS)).max' hne ∈ B := hsub hq'S
      have hq'lt : (S.erase (S.max' hS)).max' hne < S.max' hS := by
        have h1 := Finset.mem_of_mem_erase hq'S
        have h2 := Finset.ne_of_mem_erase hq'S
        have h3 := S.le_max' _ h1
        omega
      have hgap := hsep _ hq'B _ hqB hq'lt
      calc p₀ + (n+1) * (N+1) = (p₀ + n * (N+1)) + (N+1) := by ring
        _ ≤ (S.erase (S.max' hS)).max' hne + (N+1) := Nat.add_le_add_right hih _
        _ ≤ S.max' hS := by omega

/-! ### The separated reciprocal sum is at most a harmonic sum -/

lemma os_sum_inv_le_harmonic {B : Finset ℕ} {N p₀ : ℕ}
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) (hp₀ : p₀ ∈ B) (hN : 1 ≤ N) :
    ∀ n : ℕ, ∀ S : Finset ℕ, S ⊆ B → (∀ p ∈ S, p₀ < p) → S.card = n →
      ∑ p ∈ S, ((p:ℝ) - (p₀:ℝ))⁻¹ ≤ (N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 n, ((j:ℝ))⁻¹ := by
  intro n
  induction n with
  | zero =>
    intro S _ _ hcard
    rw [Finset.card_eq_zero.mp hcard]
    simp
  | succ n ih =>
    intro S hSB hall hcard
    have hS : S.Nonempty := Finset.card_pos.mp (by omega)
    have hqS : S.max' hS ∈ S := S.max'_mem hS
    have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
    -- lower bound on the largest gap
    have hqmax := os_ge_of_card_le hsep hp₀ (n+1) S hSB hall (le_of_eq hcard.symm) hS
    have hgapN : (n+1) * N + p₀ ≤ S.max' hS := by
      have h1 : (n+1) * N ≤ (n+1) * (N+1) := Nat.mul_le_mul_left _ (by omega)
      omega
    have hgapR : ((n:ℝ)+1) * N ≤ (S.max' hS : ℝ) - p₀ := by
      have h2 : (((n+1) * N + p₀ : ℕ) : ℝ) ≤ ((S.max' hS : ℕ) : ℝ) := by
        exact_mod_cast hgapN
      push_cast at h2
      linarith
    have hpos : (0:ℝ) < ((n:ℝ)+1) * N := by positivity
    have hterm : ((S.max' hS : ℝ) - (p₀:ℝ))⁻¹ ≤ (N:ℝ)⁻¹ * ((n:ℝ)+1)⁻¹ := by
      calc ((S.max' hS : ℝ) - (p₀:ℝ))⁻¹ ≤ (((n:ℝ)+1) * N)⁻¹ := inv_anti₀ hpos hgapR
        _ = (N:ℝ)⁻¹ * ((n:ℝ)+1)⁻¹ := by rw [mul_inv]; ring
    -- induction on the rest
    have hih := ih (S.erase (S.max' hS))
      (fun p hp => hSB (Finset.mem_of_mem_erase hp))
      (fun p hp => hall p (Finset.mem_of_mem_erase hp))
      (by rw [Finset.card_erase_of_mem hqS, hcard]; omega)
    have hsplit : ((S.max' hS : ℝ) - (p₀:ℝ))⁻¹
        + ∑ p ∈ S.erase (S.max' hS), ((p:ℝ) - (p₀:ℝ))⁻¹
        = ∑ p ∈ S, ((p:ℝ) - (p₀:ℝ))⁻¹ :=
      Finset.add_sum_erase S (fun p => ((p:ℝ) - (p₀:ℝ))⁻¹) hqS
    have htop : ∑ j ∈ Finset.Icc 1 (n+1), ((j:ℝ))⁻¹
        = ∑ j ∈ Finset.Icc 1 n, ((j:ℝ))⁻¹ + ((n:ℝ)+1)⁻¹ := by
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      push_cast
      ring
    calc ∑ p ∈ S, ((p:ℝ) - (p₀:ℝ))⁻¹
        = ((S.max' hS : ℝ) - (p₀:ℝ))⁻¹
          + ∑ p ∈ S.erase (S.max' hS), ((p:ℝ) - (p₀:ℝ))⁻¹ := hsplit.symm
      _ ≤ (N:ℝ)⁻¹ * ((n:ℝ)+1)⁻¹ + (N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 n, ((j:ℝ))⁻¹ :=
          add_le_add hterm hih
      _ = (N:ℝ)⁻¹ * (∑ j ∈ Finset.Icc 1 n, ((j:ℝ))⁻¹ + ((n:ℝ)+1)⁻¹) := by ring
      _ = (N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 (n+1), ((j:ℝ))⁻¹ := by rw [htop]

/-- The key reciprocal-gap sum bound: `∑_{p ∈ B, p > p₀} 1/(p - p₀) ≤ (1 + log K)/N`. -/
lemma os_sep_sum_inv {B : Finset ℕ} {N K p₀ : ℕ} (hcard : B.card = K)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) (hN : 1 ≤ N) (hp₀ : p₀ ∈ B) :
    ∑ p ∈ B.filter (fun p => p₀ < p), ((p:ℝ) - (p₀:ℝ))⁻¹ ≤ (1 + Real.log K) / N := by
  classical
  have h1 := os_sum_inv_le_harmonic hsep hp₀ hN (B.filter (fun p => p₀ < p)).card
    (B.filter (fun p => p₀ < p)) (Finset.filter_subset _ _)
    (fun p hp => (Finset.mem_filter.mp hp).2) rfl
  have h2 : ∑ j ∈ Finset.Icc 1 (B.filter (fun p => p₀ < p)).card, ((j:ℝ))⁻¹
      ≤ ∑ j ∈ Finset.Icc 1 K, ((j:ℝ))⁻¹ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => by positivity)
    apply Finset.Icc_subset_Icc le_rfl
    rw [← hcard]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have h3 := sum_inv_le_one_add_log K
  have hNinv : (0:ℝ) ≤ (N:ℝ)⁻¹ := by positivity
  calc ∑ p ∈ B.filter (fun p => p₀ < p), ((p:ℝ) - (p₀:ℝ))⁻¹
      ≤ (N:ℝ)⁻¹ * ∑ j ∈ Finset.Icc 1 (B.filter (fun p => p₀ < p)).card, ((j:ℝ))⁻¹ := h1
    _ ≤ (N:ℝ)⁻¹ * (1 + Real.log K) :=
        mul_le_mul_of_nonneg_left (le_trans h2 h3) hNinv
    _ = (1 + Real.log K) / N := by rw [div_eq_mul_inv, mul_comm]

/-! ### Geometric tail -/

lemma os_geom_le_two {q : ℝ} (h0 : 0 ≤ q) (h2 : q ≤ 1/2) :
    ∀ n : ℕ, ∑ i ∈ Finset.range n, q ^ i ≤ 2 := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have h3 : ∑ i ∈ Finset.range n, q ^ (i+1) = q * ∑ i ∈ Finset.range n, q ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring
    rw [h3, pow_zero]
    have ha : q * ∑ i ∈ Finset.range n, q ^ i ≤ q * 2 := mul_le_mul_of_nonneg_left ih h0
    have hb : q * 2 ≤ 1 := by linarith
    linarith

lemma os_geom_tail_le {q : ℝ} (h0 : 0 ≤ q) (h2 : q ≤ 1/2) (K : ℕ) :
    ∑ k ∈ Finset.Icc 2 K, q ^ (k-1) ≤ 2 * q := by
  have h1 : ∑ k ∈ Finset.Icc 2 K, q ^ (k-1) = ∑ k ∈ Finset.Icc 2 K, q * q^(k-2) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have he : k - 1 = (k-2) + 1 := by omega
    rw [he, pow_succ]
    ring
  rw [h1, ← Finset.mul_sum]
  have h3 : ∑ k ∈ Finset.Icc 2 K, q^(k-2) ≤ 2 := by
    have hIcc : Finset.Icc 2 K = Finset.Ico 2 (K+1) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    have hcongr : ∀ i ∈ Finset.range (K+1-2), q^((2+i)-2) = q^i := fun i _ => by
      congr 1
      omega
    rw [Finset.sum_congr rfl hcongr]
    exact os_geom_le_two h0 h2 _
  calc q * ∑ k ∈ Finset.Icc 2 K, q^(k-2) ≤ q * 2 := mul_le_mul_of_nonneg_left h3 h0
    _ = 2 * q := by ring

/-! ### Summing `1/D(v)` over subsets with a given minimum and cardinality -/

lemma os_fiber_D_inv_le {B : Finset ℕ} {N K : ℕ} (hcard : B.card = K)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) (hN : 1 ≤ N)
    {p₀ : ℕ} (hp₀ : p₀ ∈ B) {k : ℕ} (hk : 1 ≤ k) :
    ∑ v ∈ (B.powerset.filter (fun v => v.card = k)).filter (fun v => os_min v = p₀),
        (os_D v)⁻¹
      ≤ ((1 + Real.log K) / N) ^ (k - 1) := by
  classical
  have hfnn : ∀ p ∈ B.filter (fun p => p₀ < p), (0:ℝ) ≤ ((p:ℝ) - (p₀:ℝ))⁻¹ := by
    intro p hp
    have h1 : p₀ < p := (Finset.mem_filter.mp hp).2
    have h2 : (p₀:ℝ) < (p:ℝ) := by exact_mod_cast h1
    exact inv_nonneg.mpr (by linarith)
  have hFmem : ∀ v ∈ (B.powerset.filter (fun v => v.card = k)).filter
      (fun v => os_min v = p₀), v ⊆ B ∧ v.card = k ∧ os_min v = p₀ := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := Finset.mem_filter.mp hv
    obtain ⟨hv3, hv4⟩ := Finset.mem_filter.mp hv1
    exact ⟨Finset.mem_powerset.mp hv3, hv4, hv2⟩
  have hp₀v : ∀ v ∈ (B.powerset.filter (fun v => v.card = k)).filter
      (fun v => os_min v = p₀), p₀ ∈ v := by
    intro v hv
    have hne : v.Nonempty := Finset.card_pos.mp (by rw [(hFmem v hv).2.1]; omega)
    exact (hFmem v hv).2.2 ▸ os_min_mem hne
  have hterm : ∀ v ∈ (B.powerset.filter (fun v => v.card = k)).filter
      (fun v => os_min v = p₀), (os_D v)⁻¹ = ∏ p ∈ v.erase p₀, ((p:ℝ) - (p₀:ℝ))⁻¹ := by
    intro v hv
    unfold os_D
    rw [(hFmem v hv).2.2, ← Finset.prod_inv_distrib]
  have hinj : Set.InjOn (fun v : Finset ℕ => v.erase p₀)
      ↑((B.powerset.filter (fun v => v.card = k)).filter (fun v => os_min v = p₀)) := by
    intro v hv v' hv' he
    have hv1 := Finset.mem_coe.mp hv
    have hv'1 := Finset.mem_coe.mp hv'
    have he' : v.erase p₀ = v'.erase p₀ := he
    calc v = insert p₀ (v.erase p₀) := (Finset.insert_erase (hp₀v v hv1)).symm
      _ = insert p₀ (v'.erase p₀) := by rw [he']
      _ = v' := Finset.insert_erase (hp₀v v' hv'1)
  have himg : ∀ v ∈ (B.powerset.filter (fun v => v.card = k)).filter
      (fun v => os_min v = p₀), v.erase p₀ ∈
        (B.filter (fun p => p₀ < p)).powerset.filter (fun w => w.card = k - 1) := by
    intro v hv
    obtain ⟨hvB, hvc, hvm⟩ := hFmem v hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · intro p hp
      refine Finset.mem_filter.mpr ⟨hvB (Finset.mem_of_mem_erase hp), ?_⟩
      have h1 : os_min v ≤ p := os_min_le (Finset.mem_of_mem_erase hp)
      have h2 : p ≠ p₀ := Finset.ne_of_mem_erase hp
      omega
    · rw [Finset.card_erase_of_mem (hp₀v v hv), hvc]
  calc ∑ v ∈ (B.powerset.filter (fun v => v.card = k)).filter
        (fun v => os_min v = p₀), (os_D v)⁻¹
      = ∑ v ∈ (B.powerset.filter (fun v => v.card = k)).filter
          (fun v => os_min v = p₀), ∏ p ∈ v.erase p₀, ((p:ℝ) - (p₀:ℝ))⁻¹ :=
        Finset.sum_congr rfl hterm
    _ = ∑ w ∈ ((B.powerset.filter (fun v => v.card = k)).filter
          (fun v => os_min v = p₀)).image (fun v : Finset ℕ => v.erase p₀),
            ∏ p ∈ w, (((p:ℕ):ℝ) - (p₀:ℝ))⁻¹ :=
        (Finset.sum_image
          (f := fun w : Finset ℕ => ∏ p ∈ w, ((p:ℝ) - (p₀:ℝ))⁻¹) hinj).symm
    _ ≤ ∑ w ∈ (B.filter (fun p => p₀ < p)).powerset.filter (fun w => w.card = k - 1),
          ∏ p ∈ w, ((p:ℝ) - (p₀:ℝ))⁻¹ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro w hw
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
          exact himg v hv
        · intro w hw _
          refine Finset.prod_nonneg fun p hp => ?_
          exact hfnn p (Finset.mem_powerset.mp (Finset.mem_filter.mp hw).1 hp)
    _ ≤ (∑ p ∈ B.filter (fun p => p₀ < p), ((p:ℝ) - (p₀:ℝ))⁻¹) ^ (k-1) :=
        os_esymm_le_pow_sum hfnn (k-1)
    _ ≤ ((1 + Real.log K) / N) ^ (k-1) := by
        refine pow_le_pow_left₀ (Finset.sum_nonneg hfnn) ?_ _
        exact os_sep_sum_inv hcard hsep hN hp₀

/-- Summing `1/D(v)` over all `k`-element subsets of `B`. -/
lemma os_sum_D_inv_le {B : Finset ℕ} {N K : ℕ} (hcard : B.card = K)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p) (hN : 1 ≤ N) {k : ℕ} (hk : 1 ≤ k) :
    ∑ v ∈ B.powerset.filter (fun v => v.card = k), (os_D v)⁻¹
      ≤ (K:ℝ) * ((1 + Real.log K) / N) ^ (k - 1) := by
  classical
  have hmaps : ∀ v ∈ B.powerset.filter (fun v => v.card = k), os_min v ∈ B := by
    intro v hv
    obtain ⟨hv1, hv2⟩ := Finset.mem_filter.mp hv
    have hne : v.Nonempty := Finset.card_pos.mp (by omega)
    exact Finset.mem_powerset.mp hv1 (os_min_mem hne)
  have hfib := (Finset.sum_fiberwise_of_maps_to hmaps (fun v => (os_D v)⁻¹)).symm
  rw [hfib]
  calc ∑ p₀ ∈ B, ∑ v ∈ (B.powerset.filter (fun v => v.card = k)).filter
        (fun v => os_min v = p₀), (os_D v)⁻¹
      ≤ ∑ p₀ ∈ B, ((1 + Real.log K) / N) ^ (k - 1) :=
        Finset.sum_le_sum fun p₀ hp₀ => os_fiber_D_inv_le hcard hsep hN hp₀ hk
    _ = (B.card : ℝ) * ((1 + Real.log K) / N) ^ (k - 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (K:ℝ) * ((1 + Real.log K) / N) ^ (k - 1) := by rw [hcard]

/-! ### Negated root sets: bridging to `F_const_gap` -/

lemma os_neg_injective : Function.Injective (fun p : ℕ => -(p:ℝ)) := by
  intro p q h
  have h' : -(p:ℝ) = -(q:ℝ) := h
  have h2 : (p:ℝ) = (q:ℝ) := by linarith
  exact_mod_cast h2

lemma os_neg_injOn (v : Finset ℕ) : Set.InjOn (fun p : ℕ => -(p:ℝ)) ↑v :=
  os_neg_injective.injOn

lemma os_prod_neg_image (v : Finset ℕ) (x : ℝ) :
    ∏ c ∈ v.image (fun p : ℕ => -(p:ℝ)), (x - c) = ∏ p ∈ v, (x + (p:ℝ)) := by
  rw [Finset.prod_image (os_neg_injOn v)]
  exact Finset.prod_congr rfl fun p _ => by ring

lemma os_max_image_neg {v : Finset ℕ} (hv : v.Nonempty) :
    (v.image (fun p : ℕ => -(p:ℝ))).max' (hv.image _) = -((v.min' hv : ℕ) : ℝ) := by
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    have h1 : v.min' hv ≤ p := v.min'_le p hp
    have h2 : ((v.min' hv : ℕ) : ℝ) ≤ (p:ℝ) := by exact_mod_cast h1
    simp only [neg_le_neg_iff]
    exact h2
  · apply Finset.le_max'
    exact Finset.mem_image.mpr ⟨v.min' hv, v.min'_mem hv, rfl⟩

/-- Class-2(ii) gap bound: if a consecutive same-`ω` pair has all shifted elementary
symmetric sums equal below the cardinality, then `b - a ≥ N · D(b.primeFactors)`. -/
lemma os_const_gap_ge {B : Finset ℕ} {x₀ N : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (hwin : ∀ p ∈ B, x₀ < p)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p)
    {a b : ℕ} (ha : a ∈ (∏ p ∈ B, p).divisors) (hb : b ∈ (∏ p ∈ B, p).divisors)
    (hab : a < b) (hcard2 : 2 ≤ a.primeFactors.card)
    (hcardeq : a.primeFactors.card = b.primeFactors.card)
    (heq : ∀ j, j < a.primeFactors.card →
      esymmShift x₀ a.primeFactors j = esymmShift x₀ b.primeFactors j) :
    (N:ℝ) * os_D b.primeFactors ≤ (b:ℝ) - (a:ℝ) := by
  have hu : a.primeFactors ⊆ B := os_primeFactors_subset hprime ha
  have hv : b.primeFactors ⊆ B := os_primeFactors_subset hprime hb
  have hune : a.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  have hvne : b.primeFactors.Nonempty := Finset.card_pos.mp (by omega)
  have hcasta : (a:ℝ) = ∏ p ∈ a.primeFactors, (p:ℝ) := os_cast_eq_prod hprime ha
  have hcastb : (b:ℝ) = ∏ p ∈ b.primeFactors, (p:ℝ) := os_cast_eq_prod hprime hb
  have hℓ : (0:ℝ) < (b:ℝ) - (a:ℝ) := by
    have h1 : (a:ℝ) < (b:ℝ) := by exact_mod_cast hab
    linarith
  have hconst := F_const_of_esymm_eq (x₀ := x₀) (s := b.primeFactors) (s' := a.primeFactors)
    (fun p hp => (hwin p (hv hp)).le) (fun p hp => (hwin p (hu hp)).le)
    hcardeq.symm
    (fun j hj => (heq j (by omega)).symm)
  have heqF : ∀ x : ℝ,
      ∏ c ∈ b.primeFactors.image (fun p : ℕ => -(p:ℝ)), (x - c)
      = (∏ c ∈ a.primeFactors.image (fun p : ℕ => -(p:ℝ)), (x - c)) + ((b:ℝ) - (a:ℝ)) := by
    intro x
    rw [os_prod_neg_image, os_prod_neg_image, hconst x, ← hcasta, ← hcastb]
  obtain ⟨hltmax, hgap⟩ := F_const_gap (hvne.image _) (hune.image _) hℓ heqF
  rw [os_max_image_neg hvne, os_max_image_neg hune] at hltmax hgap
  -- the minimum of `b`'s factors exceeds the minimum of `a`'s by more than `N`
  have hminlt : a.primeFactors.min' hune < b.primeFactors.min' hvne := by
    have h1 : ((a.primeFactors.min' hune : ℕ) : ℝ) < ((b.primeFactors.min' hvne : ℕ):ℝ) := by
      linarith
    exact_mod_cast h1
  have hminB_a : a.primeFactors.min' hune ∈ B := hu (a.primeFactors.min'_mem hune)
  have hminB_b : b.primeFactors.min' hvne ∈ B := hv (b.primeFactors.min'_mem hvne)
  have hsepmin := hsep _ hminB_a _ hminB_b hminlt
  have hgapmin : (N:ℝ) + 1 ≤ ((b.primeFactors.min' hvne : ℕ):ℝ)
      - ((a.primeFactors.min' hune : ℕ):ℝ) := by
    have h1 : a.primeFactors.min' hune + (N+1) ≤ b.primeFactors.min' hvne := by omega
    have h2 : ((a.primeFactors.min' hune : ℕ):ℝ) + ((N:ℝ)+1)
        ≤ ((b.primeFactors.min' hvne : ℕ):ℝ) := by exact_mod_cast h1
    linarith
  -- identify the product in `hgap` with `os_D b.primeFactors`
  have hprodD : ∏ c ∈ (b.primeFactors.image (fun p : ℕ => -(p:ℝ))).erase
        (-((b.primeFactors.min' hvne : ℕ):ℝ)),
        (-((b.primeFactors.min' hvne : ℕ):ℝ) - c) = os_D b.primeFactors := by
    have h1 : (b.primeFactors.image (fun p : ℕ => -(p:ℝ))).erase
        (-((b.primeFactors.min' hvne : ℕ):ℝ))
        = (b.primeFactors.erase (b.primeFactors.min' hvne)).image (fun p : ℕ => -(p:ℝ)) :=
      (Finset.image_erase os_neg_injective b.primeFactors (b.primeFactors.min' hvne)).symm
    rw [h1, os_prod_neg_image]
    have hosmin : os_min b.primeFactors = b.primeFactors.min' hvne := os_min_eq hvne
    unfold os_D
    rw [hosmin]
    exact Finset.prod_congr rfl fun p _ => by ring
  rw [hprodD] at hgap
  have hDnn : 0 ≤ os_D b.primeFactors := (os_D_pos hsep hv hvne).le
  calc (N:ℝ) * os_D b.primeFactors
      ≤ (-((a.primeFactors.min' hune : ℕ):ℝ) - -((b.primeFactors.min' hvne : ℕ):ℝ))
          * os_D b.primeFactors := by
        refine mul_le_mul_of_nonneg_right ?_ hDnn
        linarith
    _ ≤ (b:ℝ) - (a:ℝ) := hgap

/-! ### Class 2, sub-case (ii): the weighted divisor sum -/

lemma os_gsum_le {B : Finset ℕ} {N K : ℕ} (hprime : ∀ p ∈ B, p.Prime)
    (hcard : B.card = K) (hN : 1 ≤ N)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p)
    (hlogK : 2 * (1 + Real.log K) ≤ N) :
    ∑ b ∈ (∏ p ∈ B, p).divisors,
        (if 2 ≤ b.primeFactors.card then ((N:ℝ) * os_D b.primeFactors)⁻¹ else 0)
      ≤ 2*K*(1 + Real.log K)/N^2 := by
  classical
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hNne : (N:ℝ) ≠ 0 := hN0.ne'
  have hq0 : (0:ℝ) ≤ (1 + Real.log K)/N :=
    div_nonneg (one_add_log_natCast_nonneg K) (Nat.cast_nonneg N)
  have hq2 : (1 + Real.log K)/N ≤ 1/2 := by
    rw [div_le_div_iff₀ hN0 (by norm_num : (0:ℝ) < 2)]
    linarith
  have hstep1 : ∑ b ∈ (∏ p ∈ B, p).divisors,
      (if 2 ≤ b.primeFactors.card then ((N:ℝ) * os_D b.primeFactors)⁻¹ else 0)
      = ∑ v ∈ B.powerset.filter (fun v => 2 ≤ v.card), ((N:ℝ) * os_D v)⁻¹ := by
    rw [divisors_prodPrimes hprime,
      Finset.sum_image (f := fun b => if 2 ≤ b.primeFactors.card
        then ((N:ℝ) * os_D b.primeFactors)⁻¹ else 0) (prodPrimes_injOn hprime),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [primeFactors_prodPrimes fun p hp => hprime p (Finset.mem_powerset.mp hv hp)]
  rw [hstep1]
  have hmaps : ∀ v ∈ B.powerset.filter (fun v => 2 ≤ v.card),
      v.card ∈ Finset.Icc 2 K := by
    intro v hv
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hv
    refine Finset.mem_Icc.mpr ⟨h2, ?_⟩
    rw [← hcard]
    exact Finset.card_le_card (Finset.mem_powerset.mp h1)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun v => ((N:ℝ) * os_D v)⁻¹)]
  have hperk : ∀ k ∈ Finset.Icc 2 K,
      ∑ v ∈ (B.powerset.filter (fun v => 2 ≤ v.card)).filter (fun v => v.card = k),
        ((N:ℝ) * os_D v)⁻¹
      ≤ (N:ℝ)⁻¹ * ((K:ℝ) * ((1 + Real.log K) / N) ^ (k - 1)) := by
    intro k hk
    obtain ⟨hk2, hkK⟩ := Finset.mem_Icc.mp hk
    have hDpos : ∀ v ∈ B.powerset.filter (fun v => v.card = k), (0:ℝ) < os_D v := by
      intro v hv
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hv
      exact os_D_pos hsep (Finset.mem_powerset.mp h1)
        (Finset.card_pos.mp (by omega))
    calc ∑ v ∈ (B.powerset.filter (fun v => 2 ≤ v.card)).filter (fun v => v.card = k),
          ((N:ℝ) * os_D v)⁻¹
        ≤ ∑ v ∈ B.powerset.filter (fun v => v.card = k), ((N:ℝ) * os_D v)⁻¹ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro v hv
            obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hv
            exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp h1).1, h2⟩
          · intro v hv _
            have hD := hDpos v hv
            positivity
      _ = (N:ℝ)⁻¹ * ∑ v ∈ B.powerset.filter (fun v => v.card = k), (os_D v)⁻¹ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v hv => by rw [mul_inv]
      _ ≤ (N:ℝ)⁻¹ * ((K:ℝ) * ((1 + Real.log K) / N) ^ (k - 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact os_sum_D_inv_le hcard hsep hN (by omega)
  calc ∑ k ∈ Finset.Icc 2 K,
        ∑ v ∈ (B.powerset.filter (fun v => 2 ≤ v.card)).filter (fun v => v.card = k),
          ((N:ℝ) * os_D v)⁻¹
      ≤ ∑ k ∈ Finset.Icc 2 K, (N:ℝ)⁻¹ * ((K:ℝ) * ((1 + Real.log K)/N) ^ (k-1)) :=
        Finset.sum_le_sum hperk
    _ = (N:ℝ)⁻¹ * (K:ℝ) * ∑ k ∈ Finset.Icc 2 K, ((1 + Real.log K)/N) ^ (k-1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ (N:ℝ)⁻¹ * (K:ℝ) * (2 * ((1 + Real.log K)/N)) :=
        mul_le_mul_of_nonneg_left (os_geom_tail_le hq0 hq2 K) (by positivity)
    _ = 2*K*(1 + Real.log K)/N^2 := by
        field_simp

/-- Class 2, sub-case (ii): consecutive same-`ω ≥ 2` pairs with all shifted symmetric
sums equal. -/
lemma os_sameCard_ii_le {B : Finset ℕ} {x₀ H N K : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (hcard : B.card = K) (hN : 1 ≤ N)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p)
    (hlogK : 2 * (1 + Real.log K) ≤ N) :
    pairSumOn ((∏ p ∈ B, p).divisors)
        (fun a b => 2 ≤ a.primeFactors.card ∧ a.primeFactors.card = b.primeFactors.card ∧
          IsConsecutive ((∏ p ∈ B, p).divisors) a b ∧
          ∀ j, j < a.primeFactors.card →
            esymmShift x₀ a.primeFactors j = esymmShift x₀ b.primeFactors j)
      ≤ 2*K*(1 + Real.log K)/N^2 := by
  classical
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have hgnn : ∀ b ∈ (∏ p ∈ B, p).divisors,
      (0:ℝ) ≤ (if 2 ≤ b.primeFactors.card then ((N:ℝ) * os_D b.primeFactors)⁻¹ else 0) := by
    intro b hb
    split
    · rename_i h2
      have hD := os_D_pos hsep (os_primeFactors_subset hprime hb)
        (Finset.card_pos.mp (by omega))
      positivity
    · exact le_rfl
  refine le_trans (os_pairSumOn_le_of_forall fun S hS => ?_)
    (os_gsum_le hprime hcard hN hsep hlogK)
  have hterm : ∀ p ∈ S, invGap p.1 p.2
      ≤ (if 2 ≤ p.2.primeFactors.card then ((N:ℝ) * os_D p.2.primeFactors)⁻¹ else 0) := by
    intro p hp
    obtain ⟨ha, hb, hlt, h2, hceq, hcons, hall⟩ := hS p hp
    have hgap := os_const_gap_ge hprime (fun q hq => (hwin q hq).1) hsep
      ha hb hlt h2 hceq hall
    have hDpos := os_D_pos hsep (os_primeFactors_subset hprime hb)
      (Finset.card_pos.mp (by omega : 0 < p.2.primeFactors.card))
    have hND : (0:ℝ) < (N:ℝ) * os_D p.2.primeFactors := by positivity
    have h2b : 2 ≤ p.2.primeFactors.card := by omega
    rw [if_pos h2b]
    exact inv_anti₀ hND hgap
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2) ↑S := by
    intro p hp p' hp' he
    have hp1 := hS p (Finset.mem_coe.mp hp)
    have hp'1 := hS p' (Finset.mem_coe.mp hp')
    have he' : p.2 = p'.2 := he
    obtain ⟨-, -, -, -, -, hcons, -⟩ := hp1
    obtain ⟨-, -, -, -, -, hcons', -⟩ := hp'1
    have h1 : p.1 = p'.1 := os_consec_pred_unique hcons (he' ▸ hcons')
    exact Prod.ext h1 he'
  calc ∑ p ∈ S, invGap p.1 p.2
      ≤ ∑ p ∈ S, (if 2 ≤ p.2.primeFactors.card
          then ((N:ℝ) * os_D p.2.primeFactors)⁻¹ else 0) := Finset.sum_le_sum hterm
    _ = ∑ b ∈ S.image (fun p : ℕ × ℕ => p.2), (if 2 ≤ b.primeFactors.card
          then ((N:ℝ) * os_D b.primeFactors)⁻¹ else 0) :=
        (Finset.sum_image (f := fun b : ℕ => if 2 ≤ b.primeFactors.card
          then ((N:ℝ) * os_D b.primeFactors)⁻¹ else 0) hinj).symm
    _ ≤ ∑ b ∈ (∏ p ∈ B, p).divisors, (if 2 ≤ b.primeFactors.card
          then ((N:ℝ) * os_D b.primeFactors)⁻¹ else 0) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b hb _ => hgnn b hb
        intro b hb
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
        exact (hS p hp).2.1

/-- Class 2, sub-case (i): some shifted symmetric sum differs, so the gap is at
least `x₀/2`. -/
lemma os_sameCard_i_le {B : Finset ℕ} {x₀ H K : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (hcard : B.card = K) (hH : 1 ≤ H)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hbig : 8 * (2*H)^(K+1) ≤ x₀) :
    pairSumOn ((∏ p ∈ B, p).divisors)
        (fun a b => 2 ≤ a.primeFactors.card ∧ a.primeFactors.card = b.primeFactors.card ∧
          IsConsecutive ((∏ p ∈ B, p).divisors) a b ∧
          ∃ j, j < a.primeFactors.card ∧
            esymmShift x₀ a.primeFactors j ≠ esymmShift x₀ b.primeFactors j)
      ≤ 2*(4:ℝ)^K/x₀ := by
  classical
  have h2H1 : 1 ≤ (2*H)^(K+1) := Nat.one_le_pow _ _ (by omega)
  have hx₀8 : 8 ≤ x₀ := by omega
  have hx0R : (0:ℝ) < (x₀:ℝ) := by exact_mod_cast (by omega : 0 < x₀)
  refine os_pairSumOn_le_of_forall fun S hS => ?_
  have hterm : ∀ p ∈ S, invGap p.1 p.2 ≤ 2/(x₀:ℝ) := by
    intro p hp
    obtain ⟨ha, hb, hlt, h2, hceq, hcons, hj⟩ := hS p hp
    have hKa : p.1.primeFactors.card ≤ K := by
      rw [← hcard]
      exact Finset.card_le_card (os_primeFactors_subset hprime ha)
    have hga := F_nonconst_gap (x₀ := x₀) (H := H) (K := K)
      (fun q hq => hwin q (os_primeFactors_subset hprime ha hq))
      (fun q hq => hwin q (os_primeFactors_subset hprime hb hq))
      hceq hKa hH hbig hj
    rw [← os_cast_eq_prod hprime ha, ← os_cast_eq_prod hprime hb] at hga
    have habR : (p.1:ℝ) < (p.2:ℝ) := by exact_mod_cast hlt
    rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hga
    have hhalf : (0:ℝ) < (x₀:ℝ)/2 := by linarith
    calc invGap p.1 p.2 ≤ ((x₀:ℝ)/2)⁻¹ := inv_anti₀ hhalf hga
      _ = 2/(x₀:ℝ) := by rw [inv_div]
  have hsub : S ⊆ (∏ p ∈ B, p).divisors ×ˢ (∏ p ∈ B, p).divisors := by
    intro p hp
    exact Finset.mem_product.mpr ⟨(hS p hp).1, (hS p hp).2.1⟩
  have hScard : (S.card : ℝ) ≤ (2:ℝ)^K * (2:ℝ)^K := by
    have h1 : S.card ≤ ((∏ p ∈ B, p).divisors ×ˢ (∏ p ∈ B, p).divisors).card :=
      Finset.card_le_card hsub
    have h2 : ((∏ p ∈ B, p).divisors ×ˢ (∏ p ∈ B, p).divisors).card = 2^K * 2^K := by
      rw [Finset.card_product, card_divisors_prodPrimes hprime, hcard]
    rw [h2] at h1
    exact_mod_cast h1
  calc ∑ p ∈ S, invGap p.1 p.2 ≤ ∑ _p ∈ S, 2/(x₀:ℝ) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (2/(x₀:ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((2:ℝ)^K * (2:ℝ)^K) * (2/(x₀:ℝ)) := by
        refine mul_le_mul_of_nonneg_right hScard (by positivity)
    _ = 2*(4:ℝ)^K/x₀ := by
        have h4 : (2:ℝ)^K * (2:ℝ)^K = (4:ℝ)^K := by
          rw [← mul_pow]
          norm_num
        rw [h4]
        ring

/-! ### Class 2: consecutive pairs with equal `ω ≥ 2` -/

theorem oneScale_sameCard_le {B : Finset ℕ} {x₀ H N K : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (hcard : B.card = K) (hN : 1 ≤ N) (hH : 1 ≤ H)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p)
    (hbig : 8 * (2*H)^(K+1) ≤ x₀)
    (hlogK : 2 * (1 + Real.log K) ≤ N) :
    pairSumOn ((∏ p ∈ B, p).divisors)
        (fun a b => 2 ≤ a.primeFactors.card ∧ a.primeFactors.card = b.primeFactors.card ∧
                    IsConsecutive ((∏ p ∈ B, p).divisors) a b)
      ≤ 2*K*(1 + Real.log K)/N^2 + 2*(4:ℝ)^K/x₀ := by
  classical
  have hmono : pairSumOn ((∏ p ∈ B, p).divisors)
      (fun a b => 2 ≤ a.primeFactors.card ∧ a.primeFactors.card = b.primeFactors.card ∧
        IsConsecutive ((∏ p ∈ B, p).divisors) a b)
      ≤ pairSumOn ((∏ p ∈ B, p).divisors)
        (fun a b =>
          (2 ≤ a.primeFactors.card ∧ a.primeFactors.card = b.primeFactors.card ∧
            IsConsecutive ((∏ p ∈ B, p).divisors) a b ∧
            ∀ j, j < a.primeFactors.card →
              esymmShift x₀ a.primeFactors j = esymmShift x₀ b.primeFactors j) ∨
          (2 ≤ a.primeFactors.card ∧ a.primeFactors.card = b.primeFactors.card ∧
            IsConsecutive ((∏ p ∈ B, p).divisors) a b ∧
            ∃ j, j < a.primeFactors.card ∧
              esymmShift x₀ a.primeFactors j ≠ esymmShift x₀ b.primeFactors j)) := by
    refine pairSumOn_mono_pred fun a b _ _ _ hC => ?_
    obtain ⟨h2, hceq, hcons⟩ := hC
    by_cases hall : ∀ j, j < a.primeFactors.card →
        esymmShift x₀ a.primeFactors j = esymmShift x₀ b.primeFactors j
    · exact Or.inl ⟨h2, hceq, hcons, hall⟩
    · push Not at hall
      obtain ⟨j, hj, hne⟩ := hall
      exact Or.inr ⟨h2, hceq, hcons, j, hj, hne⟩
  refine le_trans hmono (le_trans (pairSumOn_or_le _ _ _) ?_)
  exact add_le_add (os_sameCard_ii_le hprime hcard hN hwin hsep hlogK)
    (os_sameCard_i_le hprime hcard hH hwin hbig)

/-! ### The trichotomy glue: the full one-scale gap-sum bound -/

theorem oneScale_gapSum_le {B : Finset ℕ} {x₀ H N K : ℕ}
    (hprime : ∀ p ∈ B, p.Prime) (hcard : B.card = K) (hN : 1 ≤ N) (hH : 1 ≤ H)
    (hwin : ∀ p ∈ B, x₀ < p ∧ p ≤ x₀ + H)
    (hsep : ∀ p ∈ B, ∀ q ∈ B, p < q → N < q - p)
    (hbig : 8 * (2*H)^(K+1) ≤ x₀) (hKH : 2*K*H ≤ x₀) (hx₀ : 4 ≤ x₀)
    (hlogK : 2 * (1 + Real.log K) ≤ N) :
    gapSum ((∏ p ∈ B, p).divisors)
      ≤ (K:ℝ)/N + (2*K*(1 + Real.log K)/N^2 + 2*(4:ℝ)^K/x₀) + (2:ℝ)^(K+3)*K/x₀ := by
  classical
  have hcover : ∀ a b, IsConsecutive ((∏ p ∈ B, p).divisors) a b →
      ((a ∈ B ∧ b ∈ B ∧ IsConsecutive ((∏ p ∈ B, p).divisors) a b) ∨
       ((2 ≤ a.primeFactors.card ∧ a.primeFactors.card = b.primeFactors.card ∧
         IsConsecutive ((∏ p ∈ B, p).divisors) a b) ∨
        a.primeFactors.card ≠ b.primeFactors.card)) := by
    intro a b hcons
    have ha := hcons.1
    have hb := hcons.2.1
    have hab := hcons.2.2.1
    by_cases hceq : a.primeFactors.card = b.primeFactors.card
    · rcases Nat.lt_or_ge a.primeFactors.card 2 with hlt2 | hge2
      · have hcase : a.primeFactors.card = 0 ∨ a.primeFactors.card = 1 := by omega
        rcases hcase with h0 | h1
        · exfalso
          have ha1 : a = 1 := os_eq_one_of_card_zero hprime ha h0
          have hb1 : b = 1 := os_eq_one_of_card_zero hprime hb (by omega)
          omega
        · exact Or.inl ⟨os_mem_B_of_card_one hprime ha h1,
            os_mem_B_of_card_one hprime hb (by omega), hcons⟩
      · exact Or.inr (Or.inl ⟨hge2, hceq, hcons⟩)
    · exact Or.inr (Or.inr hceq)
  have h1 : gapSum ((∏ p ∈ B, p).divisors)
      ≤ (K:ℝ)/N + ((2*K*(1 + Real.log K)/N^2 + 2*(4:ℝ)^K/x₀) + (2:ℝ)^(K+3)*K/x₀) := by
    refine le_trans (gapSum_le_pairSumOn hcover) ?_
    refine le_trans (pairSumOn_or_le _ _ _) ?_
    refine add_le_add (oneScale_primePart_le hcard hsep hN) ?_
    refine le_trans (pairSumOn_or_le _ _ _) ?_
    exact add_le_add
      (oneScale_sameCard_le hprime hcard hN hH hwin hsep hbig hlogK)
      (oneScale_diffCard_le hprime hcard hwin hKH hx₀ hH)
  linarith

end Erdos884
