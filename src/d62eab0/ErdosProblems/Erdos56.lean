/-

This is a Lean formalization of a solution to Erdős Problem 56.
https://www.erdosproblems.com/56

The original human proof was found by: Rudolf Ahlswede and Levon H. Khachatrian 

Ahlswede, Rudolf; Khachatrian, Levon H. On extremal sets without coprimes. Acta Arithmetica 66(1): 89–99 (1994). 

ChatGPT from OpenAI explained some proof of this result (not
necessarily the original human proof, instead prioritizing clarity).

The LaTeX file output from the previous step was auto-formalized into
Lean by Aristotle from Harmonic.

The final theorem statement is from the Formal Conjectures project
organized by Google DeepMind.  (Note: it was modified slightly by
hand, because Aristotle found that it was missing a condition!)

The proof is verified by Lean.  The exact version numbers below may be
necessary to type-check this proof.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

def P (k : ℕ) : ℕ := ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

def E (n k : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter (fun m => m.gcd (P k) > 1)

def has_no_k_plus_1_coprime (A : Finset ℕ) (k : ℕ) : Prop :=
  ∀ S ⊆ A, (S : Set ℕ).Pairwise Nat.Coprime → S.card ≤ k

noncomputable def f (n k : ℕ) : ℕ :=
  ((Finset.powerset (Finset.Icc 1 n)).filter (fun A => has_no_k_plus_1_coprime A k)).sup Finset.card

def t_val : ℕ := 209
def k_val : ℕ := 212

def p (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

def C_set : Finset ℕ :=
  ((Finset.range 9).product (Finset.range 9)).image
    (fun x => p (t_val + x.1) * p (t_val + x.2))
  |>.filter (fun m => ∃ i j, 0 ≤ i ∧ i < j ∧ j ≤ 8 ∧ m = p (t_val + i) * p (t_val + j))

def B_set (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter (fun m => m.gcd (P (t_val - 1)) > 1)

def A_set (n : ℕ) : Finset ℕ := B_set n ∪ C_set

def satisfies_H (t : ℕ) : Prop :=
  p (t + 7) * p (t + 8) < p t * p (t + 9) ∧ p (t + 9) < (p t) ^ 2

def interval_start (t : ℕ) : ℕ := p (t + 7) * p (t + 8)
def interval_end (t : ℕ) : ℕ := p t * p (t + 9)

def B (t n : ℕ) : Finset ℕ := (Finset.Icc 1 n).filter (fun m => m.gcd (P (t - 1)) > 1)

def C (t : ℕ) : Finset ℕ :=
  ((Finset.range 9).product (Finset.range 9)).image
    (fun x => p (t + x.1) * p (t + x.2))
  |>.filter (fun m => ∃ i j, i < j ∧ j ≤ 8 ∧ m = p (t + i) * p (t + j))

def A (t n : ℕ) : Finset ℕ := B t n ∪ C t

def D (t n : ℕ) : Finset ℕ := (E n (t + 3)) \ (B t n)

lemma E_no_k_plus_1 (n k : ℕ) : has_no_k_plus_1_coprime (E n k) k := by
  intro S;
  -- For each element $s \in S$, there exists a prime $p_j$ in the set $\{p_1, p_2, \ldots, p_k\}$ such that $p_j \mid s$.
  intro hS_sub hS_coprime
  have h_prime_divisors : ∀ s ∈ S, ∃ j ∈ Finset.range k, Nat.Prime (Nat.nth Nat.Prime j) ∧ Nat.nth Nat.Prime j ∣ s := by
    intro s hs; specialize hS_sub hs; unfold E at hS_sub; aesop;
    -- Since $\gcd(s, P(k)) > 1$, there exists a prime $p$ such that $p \mid s$ and $p \mid P(k)$.
    obtain ⟨p, hp_prime, hp_div_s, hp_div_Pk⟩ : ∃ p, Nat.Prime p ∧ p ∣ s ∧ p ∣ P k := by
      -- Since $\gcd(s, P(k)) > 1$, there exists a prime $p$ that divides both $s$ and $P(k)$ by the definition of gcd.
      apply Nat.Prime.not_coprime_iff_dvd.mp; exact ne_of_gt right;
    -- Since $p \mid P(k)$, we know that $p$ is one of the first $k$ primes.
    have hp_prime_index : p ∈ Finset.image (fun i => Nat.nth Nat.Prime i) (Finset.range k) := by
      unfold P at hp_div_Pk; aesop;
      -- Since $p$ divides the product of the first $k$ primes, it must divide at least one of those primes.
      have hp_div_prime : ∃ i ∈ Finset.range k, p ∣ Nat.nth Nat.Prime i := by
        haveI := Fact.mk hp_prime; simp_all +decide [ ← ZMod.natCast_zmod_eq_zero_iff_dvd, Finset.prod_eq_zero_iff ] ;
      obtain ⟨ i, hi, hi' ⟩ := hp_div_prime; exact ⟨ i, Finset.mem_range.mp hi, by have := Nat.prime_dvd_prime_iff_eq hp_prime ( Nat.prime_nth_prime i ) ; aesop ⟩ ;
    aesop;
  choose! f hf using h_prime_divisors;
  have h_distinct_primes : Finset.card (Finset.image f S) ≤ k := by
    exact le_trans ( Finset.card_le_card ( Finset.image_subset_iff.mpr fun x hx => Finset.mem_range.mpr ( hf x hx |>.1 |> Finset.mem_range.mp ) ) ) ( by simpa );
  rwa [ Finset.card_image_of_injOn fun x hx y hy hxy => Classical.not_not.1 fun h => Nat.Prime.not_dvd_one ( hf x hx |>.2.1 ) <| hS_coprime hx hy h |> fun h => h.gcd_eq_one ▸ Nat.dvd_gcd ( hf x hx |>.2.2 ) ( hxy.symm ▸ hf y hy |>.2.2 ) ] at h_distinct_primes


lemma C_subset_n (t n : ℕ) (h_H : satisfies_H t) (h_n : interval_start t ≤ n) : C t ⊆ Finset.Icc 1 n := by
  intro x hx;
  -- Since $x \in C t$, we have $x = p(t+i) * p(t+j)$ for some $0 \leq i < j \leq 8$.
  obtain ⟨i, j, hi, hj, hx_eq⟩ : ∃ i j, 0 ≤ i ∧ i < j ∧ j ≤ 8 ∧ x = p (t + i) * p (t + j) := by
    unfold C at hx; aesop;
  -- Since $p$ is strictly increasing, $p(t+i) \leq p(t+7)$ and $p(t+j) \leq p(t+8)$.
  have h_p_le : p (t + i) ≤ p (t + 7) ∧ p (t + j) ≤ p (t + 8) := by
    -- Since $p$ is strictly increasing, if $i < j$, then $p(t+i) < p(t+j)$. Also, since $j \leq 8$, we have $p(t+j) \leq p(t+8)$.
    have h_p_le : ∀ i j : ℕ, i < j → j ≤ 8 → p (t + i) ≤ p (t + 7) ∧ p (t + j) ≤ p (t + 8) := by
      intros i j hij hj8;
      exact ⟨ Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( by omega ), Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( by omega ) ⟩;
    exact h_p_le i j hj hx_eq.1;
  exact Finset.mem_Icc.mpr ⟨ by nlinarith only [ hx_eq.2, h_p_le, Nat.Prime.pos ( show Nat.Prime ( p ( t + i ) ) from Nat.prime_nth_prime _ ), Nat.Prime.pos ( show Nat.Prime ( p ( t + j ) ) from Nat.prime_nth_prime _ ) ], by nlinarith only [ hx_eq.2, h_p_le, h_n, show interval_start t = p ( t + 7 ) * p ( t + 8 ) from rfl ] ⟩

lemma B_disjoint_C (t n : ℕ) : Disjoint (B t n) (C t) := by
  -- If $x \in B t n$, then $x$ is not coprime with $P(t-1)$, which means $x$ has a prime factor $q \leq p(t-1)$.
  have hB_factor : ∀ x ∈ B t n, ∃ q, Nat.Prime q ∧ q ∣ x ∧ q ≤ p (t - 1) := by
    -- Since $x$ is not coprime with $P(t-1)$, it must have a prime factor $q$ that divides $P(t-1)$.
    intro x hx
    obtain ⟨q, hq_prime, hq_div⟩ : ∃ q, Nat.Prime q ∧ q ∣ x ∧ q ∣ P (t - 1) := by
      -- Since $x$ is not coprime with $P(t-1)$, their greatest common divisor is greater than 1, which implies there exists a prime $q$ that divides both $x$ and $P(t-1)$.
      have h_gcd : Nat.gcd x (P (t - 1)) > 1 := by
        unfold B at hx; aesop;
      -- Since the gcd of x and P(t-1) is greater than 1, there exists a prime q that divides both x and P(t-1).
      apply Nat.Prime.not_coprime_iff_dvd.mp; exact ne_of_gt h_gcd;
    refine' ⟨ q, hq_prime, hq_div.1, _ ⟩;
    -- Since $q$ divides $P(t-1)$, it must be one of the prime factors of $P(t-1)$.
    have hq_factor : q ∈ Finset.image (fun i => Nat.nth Nat.Prime i) (Finset.range (t - 1)) := by
      have hq_prime_div : q ∣ ∏ i in Finset.range (t - 1), Nat.nth Nat.Prime i := by
        exact hq_div.2;
      simp_all +decide [ Nat.Prime.dvd_iff_not_coprime, Nat.coprime_prod_right_iff ];
      obtain ⟨ a, ha₁, ha₂ ⟩ := hq_prime_div; exact ⟨ a, ha₁, by have := Nat.coprime_primes hq_prime ( Nat.prime_nth_prime a ) ; aesop ⟩ ;
    norm_num +zetaDelta at *;
    obtain ⟨ a, ha₁, ha₂ ⟩ := hq_factor; exact ha₂ ▸ Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( Nat.le_sub_one_of_lt ha₁ ) ;
  -- If $x \in C t$, then $x$ is a product of primes $p(t+i)$ and $p(t+j)$ where $i, j \geq 0$. Since $p$ is strictly increasing, $p(t+i) \geq p(t)$ and $p(t+j) \geq p(t)$.
  have hC_factor : ∀ x ∈ C t, ∀ q, Nat.Prime q → q ∣ x → q ≥ p t := by
    -- Since $p$ is strictly increasing, $p(t+i) \geq p(t)$ and $p(t+j) \geq p(t)$ for any $i, j \geq 0$.
    have h_prime_factors : ∀ i j : ℕ, 0 ≤ i → i < j → j ≤ 8 → p (t + i) ≥ p t ∧ p (t + j) ≥ p t := by
      -- Since $p$ is strictly increasing, for any $m \geq n$, we have $p(m) \geq p(n)$.
      have h_prime_mono : ∀ m n : ℕ, m ≥ n → p m ≥ p n := by
        aesop;
        unfold p;
        rw [ Nat.nth_le_nth _ ];
        · omega;
        · exact Nat.infinite_setOf_prime;
      exact fun i j hi hj hj' => ⟨ h_prime_mono _ _ ( by linarith ), h_prime_mono _ _ ( by linarith ) ⟩;
    -- Since $x \in C t$, we can write $x = p(t+i) * p(t+j)$ for some $0 \leq i < j \leq 8$.
    intro x hx q hq_prime hq_div
    obtain ⟨i, j, hi, hj, hx_eq⟩ : ∃ i j : ℕ, 0 ≤ i ∧ i < j ∧ j ≤ 8 ∧ x = p (t + i) * p (t + j) := by
      unfold C at hx; aesop;
    simp_all +decide [ Nat.Prime.dvd_mul ];
    rcases hq_div with ( h | h ) <;> have := Nat.prime_dvd_prime_iff_eq hq_prime ( show Nat.Prime ( p ( t + i ) ) from Nat.prime_nth_prime _ ) <;> have := Nat.prime_dvd_prime_iff_eq hq_prime ( show Nat.Prime ( p ( t + j ) ) from Nat.prime_nth_prime _ ) <;> aesop;
    · linarith [ h_prime_factors i j hj left ];
    · linarith [ h_prime_factors i j hj left ];
  -- If there exists an element $x$ in both $B t n$ and $C t$, then by $hB_factor$, there exists a prime $q$ such that $q \mid x$ and $q \leq p(t-1)$. But by $hC_factor$, any prime divisor of $x$ must be $\geq p(t)$. This is a contradiction because $p(t-1) < p(t)$.
  have h_contradiction : ∀ x, x ∈ B t n → x ∈ C t → False := by
    -- If there exists an element $x$ in both $B t n$ and $C t$, then by $hB_factor$, there exists a prime $q$ such that $q \mid x$ and $q \leq p(t-1)$. But by $hC_factor$, any prime divisor of $x$ must be $\geq p(t)$. This is a contradiction because $p(t-1) < p(t)$, so $q$ cannot be both $\leq p(t-1)$ and $\geq p(t)$.
    intros x hx_B hx_C
    obtain ⟨q, hq_prime, hq_div_x, hq_le⟩ := hB_factor x hx_B
    have hq_ge : q ≥ p t := hC_factor x hx_C q hq_prime hq_div_x
    have h_contradiction : p t ≤ p (t - 1) := by
      grind;
    rcases t with ( _ | _ | t ) <;> simp_all +decide [ Nat.nth_zero ];
    · unfold B at hx_B; unfold C at hx_C; aesop;
      unfold P at right; aesop;
    · unfold B C at * ; aesop;
      unfold P at * ; aesop;
    · exact h_contradiction.not_lt ( Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( Nat.lt_succ_self _ ) );
  exact Finset.disjoint_left.mpr h_contradiction


lemma t_ge_one_of_satisfies_H (t : ℕ) (h : satisfies_H t) : t ≥ 1 := by
  contrapose! h; aesop; ( unfold satisfies_H at *; aesop );
  unfold p at * ; norm_num at *;
  linarith [ Nat.Prime.two_le ( Nat.prime_nth_prime 6 ), Nat.Prime.two_le ( Nat.prime_nth_prime 7 ), Nat.Prime.two_le ( Nat.prime_nth_prime 8 ), Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( show 6 < 7 by norm_num ), Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( show 7 < 8 by norm_num ) ]

lemma C_map_injective (t : ℕ) (ht : t ≥ 1) :
  ∀ i j k l, 0 ≤ i ∧ i < j ∧ j ≤ 8 → 0 ≤ k ∧ k < l ∧ l ≤ 8 →
  p (t + i) * p (t + j) = p (t + k) * p (t + l) → i = k ∧ j = l := by
    -- By the uniqueness of prime factorization, the sets {p(t+i), p(t+j)} and {p(t+k), p(t+l)} must be equal.
    intros i j k l hi hj h_eq
    have h_set_eq : ({p (t + i), p (t + j)} : Finset ℕ) = ({p (t + k), p (t + l)} : Finset ℕ) := by
      -- Since $p$ is injective, the sets $\{p(t+i), p(t+j)\}$ and $\{p(t+k), p(t+l)\}$ must be equal.
      have h_prime_factors : ∀ {a b c d : ℕ}, Nat.Prime a → Nat.Prime b → Nat.Prime c → Nat.Prime d → a * b = c * d → ({a, b} : Finset ℕ) = ({c, d} : Finset ℕ) := by
        -- Since $a$ and $b$ are primes, the prime factors of $a * b$ are exactly $a$ and $b$. Similarly, the prime factors of $c * d$ are $c$ and $d$. Therefore, the sets $\{a, b\}$ and $\{c, d\}$ must be equal.
        intros a b c d ha hb hc hd h_eq
        have h_prime_factors : Nat.primeFactors (a * b) = {a, b} ∧ Nat.primeFactors (c * d) = {c, d} := by
          rw [ Nat.primeFactors_mul, Nat.primeFactors_mul ] <;> aesop;
        aesop;
      exact h_prime_factors ( Nat.prime_nth_prime _ ) ( Nat.prime_nth_prime _ ) ( Nat.prime_nth_prime _ ) ( Nat.prime_nth_prime _ ) h_eq;
    -- Since $p$ is strictly increasing, we have $p(t+i) = p(t+k)$ and $p(t+j) = p(t+l)$ or $p(t+i) = p(t+l)$ and $p(t+j) = p(t+k)$.
    have h_cases : p (t + i) = p (t + k) ∧ p (t + j) = p (t + l) ∨ p (t + i) = p (t + l) ∧ p (t + j) = p (t + k) := by
      rw [ Finset.ext_iff ] at h_set_eq ; aesop;
      cases h_set_eq ( p ( t + i ) ) ; cases h_set_eq ( p ( t + j ) ) ; aesop;
    unfold p at *;
    aesop;
    · have := Nat.nth_injective ( Nat.infinite_setOf_prime ) left_2; omega;
    · have := Nat.nth_injective ( Nat.infinite_setOf_prime ) right_2; aesop;
      omega;
    · have := Nat.nth_injective ( Nat.infinite_setOf_prime ) left_2; have := Nat.nth_injective ( Nat.infinite_setOf_prime ) right_2; aesop;
      omega;
    · have := Nat.nth_injective ( Nat.infinite_setOf_prime ) left_2; have := Nat.nth_injective ( Nat.infinite_setOf_prime ) right_2; omega;

lemma card_C (t : ℕ) (h : satisfies_H t) : (C t).card = 36 := by
  -- By definition of $C$, the set $C t$ is the image of the set of pairs $(i, j)$ with $0 \leq i < j \leq 8$ under the map $(i, j) \mapsto p(t+i)p(t+j)$.
  have hC_image : C t = Finset.image (fun (x : ℕ × ℕ) => Nat.nth Nat.Prime (t + x.1 - 1) * Nat.nth Nat.Prime (t + x.2 - 1)) (Finset.filter (fun x => x.1 < x.2 ∧ x.2 ≤ 8) (Finset.product (Finset.range 9) (Finset.range 9))) := by
    -- By definition of $C$, we know that $C t$ is the image of the set of pairs $(i, j)$ with $0 \leq i < j \leq 8$ under the map $(i, j) \mapsto p(t+i)p(t+j)$.
    ext; simp [C];
    constructor;
    · rintro ⟨ ⟨ a, b, ⟨ ha, hb ⟩, rfl ⟩, i, j, hij, hj, h ⟩ ; use i, j ; aesop;
      · linarith;
      · linarith;
    · aesop;
  -- To prove the cardinality, we show that the function (i, j) ↦ p(t+i)p(t+j) is injective on the set of pairs (i, j) with 0 ≤ i < j ≤ 8.
  have h_inj : ∀ i j k l : ℕ, 0 ≤ i → i < j → j ≤ 8 → 0 ≤ k → k < l → l ≤ 8 → Nat.nth Nat.Prime (t + i - 1) * Nat.nth Nat.Prime (t + j - 1) = Nat.nth Nat.Prime (t + k - 1) * Nat.nth Nat.Prime (t + l - 1) → i = k ∧ j = l := by
    -- Since the primes are distinct and ordered, the equality of the products implies the equality of the indices.
    intros i j k l hi hj hj8 hk hl hl8 h_eq
    have h_prime_eq : Nat.nth Nat.Prime (t + i - 1) = Nat.nth Nat.Prime (t + k - 1) ∧ Nat.nth Nat.Prime (t + j - 1) = Nat.nth Nat.Prime (t + l - 1) ∨ Nat.nth Nat.Prime (t + i - 1) = Nat.nth Nat.Prime (t + l - 1) ∧ Nat.nth Nat.Prime (t + j - 1) = Nat.nth Nat.Prime (t + k - 1) := by
      have := congr_arg ( fun x => x.factorization ( Nat.nth Nat.Prime ( t + i - 1 ) ) ) h_eq ; norm_num [ Nat.factorization_mul, Nat.Prime.ne_zero ] at this;
      rw [ Finsupp.single_apply, Finsupp.single_apply, Finsupp.single_apply ] at this ; aesop;
      · exact absurd h_2 ( Nat.Prime.ne_zero ( Nat.prime_nth_prime _ ) );
      · nlinarith [ Nat.Prime.one_lt ( Nat.prime_nth_prime ( t + i - 1 ) ) ];
    cases h_prime_eq <;> simp_all +decide [ Nat.nth_injective ];
    · have := Nat.nth_injective ( Nat.infinite_setOf_prime ) ( by tauto : Nat.nth Nat.Prime ( t + i - 1 ) = Nat.nth Nat.Prime ( t + k - 1 ) ) ; ( have := Nat.nth_injective ( Nat.infinite_setOf_prime ) ( by tauto : Nat.nth Nat.Prime ( t + j - 1 ) = Nat.nth Nat.Prime ( t + l - 1 ) ) ; aesop; );
      · rcases t with ( _ | _ | t ) <;> simp_all +arith +decide;
        have := h.1; ( have := h.2; ( norm_num [ Nat.nth_zero ] at *; ) );
        unfold p at * ; simp_all +decide [ Nat.Prime.two_le ];
        linarith [ Nat.Prime.two_le ( Nat.prime_nth_prime 6 ), Nat.Prime.two_le ( Nat.prime_nth_prime 7 ), Nat.Prime.two_le ( Nat.prime_nth_prime 8 ), Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( show 6 < 7 by norm_num ), Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( show 7 < 8 by norm_num ) ];
      · omega;
    · have := Nat.nth_injective ( Nat.infinite_setOf_prime ) ( by aesop : Nat.nth Nat.Prime ( t + i - 1 ) = Nat.nth Nat.Prime ( t + l - 1 ) ) ; have := Nat.nth_injective ( Nat.infinite_setOf_prime ) ( by aesop : Nat.nth Nat.Prime ( t + j - 1 ) = Nat.nth Nat.Prime ( t + k - 1 ) ) ; omega;
  exact hC_image.symm ▸ Finset.card_image_of_injOn ( fun x hx y hy hxy => by specialize h_inj x.1 x.2 y.1 y.2; aesop )

lemma card_A (t n : ℕ) (h_disjoint : Disjoint (B t n) (C t)) (h : satisfies_H t) : (A t n).card = (B t n).card + 36 := by
  -- By definition of C, we know that its cardinality is 36.
  have h_C_card : (C t).card = 36 := by
    -- Let's prove that the map $x \mapsto p_{t+x}$ is injective for $0 \leq x \leq 8$.
    have h_map_injective : Function.Injective (fun x : ℕ => p (t + x)) := by
      have h_inj : StrictMono (fun x => p (t + x)) := by
        refine' strictMono_nat_of_lt_succ fun x => _;
        apply Nat.nth_strictMono;
        · exact Nat.infinite_setOf_prime;
        · simp +zetaDelta at *;
          contrapose! h; aesop;
          cases a ; aesop;
          unfold p at *;
          norm_num [ Nat.nth_zero ] at *;
          rw [ show InfSet.sInf ( setOf Nat.Prime ) = 2 by exact le_antisymm ( Nat.sInf_le Nat.prime_two ) ( le_csInf ⟨ 2, Nat.prime_two ⟩ fun x hx => Nat.Prime.two_le hx ) ] at * ; norm_num at *;
          linarith [ Nat.Prime.two_le ( Nat.prime_nth_prime 6 ), Nat.Prime.two_le ( Nat.prime_nth_prime 7 ), Nat.Prime.two_le ( Nat.prime_nth_prime 8 ), Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( show 6 < 7 by norm_num ), Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( show 7 < 8 by norm_num ) ];
      exact h_inj.injective;
    -- Since the map $x \mapsto p_{t+x}$ is injective, the image of the set of pairs $\{(i,j) \mid 0 \leq i < j \leq 8\}$ under this map has the same cardinality as the set of pairs itself.
    have h_image_card : (Finset.image (fun (x : ℕ × ℕ) => p (t + x.1) * p (t + x.2)) (Finset.filter (fun (x : ℕ × ℕ) => x.1 < x.2 ∧ x.2 ≤ 8) (Finset.product (Finset.range 9) (Finset.range 9)))).card = (Finset.filter (fun (x : ℕ × ℕ) => x.1 < x.2 ∧ x.2 ≤ 8) (Finset.product (Finset.range 9) (Finset.range 9))).card := by
      apply Finset.card_image_of_injOn;
      intros x hx y hy hxy;
      -- Since the primes are distinct, the products being equal implies that the sets {p(t+x.1), p(t+x.2)} and {p(t+y.1), p(t+y.2)} are the same.
      have h_sets_eq : ({p (t + x.1), p (t + x.2)} : Finset ℕ) = ({p (t + y.1), p (t + y.2)} : Finset ℕ) := by
        have h_prime_factors : Nat.primeFactors (p (t + x.1) * p (t + x.2)) = {p (t + x.1), p (t + x.2)} ∧ Nat.primeFactors (p (t + y.1) * p (t + y.2)) = {p (t + y.1), p (t + y.2)} := by
          have h_prime_factors : ∀ i j : ℕ, Nat.Prime (p (t + i)) ∧ Nat.Prime (p (t + j)) → i ≠ j → Nat.primeFactors (p (t + i) * p (t + j)) = {p (t + i), p (t + j)} := by
            intros i j h_prime_factors h_neq; rw [ Nat.primeFactors_mul ] <;> aesop;
          exact ⟨ h_prime_factors _ _ ⟨ Nat.prime_nth_prime _, Nat.prime_nth_prime _ ⟩ ( by aesop ), h_prime_factors _ _ ⟨ Nat.prime_nth_prime _, Nat.prime_nth_prime _ ⟩ ( by aesop ) ⟩;
        grind;
      simp_all +decide [ Finset.Subset.antisymm_iff, Finset.subset_iff ];
      simp_all +decide [ h_map_injective.eq_iff ];
      grind +ring;
    -- Since $C t$ is defined as the image of the set of pairs under the map, we can conclude that their cardinalities are equal.
    have h_C_eq_image : C t = Finset.image (fun (x : ℕ × ℕ) => p (t + x.1) * p (t + x.2)) (Finset.filter (fun (x : ℕ × ℕ) => x.1 < x.2 ∧ x.2 ≤ 8) (Finset.product (Finset.range 9) (Finset.range 9))) := by
      ext; simp [C];
      constructor;
      · rintro ⟨ ⟨ a, b, ⟨ ha, hb ⟩, rfl ⟩, i, j, hij, hj, h ⟩ ; exact ⟨ i, j, ⟨ ⟨ by linarith, by linarith ⟩, hij, hj ⟩, h.symm ⟩;
      · rintro ⟨ a, b, ⟨ ⟨ ha, hb ⟩, hab, hb' ⟩, rfl ⟩ ; exact ⟨ ⟨ a, b, ⟨ ha, hb ⟩, rfl ⟩, a, b, hab, hb', rfl ⟩;
    exact h_C_eq_image ▸ h_image_card;
  rw [ ← h_C_card, ← Finset.card_union_of_disjoint h_disjoint, A ]


lemma p_strictMono_new {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) : p i < p j := by
  apply Nat.nth_strictMono;
  · exact Nat.infinite_setOf_prime;
  · -- Since $i < j$, subtracting 1 from both sides preserves the inequality.
    apply Nat.sub_lt_sub_right; exact hi; exact hij

lemma t_ge_one_of_satisfies_H_new (t : ℕ) (h : satisfies_H t) : t ≥ 1 := by
  exact t_ge_one_of_satisfies_H t h

lemma C_map_injective_new (t : ℕ) (ht : t ≥ 1) :
  ∀ i j k l, 0 ≤ i ∧ i < j ∧ j ≤ 8 → 0 ≤ k ∧ k < l ∧ l ≤ 8 →
  p (t + i) * p (t + j) = p (t + k) * p (t + l) → i = k ∧ j = l := by
    -- Apply the uniqueness factorization lemma.
    apply C_map_injective t ht

lemma card_C_new (t : ℕ) (h : satisfies_H t) : (C t).card = 36 := by
  -- Apply the lemma `card_C` with the given `h`.
  apply card_C; assumption

lemma card_A_new (t n : ℕ) (h_disjoint : Disjoint (B t n) (C t)) (h : satisfies_H t) : (A t n).card = (B t n).card + 36 := by
  rw [ show A t n = B t n ∪ C t from rfl, ← card_C t h, Finset.card_union_of_disjoint h_disjoint ]


lemma max_B (t n : ℕ) : has_no_k_plus_1_coprime (B t n) (t - 1) := by
  -- For each $u \in B$, there exists a prime $p_i$ in the set $\{p_1, p_2, \dots, p_{t-1}\}$ such that $p_i \mid u$.
  have h_prime_divisor (u : ℕ) (hu : u ∈ B t n) : ∃ i ∈ Finset.range (t - 1), Nat.nth Nat.Prime i ∣ u := by
    unfold B at hu; aesop;
    contrapose! right;
    exact le_of_eq ( Nat.Coprime.prod_right fun i hi => Nat.coprime_comm.mp <| Nat.Prime.coprime_iff_not_dvd ( Nat.prime_nth_prime i ) |>.2 <| right i <| Finset.mem_range.mp hi );
  -- For any pairwise coprime subset S of B, each element in S must be associated with a unique prime from the set {p_1, ..., p_{t-1}}.
  have h_association (S : Finset ℕ) (hS : S ⊆ B t n) (h_pairwise_coprime : (S : Set ℕ).Pairwise Nat.Coprime) : S.card ≤ (Finset.range (t - 1)).card := by
    field_simp;
    choose! f hf using h_prime_divisor;
    have h_unique_prime : ∀ u v : ℕ, u ∈ S → v ∈ S → u ≠ v → f u ≠ f v := by
      intro u v hu hv huv h; have := Nat.dvd_gcd ( hf u ( hS hu ) |>.2 ) ( h.symm ▸ hf v ( hS hv ) |>.2 ) ; aesop;
      simp_all +decide [ h_pairwise_coprime hu hv huv ];
      exact Nat.Prime.ne_one ( Nat.prime_nth_prime _ ) this;
    have h_unique_prime : (Finset.image f S).card ≤ (Finset.range (t - 1)).card := by
      exact Finset.card_le_card ( Finset.image_subset_iff.mpr fun u hu => hf u ( hS hu ) |>.1 );
    rwa [ Finset.card_image_of_injOn fun u hu v hv huv => by contrapose! huv; solve_by_elim, Finset.card_range ] at h_unique_prime;
  aesop


lemma max_C (t : ℕ) : has_no_k_plus_1_coprime (C t) 4 := by
  -- Define the function f that maps each element of C t to its corresponding pair of indices.
  set f : ℕ → Finset ℕ := fun x => Finset.filter (fun i => x % p (t + i) = 0) (Finset.range 9);
  -- Let $S$ be a pairwise coprime subset of $C$.
  intro S hS hS_coprime
  have h_disjoint : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (f x) (f y) := by
    -- If there exists an $i$ such that $p(t+i)$ divides both $x$ and $y$, then $p(t+i)$ would divide their gcd, which is 1. This is impossible since $p(t+i)$ is a prime number greater than 1.
    intros x hx y hy hxy
    by_contra h_inter
    obtain ⟨i, hi⟩ : ∃ i, i ∈ f x ∧ i ∈ f y := by
      -- By definition of disjointness, if two sets are not disjoint, then there exists an element in their intersection.
      apply Finset.not_disjoint_iff.mp h_inter;
    have h_div : p (t + i) ∣ Nat.gcd x y := by
      exact Nat.dvd_gcd ( Nat.dvd_of_mod_eq_zero ( Finset.mem_filter.mp hi.1 |>.2 ) ) ( Nat.dvd_of_mod_eq_zero ( Finset.mem_filter.mp hi.2 |>.2 ) );
    have := hS_coprime hx hy hxy; simp_all +decide [ Nat.dvd_gcd_iff ] ;
    exact Nat.Prime.ne_one ( Nat.prime_nth_prime _ ) h_div;
  -- The union of the images of S under f is a subset of {0, 1, ..., 8}, which has 9 elements.
  have h_union_card : (Finset.biUnion S f).card ≤ 9 := by
    -- Since each $f(x)$ is a subset of $\{0, 1, ..., 8\}$, the union of these subsets is also a subset of $\{0, 1, ..., 8\}$.
    have h_union_subset : Finset.biUnion S f ⊆ Finset.range 9 := by
      exact Finset.biUnion_subset.mpr fun x hx => Finset.filter_subset _ _;
    -- Since the union of the images of S under f is a subset of {0, 1, ..., 8}, its cardinality is at most 9.
    apply Finset.card_le_card h_union_subset;
  -- Since each element in S contributes at least 2 elements to the union, we have $2 * S.card \leq 9$.
  have h_card_f : ∀ x ∈ S, (f x).card ≥ 2 := by
    -- Since each element in S is of the form p(t+i) * p(t+j) with i < j, the set f x will contain at least i and j, making its cardinality at least 2.
    intros x hx
    obtain ⟨i, j, hij, hx_eq⟩ : ∃ i j, 0 ≤ i ∧ i < j ∧ j ≤ 8 ∧ x = p (t + i) * p (t + j) := by
      have := hS hx; unfold C at this; aesop;
    refine Finset.one_lt_card.mpr ⟨ i, ?_, j, ?_, ?_ ⟩ <;> aesop;
    · linarith;
    · linarith;
  -- Since the f(x) are pairwise disjoint, the sum of their cardinalities is equal to the cardinality of their union.
  have h_sum_card : ∑ x in S, (f x).card = (Finset.biUnion S f).card := by
    rw [ Finset.card_biUnion ] ; aesop;
  exact Nat.le_of_lt_succ ( by have := Finset.sum_le_sum h_card_f; norm_num at *; linarith )


lemma p_t_injective (t : ℕ) (ht : t ≥ 1) : Function.Injective (fun i => p (t + i)) := by
  -- Since $p$ is strictly increasing, if $p(t + i) = p(t + j)$, then $t + i = t + j$, which implies $i = j$.
  have h_inj : StrictMono (fun i => p (t + i)) := by
    exact fun i j hij => p_strictMono_new ( by linarith ) ( by linarith );
  exact StrictMono.injective h_inj

def prime_indices (t x : ℕ) : Finset ℕ := (Finset.range 9).filter (fun i => p (t + i) ∣ x)

lemma prime_indices_card (t x : ℕ) (hx : x ∈ C t) (ht : t ≥ 1) : (prime_indices t x).card = 2 := by
  -- Since $x \in C t$, there exist $a$ and $b$ such that $x = p(t+a) * p(t+b)$ and $0 \leq a < b \leq 8$.
  obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b, 0 ≤ a ∧ a < b ∧ b ≤ 8 ∧ x = p (t + a) * p (t + b) := by
    unfold C at hx; aesop;
  -- Since $p(t+i)$ divides $x$ if and only if $i = a$ or $i = b$, the set $\{i \mid p(t+i) \mid x\}$ is exactly $\{a, b\}$.
  have h_set_eq : {i | p (t + i) ∣ x} = {a, b} := by
    ext i; aesop;
    -- Since $p(t+i)$ divides $p(t+a) * p(t+b)$ and $p$ is injective, it must divide one of $p(t+a)$ or $p(t+b)$.
    have h_div : p (t + i) ∣ p (t + a) ∨ p (t + i) ∣ p (t + b) := by
      convert Nat.Prime.dvd_mul ( show Nat.Prime ( p ( t + i ) ) from Nat.prime_nth_prime _ ) |>.1 a_1 using 1;
    -- Since $p$ is injective, if $p(t+i)$ divides $p(t+a)$, then $t+i = t+a$, implying $i = a$. Similarly, if $p(t+i)$ divides $p(t+b)$, then $t+i = t+b$, implying $i = b$.
    have h_inj : ∀ i j, p (t + i) = p (t + j) → i = j := by
      exact fun i j hij => by simpa using StrictMono.injective ( show StrictMono ( fun x => p ( t + x ) ) from fun i j hij => by simpa using p_strictMono_new ( by linarith ) ( by linarith ) ) hij;
    exact Or.imp ( fun h => h_inj _ _ <| Nat.prime_dvd_prime_iff_eq ( by exact Nat.prime_nth_prime _ ) ( by exact Nat.prime_nth_prime _ ) |>.1 h ) ( fun h => h_inj _ _ <| Nat.prime_dvd_prime_iff_eq ( by exact Nat.prime_nth_prime _ ) ( by exact Nat.prime_nth_prime _ ) |>.1 h ) h_div;
  unfold prime_indices;
  rw [ Set.ext_iff ] at h_set_eq;
  rw [ Finset.card_eq_two ];
  exact ⟨ a, b, ne_of_lt hb, by ext i; aesop <;> linarith ⟩

lemma prime_indices_disjoint (t x y : ℕ) (hx : x ∈ C t) (hy : y ∈ C t) (h : Nat.Coprime x y) : Disjoint (prime_indices t x) (prime_indices t y) := by
  -- If $p(t+i)$ divides both $x$ and $y$, then it divides their gcd, which is 1. But since $p(t+i)$ is a prime, it can't divide 1. Hence, $i$ can't be in both prime_indices $t$ $x$ and prime_indices $t$ $y$.
  have h_not_div : ∀ i, p (t + i) ∣ x → p (t + i) ∣ y → False := by
    exact fun i hi hy => absurd ( Nat.dvd_gcd hi hy ) ( by rw [ h.gcd_eq_one ] ; exact Nat.Prime.not_dvd_one ( Nat.prime_nth_prime _ ) );
  exact Finset.disjoint_left.mpr fun i hi₁ hi₂ => h_not_div i ( Finset.mem_filter.mp hi₁ |>.2 ) ( Finset.mem_filter.mp hi₂ |>.2 )


lemma max_C_bound (t : ℕ) (ht : t ≥ 1) : has_no_k_plus_1_coprime (C t) 4 := by
  exact?


lemma card_union_indices (t : ℕ) (ht : t ≥ 1) (S : Finset ℕ) (hS : S ⊆ C t) (h_coprime : (S : Set ℕ).Pairwise Nat.Coprime) :
  (Finset.biUnion S (prime_indices t)).card = 2 * S.card := by
    -- Since each element in S has exactly two prime indices, and the prime indices sets are pairwise disjoint, the cardinality of the union is the sum of the cardinalities of each prime indices set.
    have h_card_union : (S.biUnion (prime_indices t)).card = ∑ x in S, (prime_indices t x).card := by
      rw [ Finset.card_biUnion ];
      exact fun x hx y hy hxy => prime_indices_disjoint t x y ( hS hx ) ( hS hy ) ( h_coprime hx hy hxy );
    rw [ h_card_union, Finset.sum_congr rfl fun x hx => prime_indices_card t x ( hS hx ) ht ] ; simp +decide [ mul_comm ]

lemma card_union_le_nine (t : ℕ) (S : Finset ℕ) (hS : S ⊆ C t) :
  (Finset.biUnion S (prime_indices t)).card ≤ 9 := by
    exact le_trans ( Finset.card_le_card ( Finset.biUnion_subset.mpr fun x hx => Finset.filter_subset _ _ ) ) ( by norm_num )

lemma max_C_bound_final (t : ℕ) (ht : t ≥ 1) : has_no_k_plus_1_coprime (C t) 4 := by
  exact max_C_bound t ht


lemma max_C_proven (t : ℕ) (ht : t ≥ 1) : has_no_k_plus_1_coprime (C t) 4 := by
  intro S hS h_coprime
  have h1 := card_union_indices t ht S hS h_coprime
  have h2 := card_union_le_nine t S hS
  rw [h1] at h2
  linarith

lemma card_split (A B S : Finset ℕ) (h_disjoint : Disjoint A B) (h_subset : S ⊆ A ∪ B) :
  S.card = (S ∩ A).card + (S ∩ B).card := by
    -- We can use the fact that for any finite sets $X$ and $Y$, if $X$ and $Y$ are disjoint then $|X \cup Y| = |X| + |Y|$.
    have h_card_union : (S ∩ A ∪ S ∩ B).card = (S ∩ A).card + (S ∩ B).card := by
      exact Finset.card_union_of_disjoint ( Finset.disjoint_left.mpr fun x hx hx' => Finset.disjoint_left.mp h_disjoint ( Finset.mem_of_mem_inter_right hx ) ( Finset.mem_of_mem_inter_right hx' ) ) |> Eq.trans <| by aesop;
    convert h_card_union using 2 ; ext ; aesop;
    -- Since $S \subseteq A \cup B$, if $a \in S$, then $a \in A \cup B$.
    apply Finset.mem_union.mp; exact h_subset a_1


lemma A_no_k_plus_1 (t n : ℕ) (h_H : satisfies_H t) : has_no_k_plus_1_coprime (A t n) (t + 3) := by
  -- Let S be a pairwise coprime subset of A(t, n). Then S can be split into S ∩ B(t, n) and S ∩ C(t).
  intro S hS
  have h_split : S.card = (S ∩ B t n).card + (S ∩ C t).card := by
    -- Since $B t n$ and $C t$ are disjoint, the intersection of $S$ with $B t n$ and $S$ with $C t$ are also disjoint.
    have h_disjoint : Disjoint (S ∩ B t n) (S ∩ C t) := by
      exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.disjoint_left.mp ( B_disjoint_C t n ) ( Finset.mem_inter.mp hx₁ |>.2 ) ( Finset.mem_inter.mp hx₂ |>.2 );
    rw [ ← Finset.card_union_of_disjoint h_disjoint, ← Finset.inter_union_distrib_left ];
    rw [ Finset.inter_eq_left.mpr ] ; aesop;
  -- Since $S$ is pairwise coprime, both $S \cap B(t, n)$ and $S \cap C(t)$ must also be pairwise coprime.
  intro h_pairwise_coprime
  have h_B : (S ∩ B t n).card ≤ t - 1 := by
    have := max_B t n;
    exact this _ ( Finset.inter_subset_right ) ( fun x hx y hy hxy => h_pairwise_coprime ( Finset.mem_of_mem_inter_left hx ) ( Finset.mem_of_mem_inter_left hy ) hxy ) |> le_trans ( by aesop )
  have h_C : (S ∩ C t).card ≤ 4 := by
    have := max_C_proven t ( t_ge_one_of_satisfies_H_new t h_H );
    exact this _ ( Finset.inter_subset_right ) ( fun x hx y hy hxy => h_pairwise_coprime ( Finset.mem_of_mem_inter_left hx ) ( Finset.mem_of_mem_inter_left hy ) hxy );
  linarith [ Nat.sub_add_cancel ( show 1 ≤ t from t_ge_one_of_satisfies_H t h_H ) ]


lemma C_map_injective_final (t : ℕ) (ht : t ≥ 1) :
  ∀ i j k l, 0 ≤ i ∧ i < j ∧ j ≤ 8 → 0 ≤ k ∧ k < l ∧ l ≤ 8 →
  p (t + i) * p (t + j) = p (t + k) * p (t + l) → i = k ∧ j = l := by
    exact?

lemma card_C_eq_36 (t : ℕ) (ht : t ≥ 1) : (C t).card = 36 := by
  -- Since $C t$ is the image of the set of pairs $(i, j)$ with $0 \leq i < j \leq 8$ under the injective map $(i, j) \mapsto p (t + i) * p (t + j)$, it must have the same cardinality as the domain.
  have h_card_eq : (Finset.image (fun x => p (t + x.1) * p (t + x.2)) (Finset.filter (fun x => x.1 < x.2) (Finset.product (Finset.range 9) (Finset.range 9)))).card = 36 := by
    rw [ Finset.card_image_of_injOn ];
    · native_decide;
    · intros x hx y hy hxy;
      have := C_map_injective_new t ht x.1 x.2 y.1 y.2 ; aesop;
      · exact this ( by linarith ) ( by linarith ) |>.1;
      · exact this ( by linarith ) ( by linarith ) |>.2;
  -- Since the function is injective, the cardinality of the image is equal to the cardinality of the domain.
  have h_card_eq : (Finset.image (fun x => p (t + x.1) * p (t + x.2)) (Finset.filter (fun x => x.1 < x.2) (Finset.product (Finset.range 9) (Finset.range 9)))).card = (C t).card := by
    -- Since the function is injective, the cardinality of the image is equal to the cardinality of the domain. Therefore, we can conclude that the cardinality of the image is 36.
    apply congr_arg Finset.card;
    ext; simp [C];
    exact ⟨ fun ⟨ a, b, h, h' ⟩ => ⟨ ⟨ a, b, ⟨ h.1, h' ⟩ ⟩, ⟨ a, b, h.2, by linarith, h'.symm ⟩ ⟩, fun ⟨ ⟨ a, b, ⟨ h₁, h₂ ⟩ ⟩, ⟨ i, j, h₃, h₄, h₅ ⟩ ⟩ => ⟨ i, j, ⟨ ⟨ by linarith, by linarith ⟩, h₃ ⟩, h₅.symm ⟩ ⟩;
  grind


lemma has_no_k_plus_1_coprime_union (B C : Finset ℕ) (k_B k_C : ℕ)
  (h_disjoint : Disjoint B C)
  (h_B : has_no_k_plus_1_coprime B k_B)
  (h_C : has_no_k_plus_1_coprime C k_C) :
  has_no_k_plus_1_coprime (B ∪ C) (k_B + k_C) := by
    intro S hS h_coprime;
    -- By card_split, we have |S| = |S ∩ B| + |S ∩ C|.
    have h_card_split : S.card = (S ∩ B).card + (S ∩ C).card := by
      rw [ ← Finset.card_union_of_disjoint ];
      · rw [ ← Finset.inter_union_distrib_left, Finset.inter_eq_left.mpr hS ];
      · simp_all +decide [ Finset.disjoint_left ];
    refine' h_card_split ▸ add_le_add ( h_B _ _ _ ) ( h_C _ _ _ );
    · exact Finset.inter_subset_right;
    · exact fun x hx y hy hxy => h_coprime ( Finset.mem_of_mem_inter_left hx ) ( Finset.mem_of_mem_inter_left hy ) hxy;
    · exact Finset.inter_subset_right;
    · exact fun x hx y hy hxy => h_coprime ( by aesop ) ( by aesop ) hxy

lemma A_no_k_plus_1_final (t n : ℕ) (h_H : satisfies_H t) (h_disjoint : Disjoint (B t n) (C t)) :
  has_no_k_plus_1_coprime (A t n) (t + 3) := by
    exact?


def D_primes (t : ℕ) : Finset ℕ := (Finset.range 4).image (fun i => p (t + i))
def D_squares (t : ℕ) : Finset ℕ := (Finset.range 4).image (fun i => p (t + i) ^ 2)
def D_products (t : ℕ) : Finset ℕ :=
  ((Finset.range 4).product (Finset.range 9)).image (fun x => p (t + x.1) * p (t + x.2))
  |>.filter (fun m => ∃ i j, 0 ≤ i ∧ i ≤ 3 ∧ 1 ≤ j ∧ j ≤ 8 ∧ i < j ∧ m = p (t + i) * p (t + j))

def D_union (t : ℕ) : Finset ℕ := D_primes t ∪ D_squares t ∪ D_products t

lemma D_union_subset_D (t n : ℕ) (h_H : satisfies_H t) (h_n : interval_start t ≤ n) :
  D_union t ⊆ D t n := by
    intro x hx;
    unfold D at *; aesop;
    · -- By definition of $D_union$, we know that $x$ is either in $D_primes$, $D_squares$, or $D_products$.
      cases' Finset.mem_union.mp hx with hx_prime hx_square hx_product;
      · unfold D_primes D_squares at hx_prime; aesop;
        · unfold E; aesop;
          · exact Nat.Prime.pos ( by unfold p; exact Nat.prime_nth_prime _ );
          · -- Since $p(t+w)$ is a prime number and $p(t+7) * p(t+8) \leq n$, it follows that $p(t+w) \leq p(t+8)$.
            have h_prime_le : p (t + w) ≤ p (t + 8) := by
              -- Since $p$ is strictly increasing, we have $p(t + w) \leq p(t + 8)$ for $w < 4$.
              have h_prime_le : StrictMono (fun i => p (t + i)) := by
                exact fun i j hij => p_strictMono_new ( by linarith [ t_ge_one_of_satisfies_H t h_H ] ) ( by linarith );
              exact h_prime_le.monotone ( by linarith );
            -- Since $p(t+7) * p(t+8) \leq n$, we have $p(t+8) \leq n$.
            have h_prime_le_n : p (t + 8) ≤ n := by
              have h_prime_le_n : p (t + 8) ≤ p (t + 7) * p (t + 8) := by
                exact le_mul_of_one_le_left ( Nat.zero_le _ ) ( Nat.Prime.pos ( by unfold p; exact Nat.prime_nth_prime _ ) );
              exact le_trans h_prime_le_n h_n;
            linarith;
          · -- Since $p(t+w)$ is a prime number greater than $t$, it must divide $P(t+3)$.
            have h_div : p (t + w) ∣ P (t + 3) := by
              have h_div : p (t + w) ∈ Finset.image (fun i => Nat.nth Nat.Prime i) (Finset.range (t + 3)) := by
                unfold p; aesop;
                exact ⟨ t + w - 1, by omega, rfl ⟩;
              unfold P; aesop;
              exact right ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_range.mpr left_1 );
            rw [ Nat.gcd_eq_left h_div ] ; exact Nat.Prime.one_lt ( by unfold p; exact Nat.prime_nth_prime _ );
        · -- Since $p(t + w)$ is a prime number, $p(t + w)^2$ is greater than 1 and less than or equal to $n$.
          have h_bounds : 1 ≤ p (t + w) ^ 2 ∧ p (t + w) ^ 2 ≤ n := by
            have h_bounds : p (t + w) ^ 2 ≤ p (t + 3) * p (t + 8) := by
              have h_bounds : p (t + w) ≤ p (t + 3) := by
                interval_cases w <;> norm_num [ p ];
                · rw [ Nat.nth_le_nth _ ];
                  · omega;
                  · exact Nat.infinite_setOf_prime;
                · rw [ Nat.nth_le_nth _ ];
                  · linarith;
                  · exact Nat.infinite_setOf_prime;
                · rw [ Nat.nth_le_nth _ ];
                  · linarith;
                  · exact Nat.infinite_setOf_prime;
              nlinarith [ show p ( t + 8 ) ≥ p ( t + 3 ) from Nat.le_of_lt ( p_strictMono_new ( by linarith [ t_ge_one_of_satisfies_H t h_H ] ) ( by linarith ) ) ];
            unfold interval_start at h_n;
            unfold p at * ; aesop;
            · exact Nat.one_le_pow _ _ ( Nat.Prime.pos ( by aesop ) );
            · refine le_trans h_bounds ?_;
              exact le_trans ( Nat.mul_le_mul ( Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( by linarith ) ) le_rfl ) h_n;
          unfold E; aesop;
          -- Since $p(t + w)$ is a prime number, $p(t + w)$ divides $P(t + 3)$.
          have h_div : p (t + w) ∣ P (t + 3) := by
            have h_div : p (t + w) ∈ Finset.image (fun i => Nat.nth Nat.Prime i) (Finset.range (t + 3)) := by
              interval_cases w <;> norm_num [ Finset.mem_image, Finset.mem_range ];
              · exact ⟨ t - 1, by omega, rfl ⟩;
              · unfold p; aesop;
              · exact ⟨ t + 2 - 1, by omega, by rfl ⟩;
              · unfold p; aesop;
            unfold P; aesop;
            exact right_1 ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_range.mpr left_2 );
          exact lt_of_lt_of_le ( by nlinarith only [ show p ( t + w ) > 1 from Nat.Prime.one_lt ( by unfold p; exact Nat.prime_nth_prime _ ) ] ) ( Nat.le_of_dvd ( Nat.gcd_pos_of_pos_left _ ( by positivity ) ) ( Nat.dvd_gcd ( dvd_pow_self _ two_ne_zero ) h_div ) );
      · unfold D_products at hx_square; aesop;
        unfold E; aesop;
        · exact Nat.mul_pos ( Nat.Prime.pos ( by unfold p; aesop ) ) ( Nat.Prime.pos ( by unfold p; aesop ) );
        · -- Since $p(t + w_1) * p(t + w_3)$ is a product of two primes in the range $[t, t+8]$, and $interval_start t = p(t+7) * p(t+8)$, we have $p(t + w_1) * p(t + w_3) \leq p(t+7) * p(t+8)$.
          have h_prod_le_interval_start : p (t + w_1) * p (t + w_3) ≤ p (t + 7) * p (t + 8) := by
            gcongr;
            · apply_rules [ Nat.nth_monotone ];
              · exact Nat.infinite_setOf_prime;
              · omega;
            · apply_rules [ Nat.nth_monotone ];
              · exact Nat.infinite_setOf_prime;
              · omega;
          exact le_trans h_prod_le_interval_start h_n;
        · refine' lt_of_lt_of_le _ ( Nat.le_of_dvd _ ( Nat.dvd_gcd ( dvd_mul_right _ _ ) ( Finset.dvd_prod_of_mem _ _ ) ) );
          · exact Nat.Prime.one_lt ( Nat.prime_nth_prime _ );
          · exact Nat.gcd_pos_of_pos_right _ ( Finset.prod_pos fun i hi => Nat.Prime.pos ( by aesop ) );
          · exact Finset.mem_range.mpr ( by omega );
    · -- Since $x \in D_union t$, we know that $x$ is coprime with $P(t-1)$.
      have h_coprime : Nat.gcd x (P (t - 1)) = 1 := by
        have h_coprime : ∀ i ∈ Finset.range (t - 1), Nat.gcd x (Nat.nth Nat.Prime i) = 1 := by
          unfold D_union at hx; aesop;
          · unfold D_primes at h; aesop;
            rw [ Nat.gcd_comm ];
            have h_coprime : Nat.nth Nat.Prime i ≠ p (t + w) := by
              refine' ne_of_lt ( Nat.nth_strictMono _ _ );
              · exact Nat.infinite_setOf_prime;
              · omega;
            exact Nat.coprime_iff_gcd_eq_one.mpr ( by have := Nat.coprime_primes ( Nat.prime_nth_prime i ) ( show Nat.Prime ( p ( t + w ) ) from Nat.prime_nth_prime _ ) ; aesop );
          · unfold D_squares at h; aesop;
            rw [ Nat.coprime_primes ] <;> norm_num;
            · refine' ne_of_gt _;
              refine' Nat.nth_strictMono _ _;
              · exact Nat.infinite_setOf_prime;
              · omega;
            · exact Nat.prime_nth_prime _;
          · unfold D_products at h_2; aesop;
            -- Since $p(t+w_1)$ and $p(t+w_3)$ are primes greater than $i$, they are coprime with $Nat.nth Nat.Prime i$.
            have h_coprime : Nat.gcd (p (t + w_1)) (Nat.nth Nat.Prime i) = 1 ∧ Nat.gcd (p (t + w_3)) (Nat.nth Nat.Prime i) = 1 := by
              have h_coprime : p (t + w_1) > Nat.nth Nat.Prime i ∧ p (t + w_3) > Nat.nth Nat.Prime i := by
                have h_coprime : ∀ j > i, Nat.nth Nat.Prime j > Nat.nth Nat.Prime i := by
                  intro j hj; rw [ gt_iff_lt ] ; rw [ Nat.nth_lt_nth ] ; aesop;
                  exact Nat.infinite_setOf_prime;
                exact ⟨ h_coprime _ ( by omega ), h_coprime _ ( by omega ) ⟩;
              exact ⟨ Nat.coprime_iff_gcd_eq_one.mpr <| by have := Nat.coprime_primes ( show Nat.Prime ( p ( t + w_1 ) ) from Nat.prime_nth_prime _ ) ( show Nat.Prime ( Nat.nth Nat.Prime i ) from Nat.prime_nth_prime _ ) ; aesop, Nat.coprime_iff_gcd_eq_one.mpr <| by have := Nat.coprime_primes ( show Nat.Prime ( p ( t + w_3 ) ) from Nat.prime_nth_prime _ ) ( show Nat.Prime ( Nat.nth Nat.Prime i ) from Nat.prime_nth_prime _ ) ; aesop ⟩;
            exact Nat.Coprime.mul h_coprime.1 h_coprime.2;
        exact Nat.Coprime.prod_right h_coprime;
      unfold B at a; aesop;


lemma D_primes_subset (t n : ℕ) (h_H : satisfies_H t) (h_n : interval_start t ≤ n) :
  D_primes t ⊆ D t n := by
    -- Each element of D_primes t is in E(n, t+3) and not in B t n, hence in D t n.
    intros x hx
    obtain ⟨i, hi⟩ : ∃ i ∈ Finset.range 4, x = p (t + i) := by
      -- By definition of $D_primes$, if $x \in D_primes t$, then there exists $i \in \{0, 1, 2, 3\}$ such that $x = p (t + i)$.
      simp [D_primes] at hx;
      aesop;
    -- Since $x \in D_primes t$, we have $x \in D_union t$.
    have hx_D_union : x ∈ D_union t := by
      unfold D_union; aesop;
    exact D_union_subset_D t n h_H h_n hx_D_union

lemma D_squares_subset (t n : ℕ) (h_H : satisfies_H t) (h_n : interval_start t ≤ n) :
  D_squares t ⊆ D t n := by
    intro x hx; unfold D_squares at hx; aesop;
    -- Since $p(t + w)$ is a prime number, $p(t + w)^2$ is divisible by $p(t + w)$, which is one of the primes in $P(t+3)$. Therefore, $p(t + w)^2$ is in $E(n, t+3)$.
    have h_in_E : p (t + w) ^ 2 ∈ E n (t + 3) := by
      -- Since $p(t+w)$ is a prime number, $p(t+w)^2$ is in the interval $[1, n]$ and not coprime with $P(t+3)$.
      have h_interval : p (t + w) ^ 2 ≤ n := by
        -- Since $p(t+w)$ is a prime number, $p(t+w)^2$ is in the interval $[1, n]$ and not coprime with $P(t+3)$, thus $p(t+w)^2 \leq n$.
        have h_interval : p (t + w) ^ 2 ≤ p (t + 3) ^ 2 := by
          -- Since $p$ is the nth prime and primes are strictly increasing, if $w < 4$, then $t + w \leq t + 3$.
          have h_prime_le : p (t + w) ≤ p (t + 3) := by
            apply_rules [ monotone_nat_of_le_succ, Nat.le_of_lt_succ ];
            · unfold p;
              intro n; cases n <;> norm_num [ Nat.nth_zero ] ; exact Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( by linarith ) ;
            · grind;
          exact Nat.pow_le_pow_left h_prime_le 2;
        have h_interval : p (t + 3) ^ 2 < p (t + 7) * p (t + 8) := by
          have h_interval : p (t + 3) < p (t + 7) ∧ p (t + 3) < p (t + 8) := by
            exact ⟨ p_strictMono_new ( by linarith [ t_ge_one_of_satisfies_H t h_H ] ) ( by linarith ), p_strictMono_new ( by linarith [ t_ge_one_of_satisfies_H t h_H ] ) ( by linarith ) ⟩;
          nlinarith only [ h_interval ];
        exact le_trans ‹_› ( le_trans h_interval.le h_n );
      unfold E; aesop;
      · exact Nat.one_le_pow _ _ ( Nat.Prime.pos ( by unfold p; exact Nat.prime_nth_prime _ ) );
      · -- Since $p(t+w)$ is a prime number, it divides $P(t+3)$.
        have h_div : p (t + w) ∣ P (t + 3) := by
          have h_div : p (t + w) ∣ ∏ i in Finset.range (t + 3), Nat.nth Nat.Prime i := by
            have h_prime : p (t + w) ∈ Finset.image (fun i => Nat.nth Nat.Prime i) (Finset.range (t + 3)) := by
              unfold p; aesop;
              exact ⟨ t + w - 1, by omega, rfl ⟩
            rw [ Finset.mem_image ] at h_prime; obtain ⟨ i, hi, hi' ⟩ := h_prime; exact hi'.symm ▸ Finset.dvd_prod_of_mem _ hi;
          exact h_div;
        exact lt_of_lt_of_le ( Nat.Prime.one_lt ( by unfold p; exact Nat.prime_nth_prime _ ) ) ( Nat.le_of_dvd ( Nat.gcd_pos_of_pos_left _ ( pow_pos ( Nat.Prime.pos ( by unfold p; exact Nat.prime_nth_prime _ ) ) _ ) ) ( Nat.dvd_gcd ( dvd_pow_self _ two_ne_zero ) h_div ) );
    unfold D; aesop;
    unfold B at a; unfold E at h_in_E; aesop;
    -- Since $p(t + w)$ is a prime number, $p(t + w)^2$ is coprime to $P(t-1)$.
    have h_coprime : Nat.gcd (p (t + w)) (P (t - 1)) = 1 := by
      -- Since $p(t + w)$ is a prime number and $P(t - 1)$ is the product of the first $t - 1$ primes, $p(t + w)$ cannot divide any of the primes in $P(t - 1)$.
      have h_not_div : ∀ i < t - 1, ¬(p (t + w) ∣ Nat.nth Nat.Prime i) := by
        -- Since $p(t + w)$ is a prime number and $i < t - 1$, $p(t + w)$ cannot divide any prime number less than or equal to $p(t - 1)$.
        intros i hi
        have h_prime_gt : p (t + w) > Nat.nth Nat.Prime i := by
          refine' Nat.nth_strictMono _ _;
          · exact Nat.infinite_setOf_prime;
          · omega;
        exact Nat.not_dvd_of_pos_of_lt ( Nat.Prime.pos ( by aesop ) ) h_prime_gt;
      refine' Nat.Coprime.prod_right fun i hi => _;
      exact Nat.Prime.coprime_iff_not_dvd ( show Nat.Prime ( p ( t + w ) ) from Nat.prime_nth_prime _ ) |>.2 ( h_not_div i ( Finset.mem_range.mp hi ) );
    simp_all +decide [ Nat.Coprime, Nat.Coprime.pow_left ]

lemma D_products_subset (t n : ℕ) (h_H : satisfies_H t) (h_n : interval_start t ≤ n) :
  D_products t ⊆ D t n := by
    -- To show that D_products t is a subset of D t n, we need to verify that each element of D_products t is in E(n, t+3) and not in B(t, n).
    intro x hx
    obtain ⟨i, j, hi, hj, h_prod⟩ : ∃ i j, 0 ≤ i ∧ i ≤ 3 ∧ 1 ≤ j ∧ j ≤ 8 ∧ i < j ∧ x = p (t + i) * p (t + j) := by
      unfold D_products at hx; aesop;
    refine' Finset.mem_sdiff.mpr ⟨ _, _ ⟩;
    · -- Since $p(t+i)$ is a prime factor of $P(t+3)$ and $x = p(t+i) * p(t+j)$, it follows that $x$ is not coprime with $P(t+3)$.
      have h_not_coprime : ¬Nat.Coprime x (P (t + 3)) := by
        -- Since $p(t+i)$ is a prime factor of $P(t+3)$ and $x = p(t+i) * p(t+j)$, it follows that $p(t+i)$ divides $x$ and $P(t+3)$.
        have h_div : p (t + i) ∣ x ∧ p (t + i) ∣ P (t + 3) := by
          aesop;
          -- Since $p(t+i)$ is a prime factor of $P(t+3)$, it must divide $P(t+3)$.
          have h_factor : p (t + i) ∈ Finset.image (fun k => Nat.nth Nat.Prime k) (Finset.range (t + 3)) := by
            unfold p; aesop;
            exact ⟨ t + i - 1, by omega, rfl ⟩;
          unfold P; aesop;
          exact right ▸ Finset.dvd_prod_of_mem _ ( Finset.mem_range.mpr left_3 );
        exact fun h => Nat.Prime.not_dvd_one ( show Nat.Prime ( p ( t + i ) ) from Nat.prime_nth_prime _ ) ( h.gcd_eq_one ▸ Nat.dvd_gcd h_div.1 h_div.2 );
      unfold E; aesop;
      · exact Nat.mul_pos ( Nat.Prime.pos ( by unfold p; aesop ) ) ( Nat.Prime.pos ( by unfold p; aesop ) );
      · -- Since $p(t+i)$ and $p(t+j)$ are primes greater than or equal to $p(t)$, we have $p(t+i) \leq p(t+3)$ and $p(t+j) \leq p(t+8)$.
        have h_pi_le_pt3 : p (t + i) ≤ p (t + 3) := by
          apply_rules [ Nat.nth_monotone ];
          · exact Nat.infinite_setOf_prime;
          · omega
        have h_pj_le_pt8 : p (t + j) ≤ p (t + 8) := by
          unfold p; interval_cases j <;> norm_num;
          all_goals exact Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( by linarith ) ;
        -- Since $p(t+3) < p(t+7)$ and $p(t+8) < p(t+8)$, we have $p(t+3) * p(t+8) < p(t+7) * p(t+8)$.
        have h_prod_lt_interval : p (t + 3) * p (t + 8) < p (t + 7) * p (t + 8) := by
          bound;
          · exact Nat.Prime.pos ( by unfold p; aesop );
          · apply p_strictMono_new; linarith; linarith;
        exact le_trans ( Nat.mul_le_mul h_pi_le_pt3 h_pj_le_pt8 ) ( le_trans h_prod_lt_interval.le h_n );
      · -- Since the gcd is not 1, it must be greater than 1.
        apply Nat.lt_of_le_of_ne; exact Nat.gcd_pos_of_pos_right _ (by
        exact Finset.prod_pos fun i hi => Nat.Prime.pos <| by aesop); exact Ne.symm h_not_coprime;
    · unfold B; aesop;
      -- Since $p(t+i)$ and $p(t+j)$ are primes greater than $p(t-1)$, they are coprime with $P(t-1)$.
      have h_coprime : Nat.gcd (p (t + i)) (P (t - 1)) = 1 ∧ Nat.gcd (p (t + j)) (P (t - 1)) = 1 := by
        have h_coprime : ∀ k, k ≥ t → Nat.gcd (p k) (P (t - 1)) = 1 := by
          unfold P p; aesop;
          refine' Nat.Coprime.prod_right fun i hi => _;
          rw [ Nat.coprime_primes ] <;> aesop;
          exact absurd a_3 ( ne_of_gt ( Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( by omega ) ) );
        exact ⟨ h_coprime _ ( by linarith ), h_coprime _ ( by linarith ) ⟩;
      exact Nat.le_of_eq ( Nat.Coprime.mul h_coprime.1 h_coprime.2 )

lemma D_union_subset (t n : ℕ) (h_H : satisfies_H t) (h_n : interval_start t ≤ n) :
  D_union t ⊆ D t n := by
  intro x hx
  rcases Finset.mem_union.mp hx with h | h
  · rcases Finset.mem_union.mp h with h_prime | h_square
    · exact D_primes_subset t n h_H h_n h_prime
    · exact D_squares_subset t n h_H h_n h_square
  · exact D_products_subset t n h_H h_n h


lemma p_lt_interval_start (t : ℕ) (ht : t ≥ 1) : p (t + 3) < interval_start t := by
  -- Since $p$ is strictly increasing for indices $\geq 1$, we have $p(t+3) < p(t+7)$ and $p(t+3) < p(t+8)$.
  have h_p_lt : p (t + 3) < p (t + 7) ∧ p (t + 3) < p (t + 8) := by
    exact ⟨ p_strictMono_new ( by linarith ) ( by linarith ), p_strictMono_new ( by linarith ) ( by linarith ) ⟩;
  -- Since $p(t+7)$ and $p(t+8)$ are primes, their product $p(t+7) * p(t+8)$ is greater than either of them.
  have h_prod_gt : p (t + 7) * p (t + 8) > p (t + 7) ∧ p (t + 7) * p (t + 8) > p (t + 8) := by
    exact ⟨ lt_mul_of_one_lt_right ( Nat.Prime.pos ( by exact Nat.prime_nth_prime _ ) ) ( Nat.Prime.one_lt ( by exact Nat.prime_nth_prime _ ) ), lt_mul_of_one_lt_left ( Nat.Prime.pos ( by exact Nat.prime_nth_prime _ ) ) ( Nat.Prime.one_lt ( by exact Nat.prime_nth_prime _ ) ) ⟩;
  -- Since $p(t+3) < p(t+7)$ and $p(t+3) < p(t+8)$, and $p(t+7) * p(t+8) > p(t+7)$ and $p(t+7) * p(t+8) > p(t+8)$, it follows that $p(t+3) < p(t+7) * p(t+8)$.
  apply lt_of_lt_of_le h_p_lt.left (Nat.le_of_lt h_prod_gt.left)


lemma D_prime_factors_ge_pt (t n : ℕ) (u : ℕ) (hu : u ∈ D t n) :
  ∀ q, Nat.Prime q → q ∣ u → q ≥ p t := by
    -- Since $u \in D t n$, we have $u \notin B t n$, which means $\gcd(u, P(t-1)) = 1$.
    have h_gcd : Nat.gcd u (P (t - 1)) = 1 := by
      unfold D at hu; aesop;
      unfold B at right; aesop;
      unfold E at left; aesop;
      exact le_antisymm right ( Nat.gcd_pos_of_pos_left _ left );
    -- Since $P(t-1)$ is the product of the first $t-1$ primes, if $q$ divides $u$ and $\gcd(u, P(t-1)) = 1$, then $q$ cannot be any of the first $t-1$ primes.
    have h_not_first_t_minus_1_primes : ∀ q, Nat.Prime q → q ∣ u → ¬(q ∈ Finset.image (Nat.nth Nat.Prime) (Finset.range (t - 1))) := by
      -- If $q$ is in the image of the first $t-1$ primes, then $q$ divides $P(t-1)$.
      intros q hq_prime hq_div_u hq_image
      have hq_div_P : q ∣ P (t - 1) := by
        aesop;
        exact Finset.dvd_prod_of_mem _ ( Finset.mem_range.mpr left );
      exact hq_prime.not_dvd_one <| h_gcd ▸ Nat.dvd_gcd hq_div_u hq_div_P;
    -- Since $q$ is not in the first $t-1$ primes, it must be one of the primes starting from $p_t$ onwards.
    have h_q_ge_pt : ∀ q, Nat.Prime q → q ∣ u → ∃ i ≥ t - 1, q = Nat.nth Nat.Prime i := by
      intros q hq_prime hq_div
      obtain ⟨i, hi⟩ : ∃ i, q = Nat.nth Nat.Prime i := by
        refine' ⟨ Nat.count ( Nat.Prime ) q, _ ⟩;
        field_simp;
      exact ⟨ i, not_lt.mp fun contra => h_not_first_t_minus_1_primes q hq_prime hq_div <| hi ▸ Finset.mem_image.mpr ⟨ i, Finset.mem_range.mpr contra, rfl ⟩, hi ⟩;
    intro q hq hq'; cases t <;> aesop;
    · unfold p; aesop;
      exact hq.two_le;
    · obtain ⟨ i, hi, rfl ⟩ := h_q_ge_pt q hq hq'; have := Nat.nth_monotone ( Nat.infinite_setOf_prime ) hi; aesop;


lemma D_prime_factors_ge_pt_new (t n : ℕ) (u : ℕ) (hu : u ∈ D t n) :
  ∀ q, Nat.Prime q → q ∣ u → q ≥ p t := by
    exact?


lemma prime_dvd_P_of_lt_pt (t : ℕ) (q : ℕ) (hq : Nat.Prime q) (h_lt : q < p t) :
  q ∣ P (t - 1) := by
    -- Since $q$ is a prime less than $p(t)$, it must be one of the primes in the set $\{p(1), p(2), \ldots, p(t-1)\}$.
    have h_prime_in_set : q ∈ Finset.image (fun i => Nat.nth Nat.Prime i) (Finset.range (t - 1)) := by
      -- Since $q$ is a prime less than $p(t)$, and $p(t)$ is the $t$-th prime, $q$ must be one of the first $t-1$ primes.
      have h_prime_in_range : ∃ i ∈ Finset.range (t - 1), Nat.nth Nat.Prime i = q := by
        have h_prime_lt_pt : q < Nat.nth Nat.Prime (t - 1) := by
          convert h_lt using 1
        -- Since $q$ is a prime less than the $(t-1)$th prime, and the primes are ordered, $q$ must be one of the primes in the first $t-1$ primes.
        have h_prime_in_range : ∃ i, Nat.nth Nat.Prime i = q := by
          -- Since $q$ is a prime number, and the nth prime function is surjective onto the set of primes, there must exist some $i$ such that $Nat.nth Nat.Prime i = q$.
          use Nat.count (Nat.Prime) q;
          exact Nat.nth_count hq;
        aesop;
        exact ⟨ w, Nat.lt_of_not_ge fun h => h_prime_lt_pt.not_le <| Nat.nth_monotone ( Nat.infinite_setOf_prime ) h, rfl ⟩;
      aesop;
    rw [ Finset.mem_image ] at h_prime_in_set; obtain ⟨ i, hi, rfl ⟩ := h_prime_in_set; exact Finset.dvd_prod_of_mem _ hi;

lemma D_prime_factors_ge_pt_final (t n : ℕ) (u : ℕ) (hu : u ∈ D t n) :
  ∀ q, Nat.Prime q → q ∣ u → q ≥ p t := by
    exact?


lemma D_has_small_prime_factor (t n : ℕ) (u : ℕ) (hu : u ∈ D t n) :
  ∃ q, Nat.Prime q ∧ q ∣ u ∧ q ≤ p (t + 3) := by
    -- Since $u \in E(n, t+3)$, there exists a prime $q$ such that $q \mid u$ and $q \mid P(t+3)$.
    obtain ⟨q, hq_prime, hq_div_u, hq_div_P⟩ : ∃ q, Nat.Prime q ∧ q ∣ u ∧ q ∣ P (t + 3) := by
      have h_prime_factor : Nat.gcd u (P (t + 3)) > 1 := by
        unfold D at hu; aesop;
        -- By definition of $E(n, k)$, if $u \in E(n, t+3)$, then $\gcd(u, P(t+3)) > 1$.
        apply Finset.mem_filter.mp left |>.2;
      exact Nat.Prime.not_coprime_iff_dvd.mp h_prime_factor.ne';
    -- Since $q$ divides $P(t+3)$, it must be one of the primes in the product $P(t+3)$.
    have hq_prime_divisors : q ∈ Finset.image (fun i => Nat.nth Nat.Prime i) (Finset.range (t + 3)) := by
      have hq_prime_divisors : q ∣ ∏ i in Finset.range (t + 3), Nat.nth Nat.Prime i := by
        exact hq_div_P;
      simp_all +decide [ Nat.Prime.dvd_iff_not_coprime, Nat.coprime_prod_right_iff ];
      -- Since $q$ is prime and not coprime with $Nat.nth Nat.Prime x$, it must be that $q = Nat.nth Nat.Prime x$.
      obtain ⟨x, hx₁, hx₂⟩ := hq_prime_divisors
      have hx₃ : q = Nat.nth Nat.Prime x := by
        have := Nat.coprime_primes hq_prime ( Nat.prime_nth_prime x ) ; aesop;
      aesop;
    unfold p; aesop;
    exact ⟨ _, Nat.prime_nth_prime _, hq_div_u, Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( by linarith ) ⟩


lemma has_no_k_plus_1_coprime_union_v2 (B C : Finset ℕ) (k_B k_C : ℕ)
  (h_disjoint : Disjoint B C)
  (h_B : has_no_k_plus_1_coprime B k_B)
  (h_C : has_no_k_plus_1_coprime C k_C) :
  has_no_k_plus_1_coprime (B ∪ C) (k_B + k_C) := by
  intro S hS h_coprime
  rw [card_split B C S h_disjoint hS]
  apply add_le_add
  · apply h_B
    · exact Finset.inter_subset_right
    · exact h_coprime.mono (Finset.inter_subset_left)
  · apply h_C
    · exact Finset.inter_subset_right
    · exact h_coprime.mono (Finset.inter_subset_left)

lemma D_prime_factors_ge_pt_v7 (t n : ℕ) (u : ℕ) (hu : u ∈ D t n) :
  ∀ q, Nat.Prime q → q ∣ u → q ≥ p t := by
  intro q hq hqu
  by_contra h_lt
  push_neg at h_lt
  have h_div_P : q ∣ P (t - 1) := prime_dvd_P_of_lt_pt t q hq h_lt
  have h_coprime : Nat.gcd u (P (t - 1)) = 1 := by
    have h_not_in_B : u ∉ B t n := (Finset.mem_sdiff.mp hu).2
    have h_in_E : u ∈ E n (t + 3) := (Finset.mem_sdiff.mp hu).1
    have h_in_Icc : u ∈ Finset.Icc 1 n := (Finset.mem_filter.mp h_in_E).1
    have h_u_pos : u > 0 := (Finset.mem_Icc.mp h_in_Icc).1
    have h_P_pos : P (t - 1) > 0 := by
      unfold P
      apply Finset.prod_pos
      intros
      exact Nat.Prime.pos (Nat.prime_nth_prime _)
    by_contra h_gcd_ne_1
    have h_gcd_gt_1 : u.gcd (P (t - 1)) > 1 := by
      apply Nat.lt_of_le_of_ne (Nat.gcd_pos_of_pos_left (P (t - 1)) h_u_pos) (Ne.symm h_gcd_ne_1)
    apply h_not_in_B
    rw [B, Finset.mem_filter]
    exact ⟨h_in_Icc, h_gcd_gt_1⟩
  have h_div_gcd : q ∣ Nat.gcd u (P (t - 1)) := Nat.dvd_gcd hqu h_div_P
  rw [h_coprime] at h_div_gcd
  exact Nat.Prime.not_dvd_one hq h_div_gcd


def D_extra (t : ℕ) : Finset ℕ := {p t * p (t + 9)}

def D_plus (t : ℕ) : Finset ℕ := D_union t ∪ D_extra t

lemma satisfies_H_209 : satisfies_H 209 := by
  -- We'll use that $p_{209} = 1289$, $p_{210} = 1291$, ..., $p_{218} = 1361$, and $p_{219} = 1373$.
  have h_p_values : Nat.nth Nat.Prime 208 = 1289 ∧ Nat.nth Nat.Prime 209 = 1291 ∧ Nat.nth Nat.Prime 210 = 1297 ∧ Nat.nth Nat.Prime 211 = 1301 ∧ Nat.nth Nat.Prime 212 = 1303 ∧ Nat.nth Nat.Prime 213 = 1307 ∧ Nat.nth Nat.Prime 214 = 1319 ∧ Nat.nth Nat.Prime 215 = 1321 ∧ Nat.nth Nat.Prime 216 = 1327 ∧ Nat.nth Nat.Prime 217 = 1361 := by
    -- We'll use the fact that the nth prime is the nth element in the list of primes.
    have h_prime_list : ∀ n, Nat.nth Nat.Prime n = Nat.recOn n 2 (fun n p => Nat.find (Nat.exists_infinite_primes (p + 1))) := by
      intro n;
      induction n <;> simp_all +decide [ Nat.nth_zero ];
      · exact le_antisymm ( Nat.sInf_le Nat.prime_two ) ( le_csInf ⟨ 2, Nat.prime_two ⟩ fun x hx => Nat.Prime.two_le hx );
      · rw [ Nat.nth_eq_sInf ];
        refine' le_antisymm _ _;
        · norm_num +zetaDelta at *;
          intro m hm₁ hm₂ hm₃; exact hm₁.not_le <| Nat.sInf_le ⟨ hm₃, fun k hk => by linarith [ Nat.nth_monotone ( Nat.infinite_setOf_prime ) <| Nat.le_of_lt_succ hk ] ⟩ ;
        · refine' le_csInf _ _;
          · exact ⟨ _, Nat.prime_nth_prime _, fun k hk => Nat.nth_strictMono ( Nat.infinite_setOf_prime ) ( Nat.lt_succ_of_le ( Nat.le_of_lt_succ hk ) ) ⟩;
          · aesop;
            exact ⟨ b, le_rfl, Nat.succ_le_of_lt ( a ▸ right _ ( Nat.lt_succ_self _ ) ), left ⟩;
    -- Apply the hypothesis `h_prime_list` to each `n` in the goal.
    simp [h_prime_list];
    native_decide;
  unfold satisfies_H; norm_num [ h_p_values ] ;
  unfold p; norm_num [ h_p_values ] ;

lemma m_structure (t : ℕ) (m : ℕ) (h_t : t = 209) (hm_le : m ≤ p (t + 9)) (hm_factors : ∀ r, Nat.Prime r → r ∣ m → p t ≤ r) : m = 1 ∨ Nat.Prime m := by
  -- If $m$ is composite, then $m = a * b$ for some $a, b > 1$.
  by_cases h_composite : ∃ a b, 1 < a ∧ 1 < b ∧ m = a * b;
  · -- Since $a$ and $b$ are both greater than 1, their prime factors are all at least $p t$. Therefore, $a \geq p t$ and $b \geq p t$.
    obtain ⟨a, b, ha, hb, hm⟩ := h_composite
    have ha_ge_pt : a ≥ p t := by
      exact hm_factors _ ( Nat.minFac_prime ha.ne' ) ( hm.symm ▸ dvd_mul_of_dvd_left ( Nat.minFac_dvd _ ) _ ) |> le_trans <| Nat.minFac_le ha.le
    have hb_ge_pt : b ≥ p t := by
      exact hm_factors _ ( Nat.minFac_prime ( by linarith ) ) ( hm.symm ▸ dvd_mul_of_dvd_right ( Nat.minFac_dvd _ ) _ ) |> le_trans <| Nat.minFac_le <| by linarith;
    -- Since $p t$ is the 209th prime, we have $p t \geq 1289$.
    have h_pt_ge_1289 : p t ≥ 1289 := by
      subst h_t;
      unfold p;
      rw [ Nat.nth_eq_sInf ];
      refine' le_csInf _ _;
      · exact ⟨ _, Nat.prime_nth_prime 208, fun k hk => Nat.nth_strictMono ( Nat.infinite_setOf_prime ) hk ⟩;
      · aesop;
        contrapose! right;
        use Nat.count ( Nat.Prime ) b_1;
        interval_cases b_1 <;> norm_num at left ⊢;
        all_goals native_decide;
    -- Since $p (t + 9)$ is the 218th prime, we have $p (t + 9) \leq 1361$.
    have h_pt9_le_1361 : p (t + 9) ≤ 1361 := by
      subst h_t;
      exact Nat.le_of_lt_succ ( Nat.nth_lt_of_lt_count ( by native_decide ) );
    nlinarith only [ ha_ge_pt, hb_ge_pt, h_pt_ge_1289, h_pt9_le_1361, hm_le, hm ];
  · rcases m with ( _ | _ | m ) <;> simp_all +decide [ Nat.prime_def_lt' ];
    · contrapose! hm_factors;
      exact ⟨ 2, by norm_num, by intros; linarith, by rw [ show p 209 = Nat.nth Nat.Prime 208 by rfl ] ; exact Nat.lt_of_le_of_lt ( Nat.Prime.two_le <| Nat.prime_nth_prime 0 ) <| Nat.nth_strictMono ( Nat.infinite_setOf_prime ) <| by norm_num ⟩;
    · exact fun x hx₁ hx₂ hx₃ => h_composite x hx₁ ( ( m + 1 + 1 ) / x ) ( by nlinarith [ Nat.div_mul_cancel hx₃ ] ) ( by nlinarith [ Nat.div_mul_cancel hx₃ ] )


def D_extra_v3 (t : ℕ) : Finset ℕ := {p t * p (t + 9)}

def D_plus_v3 (t : ℕ) : Finset ℕ := D_union t ∪ D_extra_v3 t

lemma p_t_sq_gt_p_t_plus_9_v3 (t : ℕ) (h_t : t = 209) : p t ^ 2 > p (t + 9) := by
  -- By definition of $p$, we know that $p 209 = 1289$ and $p 218 = 1361$.
  have h_p209 : p 209 = 1289 := by
    -- We can use the fact that the 209th prime is known to be 1289.
    have h_prime_209 : Nat.nth Nat.Prime 208 = 1289 := by
      have h_prime_list : Nat.nth Nat.Prime 208 = 1289 := by
        have h_prime_count : Nat.count Nat.Prime 1289 = 208 := by
          native_decide
        rw [ ← h_prime_count, Nat.nth_count ];
        native_decide +revert
      exact h_prime_list;
    exact h_prime_209
  have h_p218 : p 218 = 1361 := by
    -- We'll use the fact that $p_{218}$ is the $218$-th prime number.
    have h_prime_218 : Nat.nth Nat.Prime 217 = 1361 := by
      have : Nat.count (Nat.Prime) 1361 = 217 := by
        native_decide
      rw [ ← this, Nat.nth_count ];
      norm_num;
    exact h_prime_218;
  norm_num [ h_t, h_p209, h_p218 ]

lemma m_is_prime_or_one_v3 (t : ℕ) (m : ℕ) (h_t : t = 209) (hm_le : m ≤ p (t + 9)) (hm_factors : ∀ r, Nat.Prime r → r ∣ m → p t ≤ r) : m = 1 ∨ Nat.Prime m := by
  exact?


lemma D_subset_D_plus_final (t n : ℕ) (h_t : t = 209) (h_n : n = interval_end t) : D t n ⊆ D_plus t := by
  intro u hu
  obtain ⟨hu_E, hu_B⟩ := Finset.mem_sdiff.mp hu
  have hu_prime_factors : ∀ q, Nat.Prime q → q ∣ u → q ≥ p t := by
    exact?
  have hu_product : ∃ q m, u = q * m ∧ q ∈ D_primes t ∧ m ≤ p (t + 9) := by
    -- Since $u \in E n (t + 3)$, there exists a prime $q$ such that $q \mid u$ and $q \le p (t + 3)$.
    obtain ⟨q, hq_prime, hq_div, hq_le⟩ : ∃ q, Nat.Prime q ∧ q ∣ u ∧ q ≤ p (t + 3) := by
      exact?;
    -- Since $q$ is a prime divisor of $u$ and $q \leq p(t+3)$, and $p(t)$ is the $t$-th prime, $q$ must be one of $p(t)$, $p(t+1)$, $p(t+2)$, or $p(t+3)$. Therefore, $q \in D_primes t$.
    have hq_in_D_primes : q ∈ D_primes t := by
      have hq_in_D_primes : ∃ i ∈ Finset.range 4, q = p (t + i) := by
        have hq_in_D_primes : ∃ i, t ≤ i ∧ i ≤ t + 3 ∧ q = Nat.nth Nat.Prime (i - 1) := by
          have hq_in_D_primes : ∃ i, q = Nat.nth Nat.Prime i := by
            exact ⟨ Nat.count ( Nat.Prime ) q, by rw [ Nat.nth_count ] ; aesop ⟩;
          obtain ⟨ i, rfl ⟩ := hq_in_D_primes; use i + 1; aesop;
          · contrapose! hu_prime_factors;
            refine' ⟨ Nat.nth Nat.Prime i, Nat.prime_nth_prime _, hq_div, _ ⟩;
            refine' Nat.nth_strictMono _ _ |> lt_of_lt_of_le <| Nat.le_refl _;
            · exact Nat.infinite_setOf_prime;
            · exact hu_prime_factors.trans_le ( by norm_num );
          · -- Since $p_{212}$ is the 212th prime, and the nth prime is strictly increasing, if $Nat.nth Nat.Prime i \leq p_{212}$, then $i \leq 211$.
            have h_i_le_211 : i ≤ 211 := by
              have h_prime_le : Nat.nth Nat.Prime i ≤ Nat.nth Nat.Prime 211 := by
                convert hq_le using 1
              exact le_of_not_lt fun hi => h_prime_le.not_lt <| Nat.nth_strictMono ( Nat.infinite_setOf_prime ) hi;
            exact h_i_le_211;
        obtain ⟨ i, hi₁, hi₂, hi₃ ⟩ := hq_in_D_primes; use i - t; aesop; omega;
      aesop;
      exact Finset.mem_image.mpr ⟨ w, Finset.mem_range.mpr left, rfl ⟩;
    obtain ⟨ m, rfl ⟩ := hq_div; use q, m; aesop;
    have hm_le : q * m ≤ p 209 * p 218 := by
      unfold E at hu_E; aesop;
    generalize_proofs at *;
    nlinarith [ hu_prime_factors q hq_prime ( dvd_mul_right q m ), Nat.Prime.two_le hq_prime ]
  obtain ⟨q, m, hu_eq, hq_prime_factors, hm_le⟩ := hu_product
  have hm_factors : ∀ r, Nat.Prime r → r ∣ m → p t ≤ r := by
    -- Since $m \mid u$ and $u \in D t n$, any prime divisor of $m$ must also divide $u$. Therefore, by $hu_prime_factors$, those primes must be at least $p t$.
    intros r hr_prime hr_div_m
    have hr_div_u : r ∣ u := by
      exact hu_eq.symm ▸ dvd_mul_of_dvd_right hr_div_m _
    exact hu_prime_factors r hr_prime hr_div_u
  have hm_is_prime_or_one : m = 1 ∨ Nat.Prime m := by
    simp +zetaDelta at *;
    exact?
  have hu_in_D_plus : u ∈ D_plus t := by
    cases hm_is_prime_or_one <;> simp_all +decide [ Finset.subset_iff ];
    · -- Since $q \in D_{\text{primes}} 209$, and $D_{\text{primes}} 209 \subseteq D_{\text{union}} 209$, it follows that $q \in D_{\text{plus}} 209$.
      have hq_in_D_union : q ∈ D_union 209 := by
        exact Finset.mem_union_left _ ( Finset.mem_union_left _ hq_prime_factors )
      exact Finset.mem_union_left _ hq_in_D_union;
    · -- Since $m$ is prime and $m \leq p (t + 9)$, we have $m \in \{p t, \dots, p (t + 9)\}$.
      have hm_prime_factors : m ∈ Finset.image (fun i => p (209 + i)) (Finset.range 10) := by
        have hm_prime_factors : ∃ i ∈ Finset.range 10, m = p (209 + i) := by
          have h_prime_factors : ∃ i, m = p i := by
            use Nat.count ( Nat.Prime ) m + 1;
            unfold p; aesop;
          obtain ⟨i, hi⟩ := h_prime_factors
          have h_prime_factors : i ≤ 218 := by
            contrapose! hm_le;
            exact hi.symm ▸ p_strictMono_new ( by linarith ) hm_le;
          have h_prime_factors : i ≥ 209 := by
            contrapose! hm_factors; aesop;
            exact ⟨ p i, h, dvd_rfl, by
              apply_rules [ Nat.nth_strictMono ];
              · exact Nat.infinite_setOf_prime;
              · omega ⟩;
          exact ⟨ i - 209, Finset.mem_range.mpr ( by omega ), by rw [ hi, add_tsub_cancel_of_le h_prime_factors ] ⟩;
        aesop;
      aesop;
      by_cases hw : w = 9;
      · subst hw; unfold D_plus; aesop;
        -- Since $q$ is in $D_primes 209$, $q$ must be one of $p 209$, $p 210$, $p 211$, or $p 212$. However, if $q$ were any of the latter three, then $q * p 218$ would be larger than $interval_end 209$, contradicting the fact that $q * p 218$ is in $D 209 (interval_end 209)$. Therefore, $q$ must be $p 209$.
        have hq_eq_p209 : q = p 209 := by
          unfold D_primes at hq_prime_factors; aesop;
          have hq_le_p209 : p (209 + w) * p 218 ≤ p 209 * p 218 := by
            unfold E at hu_E; aesop;
          exact le_antisymm ( by nlinarith [ Nat.Prime.two_le h ] ) ( hu_prime_factors _ ( Nat.prime_nth_prime _ ) ( dvd_mul_right _ _ ) );
        exact Or.inr ( by unfold D_extra; aesop );
      · -- Since $w \neq 9$, we have $w \leq 8$, so $p (209 + w) \in \{p 209, \dots, p 217\}$.
        have hw_le_8 : w ≤ 8 := by
          omega;
        have hw_le_8 : q * p (209 + w) ∈ D_products 209 ∪ D_squares 209 := by
          unfold D_primes at hq_prime_factors; aesop;
          -- Since $w_1 < 4$ and $w \leq 8$, we can check all possible pairs $(w_1, w)$ to see if their product is in $D_products 209$ or $D_squares 209$.
          by_cases h_cases : w_1 = w;
          · unfold D_squares; aesop;
            exact Or.inr ⟨ w_1, left_1, by ring ⟩;
          · -- Since $w_1 \neq w$, we have either $w_1 < w$ or $w < w_1$. In either case, $p (209 + w_1) * p (209 + w)$ is in $D_products 209$.
            have h_prod : p (209 + w_1) * p (209 + w) ∈ D_products 209 := by
              apply Finset.mem_filter.mpr;
              cases lt_or_gt_of_ne h_cases <;> first | exact ⟨ Finset.mem_image.mpr ⟨ ( w_1, w ), Finset.mem_product.mpr ⟨ Finset.mem_range.mpr left_1, Finset.mem_range.mpr ( by linarith ) ⟩, rfl ⟩, w_1, w, by linarith, by linarith, by linarith, by linarith, by linarith, rfl ⟩ | exact ⟨ Finset.mem_image.mpr ⟨ ( w, w_1 ), Finset.mem_product.mpr ⟨ Finset.mem_range.mpr ( by linarith ), Finset.mem_range.mpr ( by linarith ) ⟩, by ring ⟩, w, w_1, by linarith, by linarith, by linarith, by linarith, by linarith, by ring ⟩ ;
            exact Or.inl h_prod;
        simp +decide +zetaDelta (disch := grind) at *;
        -- Since $q * p (209 + w)$ is in $D_products 209$ or $D_squares 209$, and $D_plus 209$ is the union of $D_union 209$ and $D_extra 209$, it follows that $q * p (209 + w)$ is in $D_plus 209$.
        apply Finset.mem_union_left; exact (by
        unfold D_union; aesop;)
  exact hu_in_D_plus

lemma card_D_plus_final (t : ℕ) (h_t : t = 209) : (D_plus t).card ≤ 35 := by
  -- By definition of $D_union$, we know that its cardinality is at most 34.
  have hD_union_card : (D_union t).card ≤ 34 := by
    -- Let's calculate the cardinality of each component of D_union t.
    have hD_primes_card : (D_primes t).card = 4 := by
      -- Since $p$ is injective, the image of $p (t + i)$ over the range $0$ to $3$ has cardinality $4$.
      have hD_primes_card : (Finset.image (fun i => p (t + i)) (Finset.range 4)).card = 4 := by
        exact Finset.card_image_of_injective _ fun x y hxy => by simpa using StrictMono.injective ( show StrictMono ( fun i => p ( t + i ) ) from by exact fun i j hij => p_strictMono_new ( by linarith ) ( by linarith ) ) hxy;
      exact hD_primes_card
    have hD_squares_card : (D_squares t).card = 4 := by
      rw [ show D_squares t = Finset.image ( fun i => p ( t + i ) ^ 2 ) ( Finset.range 4 ) from rfl, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective, h_t ];
      unfold p; aesop;
      have := Nat.nth_injective ( Nat.infinite_setOf_prime ) a ; aesop
    have hD_products_card : (D_products t).card ≤ 26 := by
      simp +arith +decide [ D_products ];
      refine' le_trans ( Finset.card_le_card _ ) _;
      exact Finset.image ( fun x : ℕ × ℕ => p ( t + x.1 ) * p ( t + x.2 ) ) ( Finset.filter ( fun x : ℕ × ℕ => x.1 ≤ 3 ∧ 1 ≤ x.2 ∧ x.2 ≤ 8 ∧ x.1 < x.2 ) ( Finset.range 4 ×ˢ Finset.range 9 ) );
      · simp ( config := { contextual := Bool.true } ) [ Finset.subset_iff ];
        exact fun x i j hi hj hx k hk l hl hl' hkl hx' => ⟨ k, l, ⟨ ⟨ by linarith, by linarith ⟩, by linarith, by linarith, by linarith, by linarith ⟩, hx' ▸ rfl ⟩;
      · exact Finset.card_image_le.trans ( by decide );
    refine' le_trans ( Finset.card_union_le _ _ ) _ ; linarith [ Finset.card_union_le ( D_primes t ∪ D_squares t ) ( D_products t ), Finset.card_union_le ( D_primes t ) ( D_squares t ) ];
  -- Since $D_{\text{extra}} t$ is a singleton set, its cardinality is 1.
  have hD_extra_card : (D_extra t).card = 1 := by
    -- Since $p t$ and $p (t + 9)$ are primes, their product is a single element. Therefore, the set $\{p t * p (t + 9)\}$ has exactly one element.
    simp [D_extra];
  exact le_trans ( Finset.card_union_le _ _ ) ( by linarith )

lemma card_C_209_final (t : ℕ) (h_t : t = 209) : (C t).card = 36 := by
  subst h_t; exact card_C 209 satisfies_H_209;


lemma D_decomp_final (t n : ℕ) (h_t : t = 209) (h_n : n = interval_end t) (u : ℕ) (hu : u ∈ D t n) :
  ∃ q ∈ D_primes t, ∃ m, u = q * m ∧ (m = 1 ∨ (Nat.Prime m ∧ p t ≤ m)) ∧ m ≤ p (t + 9) := by
    -- Since $u \in D t n$, it must have a prime factor $q$ that divides $P(t + 3)$ but not $P(t - 1)$. Therefore, $q \in \{p t, p (t + 1), p (t + 2), p (t + 3)\}$.
    obtain ⟨q, hq_prime, hq_div⟩ : ∃ q, Nat.Prime q ∧ q ∣ u ∧ q ∈ D_primes t := by
      -- Since $u \in D t n$, it must have a prime factor $q$ that divides $P(t + 3)$ but not $P(t - 1)$. Therefore, $q \in \{p t, p (t + 1), p (t + 2), p (t + 3)\}$ by definition of $D t n$.
      obtain ⟨q, hq_prime, hq_div⟩ : ∃ q, Nat.Prime q ∧ q ∣ u ∧ q ∣ P (t + 3) ∧ ¬(q ∣ P (t - 1)) := by
        unfold D at hu; aesop;
        unfold E B at * ; aesop;
        obtain ⟨ q, hq ⟩ := Nat.Prime.not_coprime_iff_dvd.mp ( ne_of_gt right_1 );
        bound;
        exact ⟨ q, left_1, left_2, right_3, fun h => right.not_lt <| Nat.lt_of_lt_of_le ( Nat.Prime.one_lt left_1 ) <| Nat.le_of_dvd ( Nat.gcd_pos_of_pos_left _ left ) <| Nat.dvd_gcd left_2 h ⟩;
      unfold P at *; aesop;
      -- Since $q$ divides the product of the first 212 primes but not the product of the first 208 primes, $q$ must be one of the primes in the range from 208 to 211.
      have hq_range : ∃ i ∈ Finset.range 4, q = Nat.nth Nat.Prime (208 + i) := by
        have hq_range : ∃ i ∈ Finset.range 212, q = Nat.nth Nat.Prime i := by
          simp_all +contextual [ Nat.Prime.dvd_iff_not_coprime, Nat.coprime_prod_right_iff, Nat.coprime_prod_left_iff ];
          obtain ⟨ i, hi, hi' ⟩ := left_1; use i; aesop;
          have := Nat.coprime_primes hq_prime ( Nat.prime_nth_prime i ) ; aesop;
        obtain ⟨ i, hi, rfl ⟩ := hq_range;
        exact ⟨ i - 208, Finset.mem_range.mpr ( by rw [ tsub_lt_iff_left ] <;> linarith [ Finset.mem_range.mp hi, show i ≥ 208 from le_of_not_lt fun hi' => right <| Finset.dvd_prod_of_mem _ <| Finset.mem_range.mpr hi' ] ), by rw [ add_tsub_cancel_of_le <| by linarith [ Finset.mem_range.mp hi, show i ≥ 208 from le_of_not_lt fun hi' => right <| Finset.dvd_prod_of_mem _ <| Finset.mem_range.mpr hi' ] ] ⟩;
      unfold D_primes; aesop;
      exact ⟨ _, Nat.prime_nth_prime _, left, w, left_2, by interval_cases w <;> rfl ⟩;
    -- Since $u \in D t n$, we have $u \leq n = p t p (t + 9)$. Therefore, $m = u / q \leq p (t + 9)$.
    obtain ⟨m, hm⟩ : ∃ m, u = q * m ∧ m ≤ p (t + 9) := by
      -- Since $u \in D t n$, we have $u \leq n = p t p (t + 9)$. Therefore, $m = u / q \leq p (t + 9)$ because $q \geq p t$.
      have hm_le : u ≤ p t * p (t + 9) := by
        unfold D at hu; aesop;
        unfold E at left_1; aesop;
      -- Since $q \geq p t$ and $u \leq p t * p (t + 9)$, we have $m = u / q \leq p (t + 9)$.
      have hm_le : q ≥ p t := by
        -- Since $q \in D_primes t$, we have $q \geq p t$ by definition of $D_primes t$.
        have hq_ge_pt : q ∈ Finset.image (fun i => p (t + i)) (Finset.range 4) := by
          exact hq_div.2;
        aesop;
        interval_cases w <;> exact Nat.nth_monotone ( Nat.infinite_setOf_prime ) ( by norm_num );
      exact ⟨ u / q, by rw [ Nat.mul_div_cancel' hq_div.1 ], Nat.div_le_of_le_mul <| by nlinarith ⟩;
    have hm_factors : ∀ r, Nat.Prime r → r ∣ m → p t ≤ r := by
      intros r hr hr_div
      have hr_div_u : r ∣ u := by
        exact hm.1.symm ▸ dvd_mul_of_dvd_right hr_div _;
      exact?;
    have := m_is_prime_or_one_v3 t m h_t hm.2 hm_factors; aesop;

lemma D_subset_D_plus_final_v2 (t n : ℕ) (h_t : t = 209) (h_n : n = interval_end t) : D t n ⊆ D_plus t := by
  aesop;
  -- Apply the lemma that states D t n is a subset of D_plus t.
  apply D_subset_D_plus_final; norm_num; norm_num

lemma card_D_plus_final_v2 (t : ℕ) (h_t : t = 209) : (D_plus t).card ≤ 35 := by
  -- Apply the lemma `card_D_plus_final` with the given `h_t`.
  rw [h_t]
  apply card_D_plus_final
  norm_cast

lemma card_C_209_final_v2 (t : ℕ) (h_t : t = 209) : (C t).card = 36 := by
  subst h_t;
  exact?


lemma D_decomp_final_v3 (t n : ℕ) (h_t : t = 209) (h_n : n = interval_end t) (u : ℕ) (hu : u ∈ D t n) :
  ∃ q ∈ D_primes t, ∃ m, u = q * m ∧ (m = 1 ∨ (Nat.Prime m ∧ p t ≤ m)) ∧ m ≤ p (t + 9) := by
    exact?

lemma D_subset_D_plus_final_v3 (t n : ℕ) (h_t : t = 209) (h_n : n = interval_end t) : D t n ⊆ D_plus t := by
  exact?

lemma card_D_plus_final_v3 (t : ℕ) (h_t : t = 209) : (D_plus t).card ≤ 35 := by
  exact h_t.symm ▸ card_D_plus_final_v2 _ rfl

lemma card_C_209_final_v3 (t : ℕ) (h_t : t = 209) : (C t).card = 36 := by
  -- By definition of $C$, we know that its cardinality is 36 when $t = 209$.
  apply card_C_209_final_v2 t h_t


lemma D_subset_D_plus_v5 (t n : ℕ) (h_t : t = 209) (h_n : n = interval_end t) : D t n ⊆ D_plus_v3 t := by
  apply_rules [ D_subset_D_plus_final_v2 ]

lemma card_D_plus_v5 (t : ℕ) (h_t : t = 209) : (D_plus_v3 t).card ≤ 35 := by
  bound;
  -- Apply the lemma `card_D_plus_final_v3` with `t = 209`.
  apply card_D_plus_final_v3 209 rfl

lemma card_C_209_v5 (t : ℕ) (h_t : t = 209) : (C t).card = 36 := by
  -- By definition of $C$, we know that its cardinality is 36.
  apply card_C_209_final_v3 t h_t


lemma gcd_P_iff (k u : ℕ) : Nat.gcd u (P k) > 1 ↔ ∃ q, Nat.Prime q ∧ q ∣ u ∧ ∃ i < k, q = Nat.nth Nat.Prime i := by
  -- If $\gcd(u, P k) > 1$, then there exists a prime $q$ dividing both $u$ and $P k$.
  apply Iff.intro
  intro h_gcd
  obtain ⟨q, hq_prime, hq_div_u, hq_div_Pk⟩ : ∃ q, Nat.Prime q ∧ q ∣ u ∧ q ∣ P k := by
    exact Nat.Prime.not_coprime_iff_dvd.mp h_gcd.ne';
  · -- Since $q$ divides $P k$, and $P k$ is the product of the first $k$ primes, $q$ must be one of those primes.
    have hq_prime_div : q ∈ Finset.image (fun i => Nat.nth Nat.Prime i) (Finset.range k) := by
      -- Since $q$ divides $P k$ and $P k$ is the product of the first $k$ primes, $q$ must be one of those primes.
      have hq_prime_div : q ∣ Finset.prod (Finset.range k) (fun i => Nat.nth Nat.Prime i) := by
        exact hq_div_Pk;
      contrapose! hq_prime_div; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
      exact Nat.Coprime.prod_right fun i hi => hq_prime.coprime_iff_not_dvd.mpr fun h => hq_prime_div i ( Finset.mem_range.mp hi ) <| by rw [ Nat.prime_dvd_prime_iff_eq ] at h <;> aesop;
    aesop;
  · bound;
    refine' lt_of_lt_of_le left.one_lt ( Nat.le_of_dvd ( Nat.gcd_pos_of_pos_right _ <| Finset.prod_pos fun i hi => Nat.Prime.pos <| by aesop ) <| Nat.dvd_gcd left_1 <| Finset.dvd_prod_of_mem _ <| Finset.mem_range.mpr left_2 )


lemma D_decomp_final_v4 (t n : ℕ) (h_t : t = 209) (h_n : n = interval_end t) (u : ℕ) (hu : u ∈ D t n) :
  ∃ q ∈ D_primes t, ∃ m, u = q * m ∧ (m = 1 ∨ (Nat.Prime m ∧ p t ≤ m)) ∧ m ≤ p (t + 9) := by
    have := D_decomp_final_v3 209 n; aesop

lemma D_subset_D_plus_final_v4 (t n : ℕ) (h_t : t = 209) (h_n : n = interval_end t) : D t n ⊆ D_plus t := by
  exact?

lemma card_D_plus_final_v4 (t : ℕ) (h_t : t = 209) : (D_plus t).card ≤ 35 := by
  subst h_t; exact card_D_plus_final_v3 _ rfl;

lemma card_C_209_final_v4 (t : ℕ) (h_t : t = 209) : (C t).card = 36 := by
  -- Apply the lemma that states the cardinality of C t is 36 when t is 209.
  apply card_C_209_final_v3 t h_t


/--
Say a set of natural numbers is `k`-weakly divisible if any `k+1` elements
of `A` are not relatively prime.
-/
def WeaklyDivisible (k : ℕ) (A : Finset ℕ) : Prop :=
    ∀ s ∈ A.powersetCard (k + 1), ¬ Set.Pairwise s Nat.Coprime

/--
`MaxWeaklyDivisible N k` is the size of the largest k-weakly divisible subset of `{1,..., N}`
-/
noncomputable def MaxWeaklyDivisible (N k : ℕ) : ℕ :=
  sSup { n : ℕ |
    ∃ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N ∧
      WeaklyDivisible k A ∧
      A.card = n }

/--
`FirstPrimesMultiples N k` is the set of numbers in `{1,..., N}` that are
a multiple of one of the first `k` primes.
-/
noncomputable def FirstPrimesMultiples (N k : ℕ) : Finset ℕ :=
    (Finset.Icc 1 N).filter fun i => ∃ j < k, (j.nth Nat.Prime ∣ i)

/--
Suppose $A \subseteq \{1,\dots,N\}$ is such that there are no $k+1$ elements of $A$ which are
relatively prime. An example is the set of all multiples of the first $k$ primes.
Is this the largest such set?
-/
theorem erdos_56 :
  (∀ᵉ (N ≥ 2) (k > 0),
      N ≥ k.nth Nat.Prime →
      MaxWeaklyDivisible N k = (FirstPrimesMultiples N k).card) ↔
    False := by
  -- By definition of $A$, we know that $|A| = |B| + |C|$.
  have hA_card : (A 209 (p 209 * p 218)).card = (B 209 (p 209 * p 218)).card + (C 209).card := by
    rw [ ← Finset.card_union_of_disjoint ];
    · rfl;
    · exact?;
  -- Since $|C| = 36$ and $|D| \leq 35$, we have $|A| = |B| + |C| > |B| + |D| = |E|$.
  have hA_gt_E : (A 209 (p 209 * p 218)).card > (FirstPrimesMultiples (p 209 * p 218) 212).card := by
    -- Substitute hA_card and hE_card into the goal.
    rw [hA_card, show (FirstPrimesMultiples (p 209 * p 218) 212).card = (B 209 (p 209 * p 218)).card + (D 209 (p 209 * p 218)).card from ?_];
    · refine' add_lt_add_left _ _;
      refine' lt_of_le_of_lt ( Finset.card_le_card ( D_subset_D_plus_final_v4 _ _ rfl rfl ) ) _;
      exact lt_of_le_of_lt ( card_D_plus_final_v4 _ rfl ) ( by rw [ card_C_209_final_v4 _ rfl ] ; norm_num );
    · -- By definition of $B$ and $D$, we know that $B \cup D = \text{FirstPrimesMultiples}(N, k)$.
      have h_union : B 209 (p 209 * p 218) ∪ D 209 (p 209 * p 218) = FirstPrimesMultiples (p 209 * p 218) 212 := by
        ext; simp [B, D, FirstPrimesMultiples];
        unfold E; aesop;
        · -- Since $a$ is divisible by some prime in the first 208 primes, we can find such a $j$.
          obtain ⟨j, hj⟩ : ∃ j < 208, Nat.nth Nat.Prime j ∣ a := by
            contrapose! right;
            refine' Nat.le_of_eq _;
            refine' Nat.Coprime.prod_right fun i hi => _;
            exact Nat.Coprime.symm ( Nat.Prime.coprime_iff_not_dvd ( Nat.prime_nth_prime i ) |>.2 ( right i ( Finset.mem_range.mp hi ) ) );
          exact ⟨ j, by linarith, hj.2 ⟩;
        · contrapose! right;
          refine' Nat.le_of_eq ( Nat.coprime_prod_right_iff.mpr _ );
          exact fun i hi => Nat.Coprime.symm <| Nat.Prime.coprime_iff_not_dvd ( Nat.prime_nth_prime i ) |>.2 <| right i <| Finset.mem_range.mp hi;
        · refine' Or.inr ( lt_of_lt_of_le ( Nat.Prime.one_lt ( Nat.prime_nth_prime w ) ) ( Nat.le_of_dvd ( Nat.gcd_pos_of_pos_left _ left ) ( Nat.dvd_gcd right ( dvd_trans ( by norm_num ) ( Finset.dvd_prod_of_mem _ ( Finset.mem_range.mpr left_1 ) ) ) ) ) );
      rw [ ← h_union, Finset.card_union_of_disjoint ];
      unfold B D; aesop;
      rw [ Finset.disjoint_left ] ; aesop;
      unfold E B at *; aesop;
  -- Since $A$ is a $k$-weakly divisible subset and its size is larger than $E$'s, this implies that $MaxWeaklyDivisible N k$ is at least as large as $A$'s size.
  have h_max_ge_A : MaxWeaklyDivisible (p 209 * p 218) 212 ≥ (A 209 (p 209 * p 218)).card := by
    apply le_csSup;
    · exact ⟨ _, fun n hn => hn.choose_spec.2.2 ▸ Finset.card_le_card hn.choose_spec.1 ⟩;
    · refine' ⟨ A 209 ( p 209 * p 218 ), _, _, rfl ⟩;
      · simp +zetaDelta at *;
        apply Finset.union_subset;
        · exact Finset.filter_subset _ _;
        · apply C_subset_n;
          · exact?;
          · exact satisfies_H_209.1.le;
      · -- Since $A$ is constructed as the union of $B$ and $C$, and we've shown that both $B$ and $C$ have no $k+1$ pairwise coprime elements, their union should also have this property.
        have hA_weakly_divisible : has_no_k_plus_1_coprime (A 209 (p 209 * p 218)) 212 := by
          apply A_no_k_plus_1_final;
          · exact?;
          · exact?;
        intro s hs; specialize hA_weakly_divisible s; aesop;
  contrapose! hA_gt_E;
  have h_max_ge_A : MaxWeaklyDivisible (p 209 * p 218) 212 = (FirstPrimesMultiples (p 209 * p 218) 212).card := by
    apply hA_gt_E.elim;
    · aesop;
      apply a;
      · -- Since $p$ is the nth prime, and primes are always greater than or equal to 2, multiplying two primes will definitely give a number that's at least 2*2=4. So, 2 ≤ 4, which is true.
        have h_prime_ge_two : ∀ n, 2 ≤ Nat.nth Nat.Prime n := by
          exact fun n => Nat.Prime.two_le ( Nat.prime_nth_prime n );
        exact le_trans ( by norm_num ) ( Nat.mul_le_mul ( h_prime_ge_two _ ) ( h_prime_ge_two _ ) );
      · norm_num;
      · unfold p;
        refine' le_trans _ ( Nat.mul_le_mul ( Nat.nth_monotone _ <| show 208 ≥ 208 by norm_num ) ( Nat.nth_monotone _ <| show 217 ≥ 212 by norm_num ) );
        · exact le_mul_of_one_le_left ( Nat.zero_le _ ) ( Nat.Prime.pos ( by norm_num ) );
        · exact Nat.infinite_setOf_prime;
        · exact Nat.infinite_setOf_prime;
    · tauto;
  linarith
 