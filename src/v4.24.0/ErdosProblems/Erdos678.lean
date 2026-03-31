/-

This is a Lean formalization of part of Erdős Problem 678.
https://www.erdosproblems.com/forum/thread/678

The actual problem was solved positively by: Stijn Cambie

[Ca24] S. Cambie, Resolution of an Erdős' problem on least common
multiples. arXiv:2410.09138 (2024).


Cambie's paper from the arxiv was auto-formalized by Aristotle (from
Harmonic).  It actually auto-formalized the entire paper, but below we
only include the portion necessary to solve the problem (Theorem 1).

This file includes a statement of the Prime Number Theorem as an
axiom, `pi_alt`.  It is lifted directly from the PrimeNumberTheoremAnd
project.

The final statements are from a mixture of sources.


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/



/-
We have formalized the first main result of the paper "Resolution of an Erdős' problem on least common multiples".

**Main Theorem**: We proved `MainTheoremStatement` (Theorem 1 in the paper) assuming the `DensityHypothesis` (which follows from results on prime gaps, e.g., Baker-Harman-Pintz).

The formalization follows the structure of the paper, defining `M`, `m`, `good_x`, `good_y`, and using the Chinese Remainder Theorem and density arguments to construct the required integers. We handled the asymptotic inequalities and p-adic valuation arguments required for the proofs.
-/

import Mathlib

namespace Erdos678

set_option linter.mathlibStandardSet false
set_option linter.unusedTactic false

open scoped BigOperators
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

set_option maxHeartbeats 0

noncomputable section

open Real

open Filter

/-- A statement of the Prime Number Theorem -/
axiom pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
    ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x

/-
Definitions of M and m as in the proof. M is the LCM of 1 to k. m is the product of prime powers p^a dividing M such that p <= sqrt(k).
-/
def M (k : ℕ) : ℕ := (Finset.Icc 1 k).lcm id

def m (k : ℕ) : ℕ :=
  let primes_sqrt := (Finset.Icc 1 k).filter (fun p => p.Prime ∧ p * p ≤ k)
  Finset.prod primes_sqrt (fun p => p ^ ((M k).factorization p))

/-
Claim: Let $p_1 < p_2 <  \ldots < p_r$ be primes and $w_1, w_2, \ldots, w_r$ be integers, such that the combinations $\sum_{i} c_i w_i$ over all possible combinations with $0 < c_i \le p_i $ lead to all residues modulo $P=p_1p_2\ldots p_r.$ Let $B_i \subset [p_i]$ be a set of size at least $(1-\eps)p_i$ for every $1 \le i \le r$.
    If $\eps(p_1+p_2+\ldots+p_r)< n \le p_1,$ among every $n$ consecutive integers there is at least one which equals $\sum_{i} c_i w_i$ modulo $P$ where $c_i \in B_i$ for every $1 \le i \le r$.
-/
theorem claim_approx (p : List ℕ) (w : List ℤ) (hp_prime : ∀ x ∈ p, x.Prime) (hp_sorted : p.Sorted (· < ·))
    (h_cover : ∀ r : ℤ, ∃ c : List ℤ, c.length = p.length ∧ (∀ i, 0 < c.get! i ∧ c.get! i ≤ p.get! i) ∧
      (List.sum (List.zipWith (fun x y => x * y) c w)) ≡ r [ZMOD p.prod])
    (ε : ℝ) (B : List (Set ℤ)) (hB_subset : ∀ i, B.get! i ⊆ Set.Icc 1 (p.get! i))
    (hB_size : ∀ i, (B.get! i).ncard ≥ (1 - ε) * (p.get! i : ℝ))
    (n : ℕ) (hn : ε * (p.sum : ℝ) < n) (hn_le : n ≤ p.head!) :
    ∀ start : ℤ, ∃ z ∈ Set.Icc start (start + n - 1),
      ∃ c : List ℤ, c.length = p.length ∧ (∀ i, c.get! i ∈ B.get! i) ∧
      z ≡ (List.sum (List.zipWith (fun x y => x * y) c w)) [ZMOD p.prod] := by
        contrapose! hB_size;
        revert hB_size hn hn_le hB_subset hB_size hp_prime hp_sorted h_cover;
        intro hprime hsorted hcover hB hε hn;
        cases p <;> simp_all +decide;
        intro x hx;
        use List.length ‹_› + 1;
        obtain ⟨ c, hc₁, hc₂, hc₃ ⟩ := hcover x;
        grind

/-
The hypothesis that for any $\epsilon > 0$, for sufficiently large $k$, there exist two distinct primes in $(k/2, (1+\epsilon)k/2)$ and three distinct primes in $((1-\epsilon)k, k)$.
-/
def DensityHypothesis : Prop :=
  ∀ ε > 0, ∃ K, ∀ k ≥ K,
    (∃ p1 p2 : ℕ, (k : ℝ) / 2 < p1 ∧ (p1 : ℝ) < (1 + ε) * k / 2 ∧ (k : ℝ) / 2 < p2 ∧ (p2 : ℝ) < (1 + ε) * k / 2 ∧ p1 ≠ p2 ∧ p1.Prime ∧ p2.Prime) ∧
    (∃ q1 q2 q3 : ℕ, (1 - ε) * k < q1 ∧ (q1 : ℝ) < k ∧ (1 - ε) * k < q2 ∧ (q2 : ℝ) < k ∧ (1 - ε) * k < q3 ∧ (q3 : ℝ) < k ∧
      q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3 ∧ q1.Prime ∧ q2.Prime ∧ q3.Prime)

/-
Algebraic identity: If the maximum of a function on a set is at least e, and at most one element exceeds e, then the sum minus the max equals the sum of mins minus e.
-/
lemma sum_sub_max_eq_sum_min_sub_e (S : Finset ℕ) (f : ℕ → ℕ) (e : ℕ)
  (h_max : S.sup f ≥ e)
  (h_unique : (S.filter (fun i => f i > e)).card ≤ 1) :
  ∑ i ∈ S, f i - S.sup f = (∑ i ∈ S, min (f i) e) - e := by
    by_cases h_empty : S = ∅ <;> simp_all +decide [ Finset.sup ];
    -- Let $i_0$ be the unique element in $S$ such that $f(i_0) > e$.
    by_cases h_exists : ∃ i0 ∈ S, e < f i0 ∧ ∀ i ∈ S, i ≠ i0 → f i ≤ e;
    · obtain ⟨ i0, hi0₁, hi0₂, hi0₃ ⟩ := h_exists;
      -- Since $f(i0) > e$, we have $\max_{i \in S} f(i) = f(i0)$.
      have h_max_eq : Finset.sup S f = f i0 := by
        exact le_antisymm ( Finset.sup_le fun i hi => if hi' : i = i0 then hi'.symm ▸ le_rfl else hi0₃ i hi hi' |> le_trans <| by linarith ) ( Finset.le_sup ( f := f ) hi0₁ );
      -- Since $f(i0) > e$, we can split the sum into two parts: the sum over $S \setminus \{i0\}$ and the term $f(i0)$.
      have h_split_sum : ∑ i ∈ S, f i = ∑ i ∈ S.erase i0, f i + f i0 := by
        rw [ Finset.sum_erase_add _ _ hi0₁ ]
      have h_split_min_sum : ∑ i ∈ S, min (f i) e = ∑ i ∈ S.erase i0, min (f i) e + min (f i0) e := by
        rw [ Finset.sum_erase_add _ _ hi0₁ ]
      simp_all +decide [ Finset.sup ];
      exact Finset.sum_congr rfl fun x hx => by rw [ min_eq_left ( hi0₃ x ( Finset.mem_of_mem_erase hx ) ( by aesop ) ) ] ;
    · -- If no such $i_0$ exists, then for all $i \in S$, we have $f(i) \leq e$.
      have h_le_e : ∀ i ∈ S, f i ≤ e := by
        contrapose! h_exists;
        exact Exists.elim h_exists fun i hi => ⟨ i, hi.1, hi.2, fun j hj hj' => not_lt.1 fun hj'' => h_unique.not_gt <| Finset.one_lt_card.2 ⟨ j, by aesop, i, by aesop ⟩ ⟩;
      rw [ le_antisymm h_max ];
      · rw [ Finset.sum_congr rfl fun x hx => min_eq_left <| by exact Finset.le_sup ( f := f ) hx ];
      · exact Finset.sup_le fun i hi => h_le_e i hi

/-
The p-adic valuation of the ratio of the product to the LCM is equal to the sum of truncated valuations minus e, provided the max valuation is at least e and at most one element exceeds e.
-/
lemma valuation_prod_div_lcm (S : Finset ℕ) (p : ℕ) (e : ℕ)
  (hp : p.Prime)
  (h_max : S.sup (padicValNat p) ≥ e)
  (h_unique : (S.filter (fun i => padicValNat p i > e)).card ≤ 1)
  (h_nonzero : ∀ i ∈ S, i ≠ 0) :
  padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (∑ i ∈ S, min (padicValNat p i) e) - e := by
    -- By definition of $p$-adic valuation, we know that $v_p(\prod_{i \in S} i) = \sum_{i \in S} v_p(i)$ and $v_p(\text{lcm} S) = \max_{i \in S} v_p(i)$.
    have h_val_prod : padicValNat p (Finset.prod S id) = ∑ i ∈ S, padicValNat p i := by
      have h_padic_prod : ∀ (l : List ℕ), (∀ i ∈ l, i ≠ 0) → padicValNat p (List.prod l) = List.sum (List.map (fun i => padicValNat p i) l) := by
        intros l hl_nonzero
        induction' l with i l ih;
        · simp +decide [ padicValNat ];
        · by_cases hi : i = 0 <;> by_cases hl : l.prod = 0 <;> simp_all +decide [ padicValNat.mul ];
          norm_num [ ← ih ] at *;
          exact False.elim <| hl_nonzero.2 0 hl rfl;
      convert h_padic_prod ( S.toList ) _ ; aesop;
      · simp +decide [ Finset.sum_map_toList ];
      · aesop
    have h_val_lcm : padicValNat p (Finset.lcm S id) = Finset.sup S (padicValNat p) := by
      have h_val_lcm : ∀ {T : Finset ℕ}, (∀ i ∈ T, i ≠ 0) → padicValNat p (Finset.lcm T id) = Finset.sup T (padicValNat p) := by
        intros T hT_nonzero
        induction' T using Finset.induction with i T hiT ih;
        · aesop;
        · -- By definition of lcm, we have $\text{lcm}(i, \text{lcm}(T)) = \frac{i \cdot \text{lcm}(T)}{\gcd(i, \text{lcm}(T))}$.
          have h_lcm_def : padicValNat p (Nat.lcm i (Finset.lcm T id)) = max (padicValNat p i) (padicValNat p (Finset.lcm T id)) := by
            haveI := Fact.mk hp; rw [ ← Nat.factorization_def, ← Nat.factorization_def, Nat.factorization_lcm ] <;> simp_all +decide [ Nat.factorization_eq_zero_iff ] ;
            simp_all +decide [ Nat.factorization ];
          aesop;
      apply h_val_lcm; assumption;
    -- By the properties of p-adic valuations, we have $v_p(\prod_{i \in S} i / \text{lcm} S) = v_p(\prod_{i \in S} i) - v_p(\text{lcm} S)$.
    have h_val_ratio : padicValNat p ((∏ i ∈ S, i) / (Finset.lcm S id)) = (∑ i ∈ S, padicValNat p i) - (Finset.sup S (padicValNat p)) := by
      haveI := Fact.mk hp; rw [ ← h_val_prod, ← h_val_lcm, padicValNat.div_of_dvd ] ; aesop;
      exact Finset.lcm_dvd fun x hx => Finset.dvd_prod_of_mem _ hx;
    rw [ h_val_ratio, sum_sub_max_eq_sum_min_sub_e ] <;> aesop

/-
If p is a prime such that n < p^2, and S is a set of n consecutive integers containing a multiple of p, then the p-adic valuation of prod(S)/lcm(S) is the count of multiples of p in S minus 1.
-/
lemma valuation_large_p (S : Finset ℕ) (p : ℕ) (n : ℕ)
  (hp : p.Prime)
  (hS_card : S.card = n)
  (hS_consec : ∃ s, S = Finset.Icc s (s + n - 1))
  (h_len : n < p * p)
  (h_exists : ∃ z ∈ S, p ∣ z)
  (h_nonzero : ∀ z ∈ S, z ≠ 0) :
  padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (S.filter (p ∣ ·)).card - 1 := by
    -- Apply the lemma `valuation_prod_div_lcm` with $e = 1$.
    have h_apply_lemma : padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (∑ i ∈ S, min (padicValNat p i) 1) - 1 := by
      -- Apply the lemma `valuation_prod_div_lcm` with $e = 1$ and the conditions that the maximum $p$-adic valuation is at least 1 and at most one element has a $p$-adic valuation greater than 1.
      have h_apply_lemma : padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (∑ i ∈ S, min (padicValNat p i) 1) - 1 := by
        have h_max : S.sup (padicValNat p) ≥ 1 := by
          obtain ⟨ z, hz₁, hz₂ ⟩ := h_exists;
          refine' le_trans _ ( Finset.le_sup hz₁ );
          exact Nat.pos_of_ne_zero ( by intro t; simp_all +decide [ Nat.factorization_eq_zero_iff, hp.ne_one ] )
        have h_unique : (S.filter (fun i => padicValNat p i > 1)).card ≤ 1 := by
          -- If $p^2$ divides $i$, then $i \equiv 0 \pmod{p^2}$, and since $S$ contains $n$ consecutive integers, there can be at most one such $i$ in $S$.
          have h_unique : ∀ i j : ℕ, i ∈ S → j ∈ S → i % (p * p) = 0 → j % (p * p) = 0 → i = j := by
            intro i j hi hj hi' hj'; obtain ⟨ s, rfl ⟩ := hS_consec; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
            rw [ ← Nat.dvd_iff_mod_eq_zero ] at *;
            obtain ⟨ k, hk ⟩ := hi'; obtain ⟨ l, hl ⟩ := hj'; nlinarith [ show k = l by nlinarith [ Nat.sub_add_cancel ( show 1 ≤ s + n from by omega ) ] ] ;
          -- If $padicValNat p i > 1$, then $p^2$ divides $i$, and since $S$ contains $n$ consecutive integers, there can be at most one such $i$ in $S$.
          have h_div_p2 : ∀ i ∈ S, padicValNat p i > 1 → i % (p * p) = 0 := by
            intros i hi hpi
            have h_div_p2 : p ^ 2 ∣ i := by
              have h_div_p2 : p ^ (padicValNat p i) ∣ i := by
                convert Nat.ordProj_dvd i p using 1;
                rw [ Nat.factorization ] ; aesop;
              exact dvd_trans ( pow_dvd_pow _ hpi ) h_div_p2;
            simpa only [ sq ] using Nat.mod_eq_zero_of_dvd h_div_p2;
          exact Finset.card_le_one.mpr fun i hi j hj => h_unique i j ( Finset.filter_subset _ _ hi ) ( Finset.filter_subset _ _ hj ) ( h_div_p2 i ( Finset.filter_subset _ _ hi ) ( Finset.mem_filter.mp hi |>.2 ) ) ( h_div_p2 j ( Finset.filter_subset _ _ hj ) ( Finset.mem_filter.mp hj |>.2 ) )
        convert valuation_prod_div_lcm S p 1 hp h_max h_unique h_nonzero using 1;
      exact h_apply_lemma;
    rw [ h_apply_lemma, Finset.card_filter ];
    refine' congrArg₂ _ ( Finset.sum_congr rfl fun x hx => _ ) rfl;
    by_cases h : p ∣ x <;> simp_all +decide [ Nat.Prime.dvd_iff_one_le_factorization ];
    contrapose! h_nonzero; simp_all +decide [ Nat.factorization_eq_zero_iff ] ;
    grind

/-
The truncated p-adic valuation min(v_p(n), e) is periodic with period p^e for non-zero integers.
-/
lemma truncated_valuation_periodic (p e n k : ℕ) (hp : p.Prime) (h_mod : n ≡ k [MOD p ^ e])
  (hn : n ≠ 0) (hk : k ≠ 0) :
  min (padicValNat p n) e = min (padicValNat p k) e := by
    by_cases h : padicValNat p n ≥ e <;> by_cases h' : padicValNat p k ≥ e <;> simp_all +decide;
    · -- Since $n \equiv k \pmod{p^e}$, we have that $p^e \mid n$ if and only if $p^e \mid k$.
      have h_div : p ^ e ∣ n ↔ p ^ e ∣ k := by
        rw [ Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, h_mod ];
      contrapose! h_div;
      have h_div_n : p ^ e ∣ n := by
        rw [ padicValNat ] at h;
        cases e <;> aesop
      have h_div_k : ¬p ^ e ∣ k := by
        intro H; have := Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 H; simp_all +decide [ Nat.factorization ] ;
        replace := this p ; simp_all +decide [ Nat.primeFactors_pow ];
        linarith
      exact Or.inl ⟨h_div_n, h_div_k⟩;
    · -- Since $p^e \mid k$, we have $k \equiv 0 \pmod{p^e}$.
      have hk_mod : k ≡ 0 [MOD p ^ e] := by
        rw [ Nat.modEq_zero_iff_dvd ];
        have h_p_div_k : p ^ padicValNat p k ∣ k := by
          exact pow_padicValNat_dvd;
        exact dvd_trans ( pow_dvd_pow _ h' ) h_p_div_k;
      have h_div : p ^ e ∣ n := by
        exact Nat.dvd_of_mod_eq_zero ( h_mod.symm ▸ hk_mod );
      obtain ⟨ q, hq ⟩ := h_div;
      haveI := Fact.mk hp; rw [ hq, padicValNat.mul ] <;> aesop;
    · have h_div : p ^ (padicValNat p n) ∣ n ∧ ¬p ^ (padicValNat p n + 1) ∣ n := by
        haveI := Fact.mk hp; simp +decide [ Nat.ordProj_dvd, padicValNat_dvd_iff ] ;
        assumption;
      have h_div_k : p ^ (padicValNat p n) ∣ k ∧ ¬p ^ (padicValNat p n + 1) ∣ k := by
        have h_div_k : n ≡ k [MOD p ^ (padicValNat p n + 1)] := by
          exact h_mod.of_dvd <| pow_dvd_pow _ <| Nat.succ_le_of_lt h;
        exact ⟨ Nat.dvd_of_mod_eq_zero ( h_div_k.of_dvd ( pow_dvd_pow _ ( Nat.le_succ _ ) ) ▸ Nat.mod_eq_zero_of_dvd h_div.1 ), fun h => h_div.2 ( Nat.dvd_of_mod_eq_zero ( h_div_k.symm ▸ Nat.mod_eq_zero_of_dvd h ) ) ⟩;
      have h_val_eq : padicValNat p k = padicValNat p n := by
        rw [ ← Nat.factorization_def ];
        · exact le_antisymm ( Nat.le_of_not_lt fun h'' => h_div_k.2 <| Nat.dvd_trans ( pow_dvd_pow _ h'' ) <| Nat.ordProj_dvd _ _ ) ( Nat.le_of_not_lt fun h'' => by exact absurd ( Nat.dvd_trans ( pow_dvd_pow _ h'' ) h_div_k.1 ) <| Nat.pow_succ_factorization_not_dvd hk hp );
        · assumption;
      rw [h_val_eq]

/-
The sum of truncated p-adic valuations is invariant under shifting the interval by a multiple of the period p^e.
-/
lemma sum_truncated_valuation_eq (x y k p e : ℕ) (hp : p.Prime) (he : e > 0)
  (hx : x > 0) (hy : y > 0)
  (h_mod : x ≡ y + 1 [MOD p ^ e]) :
  ∑ i ∈ Finset.Icc (y + 1) (y + k), min (padicValNat p i) e =
  ∑ i ∈ Finset.Icc x (x + k - 1), min (padicValNat p i) e := by
    erw [ Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range ];
    simp +arith +decide [ Nat.add_sub_add_left, Finset.sum_range_succ' ];
    rw [ Nat.sub_add_cancel ( by linarith ), Nat.add_sub_cancel_left ];
    refine' Finset.sum_congr rfl fun i hi => _;
    apply truncated_valuation_periodic;
    · assumption;
    · simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
      ring;
    · positivity;
    · positivity

/-
The p-adic valuation of the LCM of 1 to k is the floor of log base p of k.
-/
lemma padicValNat_lcm_range (k p : ℕ) (hp : p.Prime) (hk : k ≥ 1) :
  padicValNat p (M k) = Nat.log p k := by
    revert k;
    intro k hk;
    -- The p-adic valuation of the least common multiple of a set of numbers is the maximum of the p-adic valuations of those numbers.
    have h_lcm_val : ∀ {S : Finset ℕ}, (∀ i ∈ S, i ≠ 0) → padicValNat p (Finset.lcm S id) = Finset.sup S (padicValNat p) := by
      intros S hS_nonzero
      induction' S using Finset.induction with i S hiS ih;
      · simp +decide [ Nat.lcm ];
      · -- By definition of lcm, we know that $v_p(\text{lcm}(i, S)) = \max(v_p(i), v_p(\text{lcm}(S)))$.
        have h_lcm_def : padicValNat p (Nat.lcm i (Finset.lcm S id)) = max (padicValNat p i) (padicValNat p (Finset.lcm S id)) := by
          haveI := Fact.mk hp;
          rw [ ← Nat.factorization_def, ← Nat.factorization_def, ← Nat.factorization_def ];
          · rw [ Nat.factorization_lcm ] <;> simp +decide [ hS_nonzero ];
            exact fun h => hS_nonzero 0 ( Finset.mem_insert_of_mem h ) rfl;
          · exact hp;
          · exact hp;
          · exact hp;
        aesop;
    -- Apply the lemma that the p-adic valuation of the lcm of a set of numbers is the maximum of the p-adic valuations of those numbers.
    have h_max_val : Finset.sup (Finset.Icc 1 k) (padicValNat p) = Nat.log p k := by
      refine' le_antisymm _ _;
      · simp +zetaDelta at *;
        intro b hb₁ hb₂; rw [ ← Nat.factorization_def ];
        · exact Nat.le_log_of_pow_le hp.one_lt ( Nat.le_trans ( Nat.le_of_dvd hb₁ ( Nat.ordProj_dvd _ _ ) ) hb₂ );
        · assumption;
      · refine' le_trans _ ( Finset.le_sup <| Finset.mem_Icc.mpr ⟨ Nat.one_le_pow _ _ hp.pos, Nat.pow_log_le_self _ <| by linarith ⟩ );
        haveI := Fact.mk hp; rw [ padicValNat.pow ] ; aesop;
        exact hp.ne_zero;
    exact h_max_val ▸ h_lcm_val fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ;

/-
Any interval of length at least m contains a multiple of m.
-/
lemma exists_multiple_of_len_ge (a L m : ℕ) (hm : m > 0) (hL : L ≥ m) :
  ∃ z ∈ Finset.Icc a (a + L - 1), m ∣ z := by
    norm_num +zetaDelta at *;
    -- Let $z = m \cdot \lceil a/m \rceil$. In integer arithmetic, we have $z = m \cdot ((a + m - 1) / m)$.
    use m * ((a + m - 1) / m);
    exact ⟨ ⟨ by linarith [ Nat.div_add_mod ( a + m - 1 ) m, Nat.mod_lt ( a + m - 1 ) hm, Nat.sub_add_cancel ( by linarith : 1 ≤ a + m ) ], Nat.le_sub_one_of_lt ( by linarith [ Nat.div_mul_le_self ( a + m - 1 ) m, Nat.sub_add_cancel ( by linarith : 1 ≤ a + m ) ] ) ⟩, dvd_mul_right _ _ ⟩

/-
An interval of length L <= m contains at most one multiple of m.
-/
lemma at_most_one_multiple_of_len_le (a L m : ℕ) (hm : m > 0) (hL : L ≤ m) :
  (Finset.filter (fun x => m ∣ x) (Finset.Icc a (a + L - 1))).card ≤ 1 := by
    by_contra h_contra;
    obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.mp ( not_le.mp h_contra );
    -- Since $x$ and $y$ are multiples of $m$ and lie in the interval $[a, a + L - 1]$, we have $|x - y| \geq m$.
    have h_diff : |(x : ℤ) - y| ≥ m := by
      exact Int.le_of_dvd ( abs_pos.mpr ( sub_ne_zero.mpr ( Nat.cast_injective.ne hxy ) ) ) ( by simpa using dvd_sub ( Int.natCast_dvd_natCast.mpr ( Finset.mem_filter.mp hx |>.2 ) ) ( Int.natCast_dvd_natCast.mpr ( Finset.mem_filter.mp hy |>.2 ) ) );
    simp +zetaDelta at *;
    cases abs_cases ( x - y : ℤ ) <;> omega

/-
For small primes p <= sqrt(k), the p-adic valuation of the LHS ratio is e + the p-adic valuation of the RHS ratio, where e = v_p(M).
-/
lemma valuation_small_p (k x y p : ℕ) (hp : p.Prime) (hk : k ≥ 2)
  (hx0 : x > 0) (hy0 : y > 0)
  (h_le_sqrt : p * p ≤ k)
  (hx_mod : x ≡ 1 [MOD p ^ (padicValNat p (M k))])
  (hy_mod : y ≡ 0 [MOD p ^ (padicValNat p (M k))]) :
  padicValNat p ((∏ i ∈ Finset.Icc y (y + k), i) / (Finset.Icc y (y + k)).lcm id) =
  padicValNat p (M k) + padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) := by
    -- Let $e = v_p(M(k))$. By `padicValNat_lcm_range`, $e = \lfloor \log_p k \rfloor$.
    set e := padicValNat p (M k) with heq
    have he : e = Nat.log p k := by
      convert padicValNat_lcm_range k p hp ( by linarith ) using 1;
    -- By `valuation_prod_div_lcm`, we have $v_p(\text{LHS}) = \sum_{i=y}^{y+k} \min(v_p(i), e) - e$ and $v_p(\text{RHS}) = \sum_{i=x}^{x+k-1} \min(v_p(i), e) - e$.
    have h_lhs : padicValNat p ((∏ i ∈ Finset.Icc y (y + k), i) / (Finset.Icc y (y + k)).lcm id) = (∑ i ∈ Finset.Icc y (y + k), min (padicValNat p i) e) - e := by
      convert valuation_prod_div_lcm _ _ _ hp _ _ _;
      · -- Since $y \equiv 0 \pmod{p^e}$, we have $v_p(y) \geq e$.
        have h_vp_y : padicValNat p y ≥ e := by
          have := Nat.dvd_of_mod_eq_zero hy_mod;
          obtain ⟨ c, rfl ⟩ := this;
          haveI := Fact.mk hp; rw [ padicValNat.mul ] <;> aesop;
        exact le_trans h_vp_y ( Finset.le_sup ( f := padicValNat p ) ( Finset.mem_Icc.mpr ⟨ le_rfl, by linarith ⟩ ) );
      · -- Since $p^{e+1} > k$, there can be at most one multiple of $p^{e+1}$ in the interval $[y, y+k]$.
        have h_unique_multiples : ∀ m1 m2 : ℕ, y ≤ m1 → m1 ≤ y + k → y ≤ m2 → m2 ≤ y + k → p ^ (e + 1) ∣ m1 → p ^ (e + 1) ∣ m2 → m1 = m2 := by
          intros m1 m2 hm1 hm1' hm2 hm2' hm1'' hm2''
          have h_diff : p ^ (e + 1) > k := by
            exact he.symm ▸ Nat.lt_pow_succ_log_self hp.one_lt _;
          obtain ⟨ a, ha ⟩ := hm1''; obtain ⟨ b, hb ⟩ := hm2''; nlinarith [ show a = b by nlinarith ] ;
        have h_unique_multiples : ∀ m ∈ Finset.Icc y (y + k), padicValNat p m > e → p ^ (e + 1) ∣ m := by
          intros m hm hpm;
          have h_div : p ^ (padicValNat p m) ∣ m := by
            convert Nat.ordProj_dvd m p using 1;
            rw [ Nat.factorization_def ] ; aesop;
          exact dvd_trans ( pow_dvd_pow _ hpm ) h_div;
        exact Finset.card_le_one.mpr fun m hm n hn => ‹∀ m1 m2 : ℕ, y ≤ m1 → m1 ≤ y + k → y ≤ m2 → m2 ≤ y + k → p ^ ( e + 1 ) ∣ m1 → p ^ ( e + 1 ) ∣ m2 → m1 = m2› m n ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hm |>.1 ) |>.1 ) ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hm |>.1 ) |>.2 ) ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1 ) ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hn |>.1 ) |>.2 ) ( h_unique_multiples m ( Finset.mem_filter.mp hm |>.1 ) ( Finset.mem_filter.mp hm |>.2 ) ) ( h_unique_multiples n ( Finset.mem_filter.mp hn |>.1 ) ( Finset.mem_filter.mp hn |>.2 ) );
      · exact fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ;
    have h_rhs : padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = (∑ i ∈ Finset.Icc x (x + k - 1), min (padicValNat p i) e) - e := by
      apply valuation_prod_div_lcm;
      · assumption;
      · -- By `exists_multiple_of_len_ge`, there exists a multiple of $p^e$ in the interval $[x, x+k-1]$.
        obtain ⟨z, hz⟩ : ∃ z ∈ Finset.Icc x (x + k - 1), p ^ e ∣ z := by
          have h_exists_multiple : p ^ e ≤ k := by
            exact he.symm ▸ Nat.pow_log_le_self p ( by linarith );
          exact ⟨ p ^ e * ( ( x + k - 1 ) / p ^ e ), Finset.mem_Icc.mpr ⟨ by linarith [ Nat.div_add_mod ( x + k - 1 ) ( p ^ e ), Nat.mod_lt ( x + k - 1 ) ( pow_pos hp.pos e ), Nat.sub_add_cancel ( show 1 ≤ x + k from by linarith ) ], by linarith [ Nat.div_mul_le_self ( x + k - 1 ) ( p ^ e ), Nat.sub_add_cancel ( show 1 ≤ x + k from by linarith ) ] ⟩, by norm_num ⟩;
        -- Since $p^e \mid z$, we have $v_p(z) \geq e$.
        have hz_val : padicValNat p z ≥ e := by
          obtain ⟨ c, rfl ⟩ := hz.2;
          haveI := Fact.mk hp; rw [ padicValNat.mul ] <;> aesop;
        exact le_trans hz_val ( Finset.le_sup ( f := padicValNat p ) hz.1 );
      · have h_unique : ∀ i ∈ Finset.Icc x (x + k - 1), padicValNat p i > e → i % p ^ (e + 1) = 0 := by
          intros i hi hpi
          have h_div : p ^ (e + 1) ∣ i := by
            have h_div : p ^ (padicValNat p i) ∣ i := by
              convert Nat.ordProj_dvd i p using 1;
              rw [ Nat.factorization_def ] ; aesop;
            exact dvd_trans ( pow_dvd_pow _ hpi ) h_div;
          exact Nat.mod_eq_zero_of_dvd h_div;
        have h_unique : ∀ i j : ℕ, i ∈ Finset.Icc x (x + k - 1) → j ∈ Finset.Icc x (x + k - 1) → padicValNat p i > e → padicValNat p j > e → i = j := by
          intros i j hi hj hi_gt hj_gt
          have h_div : p ^ (e + 1) ∣ i ∧ p ^ (e + 1) ∣ j := by
            exact ⟨ Nat.dvd_of_mod_eq_zero ( h_unique i hi hi_gt ), Nat.dvd_of_mod_eq_zero ( h_unique j hj hj_gt ) ⟩;
          have h_diff : |(i : ℤ) - j| < p ^ (e + 1) := by
            have h_diff : |(i : ℤ) - j| ≤ k - 1 := by
              exact abs_sub_le_iff.mpr ⟨ by linarith [ Finset.mem_Icc.mp hi, Finset.mem_Icc.mp hj, Nat.sub_add_cancel ( by linarith : 1 ≤ x + k ) ], by linarith [ Finset.mem_Icc.mp hi, Finset.mem_Icc.mp hj, Nat.sub_add_cancel ( by linarith : 1 ≤ x + k ) ] ⟩;
            have h_diff : k < p ^ (e + 1) := by
              rw [ he ];
              exact Nat.lt_pow_succ_log_self hp.one_lt _;
            grind;
          contrapose! h_diff;
          exact Int.le_of_dvd ( abs_pos.mpr ( sub_ne_zero.mpr <| mod_cast h_diff ) ) <| by simpa using dvd_sub ( Int.natCast_dvd_natCast.mpr h_div.1 ) ( Int.natCast_dvd_natCast.mpr h_div.2 ) ;
        exact Finset.card_le_one.mpr fun i hi j hj => h_unique i j ( Finset.filter_subset _ _ hi ) ( Finset.filter_subset _ _ hj ) ( Finset.mem_filter.mp hi |>.2 ) ( Finset.mem_filter.mp hj |>.2 );
      · exact fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ;
    -- By `sum_truncated_valuation_eq`, we have $\sum_{i=y}^{y+k} \min(v_p(i), e) = \sum_{i=x}^{x+k-1} \min(v_p(i), e)$.
    have h_sum_eq : ∑ i ∈ Finset.Icc y (y + k), min (padicValNat p i) e = ∑ i ∈ Finset.Icc x (x + k - 1), min (padicValNat p i) e + e := by
      have h_sum_eq : ∑ i ∈ Finset.Icc (y + 1) (y + k), min (padicValNat p i) e = ∑ i ∈ Finset.Icc x (x + k - 1), min (padicValNat p i) e := by
        apply sum_truncated_valuation_eq;
        · assumption;
        · exact he.symm ▸ Nat.log_pos hp.one_lt ( by nlinarith only [ hk, h_le_sqrt, hp.two_le ] );
        · linarith;
        · positivity;
        · simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ];
      -- Since $y \equiv 0 \pmod{p^e}$, we have $v_p(y) \geq e$.
      have h_vp_y : padicValNat p y ≥ e := by
        rw [ ← Nat.factorization_def ];
        · exact Nat.le_of_not_lt fun h => absurd ( Nat.dvd_of_mod_eq_zero hy_mod ) ( by exact fun h' => absurd ( Nat.dvd_trans ( pow_dvd_pow _ h ) h' ) ( Nat.pow_succ_factorization_not_dvd hy0.ne' hp ) );
        · assumption;
      erw [ Finset.sum_Ico_eq_sum_range ] at *;
      simp_all +decide [ add_assoc, Finset.sum_range_succ' ];
      simp_all +decide [ add_comm, add_left_comm, add_assoc, Nat.add_sub_add_left ];
    simp_all +decide [ add_comm, mul_comm ];
    rw [ Nat.add_sub_of_le ];
    -- Since $p^e \le k$, there exists some $i \in [x, x+k-1]$ such that $p^e \mid i$.
    obtain ⟨i, hi⟩ : ∃ i ∈ Finset.Icc x (k + x - 1), p ^ e ∣ i := by
      have h_exists_i : p ^ e ≤ k := by
        exact Nat.pow_log_le_self p ( by linarith ) |> le_trans ( pow_le_pow_right₀ hp.one_lt.le ( by linarith ) );
      exact ⟨ p ^ e * ( ( x + p ^ e - 1 ) / p ^ e ), Finset.mem_Icc.mpr ⟨ by linarith [ Nat.div_add_mod ( x + p ^ e - 1 ) ( p ^ e ), Nat.mod_lt ( x + p ^ e - 1 ) ( pow_pos hp.pos e ), Nat.sub_add_cancel ( by linarith [ pow_pos hp.pos e ] : 1 ≤ x + p ^ e ) ], Nat.le_sub_one_of_lt ( by linarith [ Nat.div_mul_le_self ( x + p ^ e - 1 ) ( p ^ e ), Nat.sub_add_cancel ( by linarith [ pow_pos hp.pos e ] : 1 ≤ x + p ^ e ) ] ) ⟩, by norm_num ⟩;
    refine' le_trans _ ( Finset.single_le_sum ( fun a _ => Nat.zero_le ( min ( padicValNat p a ) ( padicValNat p ( M k ) ) ) ) hi.1 );
    haveI := Fact.mk hp; rw [ padicValNat_dvd_iff ] at hi; aesop;

/-
The number of multiples of p in the interval [a, b] (with a > 0) is floor(b/p) - floor((a-1)/p).
-/
lemma count_multiples_Icc (a b p : ℕ) (hp : p > 0) (ha : a > 0) :
  (Finset.filter (fun x => p ∣ x) (Finset.Icc a b)).card = b / p - (a - 1) / p := by
    rw [ show Finset.filter ( fun x => p ∣ x ) ( Finset.Icc a b ) = Finset.image ( fun x => p * x ) ( Finset.Icc ( ( a - 1 ) / p + 1 ) ( b / p ) ) from ?_, Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ hp.ne' hxy ];
    · simp +arith +decide;
    · ext;
      norm_num +zetaDelta at *;
      constructor;
      · rintro ⟨ ⟨ ha₁, ha₂ ⟩, ha₃ ⟩;
        exact ⟨ ha₃.choose, ⟨ Nat.succ_le_of_lt ( Nat.div_lt_of_lt_mul <| by linarith [ Nat.sub_add_cancel ha, ha₃.choose_spec ] ), Nat.le_div_iff_mul_le hp |>.2 <| by linarith [ Nat.sub_add_cancel ha, ha₃.choose_spec ] ⟩, by linarith [ ha₃.choose_spec ] ⟩;
      · rintro ⟨ k, ⟨ hk₁, hk₂ ⟩, rfl ⟩;
        exact ⟨ ⟨ by nlinarith [ Nat.div_add_mod ( a - 1 ) p, Nat.mod_lt ( a - 1 ) hp, Nat.sub_add_cancel ha ], by nlinarith [ Nat.div_mul_le_self b p ] ⟩, dvd_mul_right _ _ ⟩

/-
For primes p with sqrt(k) < p <= k, the number of multiples of p in [x, x+k-1] is k/p, given the modular constraint on x.
-/
lemma count_multiples_large_p_RHS (k x p : ℕ) (hp : p.Prime) (hk : k ≥ 2) (hx0 : x > 0)
  (h_range : k.sqrt < p ∧ p ≤ k)
  (hx_p : 1 ≤ x % p ∧ x % p ≤ p - (k % p)) :
  (Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card = k / p := by
    -- Let $x = qp + r$ with $1 \le r < p$. (Since $x \% p \ge 1$).
    obtain ⟨q, r, hx⟩ : ∃ q r : ℕ, 0 < r ∧ r < p ∧ x = q * p + r := by
      exact ⟨ x / p, x % p, hx_p.1, Nat.mod_lt _ hp.pos, by rw [ Nat.div_add_mod' ] ⟩;
    -- The number of multiples of $p$ in the interval $[x, x+k-1]$ is $\lfloor \frac{x+k-1}{p} \rfloor - \lfloor \frac{x-1}{p} \rfloor$.
    have h_count_multiples : (Finset.filter (fun x => p ∣ x) (Finset.Icc x (x + k - 1))).card = (x + k - 1) / p - (x - 1) / p := by
      convert count_multiples_Icc x ( x + k - 1 ) p hp.pos hx0 using 1;
    simp_all +decide [ Nat.add_div, Nat.add_mod, Nat.mod_eq_of_lt ];
    rw [ show q * p + r + k - 1 = ( q * p + r - 1 ) + k by omega, Nat.add_div ];
    · rw [ show q * p + r - 1 = p * q + ( r - 1 ) by rw [ Nat.sub_eq_of_eq_add ] ; linarith [ Nat.sub_add_cancel hx.1 ] ] ; norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hx.2.1 ] ;
      rw [ if_neg ] <;> norm_num [ Nat.add_div, hp.pos ];
      rw [ Nat.mod_eq_of_lt ] <;> omega;
    · linarith

/-
For primes p with sqrt(k) < p <= k, the number of multiples of p in [y, y+k] is k/p + 1, given the modular constraint on y.
-/
lemma count_multiples_large_p_LHS (k y p : ℕ) (hp : p.Prime) (hk : k ≥ 2) (hy0 : y > 0)
  (h_range : k.sqrt < p ∧ p ≤ k)
  (hy_p : ∃ b, p - (k % p) ≤ b ∧ b ≤ p ∧ y ≡ b [MOD p]) :
  (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k))).card = k / p + 1 := by
    obtain ⟨ b, hb₁, hb₂, hb₃ ⟩ := hy_p;
    -- The number of multiples of p in the interval [y, y+k] is given by the formula ⌊(y+k)/p⌋ - ⌊(y-1)/p⌋.
    have h_count_formula : (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k))).card = (y + k) / p - (y - 1) / p := by
      convert count_multiples_Icc y ( y + k ) p hp.pos hy0 using 1;
    -- Since $y \equiv b \pmod p$, we have $y = qp + b$ for some integer $q$.
    obtain ⟨ q, hq ⟩ : ∃ q, y = q * p + b := by
      rw [ ← Nat.mod_add_div y p, hb₃ ];
      cases hb₂.eq_or_lt <;> simp_all +decide [ Nat.mod_eq_of_lt ];
      · exact ⟨ y / p - 1, by nlinarith [ Nat.sub_add_cancel ( show 1 ≤ y / p from Nat.div_pos ( Nat.le_of_dvd hy0 ( Nat.dvd_of_mod_eq_zero ( by simpa [ Nat.ModEq ] using hb₃ ) ) ) hp.pos ) ] ⟩;
      · exact ⟨ y / p, by ring ⟩;
    -- Substitute $y = qp + b$ into the formula.
    have h_subst : (y + k) / p = q + (k / p) + (if b + k % p ≥ p then 1 else 0) := by
      split_ifs <;> simp_all +decide [ Nat.add_div, hp.pos ];
      split_ifs <;> simp_all +decide [ Nat.div_eq_of_lt, Nat.mod_eq_of_lt ];
      · linarith [ Nat.mod_lt b hp.pos ];
      · linarith [ Nat.mod_lt b hp.pos, Nat.mod_lt k hp.pos ];
      · cases hb₂.eq_or_lt <;> simp_all +decide [ Nat.mod_eq_of_lt ];
        linarith [ Nat.mod_lt k hp.pos ];
      · cases lt_or_eq_of_le hb₂ <;> simp_all +decide [ Nat.div_eq_of_lt ];
        · linarith [ Nat.mod_eq_of_lt ‹_› ];
        · ring;
    -- Since $y = qp + b$, we have $(y - 1) / p = q$.
    have h_div_y_minus_1 : (y - 1) / p = q := by
      rcases b with ( _ | b ) <;> simp_all +decide [ Nat.add_div ];
      · exact absurd hb₁ ( Nat.sub_ne_zero_of_lt ( Nat.mod_lt _ hp.pos ) );
      · nlinarith [ Nat.div_mul_le_self ( q * p + b ) p, Nat.div_add_mod ( q * p + b ) p, Nat.mod_lt ( q * p + b ) hp.pos ];
    grind

/-
If an interval has length at most p, then the p-adic valuation of the ratio of product to LCM is 0.
-/
lemma valuation_very_large_p (S : Finset ℕ) (p : ℕ) (n : ℕ)
  (hp : p.Prime)
  (hS_card : S.card = n)
  (hS_consec : ∃ s, S = Finset.Icc s (s + n - 1))
  (h_len : n ≤ p)
  (h_nonzero : ∀ z ∈ S, z ≠ 0) :
  padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = 0 := by
    -- Apply Theorem 3 with e = 0 to get that the valuation of the ratio is zero.
    have h_val_zero : padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (∑ i ∈ S, min (padicValNat p i) 0) - 0 := by
      apply valuation_prod_div_lcm S p 0 hp;
      · exact Nat.zero_le _;
      · have h_unique : (Finset.filter (fun x => p ∣ x) S).card ≤ 1 := by
          obtain ⟨ s, rfl ⟩ := hS_consec;
          exact at_most_one_multiple_of_len_le s n p hp.pos h_len;
        refine' le_trans ( Finset.card_mono _ ) h_unique;
        intro x hx; contrapose! hx; aesop;
      · assumption;
    aesop

/-
Extension of valuation_large_p to n <= p^2.
-/
lemma valuation_large_p_le (S : Finset ℕ) (p : ℕ) (n : ℕ)
  (hp : p.Prime)
  (hS_card : S.card = n)
  (hS_consec : ∃ s, S = Finset.Icc s (s + n - 1))
  (h_len : n ≤ p * p)
  (h_exists : ∃ z ∈ S, p ∣ z)
  (h_nonzero : ∀ z ∈ S, z ≠ 0) :
  padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (S.filter (p ∣ ·)).card - 1 := by
    have h_unique : (S.filter (fun i => padicValNat p i > 1)).card ≤ 1 := by
      have h_unique : ∀ z ∈ S, ∀ w ∈ S, z ≠ w → ¬(p^2 ∣ z ∧ p^2 ∣ w) := by
        intros z hz w hw hne hdiv
        have h_diff : Int.natAbs (z - w) < p^2 := by
          rcases hS_consec with ⟨ s, rfl ⟩ ; simp_all +decide [ Finset.mem_Icc ];
          grind;
        exact h_diff.not_ge ( Nat.le_of_dvd ( Int.natAbs_pos.mpr ( sub_ne_zero_of_ne <| mod_cast hne ) ) <| by simpa [ ← Int.natCast_dvd_natCast ] using dvd_sub ( Int.natCast_dvd_natCast.mpr hdiv.1 ) ( Int.natCast_dvd_natCast.mpr hdiv.2 ) );
      have h_unique : ∀ z ∈ S, padicValNat p z > 1 → p^2 ∣ z := by
        intros z hz hpadic
        have h_div : p ^ (padicValNat p z) ∣ z := by
          exact pow_padicValNat_dvd
        generalize_proofs at *;
        exact dvd_trans ( pow_dvd_pow _ hpadic ) h_div;
      exact Finset.card_le_one.mpr fun x hx y hy => Classical.not_not.1 fun hxy => ‹∀ z ∈ S, ∀ w ∈ S, z ≠ w → ¬ ( p ^ 2 ∣ z ∧ p ^ 2 ∣ w ) › x ( Finset.filter_subset _ _ hx ) y ( Finset.filter_subset _ _ hy ) hxy ⟨ h_unique x ( Finset.filter_subset _ _ hx ) ( Finset.mem_filter.mp hx |>.2 ), h_unique y ( Finset.filter_subset _ _ hy ) ( Finset.mem_filter.mp hy |>.2 ) ⟩;
    have h_val_large_p : padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (∑ i ∈ S, min (padicValNat p i) 1) - 1 := by
      have h_val_large_p : ∀ {S : Finset ℕ} {p : ℕ}, p.Prime → (∀ i ∈ S, i ≠ 0) → (S.sup (padicValNat p)) ≥ 1 → (S.filter (fun i => padicValNat p i > 1)).card ≤ 1 → padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (∑ i ∈ S, min (padicValNat p i) 1) - 1 := by
        intros S p hp h_nonzero h_max h_unique; exact valuation_prod_div_lcm S p 1 hp h_max h_unique h_nonzero;
      apply h_val_large_p hp h_nonzero;
      · obtain ⟨ z, hz₁, hz₂ ⟩ := h_exists; exact le_trans ( Nat.pos_of_ne_zero ( by intro t; simp_all +decide [ Nat.factorization, hp.ne_one ] ) ) ( Finset.le_sup ( f := padicValNat p ) hz₁ ) ;
      · exact h_unique;
    rw [ h_val_large_p, Finset.card_filter ];
    refine' congr_arg₂ _ ( Finset.sum_congr rfl fun x hx => _ ) rfl;
    by_cases h : p ∣ x <;> simp +decide [ h, hp.dvd_iff_one_le_factorization ];
    exact Nat.pos_of_ne_zero ( by intro t; simp_all +decide [ Nat.factorization_eq_zero_iff, hp.ne_one, hp.ne_zero ] )

/-
Definition of good_x without referencing m k directly.
-/
def good_x_nom (k x m_val : ℕ) : Prop :=
  x > 0 ∧
  x % m_val = 1 ∧
  ∀ p, Nat.Prime p → Nat.sqrt k < p → p ≤ k → 1 ≤ x % p ∧ x % p ≤ p - (k % p)

/-
Definition of good_x using good_x_nom.
-/
def good_x (k x : ℕ) : Prop := good_x_nom k x (m k)

/-
Definition of good_y without referencing m k directly.
-/
def good_y_nom (k y m_val : ℕ) : Prop :=
  y > 0 ∧
  y % m_val = 0 ∧
  ∀ p, Nat.Prime p → Nat.sqrt k < p → p ≤ k → ∃ b, p - (k % p) ≤ b ∧ b ≤ p ∧ y % p = b % p

/-
Definition of good_y using good_y_nom.
-/
def good_y (k y : ℕ) : Prop := good_y_nom k y (m k)

/-
The ratio equality holds for all primes.
-/
theorem ratio_equality_final (k : ℕ) (x y : ℕ) (hk : k ≥ 2)
  (hx0 : x > 0) (hy0 : y > 0)
  (hx_good : good_x k x)
  (hy_good : good_y k y)
  : (∏ i ∈ Finset.Icc y (y + k), (i : ℚ)) / (Finset.Icc y (y + k)).lcm id =
    (M k : ℚ) * (∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) / (Finset.Icc x (x + k - 1)).lcm id := by
      -- Apply the equality of p-adic valuations for all primes p.
      have h_eq : ∀ p : ℕ, Nat.Prime p → padicValNat p ((∏ i ∈ Finset.Icc y (y + k), i) / (Finset.Icc y (y + k)).lcm id) = padicValNat p (M k) + padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) := by
        -- Apply the appropriate lemma based on the value of p relative to k.
        intros p hp
        by_cases h_case : p ≤ Nat.sqrt k;
        · apply valuation_small_p;
          all_goals norm_cast;
          · nlinarith [ Nat.sqrt_le k ];
          · have := hx_good.2.1;
            rw [ ← this, Nat.ModEq, Nat.mod_mod_of_dvd ];
            refine' dvd_trans _ ( Finset.dvd_prod_of_mem _ <| show p ∈ Finset.filter ( fun p => Nat.Prime p ∧ p * p ≤ k ) ( Finset.Icc 1 k ) from Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp.pos, by nlinarith [ Nat.sqrt_le k ] ⟩, hp, by nlinarith [ Nat.sqrt_le k ] ⟩ );
            rw [ Nat.factorization ] ; aesop;
          · have h_mod_y : y ≡ 0 [MOD m k] := by
              exact hy_good.2.1;
            refine Nat.modEq_zero_iff_dvd.mpr <| dvd_trans ?_ <| Nat.dvd_of_mod_eq_zero h_mod_y;
            unfold m;
            rw [ Finset.prod_eq_prod_diff_singleton_mul <| show p ∈ Finset.filter ( fun p => Nat.Prime p ∧ p * p ≤ k ) ( Finset.Icc 1 k ) from ?_ ];
            · exact dvd_mul_of_dvd_right ( by rw [ Nat.factorization_def ] ; aesop ) _;
            · exact Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp.pos, by nlinarith [ Nat.sqrt_le k ] ⟩, hp, by nlinarith [ Nat.sqrt_le k ] ⟩;
        · by_cases h_case2 : p > k;
          · -- Since $p > k$, we have $v_p(M) = 0$.
            have h_vp_M_zero : padicValNat p (M k) = 0 := by
              have h_vp_M_zero : Nat.log p k = 0 := by
                exact Nat.log_of_lt h_case2;
              convert padicValNat_lcm_range k p hp ( by linarith ) using 1;
              exact h_vp_M_zero.symm;
            have h_val_zero : ∀ S : Finset ℕ, S.card = k + 1 → (∃ s, S = Finset.Icc s (s + k)) → (∀ z ∈ S, z ≠ 0) → padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = 0 := by
              intros S hS_card hS_consec h_nonzero
              apply valuation_very_large_p S p (k + 1) hp hS_card hS_consec (by
              linarith) h_nonzero;
            have h_val_zero_rhs : padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = 0 := by
              have h_val_zero_rhs : ∀ S : Finset ℕ, S.card = k → (∃ s, S = Finset.Icc s (s + k - 1)) → (∀ z ∈ S, z ≠ 0) → padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = 0 := by
                intros S hS_card hS_consec hS_nonzero
                apply valuation_very_large_p S p k hp hS_card hS_consec (by
                linarith) hS_nonzero;
              apply h_val_zero_rhs;
              · simp +arith +decide [ Nat.sub_add_cancel ( by linarith : 1 ≤ x + k ) ];
                omega;
              · use x;
              · exact fun z hz => by linarith [ Finset.mem_Icc.mp hz ] ;
            rw [ h_val_zero _ _ ⟨ y, rfl ⟩ fun z hz => by linarith [ Finset.mem_Icc.mp hz ], h_vp_M_zero, h_val_zero_rhs, zero_add ];
            simp +arith +decide;
            exact Nat.sub_eq_of_eq_add <| by ring;
          · -- Apply the appropriate lemma based on the value of p relative to k and the modular conditions.
            have h_val_large_p : padicValNat p ((∏ i ∈ Finset.Icc y (y + k), i) / (Finset.Icc y (y + k)).lcm id) = (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k))).card - 1 := by
              apply valuation_large_p_le;
              exact hp;
              exact rfl;
              · exact ⟨ y, by simp +arith +decide ⟩;
              · norm_num;
                nlinarith only [ h_case, h_case2, Nat.lt_succ_sqrt k ];
              · exact ⟨ p * ( y / p + 1 ), Finset.mem_Icc.mpr ⟨ by linarith [ Nat.div_add_mod y p, Nat.mod_lt y hp.pos ], by linarith [ Nat.div_mul_le_self y p ] ⟩, by norm_num ⟩;
              · exact fun z hz => by linarith [ Finset.mem_Icc.mp hz ] ;
            have h_val_large_p_rhs : padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = (Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card - 1 := by
              apply valuation_large_p_le;
              any_goals tauto;
              · simp +arith +decide [ Nat.sub_add_comm ( by linarith : 1 ≤ x + k ) ];
                exact ⟨ x, by rw [ show k + x - 1 + 1 - x = k by omega ] ; ring_nf ⟩;
              · norm_num;
                rw [ tsub_add_cancel_of_le ] <;> nlinarith only [ hk, h_case, h_case2, Nat.lt_succ_sqrt k ];
              · have := hx_good.2.2 p hp ( by linarith ) ( by linarith );
                exact ⟨ x + ( p - x % p ), Finset.mem_Icc.mpr ⟨ by omega, by omega ⟩, by exact ⟨ ( x / p ) + 1, by linarith [ Nat.div_add_mod x p, Nat.sub_add_cancel ( show x % p ≤ p from Nat.le_of_lt ( Nat.mod_lt _ hp.pos ) ) ] ⟩ ⟩;
              · exact fun z hz => by linarith [ Finset.mem_Icc.mp hz ] ;
            have h_count_multiples : (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k))).card = (k / p) + 1 ∧ (Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card = (k / p) := by
              apply And.intro;
              · apply count_multiples_large_p_LHS;
                · assumption;
                · grind;
                · assumption;
                · exact ⟨ not_le.mp h_case, not_lt.mp h_case2 ⟩;
                · have := hy_good.2.2 p hp ( by linarith ) ( by linarith ) ; aesop;
              · apply count_multiples_large_p_RHS k x p hp hk hx0 ⟨not_le.mp h_case, not_lt.mp h_case2⟩;
                have := hx_good.2.2 p hp ( not_le.mp h_case ) ( not_lt.mp h_case2 ) ; aesop;
            have h_padicValNat_M : padicValNat p (M k) = 1 := by
              have h_padicValNat_M : padicValNat p (M k) = Nat.log p k := by
                apply padicValNat_lcm_range k p hp (by linarith);
              rw [ h_padicValNat_M, Nat.log_eq_one_iff ];
              exact ⟨ by nlinarith only [ h_case, Nat.lt_succ_sqrt k ], hp.one_lt, le_of_not_gt h_case2 ⟩;
            simp_all +decide [ Nat.div_eq_of_lt ];
            rw [ add_tsub_cancel_of_le ( Nat.div_pos ( by linarith ) hp.pos ) ];
      -- By the properties of p-adic valuations, if the valuations of two numbers are equal for all primes p, then the numbers themselves are equal.
      have h_eq_rat : ((∏ i ∈ Finset.Icc y (y + k), i) / (Finset.Icc y (y + k)).lcm id) = (M k) * ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) := by
        apply_mod_cast Nat.factorization_inj <;> norm_num;
        · exact ⟨ hy0.ne', Nat.le_of_dvd ( Finset.prod_pos fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ) ( Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi ) ⟩;
        · exact ⟨ Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop, hx0.ne', Nat.le_of_dvd ( Finset.prod_pos fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ) <| Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi ⟩;
        · ext p; by_cases hp : Nat.Prime p <;> simp_all +decide [ Nat.factorization ] ;
          haveI := Fact.mk hp; rw [ padicValNat.mul ] <;> simp_all +decide [ Nat.factorization ] ;
          · exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
          · exact ⟨ hx0.ne', Nat.le_of_dvd ( Finset.prod_pos fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ) ( Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi ) ⟩;
      rw [ Nat.div_eq_iff_eq_mul_left ] at h_eq_rat;
      · rw [ div_eq_div_iff ] <;> norm_cast <;> norm_num;
        · rw [ ← Nat.cast_prod, h_eq_rat ];
          norm_num [ mul_assoc, mul_comm, mul_left_comm ];
          rw_mod_cast [ Nat.mul_div_cancel' ];
          · exact Or.inl <| Or.inl <| by rw [ Nat.cast_prod ] ;
          · exact Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi;
        · linarith;
        · linarith;
      · exact Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) );
      · exact Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi

/-
The product of (x+i)/(y+i) for i from 0 to k-1 is at least (x/y)^k, given x < y.
-/
lemma product_ratio_lower_bound (x y k : ℕ) (hx : x > 0) (hy : y > 0) (hxy : x < y) :
  (∏ i ∈ Finset.range k, ((x + i : ℚ) / (y + i : ℚ))) ≥ ((x : ℚ) / y) ^ k := by
    -- Since $x < y$, for each $i$ in the range $0$ to $k-1$, we have $\frac{x+i}{y+i} \geq \frac{x}{y}$.
    have h_term_ge : ∀ i ∈ Finset.range k, (x + i : ℝ) / (y + i) ≥ x / y := by
      exact fun i hi => by rw [ ge_iff_le, div_le_div_iff₀ ] <;> norm_cast <;> nlinarith;
    convert Finset.prod_le_prod ?_ h_term_ge using 1 <;> norm_num [ Finset.prod_mul_distrib ];
    · rw [ le_div_iff₀ ( Finset.prod_pos fun _ _ => by positivity ) ] ; ring_nf; norm_num;
      field_simp;
      norm_cast;
    · exact fun _ _ => by positivity;

/-
The ratio of the LCMs is at least M/(y+k) * (x/y)^k.
-/
lemma lcm_ratio_bound (k : ℕ) (x y : ℕ) (hk : k ≥ 2)
  (hx0 : x > 0) (hy0 : y > 0) (hxy : x < y)
  (hx_good : good_x k x)
  (hy_good : good_y k y) :
  (Finset.Icc x (x + k - 1)).lcm id / (Finset.Icc y (y + k)).lcm id ≥
  (M k : ℚ) / (y + k) * ((x : ℚ) / y) ^ k := by
    field_simp;
    -- By the ratio equality, we have:
    have h_ratio_eq : ((M k : ℚ) * (∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) / (Finset.Icc x (x + k - 1)).lcm id) =
                       ((∏ i ∈ Finset.Icc y (y + k), (i : ℚ)) / (Finset.Icc y (y + k)).lcm id) := by
                         exact Eq.symm (ratio_equality_final k x y hk hx0 hy0 hx_good hy_good);
    -- Using `product_ratio_lower_bound`, the product is $\ge (x/y)^k$.
    have h_prod_ratio_lower_bound : (∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) / (∏ i ∈ Finset.Icc y (y + k), (i : ℚ)) ≥ ((x : ℚ) / y) ^ k / (↑y + ↑k) := by
      have h_prod_ratio_lower_bound : (∏ i ∈ Finset.range k, ((x + i : ℚ) / (y + i : ℚ))) ≥ ((x : ℚ) / y) ^ k := by
        exact product_ratio_lower_bound x y k hx0 hy0 hxy;
      have h_prod_ratio_lower_bound : (∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) = (∏ i ∈ Finset.range k, (x + i : ℚ)) ∧ (∏ i ∈ Finset.Icc y (y + k), (i : ℚ)) = (∏ i ∈ Finset.range (k + 1), (y + i : ℚ)) := by
        constructor <;> erw [ Finset.prod_Ico_eq_prod_range ];
        · rw [ Nat.sub_add_cancel ( by linarith ), add_tsub_cancel_left, Finset.prod_congr rfl ] ; aesop;
        · simp +arith +decide [ add_assoc ];
      simp_all +decide [ Finset.prod_range_succ ];
      rw [ div_mul_eq_div_div ] ; gcongr;
    rw [ ge_iff_le, div_le_iff₀ ] at * <;> try positivity;
    rw [ div_eq_iff ] at h_ratio_eq;
    · convert mul_le_mul_of_nonneg_left h_prod_ratio_lower_bound ( show ( 0 : ℚ ) ≤ ↑ ( M k ) by positivity ) using 1 ; ring_nf;
      simp_all +decide [ add_comm, mul_assoc, mul_comm, mul_left_comm ];
      by_cases h : ∏ x ∈ Finset.Icc y ( k + y ), ( x : ℚ ) = 0 <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
      exact absurd h_prod_ratio_lower_bound ( not_le_of_gt ( by positivity ) );
    · aesop

/-
If x and y satisfy the given bounds, then the quantity is greater than C.
-/
lemma final_inequality_sufficient (C : ℝ) (hC : C ≥ 1) :
  ∃ K, ∀ k ≥ K, ∀ x y : ℕ,
    x > 0 → y > 0 →
    y < (M k : ℝ) / (4 * C) - k →
    y > (M k : ℝ) / (5 * C) * (1 + 1 / k) →
    (y : ℝ) - x < (M k : ℝ) / (5 * C * k) →
    (M k : ℝ) / (y + k) * ((x : ℝ) / y) ^ k > C := by
      field_simp;
      refine' ⟨ 1, fun k hk x y hx hy h₁ h₂ h₃ => _ ⟩;
      -- We know that $(\frac{x}{y})^k > (\frac{k}{k+1})^k = (1 + \frac{1}{k})^{-k}$.
      have h_exp : ((x : ℝ) / y) ^ k > (1 + 1 / k : ℝ)⁻¹ ^ k := by
        gcongr;
        field_simp at *;
        nlinarith [ ( by norm_cast : ( 1 : ℝ ) ≤ k ), mul_le_mul_of_nonneg_left ( show ( C : ℝ ) ≥ 1 by linarith ) ( show ( 0 : ℝ ) ≤ k by positivity ) ];
      -- Since $(1 + 1/k)^k < 3$ for all $k$, we have $(1 + 1/k)^{-k} > 1/3$.
      have h_inv_exp : (1 + 1 / k : ℝ)⁻¹ ^ k > 1 / 3 := by
        have h_inv_exp : (1 + 1 / k : ℝ) ^ k < 3 := by
          -- We know that $(1 + \frac{1}{k})^k < e$ for all $k$.
          have h_exp_bound : (1 + 1 / k : ℝ) ^ k < Real.exp 1 := by
            rw [ ← Real.rpow_natCast, Real.rpow_def_of_pos ( by positivity ) ];
            exact Real.exp_lt_exp.mpr ( by nlinarith [ one_div_mul_cancel ( by positivity : ( k : ℝ ) ≠ 0 ), Real.log_lt_sub_one_of_pos ( by positivity : 0 < ( 1 + 1 / ( k : ℝ ) ) ) ( by aesop ), ( by norm_cast : ( 1 :ℝ ) ≤ k ) ] );
          exact h_exp_bound.trans_le <| Real.exp_one_lt_d9.le.trans <| by norm_num;
        simpa using inv_strictAnti₀ ( by positivity ) h_inv_exp;
      rw [ lt_div_iff₀ ] at * <;> nlinarith [ ( by norm_cast : ( 1 :ℝ ) ≤ k ) ]

/-
The number of integers in an interval of length n <= p having residues in Bad is at most |Bad|.
-/
lemma count_bad_residues_interval (p : ℕ) (hp : p > 0) (Bad : Finset ℕ) (n : ℕ) (start : ℤ)
  (hn : n ≤ p)
  (hBad : ∀ x ∈ Bad, x < p) :
  ((Finset.Icc start (start + n - 1)).filter (fun z => (z % (p : ℤ)).toNat ∈ Bad)).card ≤ Bad.card := by
    have h_inj : ∀ z ∈ Finset.Icc start (start + n - 1), ∀ w ∈ Finset.Icc start (start + n - 1), z % p = w % p → z = w := by
      intros z hz w hw h_mod;
      norm_num +zetaDelta at *;
      exact Int.modEq_iff_dvd.mp h_mod.symm |> fun ⟨ k, hk ⟩ => by nlinarith [ show k = 0 by nlinarith ] ;
    have h_card : Finset.card (Finset.image (fun z => Int.toNat (z % p)) (Finset.filter (fun z => Int.toNat (z % p) ∈ Bad) (Finset.Icc start (start + n - 1)))) ≤ Finset.card Bad := by
      exact Finset.card_le_card ( Finset.image_subset_iff.mpr fun x hx => by aesop );
    rwa [ Finset.card_image_of_injOn fun x hx y hy hxy => h_inj x ( Finset.mem_filter.mp hx |>.1 ) y ( Finset.mem_filter.mp hy |>.1 ) <| by linarith [ Int.toNat_of_nonneg ( Int.emod_nonneg x <| Nat.cast_ne_zero.mpr hp.ne' ), Int.toNat_of_nonneg ( Int.emod_nonneg y <| Nat.cast_ne_zero.mpr hp.ne' ) ] ] at h_card

/-
The number of residues modulo p not covered by B is at most epsilon * p.
-/
lemma card_bad_residues (p : ℕ) (hp : p > 0) (B : Set ℤ) (ε : ℝ)
  (hB_subset : B ⊆ Set.Icc 1 p)
  (hB_size : B.ncard ≥ (1 - ε) * p) :
  ((Finset.range p).filter (fun r => ∀ b ∈ B, Int.toNat (b % (p : ℤ)) ≠ r)).card ≤ ε * p := by
    by_cases hB_finite : B.Finite;
    · have hB_image : (Finset.image (fun b : ℤ => (b % p).toNat) (hB_finite.toFinset)).card = B.ncard := by
        have h_inj : ∀ x y : ℤ, x ∈ B → y ∈ B → (x % p).toNat = (y % p).toNat → x = y := by
          intros x y hx hy hxy
          have h_eq_mod : x % p = y % p := by
            linarith [ Int.toNat_of_nonneg ( Int.emod_nonneg x ( by positivity : ( p : ℤ ) ≠ 0 ) ), Int.toNat_of_nonneg ( Int.emod_nonneg y ( by positivity : ( p : ℤ ) ≠ 0 ) ) ];
          have := hB_subset hx; have := hB_subset hy; simp_all ( config := { decide := Bool.true } ) [ Int.emod_eq_of_lt ] ;
          by_contra hxy_ne;
          exact hxy_ne ( by obtain ⟨ k, hk ⟩ := Int.modEq_iff_dvd.mp h_eq_mod.symm; nlinarith [ show k = 0 by nlinarith ] );
        rw [ Finset.card_image_of_injOn fun x hx y hy hxy => h_inj x y ( by simpa using hx ) ( by simpa using hy ) hxy, ← Set.ncard_coe_finset ] ; aesop;
      have hB_complement : (Finset.filter (fun r => ∀ b ∈ hB_finite.toFinset, (b % p).toNat ≠ r) (Finset.range p)).card = p - (Finset.image (fun b : ℤ => (b % p).toNat) (hB_finite.toFinset)).card := by
        rw [ show ( Finset.filter ( fun r => ∀ b ∈ hB_finite.toFinset, ( b % p : ℤ ).toNat ≠ r ) ( Finset.range p ) ) = Finset.range p \ Finset.image ( fun b => ( b % p : ℤ ).toNat ) hB_finite.toFinset from ?_ ];
        · rw [ Finset.card_sdiff ] ; norm_num;
          rw [ Finset.inter_eq_left.mpr ];
          exact Finset.image_subset_iff.mpr fun x hx => Finset.mem_range.mpr <| by linarith [ Int.emod_lt_of_pos x ( by positivity : 0 < ( p : ℤ ) ), Int.toNat_of_nonneg <| Int.emod_nonneg x <| show ( p : ℤ ) ≠ 0 by positivity ] ;
        · ext; aesop;
      simp_all +decide [ Set.subset_def ];
      rw [ Nat.cast_sub ];
      · linarith;
      · have hB_image : (Finset.image (fun b : ℤ => (b % p).toNat) (hB_finite.toFinset)).card ≤ p := by
          exact le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun x hx => Finset.mem_range.mpr <| Int.toNat_lt ( Int.emod_nonneg _ <| by positivity ) |>.2 <| Int.emod_lt_of_pos _ <| by positivity ) ( by simp );
        linarith;
    · exact False.elim <| hB_finite <| Set.Finite.subset ( Set.finite_Icc 1 ( p : ℤ ) ) hB_subset

/-
The number of integers in an interval of length n <= p that do not match any residue in B is at most epsilon * p.
-/
lemma bad_count_bound (p : ℕ) (hp : p > 0) (B : Set ℤ) (ε : ℝ)
  (hB_subset : B ⊆ Set.Icc 1 (p : ℤ))
  (hB_size : B.ncard ≥ (1 - ε) * p)
  (n : ℕ) (start : ℤ) (hn : n ≤ p) :
  ((Finset.Icc start (start + n - 1)).filter (fun z => ∀ b ∈ B, ¬(z ≡ b [ZMOD p]))).card ≤ ε * p := by
    have := @card_bad_residues p hp B ε hB_subset;
    -- Apply the lemma about the count of bad residues in an interval.
    have h_card_bad_residues_interval : ((Finset.Icc start (start + n - 1)).filter (fun z => (z % (p : ℤ)).toNat ∈ ((Finset.range p).filter (fun r => ∀ b ∈ B, Int.toNat (b % (p : ℤ)) ≠ r)))).card ≤ ((Finset.range p).filter (fun r => ∀ b ∈ B, Int.toNat (b % (p : ℤ)) ≠ r)).card := by
      convert count_bad_residues_interval p hp _ n start hn _ using 1;
      aesop;
    refine' le_trans _ ( this hB_size );
    refine' mod_cast le_trans _ h_card_bad_residues_interval;
    refine Finset.card_mono ?_;
    intro z hz; simp_all +decide [ Int.ModEq, Int.emod_nonneg _ ( by positivity : ( p : ℤ ) ≠ 0 ) ] ;
    exact ⟨ Int.emod_lt_of_pos _ ( by positivity ), fun b hb => fun h => hz.2 b hb <| by linarith [ Int.toNat_of_nonneg ( Int.emod_nonneg z ( by positivity : ( p : ℤ ) ≠ 0 ) ), Int.toNat_of_nonneg ( Int.emod_nonneg b ( by positivity : ( p : ℤ ) ≠ 0 ) ) ] ⟩

/-
For two primes p1, p2, and large sets B1, B2, any interval of length n (sufficiently large) contains a number with residues in B1, B2.
-/
lemma claim_approx_2 (p1 p2 : ℕ) (hp1 : p1.Prime) (hp2 : p2.Prime) (hp_ne : p1 ≠ p2)
  (ε : ℝ) (B1 B2 : Set ℤ)
  (hB1_subset : B1 ⊆ Set.Icc 1 p1) (hB2_subset : B2 ⊆ Set.Icc 1 p2)
  (hB1_size : B1.ncard ≥ (1 - ε) * p1) (hB2_size : B2.ncard ≥ (1 - ε) * p2)
  (n : ℕ) (hn : ε * (p1 + p2) < n) (hn_le1 : n ≤ p1) (hn_le2 : n ≤ p2) :
  ∀ start : ℤ, ∃ z ∈ Set.Icc start (start + n - 1),
    ∃ c1 ∈ B1, ∃ c2 ∈ B2,
    z ≡ c1 [ZMOD p1] ∧ z ≡ c2 [ZMOD p2] := by
      intro start;
      -- Let $Bad_1 = \{ z \in I \mid \forall b \in B_1, z \not\equiv b \pmod {p_1} \}$.
      set Bad1 := (Finset.Icc start (start + n - 1)).filter (fun z => ∀ b ∈ B1, ¬(z ≡ b [ZMOD p1])) with hBad1_def
      -- Let $Bad_2 = \{ z \in I \mid \forall b \in B_2, z \not\equiv b \pmod {p_2} \}$.
      set Bad2 := (Finset.Icc start (start + n - 1)).filter (fun z => ∀ b ∈ B2, ¬(z ≡ b [ZMOD p2])) with hBad2_def;
      -- By `bad_count_bound`, $|Bad_1| \le \epsilon p_1$ and $|Bad_2| \le \epsilon p_2$.
      have hBad1_card : Bad1.card ≤ ε * p1 := by
        convert bad_count_bound p1 hp1.pos B1 ε hB1_subset hB1_size n start hn_le1 using 1
      have hBad2_card : Bad2.card ≤ ε * p2 := by
        convert bad_count_bound p2 ( Nat.cast_pos.mpr hp2.pos ) B2 ε hB2_subset hB2_size n start ( mod_cast hn_le2 ) using 1;
      -- The set of $z \in I$ that fail the condition for at least one prime is $Bad_1 \cup Bad_2$.
      have h_union_card : (Bad1 ∪ Bad2).card < n := by
        exact_mod_cast ( by linarith [ show ( Finset.card ( Bad1 ∪ Bad2 ) : ℝ ) ≤ Finset.card Bad1 + Finset.card Bad2 by exact_mod_cast Finset.card_union_le _ _ ] : ( Finset.card ( Bad1 ∪ Bad2 ) : ℝ ) < n );
      -- Since $|I| = n$, there exists $z \in I \setminus (Bad_1 \cup Bad_2)$.
      obtain ⟨z, hz⟩ : ∃ z ∈ Finset.Icc start (start + n - 1), z ∉ Bad1 ∪ Bad2 := by
        exact Finset.not_subset.mp fun h => h_union_card.not_ge <| by simpa [ Finset.card_image_of_injective, Function.Injective ] using Finset.card_le_card h;
      simp_all +decide [ Finset.mem_union, Finset.mem_filter ];
      exact ⟨ z, hz.1, by obtain ⟨ x, hx1, hx2 ⟩ := hz.2.1 hz.1.1 hz.1.2; obtain ⟨ y, hy1, hy2 ⟩ := hz.2.2 hz.1.1 hz.1.2; exact ⟨ x, hx1, y, hy1, hx2, hy2 ⟩ ⟩

/-
M_prime is M divided by p1*p2.
-/
def M_prime (k p1 p2 : ℕ) : ℕ := (M k) / (p1 * p2)

/-
p1*p2 divides M k if p1, p2 are distinct primes <= k.
-/
lemma M_prime_dvd (k p1 p2 : ℕ) (hp1 : p1.Prime) (hp2 : p2.Prime) (hp_ne : p1 ≠ p2)
  (h_le1 : p1 ≤ k) (h_le2 : p2 ≤ k) :
  p1 * p2 ∣ M k := by
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by simpa [ * ] using Nat.coprime_primes hp1 hp2 ) ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hp1.pos, h_le1 ⟩ ) ) ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hp2.pos, h_le2 ⟩ ) )

/-
M_prime is coprime to p1 and p2.
-/
lemma M_prime_coprime (k p1 p2 : ℕ) (hp1 : p1.Prime) (hp2 : p2.Prime) (hp_ne : p1 ≠ p2)
  (h_range1 : k / 2 < p1 ∧ p1 ≤ k) (h_range2 : k / 2 < p2 ∧ p2 ≤ k)
  (hk : k ≥ 4) :
  Nat.Coprime (M_prime k p1 p2) p1 ∧ Nat.Coprime (M_prime k p1 p2) p2 := by
    unfold M_prime;
    -- Since $p1$ and $p2$ are distinct primes greater than $k/2$, their squares are greater than $k$, so $p1^2$ and $p2^2$ cannot divide $M k$.
    have h_not_div_p1 : ¬(p1^2 ∣ M k) := by
      have h_not_div_p1 : Nat.factorization (M k) p1 = 1 := by
        have h_val_p1 : Nat.factorization (M k) p1 = Nat.log p1 k := by
          have := @padicValNat_lcm_range k p1 hp1;
          rw [ ← this ( by linarith ), Nat.factorization_def ] ; aesop;
        rw [ h_val_p1, Nat.log_eq_one_iff ];
        exact ⟨ by nlinarith only [ hk, h_range1, Nat.div_add_mod k 2, Nat.mod_lt k two_pos ], hp1.one_lt, h_range1.2 ⟩;
      rw [ ← Nat.factorization_le_iff_dvd ] <;> aesop
    have h_not_div_p2 : ¬(p2^2 ∣ M k) := by
      have h_log_p2 : Nat.log p2 k < 2 := by
        exact Nat.log_lt_of_lt_pow ( by linarith ) ( by nlinarith [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos ] );
      have h_log_p2 : padicValNat p2 (M k) = Nat.log p2 k := by
        apply padicValNat_lcm_range;
        · assumption;
        · grind;
      rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num;
      · intro h; have := h p2; simp_all +decide [ Nat.factorization ] ;
        linarith;
      · exact hp2.ne_zero;
      · exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
    constructor;
    · refine' Nat.Coprime.symm ( hp1.coprime_iff_not_dvd.mpr _ );
      rw [ Nat.dvd_div_iff_mul_dvd ];
      · exact fun h => h_not_div_p1 <| dvd_trans ⟨ p2, by ring ⟩ h;
      · exact M_prime_dvd k p1 p2 hp1 hp2 hp_ne h_range1.2 h_range2.2;
    · refine' Nat.Coprime.symm ( hp2.coprime_iff_not_dvd.mpr _ );
      rw [ Nat.dvd_div_iff_mul_dvd ];
      · exact fun h => h_not_div_p2 <| dvd_trans ⟨ p1, by ring ⟩ h;
      · exact M_prime_dvd k p1 p2 hp1 hp2 hp_ne h_range1.2 h_range2.2

/-
Definitions of the intervals for x and y as specified in the proof.
-/
def y_interval (k : ℕ) (C : ℝ) : Set ℝ := Set.Ioo ((M k : ℝ) / (5 * C) * (1 + 1 / k)) ((M k : ℝ) / (4 * C) - k)

def x_interval (k : ℕ) (y : ℕ) (C : ℝ) : Set ℝ := Set.Ioo ((y : ℝ) - (M k : ℝ) / (5 * C * k)) (y : ℝ)

/-
Definition of B_set and its subset property.
-/
def B_set (k p : ℕ) : Set ℤ := Set.Icc ((p : ℤ) - (k % p : ℤ)) (p : ℤ)

lemma B_set_subset (k p : ℕ) (hp : p.Prime) (hk : k > 0) : B_set k p ⊆ Set.Icc 1 p := by
  -- Take any $b \in B_set k p$. By definition, $p - (k \% p) \leq b \leq p$.
  intro b hb
  rw [B_set] at hb
  obtain ⟨hb_lower, hb_upper⟩ := hb
  exact ⟨by linarith [Nat.zero_le (k % p), Nat.mod_lt k hp.pos], by linarith [Nat.zero_le (k % p), Nat.mod_lt k hp.pos]⟩

/-
Definition of B_set_star and its subset property.
-/
def B_set_star (k p M_val : ℕ) : Set ℤ := { c ∈ Set.Icc 1 (p : ℤ) | ∃ b ∈ B_set k p, c * (M_val : ℤ) ≡ b [ZMOD p] }

lemma B_set_star_subset (k p M_val : ℕ) : B_set_star k p M_val ⊆ Set.Icc 1 p := by
  exact fun x hx => hx.1

/-
Cardinality of B_set_star is the same as B_set.
-/
lemma B_set_star_ncard (k p M_val : ℕ) (hp : p.Prime) (h_coprime : Nat.Coprime M_val p) (hk : k > 0) :
  (B_set_star k p M_val).ncard = (B_set k p).ncard := by
    apply le_antisymm;
    · -- Since $M_val$ is coprime to $p$, multiplication by $M_val$ is a bijection on $\mathbb{Z}_p$.
      have h_bijection : ∀ c1 c2 : ℤ, c1 ∈ Set.Icc 1 (p : ℤ) → c2 ∈ Set.Icc 1 (p : ℤ) → c1 * M_val ≡ c2 * M_val [ZMOD p] → c1 ≡ c2 [ZMOD p] := by
        intro c1 c2 hc1 hc2 h; haveI := Fact.mk hp; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
        exact h.resolve_right ( by rw [ ZMod.natCast_eq_zero_iff ] ; exact fun h => by have := Nat.gcd_eq_right h; aesop );
      have h_bijection : ∀ c : ℤ, c ∈ B_set_star k p M_val → ∃ b ∈ B_set k p, c * M_val ≡ b [ZMOD p] := by
        exact fun c hc => by rcases hc with ⟨ hc1, b, hb1, hb2 ⟩ ; exact ⟨ b, hb1, hb2 ⟩ ;
      choose! f hf using h_bijection;
      have h_bijection : Set.InjOn f (B_set_star k p M_val) := by
        intros c1 hc1 c2 hc2 h_eq;
        have := hf c1 hc1; have := hf c2 hc2; simp_all +decide [ Int.ModEq ] ;
        have := h_bijection c1 c2 ( hc1.1.1 ) ( hc1.1.2 ) ( hc2.1.1 ) ( hc2.1.2 ) ; simp_all +decide [ Int.emod_eq_emod_iff_emod_sub_eq_zero ] ;
        exact eq_of_sub_eq_zero ( by obtain ⟨ k, hk ⟩ := this ( by obtain ⟨ a, ha ⟩ := hf c1 hc1 |>.2; obtain ⟨ b, hb ⟩ := hf c2 hc2 |>.2; exact ⟨ a - b, by linarith ⟩ ) ; nlinarith [ hp.two_le, show k = 0 from by nlinarith [ hp.two_le, hc1.1.1, hc1.1.2, hc2.1.1, hc2.1.2 ] ] );
      apply Set.ncard_le_ncard_of_injOn;
      exacts [ fun c hc => hf c hc |>.1, h_bijection, Set.finite_Icc _ _ |> Set.Finite.subset <| fun x hx => ⟨ hx.1, hx.2 ⟩ ];
    · -- Since $M_val$ is coprime to $p$, multiplication by $M_val$ is a bijection on $\mathbb{Z}/p\mathbb{Z}$.
      have h_bijection : ∀ b ∈ B_set k p, ∃ c ∈ B_set_star k p M_val, c * (M_val : ℤ) ≡ b [ZMOD p] := by
        intro b hb
        obtain ⟨c, hc⟩ : ∃ c : ℤ, c * (M_val : ℤ) ≡ b [ZMOD p] ∧ 1 ≤ c ∧ c ≤ p := by
          -- Since $M_val$ is coprime to $p$, there exists an integer $c$ such that $c * M_val \equiv b \pmod{p}$.
          obtain ⟨c, hc⟩ : ∃ c : ℤ, c * (M_val : ℤ) ≡ b [ZMOD p] := by
            have := Nat.gcd_eq_gcd_ab M_val p;
            exact ⟨ b * Nat.gcdA M_val p, by rw [ Int.modEq_iff_dvd ] ; use Nat.gcdB M_val p * b; nlinarith [ hb.1, hb.2 ] ⟩;
          -- Since $c * M_val \equiv b \pmod{p}$, we can take $c' = c \mod p$. Then $c' * M_val \equiv b \pmod{p}$ and $0 \leq c' < p$.
          obtain ⟨c', hc'⟩ : ∃ c' : ℤ, c' * (M_val : ℤ) ≡ b [ZMOD p] ∧ 0 ≤ c' ∧ c' < p := by
            exact ⟨ c % p, by simpa [ Int.ModEq, Int.mul_emod ] using hc, Int.emod_nonneg _ ( Nat.cast_ne_zero.mpr hp.ne_zero ), Int.emod_lt_of_pos _ ( Nat.cast_pos.mpr hp.pos ) ⟩;
          by_cases hc'_zero : c' = 0;
          · simp_all +decide [ Int.ModEq ];
            exact ⟨ p, by simp +decide [ ← hc'.1 ], by linarith, by linarith ⟩;
          · exact ⟨ c', hc'.1, lt_of_le_of_ne hc'.2.1 ( Ne.symm hc'_zero ), hc'.2.2.le ⟩;
        unfold B_set_star; aesop;
      choose! f hf using h_bijection;
      -- Since $f$ is injective, the cardinality of $B_set_star k p M_val$ is at least the cardinality of $B_set k p$.
      have h_inj : Set.InjOn f (B_set k p) := by
        intro b hb b' hb' h; have := hf b hb; have := hf b' hb'; simp_all +decide [ Int.ModEq ] ;
        rw [ Int.emod_eq_emod_iff_emod_sub_eq_zero ] at this;
        simp_all +decide [ B_set ];
        obtain ⟨ a, ha ⟩ := this; nlinarith [ show a = 0 by nlinarith [ Nat.zero_le ( k % p ), Nat.mod_lt k hp.pos ] ] ;
      apply_rules [ Set.ncard_le_ncard_of_injOn ];
      · exact fun x hx => hf x hx |>.1;
      · exact Set.Finite.subset ( Set.finite_Icc 1 ( p : ℤ ) ) fun x hx => hx.1

/-
The density of B_set is at least 1 - 2*epsilon.
-/
lemma B_set_density_bound (k p : ℕ) (ε : ℝ) (hp : p.Prime)
  (h_eps_pos : ε > 0) (h_eps_small : ε ≤ 0.25)
  (h_range : (k : ℝ) / 2 < p ∧ (p : ℝ) < (1 + ε) * k / 2) :
  (B_set k p).ncard ≥ (1 - 2 * ε) * p := by
    unfold B_set;
    norm_num [ Set.ncard_eq_toFinset_card' ];
    erw [ Int.toNat_natCast ];
    norm_num +zetaDelta at *;
    rw [ Nat.mod_eq_sub_mod ];
    · by_cases h_cases : p ≤ k;
      · rw [ Nat.mod_eq_of_lt ];
        · rw [ Nat.cast_sub h_cases ] ; nlinarith [ show ( p : ℝ ) ≤ k by norm_cast ];
        · rw [ div_lt_iff₀ ] at h_range <;> norm_cast at * ; linarith [ Nat.sub_add_cancel h_cases ];
      · rw [ Nat.sub_eq_zero_of_le ( le_of_not_ge h_cases ) ] ; norm_num ; nlinarith [ show ( p : ℝ ) ≥ k + 1 by exact_mod_cast not_le.mp h_cases ];
    · exact Nat.le_of_lt_succ ( by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith )

/-
Definition of the length of the y interval.
-/
def y_interval_length (k : ℕ) (C : ℝ) : ℝ :=
  ((M k : ℝ) / (4 * C) - k) - ((M k : ℝ) / (5 * C) * (1 + 1 / k))

/-
If an interval (A, B) is large enough (scaled length > n), there exists a starting integer such that a block of n integers, when scaled, fits inside (A, B).
-/
lemma exists_start_for_interval (A B : ℝ) (M_val : ℝ) (n : ℕ) (hM : M_val > 0) (h_len : (B - A) / M_val > n) :
  ∃ start : ℤ, ∀ z : ℤ, z ∈ Set.Icc start (start + n - 1) → (z : ℝ) * M_val ∈ Set.Ioo A B := by
    norm_num +zetaDelta at *;
    have h_start : ∃ start : ℤ, (A / M_val : ℝ) < start ∧ start + n - 1 < B / M_val := by
      ring_nf at *;
      exact ⟨ ⌊A * M_val⁻¹⌋ + 1, by push_cast; linarith [ Int.lt_floor_add_one ( A * M_val⁻¹ ) ], by push_cast; linarith [ Int.floor_le ( A * M_val⁻¹ ) ] ⟩;
    cases' h_start with start h_start ; use start ; intro z h₁ h₂ ; constructor <;> nlinarith [ mul_div_cancel₀ A hM.ne', mul_div_cancel₀ B hM.ne', show ( z : ℝ ) ≥ start by exact_mod_cast h₁, show ( z : ℝ ) ≤ start + n - 1 by exact_mod_cast h₂ ]

/-
m(k) divides M_prime(k, p1, p2).
-/
lemma m_dvd_M_prime (k p1 p2 : ℕ) (hp1 : p1.Prime) (hp2 : p2.Prime) (hp_ne : p1 ≠ p2)
  (h_range1 : k.sqrt < p1 ∧ p1 ≤ k) (h_range2 : k.sqrt < p2 ∧ p2 ≤ k) :
  m k ∣ M_prime k p1 p2 := by
    -- Since $p1$ and $p2$ are distinct primes greater than $\sqrt{k}$, their product $p1 * p2$ does not divide any of the prime powers in $m$.
    have h_div : ∀ p ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ p * p ≤ k), ¬(p1 ∣ p) ∧ ¬(p2 ∣ p) := by
      norm_num +zetaDelta at *;
      exact fun p hp₁ hp₂ hp₃ hp₄ => ⟨ fun h => by have := Nat.le_of_dvd ( by linarith ) h; nlinarith [ Nat.lt_succ_sqrt k ], fun h => by have := Nat.le_of_dvd ( by linarith ) h; nlinarith [ Nat.lt_succ_sqrt k ] ⟩;
    -- Since $p1$ and $p2$ are distinct primes greater than $\sqrt{k}$, their product $p1 * p2$ does not divide any of the prime powers in $M$.
    have h_div_M : ∀ p ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ p * p ≤ k), ¬(p1 ∣ p) ∧ ¬(p2 ∣ p) → (p ^ ((M k).factorization p)) ∣ M_prime k p1 p2 := by
      intros p hp h_div_p
      have h_div_M : p ^ ((M k).factorization p) ∣ M k := by
        exact Nat.ordProj_dvd _ _;
      refine' Nat.dvd_div_of_mul_dvd _;
      refine' Nat.Coprime.mul_dvd_of_dvd_of_dvd _ _ h_div_M;
      · exact Nat.Coprime.mul_left ( hp1.coprime_iff_not_dvd.mpr h_div_p.1 ) ( hp2.coprime_iff_not_dvd.mpr h_div_p.2 ) |> Nat.Coprime.pow_right _;
      · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by simpa [ * ] using Nat.coprime_primes hp1 hp2 ) ( Nat.dvd_trans ( by aesop ) ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ : p1 ∈ Finset.Icc 1 k ) ) ) ( Nat.dvd_trans ( by aesop ) ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ : p2 ∈ Finset.Icc 1 k ) ) );
    -- Since the product of coprime divisors divides the number, we can conclude that m(k) divides M_prime.
    have h_coprime_divisors : ∀ p q : ℕ, p ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ p * p ≤ k) → q ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ p * p ≤ k) → p ≠ q → Nat.Coprime (p ^ ((M k).factorization p)) (q ^ ((M k).factorization q)) := by
      intros p q hp hq hpq; exact Nat.coprime_pow_primes _ _ ( by aesop ) ( by aesop ) ( by aesop ) ;
    have h_prod_coprime_divisors : ∀ {S : Finset ℕ}, (∀ p ∈ S, p ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ p * p ≤ k)) → (∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime (p ^ ((M k).factorization p)) (q ^ ((M k).factorization q))) → (∏ p ∈ S, p ^ ((M k).factorization p)) ∣ M_prime k p1 p2 := by
      intros S hS h_coprime; induction' S using Finset.induction with p S hS ih; aesop;
      rw [ Finset.prod_insert ‹p ∉ S› ];
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by exact Nat.Coprime.prod_right fun q hq => h_coprime p ( Finset.mem_insert_self _ _ ) q ( Finset.mem_insert_of_mem hq ) <| by aesop ) ( h_div_M p ( hS p <| Finset.mem_insert_self _ _ ) <| h_div p ( hS p <| Finset.mem_insert_self _ _ ) ) ( ih ( fun q hq => hS q <| Finset.mem_insert_of_mem hq ) ( fun q hq r hr hqr => h_coprime q ( Finset.mem_insert_of_mem hq ) r ( Finset.mem_insert_of_mem hr ) hqr ) );
    exact h_prod_coprime_divisors ( fun p hp => hp ) ( fun p hp q hq hpq => h_coprime_divisors p q hp hq hpq )

/-
M(k) is positive for k >= 1.
-/
lemma M_pos (k : ℕ) (hk : k ≥ 1) : M k > 0 := by
  exact Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) )

/-
If z satisfies the modular conditions and y = z * M', then y is good.
-/
lemma good_y_of_mod_conditions (k p1 p2 : ℕ) (z : ℤ) (y : ℕ)
  (hp1 : p1.Prime) (hp2 : p2.Prime) (hp_ne : p1 ≠ p2)
  (h_range1 : k.sqrt < p1 ∧ p1 ≤ k) (h_range2 : k.sqrt < p2 ∧ p2 ≤ k)
  (h_y_eq : (y : ℤ) = z * (M_prime k p1 p2 : ℤ))
  (h_y_pos : y > 0)
  (h_z_mod1 : ∃ c1 ∈ B_set_star k p1 (M_prime k p1 p2), z ≡ c1 [ZMOD p1])
  (h_z_mod2 : ∃ c2 ∈ B_set_star k p2 (M_prime k p1 p2), z ≡ c2 [ZMOD p2]) :
  good_y k y := by
    refine' ⟨ h_y_pos, _, _ ⟩;
    · -- By definition of $y$, we know that $y = z * M'$, and since $M'$ is divisible by $m$, it follows that $y$ is also divisible by $m$.
      have h_div : m k ∣ M_prime k p1 p2 := by
        exact m_dvd_M_prime k p1 p2 hp1 hp2 hp_ne h_range1 h_range2;
      exact Nat.mod_eq_zero_of_dvd <| by exact_mod_cast h_y_eq.symm ▸ dvd_mul_of_dvd_right ( Int.natCast_dvd_natCast.mpr h_div ) _;
    · intro p hp hp_sqrt hp_le_k
      by_cases hp_cases : p = p1 ∨ p = p2;
      · rcases hp_cases with ( rfl | rfl ) <;> simp_all +decide [ ← Int.natCast_mod, Int.ModEq ];
        · obtain ⟨ c1, hc1₁, hc1₂ ⟩ := h_z_mod1;
          obtain ⟨ b, hb₁, hb₂ ⟩ := hc1₁.2;
          refine' ⟨ b.toNat, _, _, _ ⟩ <;> simp_all +decide [ Int.ModEq ];
          · have := hb₁.1; ( have := hb₁.2; ( norm_num [ B_set ] at *; omega; ) );
          · exact hb₁.2;
          · zify;
            simp_all +decide [ Int.emod_eq_emod_iff_emod_sub_eq_zero ];
            rw [ max_eq_left ( by linarith [ Set.mem_Icc.mp ( B_set_subset k p hp1 ( by linarith [ Nat.sqrt_pos.mpr ( show 0 < k from by linarith ) ] ) hb₁ ) ] ) ] ; convert dvd_add ( hc1₂.mul_right ( M_prime k p p2 ) ) hb₂ using 1 ; ring;
        · -- Since $z \equiv c2 \pmod{p}$, we have $z * M_prime \equiv c2 * M_prime \pmod{p}$. Therefore, $y \equiv b \pmod{p}$ for some $b \in B_set k p$.
          obtain ⟨b, hb⟩ : ∃ b ∈ B_set k p, z * M_prime k p1 p ≡ b [ZMOD p] := by
            obtain ⟨ c2, hc2₁, hc2₂ ⟩ := h_z_mod2;
            obtain ⟨ b, hb₁, hb₂ ⟩ := hc2₁;
            exact ⟨ hb₁, hb₂.1, by simpa [ Int.ModEq, Int.mul_emod, hc2₂ ] using hb₂.2 ⟩;
          -- Since $b \in B_set k p$, we have $p - k \% p \leq b \leq p$.
          obtain ⟨hb1, hb2⟩ : p - k % p ≤ b ∧ b ≤ p := by
            exact ⟨ hb.1.1, hb.1.2 ⟩;
          refine' ⟨ Int.toNat b, _, _, _ ⟩;
          · grind;
          · grind;
          · zify;
            rw [ Int.toNat_of_nonneg ( by linarith [ Int.emod_lt_of_pos ( k : ℤ ) ( Nat.cast_pos.mpr hp2.pos ) ] ) ] ; aesop;
      · have h_div : p ∣ M_prime k p1 p2 := by
          refine' Nat.dvd_div_of_mul_dvd _;
          refine' Nat.Coprime.mul_dvd_of_dvd_of_dvd _ _ _;
          · rw [ Nat.coprime_mul_iff_left ];
            exact ⟨ hp1.coprime_iff_not_dvd.mpr fun h => hp_cases <| Or.inl <| by rw [ Nat.prime_dvd_prime_iff_eq ] at h <;> tauto, hp2.coprime_iff_not_dvd.mpr fun h => hp_cases <| Or.inr <| by rw [ Nat.prime_dvd_prime_iff_eq ] at h <;> tauto ⟩;
          · exact M_prime_dvd k p1 p2 hp1 hp2 hp_ne h_range1.2 h_range2.2;
          · exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hp.pos, hp_le_k ⟩ );
        use p; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
        exact Nat.mod_eq_zero_of_dvd <| by exact_mod_cast h_y_eq.symm ▸ dvd_mul_of_dvd_right ( Int.natCast_dvd_natCast.mpr <| Nat.dvd_of_mod_eq_zero h_div ) _;

/-
If the interval is large enough and densities are good, then y exists.
-/
lemma exists_y_if_large_interval (C : ℝ) (hC : C ≥ 1) (k : ℕ) (p1 p2 : ℕ)
  (hp1 : p1.Prime) (hp2 : p2.Prime) (hp_lt : p1 < p2)
  (h_range1 : k / 2 < p1 ∧ p1 ≤ k) (h_range2 : k / 2 < p2 ∧ p2 ≤ k)
  (h_len : y_interval_length k C / (M_prime k p1 p2 : ℝ) > p1 + p2)
  (h_M_prime_coprime : Nat.Coprime (M_prime k p1 p2) p1 ∧ Nat.Coprime (M_prime k p1 p2) p2)
  (h_B_density : (B_set k p1).ncard ≥ (1 - 1 / (20 * C)) * p1 ∧ (B_set k p2).ncard ≥ (1 - 1 / (20 * C)) * p2)
  (h_eps_small : 1 / (20 * C) * (p1 + p2) < p1) :
  ∃ y : ℕ, (y : ℝ) ∈ y_interval k C ∧ good_y k y := by
    revert h_len;
    intro h_len
    obtain ⟨start, hstart⟩ : ∃ start : ℤ, ∀ z : ℤ, z ∈ Set.Icc start (start + p1 - 1) → (z : ℝ) * (M_prime k p1 p2) ∈ y_interval k C := by
      apply exists_start_for_interval;
      · exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop_cat ) );
      · norm_num +zetaDelta at *;
        convert lt_of_le_of_lt _ h_len using 1;
        · unfold y_interval_length; ring;
        · linarith;
    obtain ⟨z, hz_bounds, hz_mod1, hz_mod2⟩ : ∃ z : ℤ, z ∈ Set.Icc start (start + p1 - 1) ∧ (∃ c1 ∈ B_set_star k p1 (M_prime k p1 p2), z ≡ c1 [ZMOD p1]) ∧ (∃ c2 ∈ B_set_star k p2 (M_prime k p1 p2), z ≡ c2 [ZMOD p2]) := by
      have := claim_approx_2 p1 p2 hp1 hp2 ( ne_of_lt hp_lt ) ( 1 / ( 20 * C ) ) ( B_set_star k p1 ( M_prime k p1 p2 ) ) ( B_set_star k p2 ( M_prime k p1 p2 ) ) ?_ ?_ ?_ ?_ p1 ?_ ?_ ?_ <;> norm_num at *;
      any_goals linarith;
      · exact Exists.imp ( by aesop ) ( this start );
      · exact B_set_star_subset k p1 ( M_prime k p1 p2 );
      · exact B_set_star_subset k p2 ( M_prime k p1 p2 );
      · convert h_B_density.1 using 1;
        rw [ B_set_star_ncard ] ; aesop;
        · exact h_M_prime_coprime.1;
        · grind;
      · convert h_B_density.2 using 1;
        rw [ B_set_star_ncard ];
        · assumption;
        · exact h_M_prime_coprime.2;
        · grind;
    obtain ⟨y, hy_eq⟩ : ∃ y : ℕ, (y : ℤ) = z * (M_prime k p1 p2 : ℤ) ∧ y > 0 := by
      have hy_pos : 0 < (z : ℝ) * (M_prime k p1 p2 : ℝ) := by
        exact hstart z hz_bounds |>.1.trans_le' <| by positivity;
      exact ⟨ Int.natAbs ( z * M_prime k p1 p2 ), by simp +decide [ abs_of_pos ( show 0 < z * M_prime k p1 p2 from by exact_mod_cast hy_pos ) ], Int.natAbs_pos.mpr ( show z * M_prime k p1 p2 ≠ 0 from by exact_mod_cast hy_pos.ne' ) ⟩;
    refine' ⟨ y, _, _ ⟩;
    · convert hstart z hz_bounds using 1 ; norm_cast ; aesop;
    · apply good_y_of_mod_conditions;
      exact hp1;
      exact hp2;
      exact ne_of_lt hp_lt;
      any_goals tauto;
      · exact ⟨ Nat.sqrt_lt.mpr ( by nlinarith [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos ] ), h_range1.2 ⟩;
      · exact ⟨ Nat.sqrt_lt.mpr ( by nlinarith [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos ] ), h_range2.2 ⟩

/-
Definitions for x interval length, M_prime3, B_set_x, and B_set_x_star.
-/
def x_interval_length (k : ℕ) (C : ℝ) : ℝ := (M k : ℝ) / (5 * C * k)

def M_prime3 (k q1 q2 q3 : ℕ) : ℕ := (M k) / (q1 * q2 * q3)

def B_set_x (k p : ℕ) : Set ℤ := Set.Icc 1 ((p : ℤ) - (k % p : ℤ))

/-
B_set_x is a subset of [1, p].
-/
lemma B_set_x_subset (k p : ℕ) (hp : p.Prime) (hk : k > 0) : B_set_x k p ⊆ Set.Icc 1 p := by
  exact Set.Icc_subset_Icc_right ( by linarith [ Nat.zero_le ( k % p ) ] )

/-
Cardinality of B_set_x for p in (k/2, k).
-/
lemma B_set_x_ncard (k p : ℕ) (hp : p.Prime) (h_range : (1 : ℝ) / 2 * k < p ∧ p < k) :
  (B_set_x k p).ncard = 2 * p - k := by
    rw [ show B_set_x k p = Set.Icc 1 ( p - ( k % p ) : ℤ ) by ext; aesop, Set.ncard_eq_toFinset_card' ] ; norm_num;
    rw [ show ( k : ℤ ) % p = k - p by
          norm_cast at *;
          rw [ Int.subNatNat_of_le h_range.2.le ] ; norm_cast;
          rw [ Nat.mod_eq_sub_mod h_range.2.le ];
          rw [ Nat.mod_eq_of_lt ( by rw [ div_mul_eq_mul_div, div_lt_iff₀ ] at h_range <;> norm_cast at * ; omega ) ] ] ; ring_nf ; aesop

/-
M_prime3 is positive.
-/
lemma M_prime3_pos (k q1 q2 q3 : ℕ) (hk : k ≥ 1) (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
  (h_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (h_le1 : q1 ≤ k) (h_le2 : q2 ≤ k) (h_le3 : q3 ≤ k) : M_prime3 k q1 q2 q3 > 0 := by
    -- Since q1, q2, q3 are distinct primes ≤ k, they divide M(k). Therefore, q1 * q2 * q3 divides M(k), making M_prime3 k q1 q2 q3 positive.
    have h_div : q1 * q2 * q3 ∣ M k := by
      have h_div : q1 ∣ M k ∧ q2 ∣ M k ∧ q3 ∣ M k := by
        exact ⟨ Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hq1.pos, h_le1 ⟩ ), Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hq2.pos, h_le2 ⟩ ), Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hq3.pos, h_le3 ⟩ ) ⟩;
      convert Nat.lcm_dvd ( Nat.lcm_dvd h_div.1 h_div.2.1 ) h_div.2.2 using 1;
      simp_all +decide [ Nat.lcm ];
      have := Nat.coprime_primes hq1 hq2; ( have := Nat.coprime_primes hq1 hq3; ( have := Nat.coprime_primes hq2 hq3; simp_all +decide [ Nat.Coprime, Nat.Coprime.symm, Nat.Coprime.gcd_mul ] ; ) );
    exact Nat.div_pos ( Nat.le_of_dvd ( M_pos k hk ) h_div ) ( Nat.mul_pos ( Nat.mul_pos hq1.pos hq2.pos ) hq3.pos )

/-
m(k) divides M_prime3(k, q1, q2, q3).
-/
lemma m_dvd_M_prime3 (k q1 q2 q3 : ℕ) (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
  (h_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (h_range1 : k.sqrt < q1 ∧ q1 ≤ k) (h_range2 : k.sqrt < q2 ∧ q2 ≤ k) (h_range3 : k.sqrt < q3 ∧ q3 ≤ k) :
  m k ∣ M_prime3 k q1 q2 q3 := by
    refine' Nat.Coprime.dvd_of_dvd_mul_left _ _;
    exact q1 * q2 * q3;
    · -- Since $q1$, $q2$, and $q3$ are distinct primes greater than $\sqrt{k}$, they do not divide $m(k)$.
      have h_not_div : ¬(q1 ∣ m k) ∧ ¬(q2 ∣ m k) ∧ ¬(q3 ∣ m k) := by
        have h_not_div : ∀ p ∈ Finset.filter (fun p => p.Prime ∧ p * p ≤ k) (Finset.Icc 1 k), ¬(q1 ∣ p) ∧ ¬(q2 ∣ p) ∧ ¬(q3 ∣ p) := by
          intro p hp; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ;
          exact ⟨ by rintro rfl; nlinarith [ Nat.lt_succ_sqrt k ], by rintro rfl; nlinarith [ Nat.lt_succ_sqrt k ], by rintro rfl; nlinarith [ Nat.lt_succ_sqrt k ] ⟩;
        have h_not_div_prod : ∀ {S : Finset ℕ}, (∀ p ∈ S, ¬(q1 ∣ p) ∧ ¬(q2 ∣ p) ∧ ¬(q3 ∣ p)) → ¬(q1 ∣ Finset.prod S (fun p => p ^ (Nat.factorization (Finset.lcm (Finset.Icc 1 k) id) p))) ∧ ¬(q2 ∣ Finset.prod S (fun p => p ^ (Nat.factorization (Finset.lcm (Finset.Icc 1 k) id) p))) ∧ ¬(q3 ∣ Finset.prod S (fun p => p ^ (Nat.factorization (Finset.lcm (Finset.Icc 1 k) id) p))) := by
          intros S hS; induction S using Finset.induction <;> simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
          exact ⟨ Nat.Coprime.mul_right ( Nat.Coprime.pow_right _ hS.1.1 ) ( by tauto ), Nat.Coprime.mul_right ( Nat.Coprime.pow_right _ hS.1.2.1 ) ( by tauto ), Nat.Coprime.mul_right ( Nat.Coprime.pow_right _ hS.1.2.2 ) ( by tauto ) ⟩;
        exact h_not_div_prod h_not_div;
      exact Nat.Coprime.mul_right ( Nat.Coprime.mul_right ( Nat.Coprime.symm <| hq1.coprime_iff_not_dvd.mpr h_not_div.1 ) <| Nat.Coprime.symm <| hq2.coprime_iff_not_dvd.mpr h_not_div.2.1 ) <| Nat.Coprime.symm <| hq3.coprime_iff_not_dvd.mpr h_not_div.2.2;
    · rw [ show M_prime3 k q1 q2 q3 = M k / ( q1 * q2 * q3 ) from rfl ];
      rw [ Nat.mul_div_cancel' ];
      · have h_div : (∏ p ∈ Finset.filter (fun p => p.Prime ∧ p * p ≤ k) (Finset.Icc 1 k), p ^ (M k).factorization p) ∣ (∏ p ∈ Finset.Icc 1 k, p ^ (M k).factorization p) := by
          apply_rules [ Finset.prod_dvd_prod_of_subset, Finset.filter_subset ];
        convert h_div using 1;
        conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self ( show M k ≠ 0 from Nat.ne_of_gt ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ) ] ;
        rw [ Finsupp.prod_of_support_subset ] <;> norm_num [ Finset.subset_iff ];
        intro p pp dp _; exact ⟨ pp.pos, pp.dvd_factorial.mp ( dvd_trans dp ( Finset.lcm_dvd fun i hi => Nat.dvd_factorial ( Finset.mem_Icc.mp hi |>.1 ) ( Finset.mem_Icc.mp hi |>.2 ) ) ) ⟩ ;
      · have h_div : q1 ∣ M k ∧ q2 ∣ M k ∧ q3 ∣ M k := by
          exact ⟨ Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ), Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ), Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ) ⟩;
        convert Nat.lcm_dvd ( Nat.lcm_dvd h_div.1 h_div.2.1 ) h_div.2.2 using 1;
        simp +decide [ *, Nat.lcm ];
        have := Nat.coprime_primes hq1 hq2; have := Nat.coprime_primes hq1 hq3; have := Nat.coprime_primes hq2 hq3; simp_all +decide [ Nat.Coprime, Nat.Coprime.symm, Nat.Coprime.gcd_mul ] ;

/-
M_prime3(k, q1, q2, q3) is coprime to q1, q2, and q3.
-/
lemma M_prime3_coprime (k q1 q2 q3 : ℕ) (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
  (h_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (h_range1 : k / 2 < q1 ∧ q1 ≤ k) (h_range2 : k / 2 < q2 ∧ q2 ≤ k) (h_range3 : k / 2 < q3 ∧ q3 ≤ k)
  (hk : k ≥ 9) :
  Nat.Coprime (M_prime3 k q1 q2 q3) q1 ∧ Nat.Coprime (M_prime3 k q1 q2 q3) q2 ∧ Nat.Coprime (M_prime3 k q1 q2 q3) q3 := by
    have h_divides : q1 * q2 * q3 ∣ M k := by
      refine' Nat.Coprime.mul_dvd_of_dvd_of_dvd _ _ _;
      · simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right, Nat.coprime_primes ];
      · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by simpa [ * ] using Nat.coprime_primes hq1 hq2 ) ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hq1.pos, h_range1.2 ⟩ ) ) ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hq2.pos, h_range2.2 ⟩ ) );
      · exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos ], by linarith [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos ] ⟩ );
    have h_divides : Nat.factorization (M k) q1 = 1 ∧ Nat.factorization (M k) q2 = 1 ∧ Nat.factorization (M k) q3 = 1 := by
      have h_divides : Nat.factorization (M k) q1 = Nat.log q1 k ∧ Nat.factorization (M k) q2 = Nat.log q2 k ∧ Nat.factorization (M k) q3 = Nat.log q3 k := by
        have h_log : ∀ p : ℕ, Nat.Prime p → p ≤ k → padicValNat p (M k) = Nat.log p k := by
          intros p hp hp_le_k
          apply padicValNat_lcm_range k p hp (by linarith);
        simp_all +decide [ Nat.factorization ];
      have h_log : Nat.log q1 k = 1 ∧ Nat.log q2 k = 1 ∧ Nat.log q3 k = 1 := by
        exact ⟨ Nat.le_antisymm ( Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow ( by linarith ) ( by nlinarith only [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos, h_range1, hk ] ) ) ) ( Nat.log_pos hq1.one_lt ( by linarith ) ), Nat.le_antisymm ( Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow ( by linarith ) ( by nlinarith only [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos, h_range2, hk ] ) ) ) ( Nat.log_pos hq2.one_lt ( by linarith ) ), Nat.le_antisymm ( Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow ( by linarith ) ( by nlinarith only [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos, h_range3, hk ] ) ) ) ( Nat.log_pos hq3.one_lt ( by linarith ) ) ⟩;
      aesop;
    have h_factorization : Nat.factorization (M_prime3 k q1 q2 q3) q1 = 0 ∧ Nat.factorization (M_prime3 k q1 q2 q3) q2 = 0 ∧ Nat.factorization (M_prime3 k q1 q2 q3) q3 = 0 := by
      unfold M_prime3;
      simp_all +decide [ Nat.factorization_mul, hq1.ne_zero, hq2.ne_zero, hq3.ne_zero ];
    simp_all +decide [ Nat.factorization_eq_zero_iff ];
    have h_pos : 0 < M_prime3 k q1 q2 q3 := by
      exact Nat.div_pos ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ‹q1 * q2 * q3 ∣ M k› ) ( Nat.mul_pos ( Nat.mul_pos hq1.pos hq2.pos ) hq3.pos );
    exact ⟨ Nat.Coprime.symm <| hq1.coprime_iff_not_dvd.mpr <| by aesop, Nat.Coprime.symm <| hq2.coprime_iff_not_dvd.mpr <| by aesop, Nat.Coprime.symm <| hq3.coprime_iff_not_dvd.mpr <| by aesop ⟩

/-
A version of claim_approx for 3 primes.
-/
lemma claim_approx_3 (q1 q2 q3 : ℕ) (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
  (h_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (ε : ℝ) (B1 B2 B3 : Set ℤ)
  (hB1_subset : B1 ⊆ Set.Icc 1 q1) (hB2_subset : B2 ⊆ Set.Icc 1 q2) (hB3_subset : B3 ⊆ Set.Icc 1 q3)
  (hB1_size : B1.ncard ≥ (1 - ε) * q1) (hB2_size : B2.ncard ≥ (1 - ε) * q2) (hB3_size : B3.ncard ≥ (1 - ε) * q3)
  (n : ℕ) (hn : ε * (q1 + q2 + q3) < n) (hn_le1 : n ≤ q1) (hn_le2 : n ≤ q2) (hn_le3 : n ≤ q3) :
  ∀ start : ℤ, ∃ z ∈ Set.Icc start (start + n - 1),
    ∃ c1 ∈ B1, ∃ c2 ∈ B2, ∃ c3 ∈ B3,
    z ≡ c1 [ZMOD q1] ∧ z ≡ c2 [ZMOD q2] ∧ z ≡ c3 [ZMOD q3] := by
      intro start;
      -- By the Chinese Remainder Theorem, there exists a $z$ in the interval $[start, start + n - 1]$ such that $z \equiv c1 \pmod{q1}$, $z \equiv c2 \pmod{q2}$, and $z \equiv c3 \pmod{q3}$ for some $c1 \in B1$, $c2 \in B2$, and $c3 \in B3$.
      obtain ⟨c1, hc1⟩ : ∃ c1 ∈ B1, ∃ c2 ∈ B2, ∃ c3 ∈ B3, ∃ z ∈ Set.Icc start (start + n - 1), z ≡ c1 [ZMOD q1] ∧ z ≡ c2 [ZMOD q2] ∧ z ≡ c3 [ZMOD q3] := by
        by_contra h_contra;
        -- Applying the hypothesis `h_contra` to each element in the interval $[start, start + n - 1]$, we get that for each $z$ in this interval, there exists some $c1 \in B1$, $c2 \in B2$, or $c3 \in B3$ such that $z \not\equiv c1 \pmod{q1}$, $z \not\equiv c2 \pmod{q2}$, or $z \not\equiv c3 \pmod{q3}$.
        have h_count : (Finset.Icc start (start + n - 1)).card ≤ (Finset.filter (fun z => ∀ b ∈ B1, ¬(z ≡ b [ZMOD q1])) (Finset.Icc start (start + n - 1))).card + (Finset.filter (fun z => ∀ b ∈ B2, ¬(z ≡ b [ZMOD q2])) (Finset.Icc start (start + n - 1))).card + (Finset.filter (fun z => ∀ b ∈ B3, ¬(z ≡ b [ZMOD q3])) (Finset.Icc start (start + n - 1))).card := by
          have h_count : ∀ z ∈ Finset.Icc start (start + n - 1), (∀ b ∈ B1, ¬(z ≡ b [ZMOD q1])) ∨ (∀ b ∈ B2, ¬(z ≡ b [ZMOD q2])) ∨ (∀ b ∈ B3, ¬(z ≡ b [ZMOD q3])) := by
            norm_num +zetaDelta at *;
            grind;
          have h_count : Finset.Icc start (start + n - 1) ⊆ Finset.filter (fun z => ∀ b ∈ B1, ¬(z ≡ b [ZMOD q1])) (Finset.Icc start (start + n - 1)) ∪ Finset.filter (fun z => ∀ b ∈ B2, ¬(z ≡ b [ZMOD q2])) (Finset.Icc start (start + n - 1)) ∪ Finset.filter (fun z => ∀ b ∈ B3, ¬(z ≡ b [ZMOD q3])) (Finset.Icc start (start + n - 1)) := by
            intro z hz; specialize h_count z hz; aesop;
          exact le_trans ( Finset.card_le_card h_count ) ( Finset.card_union_le _ _ |> le_trans <| add_le_add_right ( Finset.card_union_le _ _ ) _ );
        -- Applying the hypothesis `h_count` to each element in the interval $[start, start + n - 1]$, we get that for each $z$ in this interval, there exists some $c1 \in B1$, $c2 \in B2$, or $c3 \in B3$ such that $z \not\equiv c1 \pmod{q1}$, $z \not\equiv c2 \pmod{q2}$, or $z \not\equiv c3 \pmod{q3}$.
        have h_card_bound : (Finset.filter (fun z => ∀ b ∈ B1, ¬(z ≡ b [ZMOD q1])) (Finset.Icc start (start + n - 1))).card ≤ ε * q1 ∧ (Finset.filter (fun z => ∀ b ∈ B2, ¬(z ≡ b [ZMOD q2])) (Finset.Icc start (start + n - 1))).card ≤ ε * q2 ∧ (Finset.filter (fun z => ∀ b ∈ B3, ¬(z ≡ b [ZMOD q3])) (Finset.Icc start (start + n - 1))).card ≤ ε * q3 := by
          refine' ⟨ _, _, _ ⟩;
          · convert bad_count_bound q1 hq1.pos B1 ε hB1_subset hB1_size n start ( by linarith ) using 1;
          · convert bad_count_bound q2 hq2.pos B2 ε ( by simpa using hB2_subset ) ( by simpa using hB2_size ) n start ( by linarith ) using 1;
          · convert bad_count_bound q3 hq3.pos B3 ε hB3_subset hB3_size n start ( by linarith ) using 1;
        norm_num at *;
        exact h_count.not_gt <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith;
      grind

/-
The set of u in [1, p] such that u*M + 1 mod p is in B_set_x.
-/
def B_set_x_transformed (k p M_val : ℕ) : Set ℤ :=
  { u ∈ Set.Icc 1 (p : ℤ) | ∃ c ∈ B_set_x k p, u * (M_val : ℤ) + 1 ≡ c [ZMOD p] }

/-
B_set_x_transformed is a subset of {1, ..., p}.
-/
lemma B_set_x_transformed_subset (k p M_val : ℕ) :
  B_set_x_transformed k p M_val ⊆ Set.Icc 1 p := by
    exact fun x hx => hx.1

/-
The cardinality of the transformed set is equal to the cardinality of the original set.
-/
lemma B_set_x_transformed_ncard (k p M_val : ℕ) (hp : p.Prime) (h_coprime : Nat.Coprime M_val p) (hk : k > 0) :
  (B_set_x_transformed k p M_val).ncard = (B_set_x k p).ncard := by
    -- Since $M\_val$ is coprime to $p$, the map $u \mapsto u \cdot M\_val + 1$ is a bijection on the set $\{1, \dots, p\}$ modulo $p$.
    have h_bijection : ∀ (u₁ u₂ : ℤ), 1 ≤ u₁ → u₁ ≤ p → 1 ≤ u₂ → u₂ ≤ p → (u₁ * (M_val : ℤ) + 1) % p = (u₂ * (M_val : ℤ) + 1) % p → u₁ % p = u₂ % p := by
      intro u₁ u₂ hu₁ hu₁' hu₂ hu₂' h; haveI := Fact.mk hp; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff' ] ;
      rw [ ZMod.natCast_eq_zero_iff ] at h ; exact h.resolve_right ( by exact fun h' => by have := Nat.gcd_eq_right h'; aesop );
    -- Therefore, the number of solutions to $u \cdot M_val + 1 \equiv c \pmod p$ with $u \in \{1, \dots, p\}$ is 1 for each $c$.
    have h_solutions : ∀ (c : ℤ), c ∈ B_set_x k p → ∃! (u : ℤ), 1 ≤ u ∧ u ≤ p ∧ (u * (M_val : ℤ) + 1) % p = c % p := by
      intro c hc
      obtain ⟨u, hu⟩ : ∃ u : ℤ, 1 ≤ u ∧ u ≤ p ∧ (u * (M_val : ℤ) + 1) ≡ c [ZMOD p] := by
        have h_exists_u : ∃ u : ℤ, u * (M_val : ℤ) + 1 ≡ c [ZMOD p] := by
          -- Since $M_val$ is coprime to $p$, there exists an integer $u$ such that $u * M_val ≡ c - 1 \pmod{p}$.
          have h_exists_u : ∃ u : ℤ, u * (M_val : ℤ) ≡ c - 1 [ZMOD p] := by
            have h_inv : ∃ u : ℤ, u * (M_val : ℤ) ≡ 1 [ZMOD p] := by
              have := Nat.gcd_eq_gcd_ab M_val p;
              exact ⟨ Nat.gcdA M_val p, Int.modEq_iff_dvd.mpr ⟨ Nat.gcdB M_val p, by linarith ⟩ ⟩
            exact ⟨ h_inv.choose * ( c - 1 ), by convert h_inv.choose_spec.mul_right ( c - 1 ) using 1 <;> ring ⟩;
          exact ⟨ h_exists_u.choose, by convert h_exists_u.choose_spec.add_right 1 using 1; ring ⟩;
        obtain ⟨ u, hu ⟩ := h_exists_u;
        refine' ⟨ u % p + if u % p = 0 then p else 0, _, _, _ ⟩ <;> split_ifs <;> simp_all +decide [ Int.ModEq, Int.emod_nonneg _ ( Nat.cast_ne_zero.mpr hp.ne_zero ) ];
        any_goals linarith [ Int.emod_nonneg u ( Nat.cast_ne_zero.mpr hp.ne_zero ), Int.emod_lt_of_pos u ( Nat.cast_pos.mpr hp.pos ) ];
        · exact lt_of_le_of_ne ( Int.emod_nonneg _ ( Nat.cast_ne_zero.mpr hp.ne_zero ) ) ( Ne.symm ( by aesop ) );
        · rw [ Int.emod_eq_zero_of_dvd ‹_› ];
        · simp_all +decide [ Int.add_emod, Int.mul_emod, Int.emod_eq_zero_of_dvd ];
        · simpa [ Int.add_emod, Int.mul_emod ] using hu;
      refine' ⟨ u, ⟨ hu.1, hu.2.1, hu.2.2 ⟩, fun v hv => _ ⟩;
      have := h_bijection v u hv.1 hv.2.1 hu.1 hu.2.1 ( hv.2.2.trans hu.2.2.symm ) ; simp_all +decide [ Int.emod_eq_emod_iff_emod_sub_eq_zero ] ;
      obtain ⟨ a, ha ⟩ := this; nlinarith [ show a = 0 by nlinarith ] ;
    choose! f hf₁ hf₂ using h_solutions;
    -- Therefore, the set $T$ is exactly the image of $S$ under the bijection $f$.
    have h_image : B_set_x_transformed k p M_val = (fun c => f c) '' B_set_x k p := by
      ext; simp [B_set_x_transformed, hf₁, hf₂];
      constructor;
      · rintro ⟨ ⟨ hx₁, hx₂ ⟩, c, hc₁, hc₂ ⟩ ; exact ⟨ c, hc₁, hf₂ c hc₁ _ ⟨ hx₁, hx₂, hc₂ ⟩ ▸ rfl ⟩;
      · rintro ⟨ c, hc, rfl ⟩ ; specialize hf₁ c hc; aesop;
    rw [ h_image, Set.ncard_image_of_injOn ];
    intros c₁ hc₁ c₂ hc₂ h_eq;
    -- Since $f(c₁) = f(c₂)$, we have $(f(c₁) * M_val + 1) % p = c₁ % p$ and $(f(c₂) * M_val + 1) % p = c₂ % p$. Given that $f(c₁) = f(c₂)$, it follows that $c₁ % p = c₂ % p$.
    have h_mod_eq : c₁ % p = c₂ % p := by
      have := hf₁ c₁ hc₁; have := hf₁ c₂ hc₂; aesop;
    -- Since $c₁$ and $c₂$ are both in the interval $[1, p]$, and their remainders modulo $p$ are equal, they must be the same number.
    have h_eq : c₁ ≤ p ∧ c₂ ≤ p ∧ c₁ ≥ 1 ∧ c₂ ≥ 1 := by
      exact ⟨ by linarith [ Set.mem_Icc.mp ( B_set_x_subset k p hp hk hc₁ ) ], by linarith [ Set.mem_Icc.mp ( B_set_x_subset k p hp hk hc₂ ) ], by linarith [ Set.mem_Icc.mp ( B_set_x_subset k p hp hk hc₁ ) ], by linarith [ Set.mem_Icc.mp ( B_set_x_subset k p hp hk hc₂ ) ] ⟩;
    exact Int.modEq_iff_dvd.mp h_mod_eq.symm |> fun ⟨ x, hx ⟩ => by nlinarith [ show x = 0 by nlinarith ] ;

/-
If a real interval has length greater than N, it contains N consecutive integers.
-/
lemma exists_integer_interval (A B : ℝ) (N : ℕ) (h_len : B - A > N) :
  ∃ s : ℤ, ∀ z : ℤ, z ∈ Set.Icc s (s + N - 1) → (z : ℝ) ∈ Set.Ioo A B := by
    norm_num +zetaDelta at *;
    -- Since the interval $(A, B - N + 1)$ has length greater than 1, it must contain an integer.
    obtain ⟨s, hs⟩ : ∃ s : ℤ, A < s ∧ s < B - N + 1 := by
      exact ⟨ ⌊A⌋ + 1, by push_cast; linarith [ Int.lt_floor_add_one A ], by push_cast; linarith [ Int.floor_le A ] ⟩;
    exact ⟨ s, fun z hz₁ hz₂ => ⟨ by linarith [ show ( z : ℝ ) ≥ s by exact_mod_cast hz₁ ], by linarith [ show ( z : ℝ ) ≤ s + N - 1 by exact_mod_cast hz₂ ] ⟩ ⟩

/-
If z satisfies the modular conditions for q1, q2, q3, then x = z*M' + 1 is a good x.
-/
lemma good_x_of_z (k : ℕ) (z : ℕ) (q1 q2 q3 : ℕ)
  (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
  (h_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (h_range1 : k.sqrt < q1 ∧ q1 ≤ k)
  (h_range2 : k.sqrt < q2 ∧ q2 ≤ k)
  (h_range3 : k.sqrt < q3 ∧ q3 ≤ k)
  (h_z_mod1 : ((z * M_prime3 k q1 q2 q3 + 1) % q1 : ℤ) ∈ B_set_x k q1)
  (h_z_mod2 : ((z * M_prime3 k q1 q2 q3 + 1) % q2 : ℤ) ∈ B_set_x k q2)
  (h_z_mod3 : ((z * M_prime3 k q1 q2 q3 + 1) % q3 : ℤ) ∈ B_set_x k q3)
  : good_x k (z * M_prime3 k q1 q2 q3 + 1) := by
    exists Nat.succ_pos _;
    constructor;
    · -- Since $m(k) \mid M_prime3(k, q1, q2, q3)$, we have $(z * M_prime3 + 1) \equiv 1 \pmod{m(k)}$.
      have h_mod_m : (z * M_prime3 k q1 q2 q3 + 1) % (m k) = 1 % (m k) := by
        rw [ Nat.add_mod, Nat.mul_mod ];
        rw [ Nat.mod_eq_zero_of_dvd ( m_dvd_M_prime3 k q1 q2 q3 hq1 hq2 hq3 h_distinct h_range1 h_range2 h_range3 ) ] ; norm_num;
      rw [ h_mod_m, Nat.mod_eq_of_lt ];
      rcases k with ( _ | _ | k ) <;> simp_all +decide [ m ];
      · linarith;
      · refine' lt_of_lt_of_le _ ( Finset.prod_le_prod' fun p hp => Nat.le_self_pow _ _ );
        · refine' lt_of_lt_of_le _ ( Finset.prod_le_prod_of_subset_of_one_le' ( show Finset.filter ( fun p => Nat.Prime p ∧ p * p ≤ k + 1 + 1 ) ( Finset.Icc 1 ( k + 1 + 1 ) ) ≥ { 2 } from _ ) fun _ _ _ => Nat.Prime.pos <| by aesop ) <;> norm_num;
          rcases k with ( _ | _ | k ) <;> simp_all +arith +decide;
          · grind +ring;
          · rcases h_range1 with ⟨ _, _ ⟩ ; rcases h_range2 with ⟨ _, _ ⟩ ; rcases h_range3 with ⟨ _, _ ⟩ ; interval_cases q1 <;> interval_cases q2 <;> interval_cases q3 <;> trivial;
        · simp_all +decide [ Nat.factorization_eq_zero_iff ];
          exact ⟨ Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by nlinarith only [ hp.1.1, hp.2.2 ], by nlinarith only [ hp.1.2, hp.2.2 ] ⟩ ), Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop ⟩;
    · intro p hp h1 h2;
      by_cases hpq : p = q1 ∨ p = q2 ∨ p = q3;
      · rcases hpq with ( rfl | rfl | rfl ) <;> simp_all +decide [ B_set_x ];
        · exact ⟨ mod_cast h_z_mod1.1, Nat.le_sub_of_add_le <| by linarith [ Nat.mod_lt k hq1.pos, Nat.mod_lt ( z * M_prime3 k p q2 q3 + 1 ) hq1.pos ] ⟩;
        · exact ⟨ by linarith, Nat.le_sub_of_add_le <| by linarith [ Nat.mod_lt k hq2.pos, Nat.mod_lt ( z * M_prime3 k q1 p q3 + 1 ) hq2.pos ] ⟩;
        · norm_cast at *;
          rw [ Int.subNatNat_of_le ] at h_z_mod3 <;> norm_cast at * ; linarith [ Nat.mod_lt k hq3.pos ];
      · -- Since $p \neq q1$, $p \neq q2$, and $p \neq q3$, we have $p \mid M_prime3 k q1 q2 q3$.
        have hp_div_M_prime3 : p ∣ M_prime3 k q1 q2 q3 := by
          refine' Nat.dvd_div_of_mul_dvd _;
          apply_mod_cast Nat.Coprime.mul_dvd_of_dvd_of_dvd;
          · simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right, Nat.coprime_primes ];
            tauto;
          · apply_mod_cast Nat.Coprime.mul_dvd_of_dvd_of_dvd;
            · rw [ Nat.coprime_mul_iff_left ];
              exact ⟨ by have := Nat.coprime_primes hq1 hq3; tauto, by have := Nat.coprime_primes hq2 hq3; tauto ⟩;
            · apply_mod_cast Nat.Coprime.mul_dvd_of_dvd_of_dvd;
              · simpa [ * ] using Nat.coprime_primes hq1 hq2;
              · exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ );
              · exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ );
            · exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ );
          · exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hp.pos, h2 ⟩ );
        norm_num [ Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hp_div_M_prime3 ];
        norm_num [ Nat.mod_eq_of_lt hp.one_lt ];
        exact Nat.sub_pos_of_lt ( Nat.mod_lt _ hp.pos )

/-
The epsilon condition is satisfied for primes in the given range.
-/
lemma epsilon_sum_lt_min_corrected (C : ℝ) (hC : C ≥ 1) (k : ℕ) (q1 q2 q3 : ℕ)
  (h_range1_lo : (1 - 1 / (20 * C)) * k < q1) (h_range1_hi : q1 < k)
  (h_range2_lo : (1 - 1 / (20 * C)) * k < q2) (h_range2_hi : q2 < k)
  (h_range3_lo : (1 - 1 / (20 * C)) * k < q3) (h_range3_hi : q3 < k)
  (hk : k > 0) :
  1 / (20 * C) * (q1 + q2 + q3) < min q1 (min q2 q3) := by
    -- Since $q1$, $q2$, and $q3$ are all less than $k$ and greater than $(1 - 1/(20C))k$, we can bound their sum.
    have h_sum_bound : (q1 + q2 + q3 : ℝ) < 3 * k := by
      norm_cast; linarith;
    cases min_cases ( q1 : ℝ ) ( min ( q2 : ℝ ) ( q3 : ℝ ) ) <;> cases min_cases ( q2 : ℝ ) ( q3 : ℝ ) <;> simp_all +decide;
    · nlinarith [ ( by norm_cast : ( q1 : ℝ ) ≤ q2 ), ( by norm_cast : ( q2 : ℝ ) ≤ q3 ), mul_inv_cancel₀ ( by positivity : ( C : ℝ ) ≠ 0 ) ];
    · nlinarith [ inv_mul_cancel₀ ( by linarith : C ≠ 0 ), ( by norm_cast : ( q1 : ℝ ) ≤ q3 ), ( by norm_cast : ( q3 : ℝ ) ≤ q2 ∧ ( q3 : ℝ ) < q2 ) ];
    · nlinarith [ ( by norm_cast : ( q2 : ℝ ) ≤ q1 ∧ ( q2 : ℝ ) < q1 ), ( by norm_cast : ( q2 : ℝ ) ≤ q3 ), inv_mul_cancel₀ ( by positivity : ( C : ℝ ) ≠ 0 ) ];
    · nlinarith [ inv_mul_cancel₀ ( by linarith : C ≠ 0 ) ]

/-
If a real interval is large enough, it contains an integer satisfying the modular conditions for 3 primes.
-/
lemma exists_z_in_real_interval (q1 q2 q3 : ℕ) (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
  (h_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (ε : ℝ) (B1 B2 B3 : Set ℤ)
  (hB1_subset : B1 ⊆ Set.Icc 1 q1) (hB2_subset : B2 ⊆ Set.Icc 1 q2) (hB3_subset : B3 ⊆ Set.Icc 1 q3)
  (hB1_size : B1.ncard ≥ (1 - ε) * q1) (hB2_size : B2.ncard ≥ (1 - ε) * q2) (hB3_size : B3.ncard ≥ (1 - ε) * q3)
  (h_eps_cond : ε * (q1 + q2 + q3) < min q1 (min q2 q3))
  (A B : ℝ) (h_len : B - A > q1 + q2 + q3) :
  ∃ z : ℤ, (z : ℝ) ∈ Set.Ioo A B ∧
    (∃ c1 ∈ B1, z ≡ c1 [ZMOD q1]) ∧
    (∃ c2 ∈ B2, z ≡ c2 [ZMOD q2]) ∧
    (∃ c3 ∈ B3, z ≡ c3 [ZMOD q3]) := by
      have := exists_integer_interval A B ( Min.min q1 ( Min.min q2 q3 ) ) ?_;
      · obtain ⟨ s, hs ⟩ := this;
        refine' Exists.elim ( claim_approx_3 q1 q2 q3 hq1 hq2 hq3 h_distinct ε B1 B2 B3 hB1_subset hB2_subset hB3_subset hB1_size hB2_size hB3_size ( Min.min q1 ( Min.min q2 q3 ) ) _ _ _ _ _ ) _;
        any_goals tauto;
        · exact min_le_left _ _;
        · exact le_trans ( min_le_right _ _ ) ( min_le_left _ _ );
        · exact min_le_right _ _ |> le_trans <| min_le_right _ _;
      · exact lt_of_le_of_lt ( mod_cast by simp +decide [ min_le_iff ] ) h_len

/-
Forward direction of the equivalence between modular condition and set membership.
-/
lemma mod_in_B_set_x_of_exists (k p M_val : ℕ) (z : ℤ)
  (hp : p.Prime) (hk : k > 0) (h_range : k / 2 < p ∧ p < k)
  (h_coprime : Nat.Coprime M_val p)
  (h : ∃ u ∈ B_set_x_transformed k p M_val, z ≡ u [ZMOD p]) :
  ((z * (M_val : ℤ) + 1) % p : ℤ) ∈ B_set_x k p := by
    rcases h with ⟨ u, ⟨ hu_mod_p, c, hc₁, hc₂ ⟩, hu_z ⟩;
    -- Since $z \equiv u \pmod p$, we have $z * M_val + 1 \equiv u * M_val + 1 \equiv c \pmod p$.
    have h_cong : (z * M_val + 1) % p = c % p := by
      exact Eq.trans ( Int.ModEq.add ( Int.ModEq.mul_right _ hu_z ) rfl ) hc₂;
    -- Since $p$ is prime and $k \leq p$, we have $2p - k < p$, thus $1 \leq c < p$.
    have h_c_lt_p : 1 ≤ c ∧ c < p := by
      exact ⟨ by linarith [ Set.mem_Icc.mp hc₁ ], by linarith [ Set.mem_Icc.mp hc₁, show ( k % p : ℕ ) > 0 from Nat.pos_of_ne_zero fun h => by have := Nat.dvd_of_mod_eq_zero h; exact absurd ( Nat.dvd_trans ( dvd_refl _ ) this ) ( by rintro ⟨ q, hq ⟩ ; nlinarith [ show q = 1 by nlinarith [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos ] ] ) ] ⟩;
    simp_all +decide [ B_set_x ];
    exact ⟨ by rw [ Int.emod_eq_of_lt ] <;> linarith, by rw [ Int.emod_eq_of_lt ] <;> linarith ⟩

/-
Existence of z in the transformed interval satisfying modular conditions.
-/
lemma exists_z_in_z_interval (C : ℝ) (hC : C ≥ 1) (k : ℕ) (y : ℕ) (q1 q2 q3 : ℕ)
  (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
  (h_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (h_range1_lo : (1 - 1 / (20 * C)) * k < q1) (h_range1_hi : q1 < k)
  (h_range2_lo : (1 - 1 / (20 * C)) * k < q2) (h_range2_hi : q2 < k)
  (h_range3_lo : (1 - 1 / (20 * C)) * k < q3) (h_range3_hi : q3 < k)
  (h_len : x_interval_length k C / (M_prime3 k q1 q2 q3 : ℝ) > q1 + q2 + q3)
  (h_M_prime3_coprime : Nat.Coprime (M_prime3 k q1 q2 q3) q1 ∧ Nat.Coprime (M_prime3 k q1 q2 q3) q2 ∧ Nat.Coprime (M_prime3 k q1 q2 q3) q3)
  (h_B_density : (B_set_x k q1).ncard ≥ (1 - 1 / (20 * C)) * q1 ∧ (B_set_x k q2).ncard ≥ (1 - 1 / (20 * C)) * q2 ∧ (B_set_x k q3).ncard ≥ (1 - 1 / (20 * C)) * q3)
  (hk : k > 0) :
  let M' := M_prime3 k q1 q2 q3
  let L := x_interval_length k C
  let A := ((y : ℝ) - L - 1) / M'
  let B := ((y : ℝ) - 1) / M'
  ∃ z : ℤ, (z : ℝ) ∈ Set.Ioo A B ∧
    ((z * M' + 1) % q1 : ℤ) ∈ B_set_x k q1 ∧
    ((z * M' + 1) % q2 : ℤ) ∈ B_set_x k q2 ∧
    ((z * M' + 1) % q3 : ℤ) ∈ B_set_x k q3 := by
      have h_eps_cond : 1 / (20 * C) * (q1 + q2 + q3) < min q1 (min q2 q3) := by
        apply_rules [ epsilon_sum_lt_min_corrected ];
      have h_exists_z : ∃ z : ℤ, (z : ℝ) ∈ Set.Ioo ((y - x_interval_length k C - 1) / (M_prime3 k q1 q2 q3 : ℝ)) ((y - 1) / (M_prime3 k q1 q2 q3 : ℝ)) ∧
        (∃ c1 ∈ B_set_x_transformed k q1 (M_prime3 k q1 q2 q3), z ≡ c1 [ZMOD q1]) ∧
        (∃ c2 ∈ B_set_x_transformed k q2 (M_prime3 k q1 q2 q3), z ≡ c2 [ZMOD q2]) ∧
        (∃ c3 ∈ B_set_x_transformed k q3 (M_prime3 k q1 q2 q3), z ≡ c3 [ZMOD q3]) := by
          apply exists_z_in_real_interval;
          all_goals try assumption;
          any_goals exact B_set_x_transformed_subset _ _ _;
          · rw [ B_set_x_transformed_ncard ];
            · exact h_B_density.1;
            · assumption;
            · exact h_M_prime3_coprime.1;
            · grind;
          · rw [ B_set_x_transformed_ncard ] <;> aesop;
          · rw [ B_set_x_transformed_ncard ] <;> aesop;
          · ring_nf at *; linarith;
      obtain ⟨ z, hz₁, hz₂, hz₃, hz₄ ⟩ := h_exists_z;
      refine' ⟨ z, hz₁, _, _, _ ⟩ <;> simp_all +decide [ Int.ModEq ];
      · convert mod_in_B_set_x_of_exists k q1 ( M_prime3 k q1 q2 q3 ) z hq1 hk ⟨ _, _ ⟩ _ _ using 1;
        · exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ inv_mul_cancel₀ ( by positivity : ( C : ℝ ) ≠ 0 ) ] ;
        · linarith;
        · exact h_M_prime3_coprime.1;
        · exact ⟨ _, hz₂.choose_spec.1, hz₂.choose_spec.2 ⟩;
      · obtain ⟨ c2, hc2₁, hc2₂ ⟩ := hz₃;
        have := mod_in_B_set_x_of_exists k q2 ( M_prime3 k q1 q2 q3 ) z hq2 hk ⟨ by
          exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ inv_mul_cancel₀ ( by positivity : ( C : ℝ ) ≠ 0 ) ] ;, by
          linarith ⟩ ?_ ?_ <;> aesop;
      · convert mod_in_B_set_x_of_exists k q3 ( M_prime3 k q1 q2 q3 ) z hq3 hk ⟨ by
          rw [ Nat.div_lt_iff_lt_mul ] <;> norm_num at *;
          exact_mod_cast ( by nlinarith [ inv_mul_cancel₀ ( by positivity : ( C : ℝ ) ≠ 0 ) ] : ( k : ℝ ) < q3 * 2 ), by
          exact h_range3_hi ⟩ ( by
          exact h_M_prime3_coprime.2.2 ) _ using 1
        generalize_proofs at *;
        exact ⟨ _, hz₄.choose_spec.1, hz₄.choose_spec.2 ⟩

/-
Existence of a good x in the interval.
-/
lemma exists_x_if_large_interval (C : ℝ) (hC : C ≥ 1) (k : ℕ) (y : ℕ) (q1 q2 q3 : ℕ)
  (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
  (h_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (h_range1 : (1 - 1 / (20 * C)) * k < q1 ∧ q1 < k)
  (h_range2 : (1 - 1 / (20 * C)) * k < q2 ∧ q2 < k)
  (h_range3 : (1 - 1 / (20 * C)) * k < q3 ∧ q3 < k)
  (h_len : x_interval_length k C / (M_prime3 k q1 q2 q3 : ℝ) > q1 + q2 + q3)
  (h_M_prime3_coprime : Nat.Coprime (M_prime3 k q1 q2 q3) q1 ∧ Nat.Coprime (M_prime3 k q1 q2 q3) q2 ∧ Nat.Coprime (M_prime3 k q1 q2 q3) q3)
  (h_B_density : (B_set_x k q1).ncard ≥ (1 - 1 / (20 * C)) * q1 ∧ (B_set_x k q2).ncard ≥ (1 - 1 / (20 * C)) * q2 ∧ (B_set_x k q3).ncard ≥ (1 - 1 / (20 * C)) * q3)
  (h_eps_small : 1 / (20 * C) * (q1 + q2 + q3) < q1)
  (hy_large : (y : ℝ) > x_interval_length k C) :
  ∃ x : ℕ, (x : ℝ) ∈ x_interval k y C ∧ good_x k x := by
    -- Apply `exists_z_in_z_interval` to find an integer `z` that satisfies the modular conditions.
    obtain ⟨z, hz_mem, hz_mod⟩ : ∃ z : ℤ, (z : ℝ) ∈ Set.Ioo ((y - x_interval_length k C - 1) / (M_prime3 k q1 q2 q3 : ℝ)) ((y - 1) / (M_prime3 k q1 q2 q3 : ℝ)) ∧
      ((z * M_prime3 k q1 q2 q3 + 1) % q1 : ℤ) ∈ B_set_x k q1 ∧
      ((z * M_prime3 k q1 q2 q3 + 1) % q2 : ℤ) ∈ B_set_x k q2 ∧
      ((z * M_prime3 k q1 q2 q3 + 1) % q3 : ℤ) ∈ B_set_x k q3 := by
        apply exists_z_in_z_interval C hC k y q1 q2 q3 hq1 hq2 hq3 h_distinct h_range1.left h_range1.right h_range2.left h_range2.right h_range3.left h_range3.right h_len h_M_prime3_coprime h_B_density (by linarith);
    refine' ⟨ Int.toNat ( z * M_prime3 k q1 q2 q3 + 1 ), _, _ ⟩;
    · rcases z with ( _ | z ) <;> norm_num at *;
      · rw [ lt_div_iff₀ ] at * <;> norm_num at *;
        · constructor;
          · rw [ div_lt_iff₀ ] at hz_mem <;> norm_num [ x_interval_length ] at *;
            · norm_cast at *;
              rw [ Int.subNatNat_eq_coe ] at hz_mem ; push_cast at * ; linarith;
            · grind;
          · norm_cast at *;
            rw [ Int.subNatNat_eq_coe ] at hz_mem ; push_cast at * ; linarith;
        · grind;
        · exact Nat.pos_of_ne_zero ( by aesop_cat );
      · contrapose! hz_mem;
        intro h; rw [ div_add', div_lt_iff₀ ] at * <;> norm_num at *;
        · nlinarith [ show ( M_prime3 k q1 q2 q3 : ℝ ) ≥ 1 by exact_mod_cast Nat.one_le_iff_ne_zero.mpr <| by aesop_cat ];
        · exact Nat.pos_of_ne_zero ( by aesop_cat );
        · aesop;
        · aesop;
    · -- Since $q1$, $q2$, and $q3$ are greater than $\sqrt{k}$, we have $k.sqrt < q1$, $k.sqrt < q2$, and $k.sqrt < q3$.
      have h_sqrt_lt_q : k.sqrt < q1 ∧ k.sqrt < q2 ∧ k.sqrt < q3 := by
        have h_sqrt_lt_q : ∀ q : ℕ, Nat.Prime q → (1 - 1 / (20 * C)) * k < q → q < k → k.sqrt < q := by
          intros q hq hq_range hq_lt_k
          have h_sqrt_lt_q : (k : ℝ) / 2 < q := by
            nlinarith [ show ( q : ℝ ) ≥ 2 by exact_mod_cast hq.two_le, show ( k : ℝ ) ≥ q + 1 by exact_mod_cast hq_lt_k, one_div_mul_cancel ( by positivity : ( 20 * C : ℝ ) ≠ 0 ) ];
          rw [ div_lt_iff₀ ] at h_sqrt_lt_q <;> norm_cast at *;
          exact Nat.sqrt_lt.mpr ( by nlinarith only [ h_sqrt_lt_q, hq.two_le ] );
        exact ⟨ h_sqrt_lt_q q1 hq1 h_range1.1 h_range1.2, h_sqrt_lt_q q2 hq2 h_range2.1 h_range2.2, h_sqrt_lt_q q3 hq3 h_range3.1 h_range3.2 ⟩;
      convert good_x_of_z k ( Int.toNat z ) q1 q2 q3 hq1 hq2 hq3 h_distinct ⟨ h_sqrt_lt_q.1, by linarith ⟩ ⟨ h_sqrt_lt_q.2.1, by linarith ⟩ ⟨ h_sqrt_lt_q.2.2, by linarith ⟩ _ _ _;
      · rcases z with ( _ | z ) <;> norm_num at *;
        · norm_cast;
        · rw [ div_add', div_lt_iff₀ ] at hz_mem <;> norm_num at *;
          · nlinarith [ show ( M_prime3 k q1 q2 q3 : ℝ ) ≥ 1 by exact_mod_cast Nat.one_le_iff_ne_zero.mpr <| Nat.ne_of_gt <| M_prime3_pos k q1 q2 q3 ( by linarith ) hq1 hq2 hq3 h_distinct ( by linarith ) ( by linarith ) ( by linarith ) ];
          · exact Nat.pos_of_ne_zero ( by aesop_cat );
          · aesop;
      · convert hz_mod.1 using 1;
        rw [ Int.toNat_of_nonneg ];
        contrapose! hz_mem;
        refine' fun h => _;
        rw [ Set.mem_Ioo ] at h;
        rw [ div_lt_iff₀ ] at h;
        · nlinarith [ show ( z : ℝ ) ≤ -1 by exact_mod_cast Int.le_of_lt_add_one hz_mem, show ( M_prime3 k q1 q2 q3 : ℝ ) ≥ 1 by exact_mod_cast Nat.one_le_iff_ne_zero.mpr <| Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by aesop_cat ];
        · exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop_cat ) );
      · convert hz_mod.2.1 using 1;
        rw [ Int.toNat_of_nonneg ];
        contrapose! hz_mem;
        refine' fun h => _;
        rw [ Set.mem_Ioo ] at h;
        rw [ div_lt_iff₀ ] at h;
        · nlinarith [ show ( z : ℝ ) ≤ -1 by exact_mod_cast Int.le_of_lt_add_one hz_mem, show ( M_prime3 k q1 q2 q3 : ℝ ) ≥ 1 by exact_mod_cast Nat.one_le_iff_ne_zero.mpr <| Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by aesop_cat ];
        · exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop_cat ) );
      · convert hz_mod.2.2 using 1;
        rw [ Int.toNat_of_nonneg ];
        contrapose! hz_mem;
        refine' fun h => _;
        rw [ Set.mem_Ioo ] at h;
        rw [ div_lt_iff₀ ] at h;
        · nlinarith [ show ( z : ℝ ) ≤ -1 by exact_mod_cast Int.le_of_lt_add_one hz_mem, show ( M_prime3 k q1 q2 q3 : ℝ ) ≥ 1 by exact_mod_cast Nat.one_le_iff_ne_zero.mpr <| Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by aesop_cat ];
        · exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop_cat ) )

/-
The ratio of y_interval_length to M(k) tends to 1/(20C).
-/
lemma y_len_div_M_limit (C : ℝ) (hC : C ≥ 1) :
  Filter.Tendsto (fun k => y_interval_length k C / M k) Filter.atTop (nhds (1 / (20 * C))) := by
    -- As $k \to \infty$, $k/M k \to 0$ because $M k$ grows exponentially.
    have h_k_div_M_k_zero : Filter.Tendsto (fun k : ℕ => (k : ℝ) / (M k)) Filter.atTop (nhds 0) := by
      -- By definition of $M$, we know that $M(k) \geq k$ for all $k \geq 1$.
      have h_M_ge_k : ∀ k ≥ 1, (M k : ℝ) ≥ k := by
        exact fun k hk => mod_cast Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by unfold M; exact mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ( Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hk, le_rfl ⟩ ) );
      -- Since $M(k)$ is the LCM of $1, 2, \ldots, k$, it is divisible by $k$ and $k-1$ for $k \geq 2$. Therefore, $M(k) \geq k(k-1)$.
      have h_M_ge_k_k_minus_1 : ∀ k ≥ 2, (M k : ℝ) ≥ k * (k - 1) := by
        intros k hk_ge_2
        have h_M_ge_k_k_minus_1 : (M k : ℕ) ≥ k * (k - 1) := by
          have h_M_ge_k_k_minus_1 : k * (k - 1) ∣ M k := by
            have h_M_ge_k_k_minus_1 : k ∣ M k ∧ (k - 1) ∣ M k := by
              exact ⟨ Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩ ), Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.le_sub_one_of_lt ( by linarith ), Nat.sub_le_of_le_add ( by linarith ) ⟩ ) ⟩;
            exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( by cases k <;> simp_all +decide [ Nat.succ_eq_add_one ] ) h_M_ge_k_k_minus_1.1 h_M_ge_k_k_minus_1.2;
          exact Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by specialize h_M_ge_k k ( by linarith ) ; aesop ) ) h_M_ge_k_k_minus_1;
        cases k <;> norm_num at * ; norm_cast;
      refine' squeeze_zero_norm' _ _;
      use fun n => 1 / ( n - 1 );
      · filter_upwards [ Filter.eventually_ge_atTop 2 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ div_le_div_iff₀ ] <;> nlinarith [ h_M_ge_k_k_minus_1 n hn, show ( n : ℝ ) ≥ 2 by norm_cast ] ;
      · exact tendsto_const_nhds.div_atTop ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop );
    -- The remaining terms are constants, so their limits are straightforward.
    have h_const_terms : Filter.Tendsto (fun k : ℕ => (M k : ℝ) / (4 * C) / (M k) - (M k : ℝ) / (5 * C) / (M k) - (M k : ℝ) / (5 * C * k) / (M k)) Filter.atTop (nhds ((1 / (4 * C)) - (1 / (5 * C)) - 0)) := by
      have h_const_terms : Filter.Tendsto (fun k : ℕ => (1 / (4 * C)) - (1 / (5 * C)) - (1 / (5 * C * k))) Filter.atTop (nhds ((1 / (4 * C)) - (1 / (5 * C)) - 0)) := by
        exact tendsto_const_nhds.sub ( tendsto_const_nhds.div_atTop <| Filter.Tendsto.const_mul_atTop ( by positivity ) <| tendsto_natCast_atTop_atTop );
      refine h_const_terms.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop 1 ] with k hk₁ hk₂; simp [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( show 0 < M k from Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ] );
    convert h_const_terms.sub h_k_div_M_k_zero using 2 <;> ring_nf;
    unfold y_interval_length; ring;

/-
Arithmetic check for x interval length.
-/
lemma interval_length_check_x_arithmetic (C : ℝ) (hC : C ≥ 1) :
  ∃ K, ∀ k ≥ K, ∀ q1 q2 q3 : ℝ, k / 2 < q1 → q1 ≤ k → k / 2 < q2 → q2 ≤ k → k / 2 < q3 → q3 ≤ k →
  (q1 * q2 * q3) / (5 * C * k) > q1 + q2 + q3 := by
    use 160 * C + 1;
    intro k hk q1 q2 q3 hq1 hq1' hq2 hq2' hq3 hq3';
    rw [ gt_iff_lt, lt_div_iff₀ ] <;> nlinarith [ mul_le_mul_of_nonneg_left hC ( by linarith : 0 ≤ k ), mul_le_mul_of_nonneg_left hC ( by linarith : 0 ≤ q1 ), mul_le_mul_of_nonneg_left hC ( by linarith : 0 ≤ q2 ), mul_le_mul_of_nonneg_left hC ( by linarith : 0 ≤ q3 ), mul_pos ( by linarith : 0 < q1 ) ( by linarith : 0 < q2 ), mul_pos ( by linarith : 0 < q1 ) ( by linarith : 0 < q3 ), mul_pos ( by linarith : 0 < q2 ) ( by linarith : 0 < q3 ) ]

/-
Lower bound for y interval length ratio.
-/
lemma y_len_div_M_lower_bound (C : ℝ) (hC : C ≥ 1) :
  ∃ K, ∀ k ≥ K, y_interval_length k C / M k > 1 / (40 * C) := by
    have := y_len_div_M_limit C hC |> fun h => h.eventually ( lt_mem_nhds <| show 1 / ( 20 * C ) > 1 / ( 40 * C ) by gcongr ; linarith ) ; aesop

/-
Stronger asymptotic check for y interval length.
-/
lemma interval_length_check_y_strong (C : ℝ) (hC : C ≥ 1) :
  ∃ K, ∀ k ≥ K, y_interval_length k C / ((M k : ℝ) / (k * k / 4)) > 2 * k := by
    -- Using the result from y_len_div_M_lower_bound, we can find such a K.
    obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ k ≥ K, y_interval_length k C / M k > 1 / (40 * C) := by
      apply y_len_div_M_lower_bound C hC;
    -- We need to find K such that for all k ≥ K, (k * k / 4) * (1 / (40 * C)) > 2 * k.
    have h_arith : ∃ K : ℕ, ∀ k ≥ K, (k * k / 4 : ℝ) * (1 / (40 * C)) > 2 * k := by
      exact ⟨ ⌈2 * 40 * C * 4⌉₊ + 1, fun k hk => by nlinarith [ Nat.le_ceil ( 2 * 40 * C * 4 ), show ( k : ℝ ) ≥ ⌈2 * 40 * C * 4⌉₊ + 1 by exact_mod_cast hk, show ( 0 : ℝ ) ≤ 40 * C by positivity, mul_div_cancel₀ ( 1 : ℝ ) ( by positivity : ( 40 * C ) ≠ 0 ) ] ⟩;
    obtain ⟨ K', hK' ⟩ := h_arith; use Max.max K K'; intro k hk; specialize hK k ( le_trans ( le_max_left _ _ ) hk ) ; specialize hK' k ( le_trans ( le_max_right _ _ ) hk ) ; simp_all +decide [ div_eq_mul_inv ] ;
    nlinarith [ show ( 0 : ℝ ) ≤ k * k * 4⁻¹ by positivity ]

/-
m(k) grows faster than k.
-/
lemma m_gt_k (k : ℕ) : ∃ K, ∀ k ≥ K, m k > k + 1 := by
  -- Since $\sqrt{k}$ grows faster than $k$, we can find a $K$ such that for all $k \geq K$, $\sqrt{k} > k + 1$.
  use 16; intros k hk; (
  -- We'll use that $m(k)$ is the product of $p^{\lfloor \log_p k \rfloor}$ for $p \leq \sqrt{k}$.
  have h_m_prod : m k = ∏ p ∈ Finset.filter (fun p => p.Prime ∧ p * p ≤ k) (Finset.Icc 1 k), p ^ (Nat.log p k) := by
    refine' Finset.prod_congr rfl fun p hp => _;
    -- Since $p$ is a prime and $p \leq \sqrt{k}$, the highest power of $p$ that divides $M(k)$ is $p^{\log_p k}$.
    have h_factorization : Nat.factorization (M k) p = Nat.log p k := by
      convert padicValNat_lcm_range k p _ _ using 1;
      · rw [ Nat.factorization_def ] ; aesop;
      · aesop;
      · linarith;
    exact h_factorization ▸ rfl;
  -- Since $k \geq 16$, we have $\sqrt{k} \geq 4$. Therefore, $m(k)$ includes at least the primes $2$ and $3$ raised to their respective powers.
  have h_prime_factors : 2 ^ (Nat.log 2 k) * 3 ^ (Nat.log 3 k) ≤ m k := by
    rw [ h_m_prod, ← Finset.prod_sdiff <| show { 2, 3 } ⊆ Finset.filter ( fun p => Nat.Prime p ∧ p * p ≤ k ) ( Finset.Icc 1 k ) from ?_ ];
    · simp +zetaDelta at *;
      exact Finset.prod_pos fun x hx => pow_pos ( Nat.Prime.pos ( by aesop ) ) _;
    · exact Finset.insert_subset_iff.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by norm_num, by linarith ⟩, by norm_num, by linarith ⟩, Finset.singleton_subset_iff.mpr <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ by norm_num, by linarith ⟩, by norm_num, by linarith ⟩ ⟩;
  rcases k with ( _ | _ | _ | _ | _ | _ | _ | _ | _ | k ) <;> simp +arith +decide [ Nat.pow_succ' ] at *;
  have := Nat.lt_pow_succ_log_self ( by decide : 1 < 2 ) ( k + 9 ) ; ( have := Nat.lt_pow_succ_log_self ( by decide : 1 < 3 ) ( k + 9 ) ; ( norm_num [ Nat.pow_succ' ] at * ; nlinarith; ) ))

/-
Difference between good y and good x is at least m(k) - 1.
-/
lemma good_xy_diff (k x y : ℕ) (hx : good_x k x) (hy : good_y k y) (hxy : x < y) : y - x ≥ m k - 1 := by
  -- From good_x, we have x ≡ 1 [MOD m k].
  have hx_mod : x ≡ 1 [MOD m k] := by
    obtain ⟨hx0, hxmod, hx_res⟩ := hx;
    rw [ ← hxmod, Nat.ModEq, Nat.mod_mod ]

  -- From good_y, we have y ≡ 0 [MOD m k].
  have hy_mod : y ≡ 0 [MOD m k] := by
    cases hy ; aesop;
  rw [ Nat.modEq_zero_iff_dvd ] at hy_mod; obtain ⟨ c, hc ⟩ := hy_mod; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
  -- Since $x \equiv 1 \pmod{m k}$, we can write $x = m k * q + 1$ for some integer $q$.
  obtain ⟨ q, hq ⟩ : ∃ q, x = m k * q + 1 := by
    rw [ ← Nat.div_add_mod x ( m k ), hx_mod ];
    rcases hk : m k with ( _ | _ | m ) <;> simp_all +decide [ Nat.mod_eq_of_lt ];
    cases hx ; aesop;
  rw [ tsub_add_eq_add_tsub ( by nlinarith ), le_tsub_iff_left ] <;> nlinarith [ show c > q by nlinarith [ show m k > 0 from Nat.pos_of_ne_zero ( by intro t; simp_all +decide [ good_x ] ) ] ]

/-
L(a, b) is the LCM of integers in [a, b].
-/
def L (a b : ℕ) : ℕ := (Finset.Icc a b).lcm id

/-
lcm_real(s) is the LCM of elements in s, cast to Real.
-/
def lcm_real (s : Finset ℕ) : ℝ := (s.lcm id : ℕ)

/-
The statement of the main theorem.
-/
def MainTheoremStatement : Prop :=
  ∀ C : ℝ, C ≥ 1 →
  ∃ K, ∀ k ≥ K, ∃ x y : ℕ,
    0 < x ∧ x < y ∧ y > x + k ∧
    lcm_real (Finset.Icc x (x + k - 1)) > C * lcm_real (Finset.Icc y (y + k))

/-
Structure GoodPrimes.
-/
structure GoodPrimes (C : ℝ) (k : ℕ) where
  p1 : ℕ
  p2 : ℕ
  q1 : ℕ
  q2 : ℕ
  q3 : ℕ
  hp1 : p1.Prime
  hp2 : p2.Prime
  hq1 : q1.Prime
  hq2 : q2.Prime
  hq3 : q3.Prime
  hp_lt : p1 < p2
  hq_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3
  h_range_p1 : (k : ℝ) / 2 < p1 ∧ p1 ≤ k
  h_range_p2 : (k : ℝ) / 2 < p2 ∧ p2 ≤ k
  h_range_q1 : (1 - 1 / (20 * C)) * k < q1 ∧ (q1 : ℝ) < k
  h_range_q2 : (1 - 1 / (20 * C)) * k < q2 ∧ (q2 : ℝ) < k
  h_range_q3 : (1 - 1 / (20 * C)) * k < q3 ∧ (q3 : ℝ) < k

lemma epsilon_condition_y (C : ℝ) (hC : C ≥ 1) (k : ℕ) (p1 p2 : ℕ)
  (hp1_lo : (k : ℝ) / 2 < p1)
  (hp2_hi : (p2 : ℝ) < (1 + 1 / (40 * C)) * k / 2)
  (hk : k > 0) :
  1 / (20 * C) * (p1 + p2) < p1 := by
    field_simp at *;
    nlinarith [ ( by norm_cast : ( 0 :ℝ ) < k ) ]

lemma construct_xy (C : ℝ) (hC : C ≥ 1) (k : ℕ) (p1 p2 q1 q2 q3 : ℕ)
  (hp1 : p1.Prime) (hp2 : p2.Prime) (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
  (hp_lt : p1 < p2) (hq_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (h_range_p1 : (k : ℝ) / 2 < p1 ∧ (p1 : ℝ) < (1 + 1 / (40 * C)) * k / 2)
  (h_range_p2 : (k : ℝ) / 2 < p2 ∧ (p2 : ℝ) < (1 + 1 / (40 * C)) * k / 2)
  (h_range_q1 : (1 - 1 / (40 * C)) * k < q1 ∧ (q1 : ℝ) < k)
  (h_range_q2 : (1 - 1 / (40 * C)) * k < q2 ∧ (q2 : ℝ) < k)
  (h_range_q3 : (1 - 1 / (40 * C)) * k < q3 ∧ (q3 : ℝ) < k)
  (hk_large : k ≥ 10)
  (h_len_y : y_interval_length k C / (M_prime k p1 p2 : ℝ) > p1 + p2)
  (h_len_x : x_interval_length k C / (M_prime3 k q1 q2 q3 : ℝ) > q1 + q2 + q3)
  : ∃ x y : ℕ, good_x k x ∧ good_y k y ∧ (x : ℝ) ∈ x_interval k y C ∧ (y : ℝ) ∈ y_interval k C := by
    -- Apply `exists_y_if_large_interval` with `p1`, `p2`.
    obtain ⟨y, hy⟩ : ∃ y : ℕ, (y : ℝ) ∈ y_interval k C ∧ good_y k y := by
      apply exists_y_if_large_interval C hC k p1 p2 hp1 hp2 hp_lt ⟨ by
        exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith;, by
        exact_mod_cast ( by nlinarith [ show ( k : ℝ ) ≥ 10 by norm_cast, one_div_mul_cancel ( by positivity : ( 40 * C : ℝ ) ≠ 0 ) ] : ( p1 : ℝ ) ≤ k ) ⟩ ⟨ by
        exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith;, by
        exact_mod_cast ( by nlinarith [ one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ) ] : ( p2 : ℝ ) ≤ k ) ⟩ h_len_y ⟨ by
        apply (M_prime_coprime k p1 p2 hp1 hp2 hp_lt.ne ⟨ by
          exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith;, by
          exact_mod_cast ( by nlinarith [ show ( k : ℝ ) ≥ 10 by norm_cast, one_div_mul_cancel ( by positivity : ( 40 * C : ℝ ) ≠ 0 ) ] : ( p1 : ℝ ) ≤ k ) ⟩ ⟨ by
          exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith;, by
          exact_mod_cast ( by nlinarith [ one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ) ] : ( p2 : ℝ ) ≤ k ) ⟩ (by linarith)).left
        skip, by
        apply (M_prime_coprime k p1 p2 hp1 hp2 (by
        linarith) ⟨by
        exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith;, by
          exact_mod_cast ( by nlinarith [ show ( k : ℝ ) ≥ 10 by norm_cast, one_div_mul_cancel ( by positivity : ( 40 * C : ℝ ) ≠ 0 ) ] : ( p1 : ℝ ) ≤ k )⟩ ⟨by
        exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith;, by
          exact_mod_cast ( by nlinarith [ one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ) ] : ( p2 : ℝ ) ≤ k )⟩ (by
        grind)).right
        skip ⟩ ⟨ by
        have := B_set_density_bound k p1 ( 1 / ( 40 * C ) ) hp1 ( by positivity ) ( by nlinarith [ mul_div_cancel₀ ( 1 : ℝ ) ( by positivity : ( 40 * C ) ≠ 0 ) ] ) ⟨ by linarith, by linarith ⟩ ; norm_num at * ; linarith;, by
        have := B_set_density_bound k p2 ( 1 / ( 40 * C ) ) hp2 ( by positivity ) ( by nlinarith [ one_div_mul_cancel ( by positivity : ( 40 * C : ℝ ) ≠ 0 ) ] ) ⟨ by linarith, by linarith ⟩ ; norm_num at * ; linarith; ⟩
      generalize_proofs at *;
      linarith [ epsilon_condition_y C hC k p1 p2 h_range_p1.1 h_range_p2.2 ( by linarith ) ];
    -- Apply `exists_x_if_large_interval` with `q1`, `q2`, `q3`.
    obtain ⟨x, hx⟩ : ∃ x : ℕ, (x : ℝ) ∈ x_interval k y C ∧ good_x k x := by
      apply exists_x_if_large_interval C hC k y q1 q2 q3 hq1 hq2 hq3 hq_distinct ⟨ by
        nlinarith [ show ( k : ℝ ) ≥ 10 by norm_cast, one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ), one_div_mul_cancel ( by positivity : ( 20 * C ) ≠ 0 ) ], by
        exact_mod_cast h_range_q1.2 ⟩ ⟨ by
        nlinarith [ one_div_mul_cancel ( by linarith : ( 40 * C ) ≠ 0 ), one_div_mul_cancel ( by linarith : ( 20 * C ) ≠ 0 ) ], by
        exact_mod_cast h_range_q2.2 ⟩ ⟨ by
        nlinarith [ show ( k : ℝ ) ≥ 10 by norm_cast, one_div_mul_cancel ( by positivity : ( 40 * C : ℝ ) ≠ 0 ), one_div_mul_cancel ( by positivity : ( 20 * C : ℝ ) ≠ 0 ) ], by
        exact_mod_cast h_range_q3.2 ⟩ h_len_x
      generalize_proofs at *;
      · apply M_prime3_coprime k q1 q2 q3 hq1 hq2 hq3 hq_distinct ⟨ by
          exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ show ( 0 : ℝ ) < 1 / ( 40 * C ) by positivity, one_div_mul_cancel ( show ( 40 * C : ℝ ) ≠ 0 by positivity ) ] ;, by
          exact_mod_cast h_range_q1.2.le ⟩ ⟨ by
          exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ show ( 1 : ℝ ) / ( 40 * C ) ≤ 1 / 40 by gcongr ; linarith ] ;, by
          exact_mod_cast h_range_q2.2.le ⟩ ⟨ by
          exact Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ show ( k : ℝ ) ≥ 10 by norm_cast, one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ) ] ;, by
          exact_mod_cast h_range_q3.2.le ⟩ ( by linarith );
      · have h_B_density : ∀ q : ℕ, Nat.Prime q → (1 - 1 / (40 * C)) * k < q → q < k → (B_set_x k q).ncard ≥ (1 - 1 / (20 * C)) * q := by
          intros q hq hq1 hq2
          have hB_density : (B_set_x k q).ncard = 2 * q - k := by
            convert B_set_x_ncard k q hq _ using 1
            generalize_proofs at *;
            exact ⟨ by nlinarith [ show ( q : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr hq.pos, show ( k : ℝ ) ≥ 10 by exact_mod_cast hk_large, one_div_mul_cancel ( by positivity : ( 40 * C : ℝ ) ≠ 0 ) ], hq2 ⟩
          generalize_proofs at *;
          rw [ hB_density, Nat.cast_sub ] <;> norm_num;
          · nlinarith [ ( by norm_cast : ( q : ℝ ) + 1 ≤ k ), inv_mul_cancel₀ ( by linarith : C ≠ 0 ), one_div_mul_cancel ( by linarith : ( 40 * C ) ≠ 0 ) ];
          · exact_mod_cast ( by nlinarith [ one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ) ] : ( k : ℝ ) ≤ 2 * q )
        generalize_proofs at *; aesop;
      · simp +zetaDelta at *;
        nlinarith [ inv_mul_cancel₀ ( by linarith : C ≠ 0 ), ( by norm_cast; linarith : ( q1 : ℝ ) < k ), ( by norm_cast; linarith : ( q2 : ℝ ) < k ), ( by norm_cast; linarith : ( q3 : ℝ ) < k ) ];
      · unfold y_interval x_interval_length at *;
        norm_num +zetaDelta at *;
        ring_nf at *; nlinarith [ inv_mul_cancel₀ ( by positivity : ( k : ℝ ) ≠ 0 ), inv_mul_cancel₀ ( by positivity : ( C : ℝ ) ≠ 0 ), ( by norm_cast : ( 10 : ℝ ) ≤ k ) ] ;
    exact ⟨ x, y, hx.2, hy.2, hx.1, hy.1 ⟩

lemma y_len_div_M_gt_8_div_k (C : ℝ) (k : ℕ) (hk : k > 0)
  (h_interval_check : y_interval_length k C / ((M k : ℝ) / (k * k / 4)) > 2 * k) :
  y_interval_length k C / (M k : ℝ) > 8 / k := by
    field_simp at *; ( ring_nf at *; (
    -- The goal is already satisfied by h_interval_check.
    exact h_interval_check); )

/-
If the y interval length satisfies the strong condition, then it is large enough relative to M_prime and p1+p2.
-/
lemma sufficient_length_y (C : ℝ) (hC : C ≥ 1) (k : ℕ) (p1 p2 : ℕ)
  (hk : k ≥ 10)
  (hp1_prime : p1.Prime) (hp2_prime : p2.Prime) (hp_ne : p1 ≠ p2)
  (hp1 : (k : ℝ) / 2 < p1) (hp2 : (k : ℝ) / 2 < p2)
  (h_le1 : p1 ≤ k) (h_le2 : p2 ≤ k)
  (h_y_len_strong : y_interval_length k C / ((M k : ℝ) / (k * k / 4)) > 2 * k) :
  y_interval_length k C / (M_prime k p1 p2 : ℝ) > p1 + p2 := by
    have h_cross : (8 / (k : ℝ)) * (p1 * p2 : ℝ) > (p1 + p2 : ℝ) := by
      rw [ div_mul_eq_mul_div, gt_iff_lt, lt_div_iff₀ ] <;> nlinarith [ ( by norm_cast : ( 10 :ℝ ) ≤ k ) ];
    -- Substitute M_prime into the ratio and use the inequality from h_cross.
    have h_ratio : y_interval_length k C / (M_prime k p1 p2 : ℝ) = (y_interval_length k C / (M k : ℝ)) * (p1 * p2 : ℝ) := by
      rw [ show M_prime k p1 p2 = M k / ( p1 * p2 ) from rfl, Nat.cast_div ];
      · rw [ div_div_eq_mul_div ] ; push_cast ; ring;
      · exact M_prime_dvd k p1 p2 hp1_prime hp2_prime hp_ne h_le1 h_le2;
      · exact Nat.cast_ne_zero.mpr ( mul_ne_zero hp1_prime.ne_zero hp2_prime.ne_zero );
    have h_final : y_interval_length k C / (M k : ℝ) > 8 / (k : ℝ) := by
      have := y_len_div_M_gt_8_div_k C k (by linarith) h_y_len_strong
      exact this;
    exact h_ratio.symm ▸ by nlinarith [ show 0 < ( p1 : ℝ ) * p2 by exact mul_pos ( Nat.cast_pos.mpr hp1_prime.pos ) ( Nat.cast_pos.mpr hp2_prime.pos ) ] ;

/-
If the arithmetic condition holds, then the x interval length is sufficient relative to M_prime3 and q1+q2+q3.
-/
lemma sufficient_length_x (C : ℝ) (hC : C ≥ 1) (k : ℕ) (q1 q2 q3 : ℕ)
  (hk : k ≥ 10)
  (hq1_prime : q1.Prime) (hq2_prime : q2.Prime) (hq3_prime : q3.Prime)
  (hq_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (hq1 : (k : ℝ) / 2 < q1) (hq2 : (k : ℝ) / 2 < q2) (hq3 : (k : ℝ) / 2 < q3)
  (h_le1 : q1 ≤ k) (h_le2 : q2 ≤ k) (h_le3 : q3 ≤ k)
  (h_arithmetic : (q1 * q2 * q3 : ℝ) / (5 * C * k) > q1 + q2 + q3) :
  x_interval_length k C / (M_prime3 k q1 q2 q3 : ℝ) > q1 + q2 + q3 := by
    refine' lt_of_lt_of_le h_arithmetic _;
    rw [ le_div_iff₀ ( Nat.cast_pos.mpr <| M_prime3_pos k q1 q2 q3 ( by linarith ) hq1_prime hq2_prime hq3_prime hq_distinct h_le1 h_le2 h_le3 ) ];
    unfold x_interval_length M_prime3; ring_nf;
    field_simp;
    exact_mod_cast Nat.mul_div_le _ _

/-
For sufficiently large k, there exist x and y satisfying the good conditions and interval bounds.
-/
lemma exists_xy_for_large_k (C : ℝ) (hC : C ≥ 1) (h_density : DensityHypothesis) :
  ∃ K, ∀ k ≥ K, ∃ x y, good_x k x ∧ good_y k y ∧ (x : ℝ) ∈ x_interval k y C ∧ (y : ℝ) ∈ y_interval k C := by
    -- Let's choose ε = 1/(40C) and obtain K_density.
    set ε := 1 / (40 * C)
    have hK_density : ∃ K_density, ∀ k ≥ K_density, ∃ p1 p2 q1 q2 q3 : ℕ,
      p1.Prime ∧ p2.Prime ∧ q1.Prime ∧ q2.Prime ∧ q3.Prime ∧
      p1 < p2 ∧ q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3 ∧
      (k : ℝ) / 2 < p1 ∧ p1 < (1 + ε) * k / 2 ∧
      (k : ℝ) / 2 < p2 ∧ p2 < (1 + ε) * k / 2 ∧
      (1 - ε) * k < q1 ∧ q1 < k ∧
      (1 - ε) * k < q2 ∧ q2 < k ∧
      (1 - ε) * k < q3 ∧ q3 < k := by
        have := h_density ε ( by positivity );
        obtain ⟨ K, hK ⟩ := this;
        use Nat.ceil K;
        intro k hk;
        obtain ⟨ ⟨ p1, p2, hp1, hp2, hp3, hp4, hp5, hp6 ⟩, q1, q2, q3, hq1, hq2, hq3, hq4, hq5, hq6, hq7 ⟩ := hK k ( le_trans ( Nat.le_ceil _ ) hk );
        cases lt_or_gt_of_ne hp5 <;> [ exact ⟨ p1, p2, q1, q2, q3, hp6.1, hp6.2, hq7.2.2.2.1, hq7.2.2.2.2.1, hq7.2.2.2.2.2, by linarith, by tauto ⟩ ; exact ⟨ p2, p1, q1, q2, q3, hp6.2, hp6.1, hq7.2.2.2.1, hq7.2.2.2.2.1, hq7.2.2.2.2.2, by linarith, by tauto ⟩ ];
    obtain ⟨ K_density, hK_density ⟩ := hK_density;
    -- Obtain K_y and K_x from the interval length conditions.
    obtain ⟨K_y, hK_y⟩ : ∃ K_y, ∀ k ≥ K_y, y_interval_length k C / ((M k : ℝ) / (k * k / 4)) > 2 * k := by
      exact interval_length_check_y_strong C hC
    obtain ⟨K_x, hK_x⟩ : ∃ K_x, ∀ k ≥ K_x, ∀ q1 q2 q3 : ℝ, k / 2 < q1 → q1 ≤ k → k / 2 < q2 → q2 ≤ k → k / 2 < q3 → q3 ≤ k → (q1 * q2 * q3 : ℝ) / (5 * C * k) > q1 + q2 + q3 := by
      exact interval_length_check_x_arithmetic C hC;
    use Nat.max ( Nat.ceil K_density ) ( Nat.max K_y ( Nat.ceil K_x + 10 ) );
    intros k hk_ge
    obtain ⟨p1, p2, q1, q2, q3, hp1, hp2, hq1, hq2, hq3, hp_lt, hq_distinct, h_range_p1, h_range_p2, h_range_q1, h_range_q2, h_range_q3⟩ := hK_density k (by
    exact le_trans ( Nat.le_ceil _ ) ( Nat.cast_le.mpr ( le_trans ( Nat.le_max_left _ _ ) hk_ge ) ));
    apply construct_xy C hC k p1 p2 q1 q2 q3 hp1 hp2 hq1 hq2 hq3 hp_lt ⟨ hq_distinct, h_range_p1, h_range_p2 ⟩ ⟨ h_range_q1, h_range_q2 ⟩ ⟨ h_range_q3.1, h_range_q3.2.1 ⟩ ⟨ h_range_q3.2.2.1, h_range_q3.2.2.2.1 ⟩ ⟨ h_range_q3.2.2.2.2.1, h_range_q3.2.2.2.2.2.1 ⟩ ⟨ h_range_q3.2.2.2.2.2.2.1, h_range_q3.2.2.2.2.2.2.2 ⟩ (by
    linarith [ Nat.le_max_right ( ⌈K_density⌉₊ ) ( K_y.max ( ⌈K_x⌉₊ + 10 ) ), Nat.le_max_right K_y ( ⌈K_x⌉₊ + 10 ) ]) (by
    apply sufficient_length_y C hC k p1 p2 (by
    linarith [ Nat.le_max_right ( ⌈K_density⌉₊ ) ( K_y.max ( ⌈K_x⌉₊ + 10 ) ), Nat.le_max_right K_y ( ⌈K_x⌉₊ + 10 ) ]) hp1 hp2 (by
    linarith) h_range_q1 h_range_q3.1 (by
    exact_mod_cast ( by nlinarith [ show ( ε : ℝ ) ≤ 1 / 40 by rw [ div_le_iff₀ ] <;> linarith ] : ( p1 : ℝ ) ≤ k )) (by
    exact_mod_cast ( by nlinarith [ mul_div_cancel₀ ( 1 : ℝ ) ( by positivity : ( 40 * C ) ≠ 0 ) ] : ( p2 : ℝ ) ≤ k )) (by
    exact hK_y k ( by linarith [ Nat.le_max_left ( ⌈K_density⌉₊ ) ( K_y.max ( ⌈K_x⌉₊ + 10 ) ), Nat.le_max_right ( ⌈K_density⌉₊ ) ( K_y.max ( ⌈K_x⌉₊ + 10 ) ), Nat.le_max_left K_y ( ⌈K_x⌉₊ + 10 ), Nat.le_max_right K_y ( ⌈K_x⌉₊ + 10 ) ] ))) (by
    apply sufficient_length_x C hC k q1 q2 q3 (by
    linarith [ Nat.le_max_right ( ⌈K_density⌉₊ ) ( K_y.max ( ⌈K_x⌉₊ + 10 ) ), Nat.le_max_right K_y ( ⌈K_x⌉₊ + 10 ) ]) hq1 hq2 hq3 ⟨ hq_distinct, h_range_p1, h_range_p2 ⟩ (by
    linarith [ show ( 1 - ε ) * k ≥ k / 2 by nlinarith [ show ( ε : ℝ ) ≤ 1 / 40 by rw [ div_le_iff₀ ] <;> linarith ] ]) (by
    linarith [ show ( 1 - ε ) * k ≥ k / 2 by nlinarith [ show ( ε : ℝ ) ≤ 1 / 2 by rw [ div_le_iff₀ ] <;> linarith ] ]) (by
    linarith [ show ( 1 - ε ) * k ≥ k / 2 by nlinarith [ show ( ε : ℝ ) ≤ 1 / 4 by rw [ div_le_iff₀ ] <;> linarith ] ]) (by
    exact_mod_cast h_range_q3.2.2.2.1.le) (by
    exact_mod_cast h_range_q3.2.2.2.2.2.1.le) (by
    exact_mod_cast h_range_q3.2.2.2.2.2.2.2.le) (by
    apply hK_x k (by
    exact le_trans ( Nat.le_ceil _ ) ( by norm_cast; linarith [ Nat.le_max_left ( ⌈K_density⌉₊ ) ( K_y.max ( ⌈K_x⌉₊ + 10 ) ), Nat.le_max_right ( ⌈K_density⌉₊ ) ( K_y.max ( ⌈K_x⌉₊ + 10 ) ), Nat.le_max_left K_y ( ⌈K_x⌉₊ + 10 ), Nat.le_max_right K_y ( ⌈K_x⌉₊ + 10 ) ] )) q1 q2 q3 (by
    linarith [ show ( 1 - ε ) * k ≥ k / 2 by nlinarith [ show ( ε : ℝ ) ≤ 1 / 40 by rw [ div_le_iff₀ ] <;> linarith ] ]) (by
    linarith) (by
    linarith [ show ( 1 - ε ) * k ≥ k / 2 by nlinarith [ show ( ε : ℝ ) ≤ 1 / 2 by rw [ div_le_iff₀ ] <;> linarith ] ]) (by
    linarith) (by
    linarith [ show ( 1 - ε ) * k ≥ k / 2 by nlinarith [ show ( ε : ℝ ) ≤ 1 / 4 by rw [ div_le_iff₀ ] <;> linarith ] ]) (by
    linarith)))

/-
The main theorem holds, conditional on the density hypothesis.
-/
theorem main_theorem (h_density : DensityHypothesis) : MainTheoremStatement := by
  intro C hC_ge_1
  -- Obtain `K1` from `exists_xy_for_large_k`.
  obtain ⟨K1, hK1⟩ := exists_xy_for_large_k C hC_ge_1 h_density
  -- Obtain `K2` from `final_inequality_sufficient`.
  obtain ⟨K2, hK2⟩ := final_inequality_sufficient C hC_ge_1
  -- Obtain `K3` from `m_gt_k`.
  obtain ⟨K3, hK3⟩ := m_gt_k 200000
  -- Let `K = max(K1, K2, K3, 2)`.
  set K := Nat.max (Nat.max (Nat.max K1 K2) K3) 2;
  use K;
  intro k hk_ge_K
  obtain ⟨x, y, hx, hy, hx_interval, hy_interval⟩ := hK1 k (by
  exact le_trans ( Nat.le_max_left _ _ ) ( le_trans ( Nat.le_max_left _ _ ) ( le_trans ( Nat.le_max_left _ _ ) hk_ge_K ) ))
  have hx_pos : 0 < x := by
    exact hx.1
  have hy_pos : 0 < y := by
    exact hy.1
  have hy_gt_x : y > x := by
    cases hx_interval ; cases hy_interval ; aesop
  have hy_gt_x_plus_k : y > x + k := by
    have := good_xy_diff k x y hx hy hy_gt_x;
    grind
  have h_ratio : (Finset.Icc x (x + k - 1)).lcm id / (Finset.Icc y (y + k)).lcm id ≥ (M k : ℚ) / (y + k) * ((x : ℚ) / y) ^ k := by
    apply lcm_ratio_bound k x y (by
    linarith [ show k ≥ 2 by exact le_trans ( by norm_num ) ( Nat.le_trans ( Nat.le_max_right _ _ ) hk_ge_K ) ]) hx_pos hy_pos hy_gt_x hx hy
  have h_final : (M k : ℚ) / (y + k) * ((x : ℚ) / y) ^ k > C := by
    apply hK2 k (by
    exact le_trans ( Nat.le_max_right _ _ ) ( le_trans ( Nat.le_max_left _ _ ) ( le_trans ( Nat.le_max_left _ _ ) hk_ge_K ) )) x y hx_pos hy_pos (by
    exact hy_interval.2) (by
    exact hy_interval.1) (by
    unfold x_interval at hx_interval; linarith [ hx_interval.1, hx_interval.2 ] ;)
  have h_lcm : lcm_real (Finset.Icc x (x + k - 1)) > C * lcm_real (Finset.Icc y (y + k)) := by
    refine' lt_of_lt_of_le ( mul_lt_mul_of_pos_right h_final ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero _ ) ) _;
    · exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
    · convert le_div_iff₀ ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| ?_ ) |>.1 h_ratio using 1 <;> norm_cast;
      · rw [ lcm_real ];
        rw [ lcm_real ] ; norm_cast;
      · norm_num [ Finset.lcm_eq_zero_iff ];
        linarith
  use x, y

lemma prime_counting_interval_tendsto_atTop (a b : ℝ) (ha : 0 < a) (hb : a < b) :
  Tendsto (fun x => (Nat.primeCounting (Nat.floor (b * x)) : ℝ) - (Nat.primeCounting (Nat.floor (a * x)) : ℝ)) atTop atTop := by
    have pi_alt : ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
        ∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ = (1 + c x) * x / log x := by
          exact pi_alt;
    obtain ⟨c, hc⟩ := pi_alt;
    have hc_inf : Filter.Tendsto (fun x => ((1 + c (b * x)) * (b * x) / Real.log (b * x)) - ((1 + c (a * x)) * (a * x) / Real.log (a * x))) Filter.atTop Filter.atTop := by
      -- We can factor out $x / \log x$ from the expression.
      suffices h_factor : Filter.Tendsto (fun x => x / Real.log x * ((b * (1 + c (b * x))) / (1 + Real.log b / Real.log x) - (a * (1 + c (a * x))) / (1 + Real.log a / Real.log x))) Filter.atTop Filter.atTop by
        refine h_factor.congr' ?_ ; filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( 1 / b ), Filter.eventually_gt_atTop ( 1 / a ) ] with x hx₁ hx₂ hx₃ ; rw [ Real.log_mul, Real.log_mul ] <;> ring_nf <;> try linarith;
        field_simp;
        rw [ show Real.log x + Real.log b = Real.log x * ( 1 + Real.log b / Real.log x ) by rw [ mul_add, mul_div_cancel₀ _ ( ne_of_gt ( Real.log_pos hx₁ ) ) ] ; ring, show Real.log x + Real.log a = Real.log x * ( 1 + Real.log a / Real.log x ) by rw [ mul_add, mul_div_cancel₀ _ ( ne_of_gt ( Real.log_pos hx₁ ) ) ] ; ring ] ; rw [ div_mul_eq_div_div, div_mul_eq_div_div ] ; ring;
      -- As $x \to \infty$, $\frac{x}{\log x} \to \infty$ and $(1 + \frac{\log b}{\log x})^{-1} \to 1$.
      have h_frac_inf : Filter.Tendsto (fun x => x / Real.log x) Filter.atTop Filter.atTop := by
        -- We can use the change of variables $u = \log x$ to transform the limit expression.
        suffices h_log : Filter.Tendsto (fun u : ℝ => Real.exp u / u) Filter.atTop Filter.atTop by
          have := h_log.comp Real.tendsto_log_atTop;
          exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.exp_log hx ] );
        simpa using Real.tendsto_exp_div_pow_atTop 1;
      -- Since $c(x)$ is $o(1)$, we have $c(bx) \to 0$ and $c(ax) \to 0$ as $x \to \infty$.
      have h_c_zero : Filter.Tendsto (fun x => c (b * x)) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun x => c (a * x)) Filter.atTop (nhds 0) := by
        exact ⟨ by simpa using hc.1.tendsto_div_nhds_zero.comp ( Filter.tendsto_id.const_mul_atTop ( by linarith ) ), by simpa using hc.1.tendsto_div_nhds_zero.comp ( Filter.tendsto_id.const_mul_atTop ( by linarith ) ) ⟩;
      -- As $x \to \infty$, $(1 + \frac{\log b}{\log x})^{-1} \to 1$ and $(1 + \frac{\log a}{\log x})^{-1} \to 1$.
      have h_inv_one : Filter.Tendsto (fun x => 1 + Real.log b / Real.log x) Filter.atTop (nhds 1) ∧ Filter.Tendsto (fun x => 1 + Real.log a / Real.log x) Filter.atTop (nhds 1) := by
        exact ⟨ by simpa using tendsto_const_nhds.add ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop ) ), by simpa using tendsto_const_nhds.add ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop ) ) ⟩;
      apply Filter.Tendsto.atTop_mul_pos;
      exact sub_pos_of_lt ( by nlinarith : b > a );
      · exact h_frac_inf;
      · convert Filter.Tendsto.sub ( Filter.Tendsto.div ( tendsto_const_nhds.mul ( tendsto_const_nhds.add h_c_zero.1 ) ) h_inv_one.1 _ ) ( Filter.Tendsto.div ( tendsto_const_nhds.mul ( tendsto_const_nhds.add h_c_zero.2 ) ) h_inv_one.2 _ ) using 2 <;> norm_num;
    grind

/-
For any `0 < a < b` and `n`, for sufficiently large `k`, there exist `n` distinct primes in `(ak, bk)`.
-/
open Real Filter

lemma exists_distinct_primes_in_interval (a b : ℝ) (n : ℕ) (ha : 0 < a) (hb : a < b) :
  ∀ᶠ k in atTop, ∃ (S : Finset ℕ), S.card = n ∧ ∀ p ∈ S, p.Prime ∧ a * k < p ∧ p < b * k := by
    have := prime_counting_interval_tendsto_atTop a b ha hb;
    -- For sufficiently large `k`, the number of primes in `(floor(ak), floor(bk)]` is at least `n + 1`.
    obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ x ≥ K, (Nat.primeCounting ⌊b * x⌋₊ : ℝ) - (Nat.primeCounting ⌊a * x⌋₊ : ℝ) > n + 1 := by
      exact Filter.eventually_atTop.mp ( this.eventually_gt_atTop _ );
    -- Let `P` be the set of primes in `(floor(ak), floor(bk)]`.
    have hP : ∀ x ≥ K, ∃ P : Finset ℕ, P.card ≥ n + 1 ∧ ∀ p ∈ P, Nat.Prime p ∧ a * x < p ∧ p ≤ b * x := by
      intro x hx
      have hP_card : (Nat.primeCounting ⌊b * x⌋₊ : ℝ) - (Nat.primeCounting ⌊a * x⌋₊ : ℝ) ≥ n + 2 := by
        exact_mod_cast hK x hx;
      have hP_def : Finset.card (Finset.filter Nat.Prime (Finset.Icc (⌊a * x⌋₊ + 1) ⌊b * x⌋₊)) ≥ n + 2 := by
        have hP_def : Finset.card (Finset.filter Nat.Prime (Finset.Icc 1 ⌊b * x⌋₊)) - Finset.card (Finset.filter Nat.Prime (Finset.Icc 1 ⌊a * x⌋₊)) ≥ n + 2 := by
          have hP_def : Finset.card (Finset.filter Nat.Prime (Finset.Icc 1 ⌊b * x⌋₊)) = Nat.primeCounting ⌊b * x⌋₊ ∧ Finset.card (Finset.filter Nat.Prime (Finset.Icc 1 ⌊a * x⌋₊)) = Nat.primeCounting ⌊a * x⌋₊ := by
            norm_num [ Nat.primeCounting ];
            norm_num [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
            exact ⟨ by rw [ Finset.range_eq_Ico ] ; rfl, by rw [ Finset.range_eq_Ico ] ; rfl ⟩;
          exact Nat.le_sub_of_add_le ( by rw [ ← @Nat.cast_le ℝ ] ; push_cast [ hP_def ] ; linarith );
        refine le_trans hP_def ?_;
        refine' Nat.sub_le_of_le_add _;
        rw [ ← Finset.card_union_of_disjoint ];
        · exact Finset.card_mono fun p hp => by cases le_or_gt p ⌊a * x⌋₊ <;> aesop;
        · exact Finset.disjoint_left.mpr fun p hp₁ hp₂ => by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hp₁ |>.1 ), Finset.mem_Icc.mp ( Finset.mem_filter.mp hp₂ |>.1 ) ] ;
      exact ⟨ _, by linarith, fun p hp => ⟨ Finset.mem_filter.mp hp |>.2, Nat.lt_of_floor_lt <| Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1, Nat.floor_le ( show 0 ≤ b * x by exact mul_nonneg ( by linarith ) <| by linarith [ show 0 ≤ x by exact le_trans ( show 0 ≤ K by exact le_of_not_gt fun h => by have := hK 0 ( by linarith ) ; norm_num at this ; linarith ) hx ] ) |> le_trans ( Nat.cast_le.mpr <| Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2 ) ⟩ ⟩;
    filter_upwards [ Filter.eventually_ge_atTop K, Filter.eventually_gt_atTop ( b / ( b - a ) ) ] with x hx₁ hx₂;
    obtain ⟨ P, hP₁, hP₂ ⟩ := hP x hx₁;
    -- The number of primes in `P` with `p = bk` is at most 1.
    have hP_eq_bk : (Finset.filter (fun p => p = Nat.floor (b * x)) P).card ≤ 1 := by
      exact Finset.card_le_one.mpr ( by aesop );
    -- So the number of primes in `P` with `p < bk` is at least `|P| - 1 ≥ (n + 1) - 1 = n`.
    have hP_lt_bk : (Finset.filter (fun p => p < Nat.floor (b * x)) P).card ≥ n := by
      have hP_lt_bk : (Finset.filter (fun p => p < Nat.floor (b * x)) P).card + (Finset.filter (fun p => p = Nat.floor (b * x)) P).card = P.card := by
        rw [ Finset.card_filter, Finset.card_filter ];
        rw [ ← Finset.sum_add_distrib, Finset.card_eq_sum_ones ];
        exact Finset.sum_congr rfl fun p hp => by split_ifs <;> first | linarith | cases lt_or_eq_of_le ( Nat.le_of_lt_succ <| show p < ⌊b * x⌋₊ + 1 from Nat.lt_succ_of_le <| Nat.le_floor <| by linarith [ hP₂ p hp ] ) <;> aesop;
      linarith;
    obtain ⟨ S, hS ⟩ := Finset.exists_subset_card_eq hP_lt_bk;
    exact ⟨ S, hS.2, fun p hp => ⟨ hP₂ p ( Finset.mem_filter.mp ( hS.1 hp ) |>.1 ) |>.1, hP₂ p ( Finset.mem_filter.mp ( hS.1 hp ) |>.1 ) |>.2.1, by nlinarith [ hP₂ p ( Finset.mem_filter.mp ( hS.1 hp ) |>.1 ) |>.2.2, show ( p : ℝ ) < ⌊b * x⌋₊ from mod_cast Finset.mem_filter.mp ( hS.1 hp ) |>.2, Nat.floor_le ( show 0 ≤ b * x by nlinarith [ div_nonneg ( show 0 ≤ b by linarith ) ( show 0 ≤ b - a by linarith ) ] ) ] ⟩ ⟩

/--
The density hypothesis follows from the PNT (axiom).
-/
theorem density_proof : DensityHypothesis := by
  intro ε hε;
  -- Apply `exists_distinct_primes_in_interval` to find primes for the first condition.
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, ∀ k ≥ K1, ∃ (S : Finset ℕ), S.card = 2 ∧ ∀ p ∈ S, p.Prime ∧ (k / 2 : ℝ) < p ∧ p < ((1 + ε) * k / 2 : ℝ) := by
    have := exists_distinct_primes_in_interval ( 1 / 2 ) ( ( 1 + ε ) / 2 ) 2 ( by norm_num ) ( by linarith );
    rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ K1, hK1 ⟩ ; exact ⟨ K1, fun k hk => by obtain ⟨ S, hS₁, hS₂ ⟩ := hK1 k hk; exact ⟨ S, hS₁, fun p hp => ⟨ hS₂ p hp |>.1, by linarith [ hS₂ p hp |>.2.1 ], by linarith [ hS₂ p hp |>.2.2 ] ⟩ ⟩ ⟩ ;
  -- Apply `exists_distinct_primes_in_interval` to find primes for the second condition.
  obtain ⟨K2, hK2⟩ : ∃ K2 : ℝ, ∀ k ≥ K2, ∃ (S : Finset ℕ), S.card = 3 ∧ ∀ p ∈ S, p.Prime ∧ ((1 - ε) * k : ℝ) < p ∧ p < k := by
    have := exists_distinct_primes_in_interval ( 1 - Min.min ε ( 1 / 2 ) ) 1 3 ?_ ?_ <;> norm_num at *;
    · exact ⟨ this.choose, fun k hk => by obtain ⟨ S, hS₁, hS₂ ⟩ := this.choose_spec k hk; exact ⟨ S, hS₁, fun p hp => ⟨ hS₂ p hp |>.1, by nlinarith [ hS₂ p hp |>.2, min_le_left ε ( 1 / 2 ), min_le_right ε ( 1 / 2 ) ], hS₂ p hp |>.2.2 ⟩ ⟩ ⟩;
    · exact hε;
  use Max.max K1 K2; intro k hk; rcases hK1 k ( le_trans ( le_max_left _ _ ) hk ) with ⟨ S1, hS1, hS1' ⟩ ; rcases hK2 k ( le_trans ( le_max_right _ _ ) hk ) with ⟨ S2, hS2, hS2' ⟩ ; simp_all +decide [ Finset.card_eq_two, Finset.card_eq_three ] ;
  rcases hS1 with ⟨ x, y, hxy, rfl ⟩ ; rcases hS2 with ⟨ u, v, huv, w, huw, hvw, rfl ⟩ ; simp_all +decide [ Finset.mem_insert, Finset.mem_singleton ] ;
  exact ⟨ ⟨ x, hS1'.1.2.1, hS1'.1.2.2, y, hS1'.2.2.1, hS1'.2.2.2, hxy, hS1'.1.1, hS1'.2.1 ⟩, ⟨ u, hS2'.1.2.1, hS2'.1.2.2, v, hS2'.2.1.2.1, hS2'.2.1.2.2, w, hS2'.2.2.2.1, hS2'.2.2.2.2, by tauto ⟩ ⟩

/-
The LCM of k consecutive integers starting at x is bounded by (x+k)^k.
-/
lemma lcm_le_pow (x k : ℕ) : (Finset.Icc x (x + k - 1)).lcm id ≤ (x + k) ^ k := by
  -- The least common multiple (LCM) of a set of numbers is at most their product.
  have h_lcm_le_prod : ∀ (S : Finset ℕ), (S.lcm id) ≤ S.prod id := by
    intro S
    induction' S using Finset.induction with p S ih;
    · norm_num +zetaDelta at *;
    · rw [ Finset.lcm_insert, Finset.prod_insert ih ];
      exact Nat.le_trans ( Nat.div_le_self _ _ ) ( Nat.mul_le_mul_left _ ‹_› );
  refine le_trans ( h_lcm_le_prod _ ) ?_;
  erw [ Finset.prod_Ico_eq_prod_range ];
  rcases k with ( _ | k ) <;> simp_all +arith +decide [ add_assoc ];
  · cases x <;> simp_all +decide [ Finset.prod_range_succ' ];
  · exact le_trans ( Finset.prod_le_prod' fun _ _ => show x + _ ≤ x + ( k + 1 ) by linarith [ Finset.mem_range.mp ‹_› ] ) ( by norm_num )

/-
The binomial coefficient binom(n, k) is at least (n/k)^k.
-/
lemma choose_ge_pow (n k : ℕ) (hk : k ≥ 1) (hn : n ≥ k) : ((n : ℝ) / k) ^ k ≤ Nat.choose n k := by
  -- Apply the lemma h_prod_ge that states the product of fractions is at least (n/k)^k.
  have h_prod_ge_k : (∏ i ∈ Finset.range k, (n - i : ℝ)) / k ! ≥ (n / k : ℝ) ^ k := by
    have h_prod_ge_k : (∏ i ∈ Finset.range k, (n - i : ℝ)) ≥ (n / k : ℝ) ^ k * k ! := by
      have h_prod_ge_k : ∀ i ∈ Finset.range k, (n - i : ℝ) ≥ (n / k : ℝ) * (k - i) := by
        intros i hi
        field_simp;
        nlinarith only [ show ( i : ℝ ) + 1 ≤ k by norm_cast; linarith [ Finset.mem_range.mp hi ], show ( n : ℝ ) ≥ k by norm_cast ];
      refine' le_trans _ ( Finset.prod_le_prod _ h_prod_ge_k );
      · norm_num [ Finset.prod_mul_distrib ];
        exact le_of_eq ( by rw [ show ( ∏ x ∈ Finset.range k, ( k - x : ℝ ) ) = ( k ! : ℝ ) by exact Nat.recOn k ( by norm_num ) fun n ih => by rw [ Finset.prod_range_succ' ] ; simp +decide [ Nat.factorial_succ, ih, mul_comm, mul_assoc, mul_left_comm ] ] ; ring );
      · exact fun i hi => mul_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( sub_nonneg.2 ( Nat.cast_le.2 ( Finset.mem_range_le hi ) ) );
    exact le_div_iff₀ ( by positivity ) |>.2 h_prod_ge_k;
  convert h_prod_ge_k.le using 1;
  rw [ eq_div_iff ] <;> norm_cast <;> try positivity;
  rw [ mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ];
  rw [ Nat.descFactorial_eq_prod_range ];
  rw [ Nat.cast_prod, Finset.prod_congr rfl ] ; intros ; rw [ Int.subNatNat_of_le ] ; linarith [ Finset.mem_range.mp ‹_› ]

/-
The p-adic valuation of binom(n, k) is at most the p-adic valuation of the LCM of the interval (n-k, n].
-/
lemma valuation_choose_le_valuation_lcm (n k : ℕ) (p : ℕ) (hp : p.Prime) :
  padicValNat p (Nat.choose n k) ≤ padicValNat p ((Finset.Icc (n - k + 1) n).lcm id) := by
    by_cases hk : k ≤ n;
    · have h_val : padicValNat p (Nat.choose n k) = ∑ i ∈ Finset.Icc 1 (Nat.log p n), (Nat.floor ((n : ℝ) / (p ^ i)) - Nat.floor ((k : ℝ) / (p ^ i)) - Nat.floor (((n - k) : ℝ) / (p ^ i))) := by
        haveI := Fact.mk hp;
        rw [ padicValNat_choose ];
        any_goals exact Nat.lt_succ_self _;
        · have h_sum_eq : ∀ i ∈ Finset.Icc 1 (Nat.log p n), ⌊(n : ℝ) / p ^ i⌋₊ - ⌊(k : ℝ) / p ^ i⌋₊ - ⌊((n - k) : ℝ) / p ^ i⌋₊ = if p ^ i ≤ k % p ^ i + (n - k) % p ^ i then 1 else 0 := by
            intro i hi
            have h_floor_eq : ⌊(n : ℝ) / p ^ i⌋₊ = n / p ^ i ∧ ⌊(k : ℝ) / p ^ i⌋₊ = k / p ^ i ∧ ⌊((n - k) : ℝ) / p ^ i⌋₊ = (n - k) / p ^ i := by
              norm_cast;
              exact ⟨ by rw [ Nat.floor_div_natCast, Nat.floor_natCast ], by rw [ Nat.floor_div_natCast, Nat.floor_natCast ], by rw [ Nat.floor_div_natCast, Nat.floor_natCast ] ⟩;
            split_ifs <;> simp_all +decide [ Nat.div_eq_of_lt, Nat.mod_eq_of_lt ];
            · rw [ show n = k + ( n - k ) by rw [ Nat.add_sub_of_le hk ] ] ; norm_num [ Nat.add_div, hp.pos ];
              split_ifs ; omega;
            · rw [ show n = k + ( n - k ) by rw [ Nat.add_sub_of_le hk ] ] ; norm_num [ Nat.add_div ( pow_pos hp.pos _ ) ] ;
              split_ifs <;> omega;
          rw [ Finset.sum_congr rfl h_sum_eq, Finset.sum_ite ] ; aesop;
        · linarith;
      -- The term in the sum is 1 if there is a carry at position $i$, and 0 otherwise.
      have h_carry : ∀ i ∈ Finset.Icc 1 (Nat.log p n), (Nat.floor ((n : ℝ) / (p ^ i)) - Nat.floor ((k : ℝ) / (p ^ i)) - Nat.floor (((n - k) : ℝ) / (p ^ i))) ≤ if ∃ j ∈ Finset.Icc (n - k + 1) n, p ^ i ∣ j then 1 else 0 := by
        intro i hi
        set m := Nat.floor ((n : ℝ) / (p ^ i))
        set l := Nat.floor ((k : ℝ) / (p ^ i))
        set r := Nat.floor (((n - k) : ℝ) / (p ^ i))
        have h_floor : m = n / p ^ i ∧ l = k / p ^ i ∧ r = (n - k) / p ^ i := by
          norm_num +zetaDelta at *;
          norm_cast;
          exact ⟨ by rw [ Nat.floor_div_natCast, Nat.floor_natCast ], by rw [ Nat.floor_div_natCast, Nat.floor_natCast ], by rw [ Nat.floor_div_natCast, Nat.floor_natCast ] ⟩;
        split_ifs <;> simp_all +decide [ Nat.div_eq_of_lt ];
        · rw [ show n = n - k + k by rw [ Nat.sub_add_cancel hk ] ] ; norm_num [ Nat.add_div, hp.pos ] ;
          grind;
        · rw [ Nat.sub_sub, tsub_eq_zero_iff_le.mpr ];
          rw [ Nat.le_iff_lt_or_eq ];
          refine' lt_or_eq_of_le ( Nat.le_of_lt_succ _ );
          rw [ Nat.div_lt_iff_lt_mul <| pow_pos hp.pos _ ];
          contrapose! h_floor;
          exact fun _ _ => False.elim <| ‹∀ x : ℕ, n - k + 1 ≤ x → x ≤ n → ¬p ^ i ∣ x› ( ( k / p ^ i + ( n - k ) / p ^ i + 1 ) * p ^ i ) ( by nlinarith [ Nat.div_add_mod k ( p ^ i ), Nat.mod_lt k ( pow_pos hp.pos i ), Nat.div_add_mod ( n - k ) ( p ^ i ), Nat.mod_lt ( n - k ) ( pow_pos hp.pos i ), Nat.sub_add_cancel hk ] ) ( by nlinarith [ Nat.div_add_mod k ( p ^ i ), Nat.mod_lt k ( pow_pos hp.pos i ), Nat.div_add_mod ( n - k ) ( p ^ i ), Nat.mod_lt ( n - k ) ( pow_pos hp.pos i ), Nat.sub_add_cancel hk ] ) <| dvd_mul_left _ _;
      -- The maximum $i$ where there's a carry is at most the maximum $i$ where $p^i$ divides the LCM.
      have h_max_i : ∀ i ∈ Finset.Icc 1 (Nat.log p n), (∃ j ∈ Finset.Icc (n - k + 1) n, p ^ i ∣ j) → i ≤ Nat.factorization (Finset.lcm (Finset.Icc (n - k + 1) n) id) p := by
        intros i hi h_div
        obtain ⟨j, hj₁, hj₂⟩ := h_div
        have h_div_lcm : p ^ i ∣ Finset.lcm (Finset.Icc (n - k + 1) n) id := by
          exact dvd_trans hj₂ ( Finset.dvd_lcm hj₁ );
        rw [ ← Nat.factorization_le_iff_dvd ] at h_div_lcm <;> aesop;
      have h_sum_carry : ∑ i ∈ Finset.Icc 1 (Nat.log p n), (if ∃ j ∈ Finset.Icc (n - k + 1) n, p ^ i ∣ j then 1 else 0) ≤ Nat.factorization (Finset.lcm (Finset.Icc (n - k + 1) n) id) p := by
        simp +zetaDelta at *;
        exact le_trans ( Finset.card_le_card fun x hx => Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, h_max_i x ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1 ) ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ) _ ( Finset.mem_filter.mp hx |>.2.choose_spec.1.1 ) ( Finset.mem_filter.mp hx |>.2.choose_spec.1.2 ) ( Finset.mem_filter.mp hx |>.2.choose_spec.2 ) ⟩ ) ( by simp );
      convert h_sum_carry.trans' ( Finset.sum_le_sum h_carry ) using 1;
      rw [ Nat.factorization_def ] ; aesop;
    · simp +decide [ Nat.choose_eq_zero_of_lt ( not_le.mp hk ) ]

/-
The binomial coefficient binom(y+k, k+1) divides the LCM of the interval [y, y+k].
-/
lemma choose_dvd_lcm (y k : ℕ) : Nat.choose (y + k) (k + 1) ∣ (Finset.Icc y (y + k)).lcm id := by
  by_cases hy : y = 0;
  · simp +decide [ hy, Nat.choose_eq_zero_of_lt ];
  · -- Apply the lemma `valuation_choose_le_valuation_lcm` with $n = y + k$ and $m = k + 1$.
    have h_val : ∀ p, p.Prime → padicValNat p (Nat.choose (y + k) (k + 1)) ≤ padicValNat p ((Finset.Icc y (y + k)).lcm id) := by
      convert valuation_choose_le_valuation_lcm ( y + k ) ( k + 1 ) using 1;
      grind;
    rw [ ← Nat.factorization_le_iff_dvd ];
    · intro p; by_cases hp : Nat.Prime p <;> simp_all +decide [ Nat.factorization ] ;
    · exact Nat.ne_of_gt <| Nat.choose_pos <| by linarith [ Nat.pos_of_ne_zero hy ] ;
    · norm_num [ Finset.lcm_eq_zero_iff ];
      assumption

/-
The statement is false because the LCM of the y-interval (length k+1) grows asymptotically faster than the LCM of the x-interval (length k).
-/
theorem infinitely_many_examples_false :
  ¬ (∀ C : ℝ, C ≥ 1 →
  ∃ K, ∀ k ≥ K,
  ∀ X : ℕ, ∃ x y : ℕ,
    X < x ∧ x < y ∧ y > x + k ∧
    lcm_real (Finset.Icc x (x + k - 1)) > C * lcm_real (Finset.Icc y (y + k))) := by
      push_neg;
      refine' ⟨ 1, by norm_num, _ ⟩;
      intros x
      obtain ⟨k, hk⟩ : ∃ k ≥ x, ∃ X : ℕ, ∀ x y : ℕ, X < x → x < y → y > x + k → Nat.choose (y + k) (k + 1) > (x + k) ^ k := by
        have h_choose_growth : ∀ k ≥ 1, ∃ X : ℕ, ∀ x y : ℕ, X < x → x < y → y > x + k → Nat.choose (y + k) (k + 1) > (x + k) ^ k := by
          intro k hk
          have h_choose_growth : ∀ y : ℕ, y > k → Nat.choose (y + k) (k + 1) ≥ (y : ℝ) ^ (k + 1) / (k + 1) ^ (k + 1) := by
            intro y hy
            have h_choose_ge_pow : (Nat.choose (y + k) (k + 1) : ℝ) ≥ ((y + k) / (k + 1)) ^ (k + 1) := by
              have := choose_ge_pow ( y + k ) ( k + 1 ) ( by linarith ) ( by linarith ) ; aesop;
            exact le_trans ( by rw [ div_pow ] ; gcongr ; norm_cast ; linarith ) h_choose_ge_pow;
          -- Choose $X$ such that for all $x > X$, $(x + k)^k < \frac{(x + k + 1)^{k + 1}}{(k + 1)^{k + 1}}$.
          obtain ⟨X, hX⟩ : ∃ X : ℕ, ∀ x : ℕ, x > X → (x + k : ℝ) ^ k < (x + k + 1) ^ (k + 1) / (k + 1) ^ (k + 1) := by
            have h_choose_growth : Filter.Tendsto (fun x : ℕ => ((x + k + 1 : ℝ) ^ (k + 1) / (k + 1) ^ (k + 1)) / ((x + k : ℝ) ^ k)) Filter.atTop Filter.atTop := by
              -- We can factor out $(x + k)^k$ from the numerator and denominator.
              suffices h_factor : Filter.Tendsto (fun x : ℕ => ((x + k + 1 : ℝ) / (x + k)) ^ k * ((x + k + 1 : ℝ) / ((k + 1) ^ (k + 1)))) Filter.atTop Filter.atTop by
                convert h_factor using 2 ; ring_nf;
                simpa only [ mul_assoc, ← mul_pow ] using by ring;
              -- We can simplify the expression inside the limit.
              suffices h_simplify : Filter.Tendsto (fun x : ℕ => (1 + 1 / (x + k : ℝ)) ^ k * ((x + k + 1 : ℝ) / ((k + 1) ^ (k + 1)))) Filter.atTop Filter.atTop by
                field_simp;
                refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ one_add_div ( by positivity ) ] ; ring );
              -- We can use the fact that $(1 + 1 / (x + k))^k$ tends to $1$ as $x$ tends to infinity.
              have h_exp : Filter.Tendsto (fun x : ℕ => (1 + 1 / (x + k : ℝ)) ^ k) Filter.atTop (nhds 1) := by
                exact le_trans ( Filter.Tendsto.pow ( tendsto_const_nhds.add <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) _ ) <| by norm_num;
              apply Filter.Tendsto.pos_mul_atTop;
              exacts [ zero_lt_one, h_exp, Filter.Tendsto.atTop_div_const ( by positivity ) ( Filter.tendsto_atTop_add_const_right _ _ <| Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ];
            have := h_choose_growth.eventually_gt_atTop 1;
            rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ X, hX ⟩ ; exact ⟨ X, fun x hx => by have := hX x hx.le; rw [ lt_div_iff₀ ( by positivity ) ] at this; linarith ⟩ ;
          use X + k + 1;
          intros x y hx hy hxy
          have h_choose : Nat.choose (y + k) (k + 1) ≥ (y : ℝ) ^ (k + 1) / (k + 1) ^ (k + 1) := by
            exact h_choose_growth y ( by linarith );
          contrapose! h_choose;
          refine' lt_of_le_of_lt ( Nat.cast_le.mpr h_choose ) _;
          refine' lt_of_lt_of_le ( mod_cast hX x ( by linarith ) ) _;
          field_simp;
          norm_cast ; rw [ mul_comm ] ; gcongr ; linarith;
        exact ⟨ x + 1, by linarith, h_choose_growth _ <| by linarith ⟩;
      obtain ⟨ X, hX ⟩ := hk.2; use k, hk.1, X; intros x y hx hy hxy; have := hX x y hx hy hxy; norm_num at *; (
      -- By combining the inequalities from hX and the bounds on the LCMs, we get the desired result.
      have h_lcm_bound : (Finset.Icc x (x + k - 1)).lcm id ≤ (x + k) ^ k ∧ (Finset.Icc y (y + k)).lcm id ≥ (y + k).choose (k + 1) := by
        exact ⟨ lcm_le_pow x k, Nat.le_of_dvd ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ( choose_dvd_lcm y k ) ⟩;
      convert h_lcm_bound.1.trans this.le |> le_trans <| h_lcm_bound.2 using 1;
      unfold lcm_real; aesop;);

/-- The least common multiple of ${n+1, \dotsc, n+k}$. -/
def lcmInterval {α : Type*} [AddMonoid α] [CancelCommMonoidWithZero α] [NormalizedGCDMonoid α]
    [Preorder α] [LocallyFiniteOrder α] (n k : α) : α := (Finset.Ioc n (n + k)).lcm id

lemma lcmInterval_ge_choose (n k : ℕ) : lcmInterval n k ≥ Nat.choose (n + k) k := by
  have h_eq : lcmInterval n k = (Finset.Icc (n + 1) (n + k)).lcm id := by
    exact congr_arg _ ( Finset.ext fun x => by aesop );
  have := choose_dvd_lcm ( n + 1 ) ( k - 1 ) ; rcases k with ( _ | _ | k ) <;> simp_all +decide [ Nat.choose_succ_succ, add_assoc ] ;
  · linarith;
  · exact Nat.le_of_dvd ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ( by simpa only [ add_comm, add_left_comm, add_assoc ] using this )

theorem lcmInterval_growth : ∀ᶠ k in Filter.atTop, ∃ N, ∀ n ≥ N, ∀ m ≥ n + k, lcmInterval m (k + 1) > lcmInterval n k := by
  refine' Filter.eventually_atTop.mpr ⟨ 1, _ ⟩;
  -- Fix a $k \ge 1$.
  intro k hk
  -- Consider the expression $\binom{n+2k+1}{k+1} - (n+k+1)^k$.
  suffices h_suff : ∃ N, ∀ n ≥ N, Nat.choose (n + 2 * k + 1) (k + 1) > (n + k + 1) ^ k by
    -- By combining the inequalities from h_suff and the properties of lcmInterval, we can conclude the proof.
    obtain ⟨N, hN⟩ := h_suff;
    use N;
    intro n hn m hm;
    have h_lcm_m : lcmInterval m (k + 1) ≥ Nat.choose (n + 2 * k + 1) (k + 1) := by
      have h_lcm_m : lcmInterval m (k + 1) ≥ Nat.choose (m + k + 1) (k + 1) := by
        exact lcmInterval_ge_choose m (k + 1);
      exact le_trans ( Nat.choose_le_choose _ ( by linarith ) ) h_lcm_m
    have h_lcm_n : lcmInterval n k ≤ (n + k + 1) ^ k := by
      convert lcm_le_pow ( n + 1 ) k using 1;
      · exact congr_arg₂ _ ( Finset.ext fun x => by aesop ) rfl;
      · ring
    exact lt_of_le_of_lt (by
    exact h_lcm_n) (h_lcm_m.trans_lt' (hN n hn));
  -- We can bound the binomial coefficient from below by $\frac{(n+k+1)^{k+1}}{(k+1)!}$.
  have h_binom_bound : ∀ n ≥ k, Nat.choose (n + 2 * k + 1) (k + 1) ≥ (n + k + 1) ^ (k + 1) / (k + 1)! := by
    intro n hn
    have h_binom_bound : Nat.choose (n + 2 * k + 1) (k + 1) ≥ (n + k + 1) ^ (k + 1) / (k + 1)! := by
      have h_prod : ∏ i ∈ Finset.range (k + 1), (n + 2 * k + 1 - i) ≥ (n + k + 1) ^ (k + 1) := by
        exact le_trans ( by norm_num ) ( Finset.prod_le_prod' fun i hi => show n + 2 * k + 1 - i ≥ n + k + 1 from Nat.le_sub_of_add_le <| by linarith [ Finset.mem_range.mp hi ] )
      have h_binom_bound : Nat.choose (n + 2 * k + 1) (k + 1) * (k + 1)! = ∏ i ∈ Finset.range (k + 1), (n + 2 * k + 1 - i) := by
        rw [ mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose ];
        rw [ Nat.descFactorial_eq_prod_range ];
      exact Nat.div_le_of_le_mul <| by linarith;
    exact h_binom_bound;
  -- Since $(k+1)!$ is a constant, for sufficiently large $n$, $(n+k+1)^{k+1} / (k+1)!$ will be greater than $(n+k+1)^k$.
  have h_const_bound : ∃ N, ∀ n ≥ N, (n + k + 1) ^ (k + 1) / (k + 1)! > (n + k + 1) ^ k := by
    refine' ⟨ ( k + 1 ) ! + 1, fun n hn => Nat.le_div_iff_mul_le ( Nat.factorial_pos _ ) |>.2 _ ⟩;
    rw [ pow_succ' ];
    nlinarith [ Nat.factorial_pos ( k + 1 ), Nat.pow_le_pow_right ( by linarith : 1 ≤ n + k + 1 ) hk ];
  exact ⟨ Nat.max k h_const_bound.choose, fun n hn => lt_of_lt_of_le ( h_const_bound.choose_spec n ( le_trans ( le_max_right _ _ ) hn ) ) ( h_binom_bound n ( le_trans ( le_max_left _ _ ) hn ) ) ⟩

/--
The main theorem holds, conditional on the PNT (axiom)
-/
theorem main_theorem_given_pnt : MainTheoremStatement := by
  -- Apply the main theorem with the density hypothesis to conclude the proof.
  apply main_theorem; exact density_proof

/--
The main theorem spelled out, just for concreteness.  As before, it's proven assuming
the PNT as an axiom.
-/
theorem main_theorem_expanded :
  ∀ C : ℝ, C ≥ 1 →
  ∃ K, ∀ k ≥ K, ∃ x y : ℕ,
    0 < x ∧ x < y ∧ y > x + k ∧
    lcm_real (Finset.Icc x (x + k - 1)) > C * lcm_real (Finset.Icc y (y + k)) := by
  -- The main theorem holds, conditional on the PNT (axiom) by applying the `main_theorem` theorem.
  apply main_theorem_given_pnt

theorem erdos_678 :
  ∃ K, ∀ k ≥ K,
  ∃ x y : ℕ,
    0 < x ∧ x < y ∧ y > x + k ∧
    lcm_real (Finset.Icc x (x + k - 1)) > lcm_real (Finset.Icc y (y + k)) := by
  -- Apply the main theorem to conclude the proof.
  obtain ⟨K, hK⟩ := main_theorem_given_pnt 1 (by norm_num);
  -- Since $1 * lcm_real (Finset.Icc y (y + k)) = lcm_real (Finset.Icc y (y + k))$, we can conclude the proof.
  use K
  intro k hk
  obtain ⟨x, y, hx_pos, hx_lt_y, hy_gt_xk, h_lcm⟩ := hK k hk
  use x, y
  aesop

theorem not_erdos_678_fc :
    ¬(∀ᶠ k in atTop, {(m, n) | n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k}.Infinite) := by
  -- By `lcmInterval_growth`, for large enough $k$, there are no such pairs $(m, n)$ in $S_k$.
  have h_finite : ∀ᶠ k in Filter.atTop, ∃ N, ∀ n ≥ N, ∀ m ≥ n + k, lcmInterval m (k + 1) > lcmInterval n k := by
    exact lcmInterval_growth;
  intro h_inf;
  obtain ⟨ k, hk ⟩ := h_finite.and h_inf |> fun h => h.exists;
  obtain ⟨ ⟨ N, hN ⟩, h_inf ⟩ := hk;
  -- For a fixed $n < N$, the condition $\text{lcmInterval}(m, k+1) < \text{lcmInterval}(n, k)$ implies $m+1 < \text{lcmInterval}(n, k)$, so there are finitely many such $m$.
  have h_finite_fixed_n : ∀ n < N, Set.Finite {m | lcmInterval m (k + 1) < lcmInterval n k} := by
    intro n hn
    have h_bound : ∀ m, lcmInterval m (k + 1) ≥ m + 1 := by
      intro m; exact (by
      exact Nat.le_of_dvd ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ( Finset.dvd_lcm ( Finset.mem_Ioc.mpr ⟨ by linarith, by linarith ⟩ ) ));
    exact Set.finite_iff_bddAbove.mpr ⟨ lcmInterval n k, fun m hm => by linarith [ h_bound m, hm.out ] ⟩;
  -- Therefore, $S_k$ is a finite union of finite sets, so it is finite.
  have h_finite_union : Set.Finite {x : ℕ × ℕ | x.2 < N ∧ x.2 + k ≤ x.1 ∧ lcmInterval x.1 (k + 1) < lcmInterval x.2 k} := by
    exact Set.Finite.subset ( Set.Finite.prod ( Set.Finite.biUnion ( Set.finite_lt_nat N ) fun n hn => h_finite_fixed_n n hn ) ( Set.finite_lt_nat N ) ) fun x hx => by aesop;
  exact h_inf <| h_finite_union.subset fun x hx => ⟨ lt_of_not_ge fun hx' => by linarith [ hN _ hx' _ hx.1, hx.2 ], hx.1, hx.2 ⟩

theorem erdos_678_kmn_infinite :
    {(k, m, n) | 3 ≤ k ∧ n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k}.Infinite := by
  -- Assume that for every $k \geq 3$ there exists an $M_k$ such that if $n \geq M_k$ then $\mathrm{lcm}(n+k+1,\ldots,n+2k+1) > \mathrm{lcm}(n+1,\ldots,n+k)$.
  by_contra h_contra;
  -- If the set were finite, there would be a maximum k, say K. For all k ≥ K, the inequality wouldn't hold. But we know that for large k, the LCM of [n+k+1, n+2k+1] is larger than that of [n+1, n+k]. So if the set were finite, we could find a k larger than K where the inequality holds, which contradicts the assumption. Therefore, the set must be infinite.
  obtain ⟨K, hK⟩ : ∃ K, ∀ k ≥ K, ∀ n m, n + k ≤ m → lcmInterval m (k + 1) ≥ lcmInterval n k := by
    -- Since the set is finite, there exists a maximum k, say K_max, in the set.
    obtain ⟨K_max, hK_max⟩ : ∃ K_max, ∀ k ≥ K_max, ∀ n m, n + k ≤ m → lcmInterval m (k + 1) ≥ lcmInterval n k := by
      have h_finite : Set.Finite {k | ∃ n m, 3 ≤ k ∧ n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k} := by
        exact Set.Finite.subset ( Set.not_infinite.mp h_contra |> Set.Finite.image fun x => x.1 ) fun x hx => by aesop;
      obtain ⟨ K_max, hK_max ⟩ := h_finite.bddAbove;
      exact ⟨ K_max + 3, fun k hk n m hnm => not_lt.1 fun contra => by linarith [ hK_max ⟨ n, m, by linarith, hnm, contra ⟩ ] ⟩;
    use K_max + 3, fun k hk n m hnm => hK_max k ( by linarith ) n m hnm;
  -- Apply the valuation_ineq_good_p_aux lemma to obtain a contradiction with the assumption that the set is finite.
  have h_contradiction : ∃ k ≥ K, ∃ n m : ℕ, n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k := by
    -- Apply the main theorem to obtain the existence of such a k.
    obtain ⟨k, hk⟩ : ∃ k ≥ K, ∃ n m : ℕ, n + k ≤ m ∧ lcmInterval m (k + 1) < lcmInterval n k := by
      have := main_theorem_given_pnt
      -- Apply the main theorem to obtain the existence of such a k, n, and m.
      obtain ⟨k, hk⟩ := this 1 (by norm_num);
      simp +zetaDelta at *;
      obtain ⟨ x, hx, y, hy, hxy, h ⟩ := hk ( k + K + 3 ) ( by linarith ) ; use k + K + 3 ; simp_all +decide [ lcmInterval ] ;
      refine' ⟨ by linarith, x - 1, y - 1, _, _ ⟩ <;> rcases x with ( _ | x ) <;> rcases y with ( _ | y ) <;> norm_num at * <;> try linarith;
      convert h using 1;
      unfold lcm_real; norm_cast; simp +arith +decide [ Nat.Icc_succ_left ] ;
      ring_nf;
    exact ⟨ k, hk ⟩;
  obtain ⟨ k, hk₁, n, m, hnm, hkm ⟩ := h_contradiction; exact hkm.not_le <| hK k hk₁ n m hnm;

#print axioms main_theorem_expanded
-- 'main_theorem_given_expanded' depends on axioms: [pi_alt, propext, Classical.choice, Quot.sound]

#print axioms erdos_678_kmn_infinite
-- 'erdos_678_kmn_infinite' depends on axioms: [pi_alt, propext, Classical.choice, Quot.sound]

#print axioms not_erdos_678_fc
-- 'not_erdos_678_fc' depends on axioms: [propext, Classical.choice, Quot.sound]

#print axioms erdos_678
-- 'erdos_678' depends on axioms: [pi_alt, propext, Classical.choice, Quot.sound]

end

end Erdos678
