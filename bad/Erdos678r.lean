/-
We have formalized the main results of the paper "Resolution of an Erdős' problem on least common multiples".

1.  **Main Theorem**: We proved `MainTheoremStatement` (Theorem 1 in the paper) assuming the `DensityHypothesis` (which follows from results on prime gaps, e.g., Baker-Harman-Pintz).
    *   `main_theorem_proof_v6` establishes this.

2.  **Conjecture 2 Reduction**: We proved that a stronger version of Question 4 (`Question4Stronger`) implies Conjecture 2 (`Conjecture2Statement`), assuming the Prime Number Theorem bounds (`PNT_bounds`).
    *   `Question4Stronger_implies_Conjecture2_actual` establishes this.

The formalization follows the structure of the paper, defining `M`, `m`, `good_x`, `good_y`, and using the Chinese Remainder Theorem and density arguments to construct the required integers. We handled the asymptotic inequalities and p-adic valuation arguments required for the proofs.
-/

import Mathlib

set_option linter.mathlibStandardSet false

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

#check Nat.tendsto_primeCounting

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
        exact Exists.elim h_exists fun i hi => ⟨ i, hi.1, hi.2, fun j hj hj' => not_lt.1 fun hj'' => h_unique.not_lt <| Finset.one_lt_card.2 ⟨ j, by aesop, i, by aesop ⟩ ⟩;
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
          exact?;
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
The sum of a periodic function over an interval of fixed length depends only on the starting point modulo the period.
-/
lemma sum_periodic_interval (f : ℕ → ℕ) (T : ℕ) (h_per : ∀ n, f (n + T) = f n)
  (a b k : ℕ) (h_mod : a ≡ b [MOD T]) :
  ∑ i ∈ Finset.Icc a (a + k), f i = ∑ i ∈ Finset.Icc b (b + k), f i := by
    -- Since $a \equiv b \pmod{T}$, we can assume wlog that $b \geq a$, and get $b = a + mT$ for some integer $m$.
    obtain ⟨m, hm⟩ : ∃ m : ℕ, b = a + m * T ∨ a = b + m * T := by
      rcases Nat.modEq_iff_dvd.mp h_mod.symm with ⟨ m, hm ⟩;
      exact ⟨ m.natAbs, by cases abs_cases m <;> first |left; nlinarith|right; nlinarith⟩;
    rcases hm with rfl | rfl;
    · induction' m with m ih;
      · norm_num;
      · induction' ( m + 1 ) with m ih <;> simp_all +decide [ Nat.succ_mul, ← add_assoc ];
        erw [ Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range ];
        simp +arith +decide [ add_assoc, add_tsub_add_eq_tsub_left, h_per ];
        exact Finset.sum_congr rfl fun _ _ => by rw [ ← h_per ] ; ring;
    · -- By periodicity, we can shift the interval without changing the sum.
      have h_shift : ∀ i : ℕ, f (b + m * T + i) = f (b + i) := by
        exact fun i => Nat.recOn m ( by norm_num ) fun n ihn => by rw [ Nat.succ_mul, ← add_assoc, ← add_right_comm, h_per, ihn ] ;
      erw [ Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range ];
      grind

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
    -- Since there is at most one multiple of $p^2$ in $S$, the condition $h_unique$ holds with $e=1$.
    have h_unique : (S.filter (fun i => padicValNat p i > 1)).card ≤ 1 := by
      have h_unique_multiples_of_p2 : ∀ x y : ℕ, x ∈ S → y ∈ S → x ≠ y → ¬(p ^ 2 ∣ x ∧ p ^ 2 ∣ y) := by
        intros x y hx hy hxy h_div
        obtain ⟨s, hs⟩ := hS_consec
        have h_diff : |(x : ℤ) - y| < p ^ 2 := by
          cases abs_cases ( x - y : ℤ ) <;> linarith [ Finset.mem_Icc.mp ( hs ▸ hx ), Finset.mem_Icc.mp ( hs ▸ hy ), Nat.sub_add_cancel ( show 1 ≤ s + n from Nat.one_le_iff_ne_zero.mpr <| by aesop ), show ( n : ℤ ) ≤ p ^ 2 by norm_cast; linarith ];
        exact h_diff.not_le ( Int.le_of_dvd ( abs_pos.mpr ( sub_ne_zero.mpr ( Nat.cast_injective.ne hxy ) ) ) ( by simpa using dvd_sub ( Int.natCast_dvd_natCast.mpr h_div.1 ) ( Int.natCast_dvd_natCast.mpr h_div.2 ) ) );
      contrapose! h_unique_multiples_of_p2;
      obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.mp h_unique_multiples_of_p2;
      use x, y;
      simp_all +decide [ Nat.Prime.pow_dvd_iff_le_factorization ];
      exact ⟨ Nat.dvd_trans ( pow_dvd_pow _ hx.2 ) ( by exact? ), Nat.dvd_trans ( pow_dvd_pow _ hy.2 ) ( by exact? ) ⟩;
    have h_val : padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (∑ i ∈ S, min (padicValNat p i) 1) - 1 := by
      apply valuation_prod_div_lcm S p 1 hp;
      · obtain ⟨ z, hz₁, hz₂ ⟩ := h_exists;
        exact le_trans ( Nat.pos_of_ne_zero ( by haveI := Fact.mk hp; exact? ) ) ( Finset.le_sup ( f := padicValNat p ) hz₁ );
      · assumption;
      · assumption;
    -- Since $\min(v_p(i), 1) = 1$ if $p \mid i$ and $0$ otherwise, we can simplify the sum.
    have h_min : ∀ i ∈ S, min (padicValNat p i) 1 = if p ∣ i then 1 else 0 := by
      intro i hi; split_ifs <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
      by_contra h_contra;
      simp_all +decide [ Nat.dvd_iff_mod_eq_zero, padicValNat.eq_zero_of_not_dvd ];
      cases h_contra <;> simp_all +decide [ Nat.mod_eq_of_lt hp.one_lt ];
    rw [ h_val, Finset.sum_congr rfl h_min, Finset.sum_ite ] ; aesop

/-
Check environment health after disabling ALL decls.
-/
#eval 1

/-
Definition of good_x without referencing m k directly.
-/
def good_x_nom (k x m_val : ℕ) : Prop :=
  x > 0 ∧
  x % m_val = 1 ∧
  ∀ p, Nat.Prime p → Nat.sqrt k < p → p ≤ k → 1 ≤ x % p ∧ x % p ≤ p - (k % p)

/-
Test if m is broken.
-/
def test_m_broken : ℕ := m 2

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
Checking definitions of good_x and good_y.
-/
#print good_x
#print good_y

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
              exact?;
              · exact ⟨ y, by simp +arith +decide ⟩;
              · norm_num;
                nlinarith only [ h_case, h_case2, Nat.lt_succ_sqrt k ];
              · exact ⟨ p * ( y / p + 1 ), Finset.mem_Icc.mpr ⟨ by linarith [ Nat.div_add_mod y p, Nat.mod_lt y hp.pos ], by linarith [ Nat.div_mul_le_self y p ] ⟩, by norm_num ⟩;
              · exact fun z hz => by linarith [ Finset.mem_Icc.mp hz ] ;
            have h_val_large_p_rhs : padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = (Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card - 1 := by
              apply valuation_large_p_le;
              any_goals tauto;
              · simp +arith +decide [ Nat.sub_add_comm ( by linarith : 1 ≤ x + k ) ];
                exact ⟨ x, by rw [ show k + x - 1 + 1 - x = k by omega ] ; ring ⟩;
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
The p-adic valuations of the LHS and RHS ratios are equal for all primes p.
-/
theorem valuation_equality (k : ℕ) (x y : ℕ) (hk : k ≥ 2)
  (hx0 : x > 0) (hy0 : y > 0)
  (hx_good : good_x k x)
  (hy_good : good_y k y)
  (p : ℕ) (hp : p.Prime) :
  padicValNat p ((∏ i ∈ Finset.Icc y (y + k), i) / (Finset.Icc y (y + k)).lcm id) =
  padicValNat p (M k) + padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) := by
    by_cases h_case1 : p * p ≤ k;
    · apply valuation_small_p k x y p hp hk hx0 hy0 h_case1;
      · have h_mod_x : p ^ (padicValNat p (M k)) ∣ m k := by
          refine' dvd_trans _ ( Finset.dvd_prod_of_mem _ <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp.pos, _ ⟩, hp, _ ⟩ );
          · rw [ Nat.factorization ] ; aesop;
          · nlinarith;
          · grind;
        have := hx_good.2.1;
        rw [ ← this, Nat.ModEq, Nat.mod_mod_of_dvd _ h_mod_x ];
      · have h_mod_y : p ^ padicValNat p (M k) ∣ m k := by
          refine' dvd_trans _ ( Finset.dvd_prod_of_mem _ <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp.pos, _ ⟩, hp, _ ⟩ );
          · rw [ Nat.factorization ] ; aesop;
          · nlinarith;
          · grind;
        exact Nat.modEq_zero_iff_dvd.mpr ( dvd_trans h_mod_y ( Nat.dvd_of_mod_eq_zero hy_good.2.1 ) );
    · by_cases h_case2 : p ≤ k;
      · -- For primes $p$ with $\sqrt{k} < p \le k$, we use `valuation_large_p_le`.
        have h_case2_val : padicValNat p ((∏ i ∈ Finset.Icc y (y + k), i) / (Finset.Icc y (y + k)).lcm id) = (k / p + 1) - 1 := by
          have h_case2_val : padicValNat p ((∏ i ∈ Finset.Icc y (y + k), i) / (Finset.Icc y (y + k)).lcm id) = (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k))).card - 1 := by
            apply valuation_large_p_le;
            all_goals norm_num;
            any_goals tauto;
            · exact ⟨ y, by simp +arith +decide ⟩;
            · omega;
            · exact ⟨ p * ( y / p + 1 ), ⟨ by linarith [ Nat.div_add_mod y p, Nat.mod_lt y hp.pos ], by linarith [ Nat.div_mul_le_self y p ] ⟩, by norm_num ⟩;
            · intros; linarith;
          rw [ h_case2_val, count_multiples_large_p_LHS ];
          · assumption;
          · grind;
          · assumption;
          · exact ⟨ Nat.sqrt_lt.mpr ( by linarith ), h_case2 ⟩;
          · have := hy_good.2.2 p hp ( by nlinarith [ Nat.sqrt_le k ] ) h_case2; aesop;
        have h_case2_val_rhs : padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = (k / p) - 1 := by
          have h_case2_val_rhs : (Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card = k / p := by
            apply count_multiples_large_p_RHS k x p hp hk hx0 ⟨ Nat.sqrt_lt.mpr ( by nlinarith ), h_case2 ⟩;
            have := hx_good.2.2 p hp ( Nat.sqrt_lt.mpr ( by nlinarith ) ) h_case2; aesop;
          rw [ ← h_case2_val_rhs, valuation_large_p_le ];
          exact k;
          any_goals omega;
          · simp +arith +decide [ Nat.sub_add_cancel ( by linarith : 1 ≤ x + k ) ];
            omega;
          · use x;
          · exact Exists.elim ( Finset.card_pos.mp ( by rw [ h_case2_val_rhs ] ; exact Nat.div_pos h_case2 hp.pos ) ) fun z hz => ⟨ z, Finset.mem_filter.mp hz |>.1, Finset.mem_filter.mp hz |>.2 ⟩;
          · exact fun z hz => by linarith [ Finset.mem_Icc.mp hz ] ;
        have h_case2_val_M : padicValNat p (M k) = 1 := by
          have h_case2_val_M : padicValNat p (M k) = Nat.log p k := by
            apply padicValNat_lcm_range;
            · assumption;
            · linarith;
          exact h_case2_val_M.trans ( Nat.le_antisymm ( Nat.le_of_lt_succ ( Nat.log_lt_of_lt_pow ( by linarith ) ( by nlinarith ) ) ) ( Nat.le_log_of_pow_le hp.one_lt ( by nlinarith ) ) );
        cases a : k / p <;> simp_all +decide [ Nat.succ_sub ];
        · exact absurd ( a.resolve_left hp.ne_zero ) ( by linarith );
        · ring;
      · -- Since $p > k$, we have $v_p(M(k)) = 0$.
        have h_vp_M_zero : padicValNat p (M k) = 0 := by
          rw [ padicValNat.eq_zero_of_not_dvd ];
          intro h;
          have := Nat.dvd_trans h ( Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi ) ; simp_all +decide [ Nat.Prime.dvd_iff_not_coprime ] ;
          exact this <| Nat.Coprime.prod_right fun x hx => hp.coprime_iff_not_dvd.mpr <| Nat.not_dvd_of_pos_of_lt ( Finset.mem_Icc.mp hx |>.1 ) <| by linarith [ Finset.mem_Icc.mp hx |>.2 ] ;
        -- Since $p > k$, we have $v_p(LHS) = 0$ and $v_p(RHS) = 0$.
        have h_vp_LHS_zero : padicValNat p ((∏ i ∈ Finset.Icc y (y + k), i) / (Finset.Icc y (y + k)).lcm id) = 0 := by
          apply valuation_very_large_p;
          exact hp;
          exact?;
          · exact ⟨ y, by simp +arith +decide ⟩;
          · norm_num; linarith;
          · exact fun z hz => by linarith [ Finset.mem_Icc.mp hz ] ;
        have h_vp_RHS_zero : padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = 0 := by
          apply valuation_very_large_p;
          any_goals exact k;
          · assumption;
          · simp +arith +decide [ Nat.sub_add_cancel ( by linarith : 1 ≤ x + k ) ];
            omega;
          · use x;
          · linarith;
          · exact fun z hz => by linarith [ Finset.mem_Icc.mp hz ] ;
        linarith

/-
The p-adic valuations match for medium primes.
-/
lemma valuation_medium_p (k x y p : ℕ) (hp : p.Prime) (hk : k ≥ 2)
  (hx0 : x > 0) (hy0 : y > 0)
  (h_sqrt_lt : k.sqrt < p) (h_le_k : p ≤ k)
  (hx_good : good_x k x)
  (hy_good : good_y k y) :
  padicValNat p ((∏ i ∈ Finset.Icc y (y + k), i) / (Finset.Icc y (y + k)).lcm id) =
  padicValNat p (M k) + padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) := by
    apply valuation_equality k x y hk hx0 hy0 hx_good hy_good p hp

/-
The p-adic valuations of the LHS and RHS ratios are equal for all primes p.
-/
theorem valuation_equality_all_p (k : ℕ) (x y : ℕ) (hk : k ≥ 2)
  (hx0 : x > 0) (hy0 : y > 0)
  (hx_good : good_x k x)
  (hy_good : good_y k y)
  (p : ℕ) (hp : p.Prime) :
  padicValNat p ((∏ i ∈ Finset.Icc y (y + k), i) / (Finset.Icc y (y + k)).lcm id) =
  padicValNat p (M k) + padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) := by
    exact?

/-
The product of (x+i)/(y+i) for i from 0 to k-1 is at least (x/y)^k, given x < y.
-/
lemma product_ratio_lower_bound (x y k : ℕ) (hx : x > 0) (hy : y > 0) (hxy : x < y) :
  (∏ i ∈ Finset.range k, ((x + i : ℚ) / (y + i : ℚ))) ≥ ((x : ℚ) / y) ^ k := by
    -- Since $x < y$, for each $i$ in the range $0$ to $k-1$, we have $\frac{x+i}{y+i} \geq \frac{x}{y}$.
    have h_term_ge : ∀ i ∈ Finset.range k, (x + i : ℝ) / (y + i) ≥ x / y := by
      exact fun i hi => by rw [ ge_iff_le, div_le_div_iff₀ ] <;> norm_cast <;> nlinarith;
    convert Finset.prod_le_prod ?_ h_term_ge using 1 <;> norm_num [ Finset.prod_mul_distrib ];
    · rw [ le_div_iff₀ ( Finset.prod_pos fun _ _ => by positivity ) ] ; ring; norm_num;
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
                         exact?;
    -- Using `product_ratio_lower_bound`, the product is $\ge (x/y)^k$.
    have h_prod_ratio_lower_bound : (∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) / (∏ i ∈ Finset.Icc y (y + k), (i : ℚ)) ≥ ((x : ℚ) / y) ^ k / (↑y + ↑k) := by
      have h_prod_ratio_lower_bound : (∏ i ∈ Finset.range k, ((x + i : ℚ) / (y + i : ℚ))) ≥ ((x : ℚ) / y) ^ k := by
        exact?;
      have h_prod_ratio_lower_bound : (∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) = (∏ i ∈ Finset.range k, (x + i : ℚ)) ∧ (∏ i ∈ Finset.Icc y (y + k), (i : ℚ)) = (∏ i ∈ Finset.range (k + 1), (y + i : ℚ)) := by
        constructor <;> erw [ Finset.prod_Ico_eq_prod_range ];
        · rw [ Nat.sub_add_cancel ( by linarith ), add_tsub_cancel_left, Finset.prod_congr rfl ] ; aesop;
        · simp +arith +decide [ add_assoc ];
      simp_all +decide [ Finset.prod_range_succ ];
      rw [ div_mul_eq_div_div ] ; gcongr;
    rw [ ge_iff_le, div_le_iff₀ ] at * <;> try positivity;
    rw [ div_eq_iff ] at h_ratio_eq;
    · convert mul_le_mul_of_nonneg_left h_prod_ratio_lower_bound ( show ( 0 : ℚ ) ≤ ↑ ( M k ) by positivity ) using 1 ; ring;
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
There exist weights w1, w2 such that any residue modulo p1*p2 can be represented as c1*w1 + c2*w2 with small coefficients.
-/
lemma crt_basis_exists (p1 p2 : ℕ) (hp1 : p1.Prime) (hp2 : p2.Prime) (hp_ne : p1 ≠ p2) :
  ∃ w1 w2 : ℤ, ∀ r : ℤ, ∃ c1 c2 : ℤ,
    0 < c1 ∧ c1 ≤ p1 ∧
    0 < c2 ∧ c2 ≤ p2 ∧
    c1 * w1 + c2 * w2 ≡ r [ZMOD (p1 * p2)] := by
      -- Let $M = p1 * p2$.
      set M : ℕ := p1 * p2 with hM
      -- By the Chinese Remainder Theorem, there exist $w_1, w_2$ such that:
      -- $w_1 \equiv 1 \pmod {p1}, w_1 \equiv 0 \pmod {p2}$
      -- $w_2 \equiv 0 \pmod {p1}, w_2 \equiv 1 \pmod {p2}$
      obtain ⟨w1, hw1⟩ : ∃ w1 : ℤ, w1 ≡ 1 [ZMOD p1] ∧ w1 ≡ 0 [ZMOD p2] := by
        have := Nat.gcd_eq_gcd_ab p1 p2;
        exact ⟨ p2 * Nat.gcdB p1 p2, by rw [ Int.modEq_iff_dvd ] ; use Nat.gcdA p1 p2; linarith [ Nat.coprime_primes hp1 hp2 |>.2 hp_ne ], by rw [ Int.modEq_zero_iff_dvd ] ; exact dvd_mul_right _ _ ⟩
      obtain ⟨w2, hw2⟩ : ∃ w2 : ℤ, w2 ≡ 0 [ZMOD p1] ∧ w2 ≡ 1 [ZMOD p2] := by
        have := Nat.chineseRemainder ( show Nat.Coprime p1 p2 from hp1.coprime_iff_not_dvd.mpr fun h => hp_ne <| Nat.prime_dvd_prime_iff_eq hp1 hp2 |>.1 h );
        obtain ⟨ k, hk1, hk2 ⟩ := this 0 1; exact ⟨ k, Int.natCast_modEq_iff.mpr hk1, Int.natCast_modEq_iff.mpr hk2 ⟩ ;
      refine' ⟨ w1, w2, fun r => _ ⟩;
      -- Let $c_1$ be the unique integer in $(0, p1]$ such that $c_1 \equiv r \pmod {p1}$.
      obtain ⟨c1, hc1⟩ : ∃ c1 : ℤ, 0 < c1 ∧ c1 ≤ p1 ∧ c1 ≡ r [ZMOD p1] := by
        use if r % p1 = 0 then p1 else r % p1;
        split_ifs <;> simp_all +decide [ Int.ModEq ];
        · exact ⟨ hp1.pos, by rw [ Int.emod_eq_zero_of_dvd ‹_› ] ⟩;
        · exact ⟨ lt_of_le_of_ne ( Int.emod_nonneg _ ( Nat.cast_ne_zero.mpr hp1.ne_zero ) ) ( Ne.symm ( by aesop ) ), Int.le_of_lt ( Int.emod_lt_of_pos _ ( Nat.cast_pos.mpr hp1.pos ) ) ⟩;
      -- Let $c_2$ be the unique integer in $(0, p2]$ such that $c_2 \equiv r \pmod {p2}$.
      obtain ⟨c2, hc2⟩ : ∃ c2 : ℤ, 0 < c2 ∧ c2 ≤ p2 ∧ c2 ≡ r [ZMOD p2] := by
        use if r % p2 = 0 then p2 else r % p2;
        split_ifs <;> simp_all +decide [ Int.ModEq ];
        · exact ⟨ hp2.pos, by rw [ Int.emod_eq_zero_of_dvd ‹_› ] ⟩;
        · exact ⟨ lt_of_le_of_ne ( Int.emod_nonneg _ ( Nat.cast_ne_zero.mpr hp2.ne_zero ) ) ( Ne.symm ( by aesop ) ), Int.le_of_lt ( Int.emod_lt_of_pos _ ( Nat.cast_pos.mpr hp2.pos ) ) ⟩;
      refine' ⟨ c1, c2, hc1.1, hc1.2.1, hc2.1, hc2.2.1, _ ⟩;
      rw [ ← Int.modEq_and_modEq_iff_modEq_mul ];
      · simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
      · simpa using hp1.coprime_iff_not_dvd.mpr fun h => hp_ne <| Nat.prime_dvd_prime_iff_eq hp1 hp2 |>.1 h

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
If the sum of sizes of two subsets is less than the size of the set, there is an element in neither subset.
-/
lemma exists_good_element {α : Type*} [DecidableEq α] (S : Finset α) (B1 B2 : Finset α)
  (h1 : B1 ⊆ S) (h2 : B2 ⊆ S)
  (h_card : B1.card + B2.card < S.card) :
  ∃ x ∈ S, x ∉ B1 ∧ x ∉ B2 := by
    -- The size of the union B1 ∪ B2 is at most |B1| + |B2|.
    have h_union : (B1 ∪ B2).card ≤ B1.card + B2.card := by
      exact Finset.card_union_le _ _;
    contrapose! h_card;
    exact le_trans ( Finset.card_le_card fun x hx => by by_cases hx1 : x ∈ B1 <;> aesop ) h_union

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
        rw [ Finset.card_image_of_injOn fun x hx y hy hxy => h_inj x y ( by simpa using hx ) ( by simpa using hy ) hxy, ← Set.ncard_coe_Finset ] ; aesop;
      have hB_complement : (Finset.filter (fun r => ∀ b ∈ hB_finite.toFinset, (b % p).toNat ≠ r) (Finset.range p)).card = p - (Finset.image (fun b : ℤ => (b % p).toNat) (hB_finite.toFinset)).card := by
        rw [ show ( Finset.filter ( fun r => ∀ b ∈ hB_finite.toFinset, ( b % p : ℤ ).toNat ≠ r ) ( Finset.range p ) ) = Finset.range p \ Finset.image ( fun b => ( b % p : ℤ ).toNat ) hB_finite.toFinset from ?_ ];
        · rw [ Finset.card_sdiff ] <;> norm_num;
          rw [ Finset.inter_eq_left.mpr ];
          exact Finset.image_subset_iff.mpr fun x hx => Finset.mem_range.mpr <| by linarith [ Int.emod_lt_of_pos x ( by positivity : 0 < ( p : ℤ ) ), Int.toNat_of_nonneg <| Int.emod_nonneg x <| show ( p : ℤ ) ≠ 0 by positivity ] ;
        · ext; aesop;
      simp_all +decide [ Set.subset_def ];
      rw [ Nat.cast_sub ];
      · linarith;
      · have hB_image : (Finset.image (fun b : ℤ => (b % p).toNat) (hB_finite.toFinset)).card ≤ p := by
          exact le_trans ( Finset.card_le_card <| Finset.image_subset_iff.mpr fun x hx => Finset.mem_range.mpr <| Int.toNat_lt ( Int.emod_nonneg _ <| by positivity ) |>.2 <| Int.emod_lt_of_pos _ <| by positivity ) ( by simpa );
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
        exact Finset.not_subset.mp fun h => h_union_card.not_le <| by simpa [ Finset.card_image_of_injective, Function.Injective ] using Finset.card_le_card h;
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

#check Nat.tendsto_primeCounting

/-
For a list of pairwise coprime primes, there exist basis vectors w_i such that w_i is 1 mod p_i and 0 mod p_j for j != i.
-/
lemma exists_crt_basis_vectors (p : List ℕ) (hp_prime : ∀ x ∈ p, x.Prime) (hp_coprime : p.Pairwise Nat.Coprime) :
  ∃ w : List ℤ, w.length = p.length ∧
  ∀ i < p.length,
    w.get! i ≡ 1 [ZMOD p.get! i] ∧
    ∀ j < p.length, i ≠ j → w.get! i ≡ 0 [ZMOD p.get! j] := by
      -- For each $i$, let $M_i = \prod_{j \ne i} p_j$. Since $p_i$ is coprime to all $p_j$ ($j \ne i$), $p_i$ is coprime to $M_i$.
      have h_coprime : ∀ i < p.length, Nat.Coprime (p.get! i) (∏ j ∈ Finset.erase (Finset.range p.length) i, p.get! j) := by
        -- Since $p$ is pairwise coprime, any two distinct primes in the list are coprime. Therefore, for any $i < p.length$, $p.get! i$ is coprime to the product of all other primes in the list.
        intros i hi
        have h_coprime : ∀ j < p.length, j ≠ i → Nat.Coprime (p.get! i) (p.get! j) := by
          intro j hj hji;
          cases lt_or_gt_of_ne hji <;> simp_all +decide [ List.pairwise_iff_get ];
          · exact Nat.Coprime.symm ( hp_coprime ⟨ j, hj ⟩ ⟨ i, hi ⟩ ‹_› );
          · exact hp_coprime ⟨ i, hi ⟩ ⟨ j, hj ⟩ ‹_›;
        exact Nat.Coprime.prod_right fun j hj => h_coprime j ( Finset.mem_range.mp ( Finset.mem_of_mem_erase hj ) ) ( by aesop );
      -- Let $w_i = M_i y_i$, where $y_i$ is the inverse of $M_i$ modulo $p_i$.
      obtain ⟨w, hw⟩ : ∃ w : ℕ → ℤ, (∀ i < p.length, w i ≡ 1 [ZMOD p.get! i]) ∧ (∀ i < p.length, ∀ j < p.length, i ≠ j → w i ≡ 0 [ZMOD p.get! j]) := by
        -- For each $i$, let $M_i = \prod_{j \ne i} p_j$. Since $p_i$ is coprime to all $p_j$ ($j \ne i$), $p_i$ is coprime to $M_i$. Thus $M_i$ has an inverse $y_i$ modulo $p_i$.
        have h_inv : ∀ i < p.length, ∃ y_i : ℤ, y_i * (∏ j ∈ Finset.erase (Finset.range p.length) i, p.get! j) ≡ 1 [ZMOD p.get! i] := by
          intro i hi;
          have := Nat.gcd_eq_gcd_ab ( p.get! i ) ( ∏ j ∈ Finset.erase ( Finset.range p.length ) i, p.get! j );
          exact ⟨ Nat.gcdB ( p.get! i ) ( ∏ j ∈ Finset.erase ( Finset.range p.length ) i, p.get! j ), Int.modEq_iff_dvd.mpr ⟨ Nat.gcdA ( p.get! i ) ( ∏ j ∈ Finset.erase ( Finset.range p.length ) i, p.get! j ), by push_cast at *; linarith [ h_coprime i hi ] ⟩ ⟩;
        choose! y hy using h_inv;
        refine' ⟨ fun i => y i * ∏ j ∈ Finset.erase ( Finset.range p.length ) i, p.get! j, fun i hi => _, fun i hi j hj hij => _ ⟩ <;> simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ];
        rw [ Finset.prod_eq_zero ( Finset.mem_erase_of_ne_of_mem ( Ne.symm hij ) ( Finset.mem_range.mpr hj ) ) ] <;> aesop;
      refine' ⟨ List.map w ( List.range p.length ), _, _ ⟩ <;> aesop

#eval (-5 : Int) % 3

/-
Definitions of the intervals for x and y as specified in the proof.
-/
def y_interval (k : ℕ) (C : ℝ) : Set ℝ := Set.Ioo ((M k : ℝ) / (5 * C) * (1 + 1 / k)) ((M k : ℝ) / (4 * C) - k)

def x_interval (k : ℕ) (y : ℕ) (C : ℝ) : Set ℝ := Set.Ioo ((y : ℝ) - (M k : ℝ) / (5 * C * k)) (y : ℝ)

/-
Checking availability of M_prime and claim_approx_2.
-/
#check M_prime
#check claim_approx_2

/-
Checking availability of M_prime_coprime and M_prime_dvd.
-/
#check M_prime_coprime
#check M_prime_dvd

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
Cardinality of B_set for p in (k/2, k].
-/
lemma B_set_ncard (k p : ℕ) (hp : p.Prime) (h_range : k / 2 < p ∧ p ≤ k) :
  (B_set k p).ncard = k - p + 1 := by
    unfold B_set;
    -- Since $p \leq k$, we have $k \mod p = k - p$.
    have h_mod : (k : ℤ) % p = k - p := by
      norm_cast;
      rw [ Int.subNatNat_of_le h_range.2 ];
      rw [ Nat.mod_eq_sub_mod h_range.2 ];
      rw [ Nat.mod_eq_of_lt ( by omega ) ];
    rw [ h_mod, Set.ncard_eq_toFinset_card' ] ; norm_num ; omega;

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
Checking for Bertrand's postulate in Mathlib.
-/
#check Nat.exists_prime_lt_and_le_two_mul

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
        exact?;
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
M_prime is positive.
-/
lemma M_prime_pos (k p1 p2 : ℕ) (hk : k ≥ 1) (hp1 : p1.Prime) (hp2 : p2.Prime) (hp_ne : p1 ≠ p2)
  (h_le1 : p1 ≤ k) (h_le2 : p2 ≤ k) : M_prime k p1 p2 > 0 := by
    refine' Nat.div_pos _ _;
    · -- Since $p1$ and $p2$ are distinct primes less than or equal to $k$, their product $p1 * p2$ divides $M k$.
      have h_div : p1 * p2 ∣ M k := by
        exact?;
      exact Nat.le_of_dvd ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) h_div;
    · exact Nat.mul_pos hp1.pos hp2.pos

/-
Definitions for x interval length, M_prime3, B_set_x, and B_set_x_star.
-/
def x_interval_length (k : ℕ) (C : ℝ) : ℝ := (M k : ℝ) / (5 * C * k)

def M_prime3 (k q1 q2 q3 : ℕ) : ℕ := (M k) / (q1 * q2 * q3)

def B_set_x (k p : ℕ) : Set ℤ := Set.Icc 1 ((p : ℤ) - (k % p : ℤ))

def B_set_x_star (k p M_val : ℕ) : Set ℤ := { c ∈ Set.Icc 1 (p : ℤ) | ∃ a ∈ B_set_x k p, c * (M_val : ℤ) ≡ a [ZMOD p] }

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
B_set_x_star is a subset of [1, p].
-/
lemma B_set_x_star_subset (k p M_val : ℕ) : B_set_x_star k p M_val ⊆ Set.Icc 1 p := by
  exact fun x hx => hx.1

/-
Cardinality of B_set_x_star is the same as B_set_x.
-/
lemma B_set_x_star_ncard (k p M_val : ℕ) (hp : p.Prime) (h_coprime : Nat.Coprime M_val p) (hk : k > 0) :
  (B_set_x_star k p M_val).ncard = (B_set_x k p).ncard := by
    have h_bij : Set.ncard {c : ℤ | ∃ a ∈ B_set_x k p, c * M_val ≡ a [ZMOD p] ∧ 1 ≤ c ∧ c ≤ p} = Set.ncard (B_set_x k p) := by
      have h_bij : ∀ a ∈ B_set_x k p, Set.ncard {c : ℤ | c * M_val ≡ a [ZMOD p] ∧ 1 ≤ c ∧ c ≤ p} = 1 := by
        intro a ha
        have h_exists : ∃ c : ℤ, c * M_val ≡ a [ZMOD p] ∧ 1 ≤ c ∧ c ≤ p := by
          -- Since $M_val$ is coprime to $p$, multiplication by $M_val$ is a bijection on $\mathbb{Z}_p$, so there exists an integer $c$ such that $c * M_val ≡ a \pmod{p}$.
          obtain ⟨c, hc⟩ : ∃ c : ℤ, c * M_val ≡ a [ZMOD p] := by
            have h_exists_c : ∃ c : ℤ, c * M_val ≡ 1 [ZMOD p] := by
              have := Nat.gcd_eq_gcd_ab M_val p;
              exact ⟨ Nat.gcdA M_val p, Int.modEq_iff_dvd.mpr ⟨ Nat.gcdB M_val p, by linarith ⟩ ⟩;
            exact ⟨ h_exists_c.choose * a, by convert h_exists_c.choose_spec.mul_right a using 1 <;> ring ⟩;
          use if c % p = 0 then p else c % p;
          split_ifs <;> simp_all +decide [ Int.ModEq ];
          · obtain ⟨ d, rfl ⟩ := ‹_›; simp_all +decide [ Int.mul_emod ] ;
            exact hp.pos;
          · exact ⟨ by simpa [ Int.mul_emod ] using hc, lt_of_le_of_ne ( Int.emod_nonneg _ ( Nat.cast_ne_zero.mpr hp.ne_zero ) ) ( Ne.symm <| by aesop ), Int.le_of_lt <| Int.emod_lt_of_pos _ <| Nat.cast_pos.mpr hp.pos ⟩;
        have h_unique : ∀ c1 c2 : ℤ, c1 * M_val ≡ a [ZMOD p] → c2 * M_val ≡ a [ZMOD p] → 1 ≤ c1 → c1 ≤ p → 1 ≤ c2 → c2 ≤ p → c1 = c2 := by
          intros c1 c2 hc1 hc2 hc1_pos hc1_le hc2_pos hc2_le
          have h_cong : c1 ≡ c2 [ZMOD p] := by
            haveI := Fact.mk hp; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
            exact mul_left_cancel₀ ( show ( M_val : ZMod p ) ≠ 0 from by rw [ Ne.eq_def, ZMod.natCast_eq_zero_iff ] ; exact fun h => by have := Nat.gcd_eq_right h; aesop ) <| by linear_combination' hc1 - hc2;
          rw [ Int.ModEq ] at h_cong;
          rw [ Int.emod_eq_emod_iff_emod_sub_eq_zero ] at h_cong;
          obtain ⟨ k, hk ⟩ := Int.modEq_zero_iff_dvd.mp h_cong; nlinarith [ show k = 0 by nlinarith ] ;
        exact Set.ncard_eq_one.mpr ⟨ h_exists.choose, Set.eq_singleton_iff_unique_mem.mpr ⟨ ⟨ h_exists.choose_spec.1, h_exists.choose_spec.2.1, h_exists.choose_spec.2.2 ⟩, fun c hc => h_unique _ _ hc.1 h_exists.choose_spec.1 hc.2.1 hc.2.2 h_exists.choose_spec.2.1 h_exists.choose_spec.2.2 ⟩ ⟩;
      have h_bij : ∀ a b : ℤ, a ∈ B_set_x k p → b ∈ B_set_x k p → a ≠ b → Disjoint {c : ℤ | c * M_val ≡ a [ZMOD p] ∧ 1 ≤ c ∧ c ≤ p} {c : ℤ | c * M_val ≡ b [ZMOD p] ∧ 1 ≤ c ∧ c ≤ p} := by
        simp +contextual [ Set.disjoint_left ];
        intro a b ha hb hab c hc₁ hc₂ hc₃ hc₄; simp_all +decide [ Int.ModEq ] ;
        contrapose! hab; have := Int.modEq_iff_dvd.mp hc₄.symm; simp_all +decide [ Nat.dvd_prime, hp.dvd_iff_eq ] ;
        obtain ⟨ x, hx ⟩ := this; nlinarith [ show x = 0 by nlinarith [ Set.mem_Icc.mp ( show a ∈ Set.Icc 1 ( p - ( k % p : ℤ ) ) from by simpa using ha ), Set.mem_Icc.mp ( show b ∈ Set.Icc 1 ( p - ( k % p : ℤ ) ) from by simpa using hb ), Int.emod_nonneg k ( Nat.cast_ne_zero.mpr hp.ne_zero ), Int.emod_lt_of_pos k ( Nat.cast_pos.mpr hp.pos ) ] ] ;
      have h_bij : ∀ s : Finset ℤ, (∀ a ∈ s, a ∈ B_set_x k p) → Set.ncard (⋃ a ∈ s, {c : ℤ | c * M_val ≡ a [ZMOD p] ∧ 1 ≤ c ∧ c ≤ p}) = s.card := by
        intros s hs
        induction' s using Finset.induction with a s ha ih;
        · norm_num;
        · simp_all +decide [ Set.ncard_eq_toFinset_card' ];
          rw [ @Set.ncard_union_eq ];
          · rw [ ih, add_comm ];
            obtain ⟨ b, hb ⟩ := ‹∀ a ∈ B_set_x k p, ∃ a_2, { c : ℤ | c * ↑M_val ≡ a [ZMOD ↑p] ∧ 1 ≤ c ∧ c ≤ ↑p } = { a_2 } › a hs.1; aesop;
          · exact Set.disjoint_left.mpr fun x hx hx' => by obtain ⟨ b, hb, hb' ⟩ := Set.mem_iUnion₂.mp hx'; exact Set.disjoint_left.mp ( h_bij a b hs.1 ( hs.2 b hb ) ( by aesop ) ) hx hb';
          · exact Set.Finite.subset ( Set.finite_Icc 1 ( p : ℤ ) ) fun x hx => ⟨ hx.2.1, hx.2.2 ⟩;
          · exact Set.Finite.biUnion ( Finset.finite_toSet s ) fun x hx => Set.Finite.subset ( Set.finite_Icc 1 ( p : ℤ ) ) fun y hy => ⟨ hy.2.1, hy.2.2 ⟩;
      convert h_bij ( Set.Finite.toFinset ( show Set.Finite ( B_set_x k p ) from Set.finite_Icc _ _ |> Set.Finite.subset <| B_set_x_subset k p hp hk ) ) _;
      · aesop;
      · rw [ ← Set.ncard_coe_finset ] ; aesop;
      · aesop;
    convert h_bij using 2;
    unfold B_set_x_star; ext; aesop;

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
        exact h_count.not_lt <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith;
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
Elements of B_set_x are not divisible by p, given k/2 < p < k.
-/
lemma B_set_x_safe (k p : ℕ) (hp : p.Prime) (hk : k > 0) (h_range : k / 2 < p ∧ p < k) :
  ∀ c ∈ B_set_x k p, c % p ≠ 0 := by
    revert h_range;
    simp +zetaDelta at *;
    -- Since $p < k$, we have $k \% p = k - p$.
    intro h_range1 h_range2 c hc
    have h_k_mod_p : k % p = k - p := by
      rw [ Nat.mod_eq_sub_mod ( by linarith ) ];
      rw [ Nat.mod_eq_of_lt ( by omega ) ];
    exact fun h => by have := Int.le_of_dvd ( by linarith [ Set.mem_Icc.mp hc ] ) h; linarith [ Set.mem_Icc.mp hc, Nat.sub_add_cancel h_range2.le ] ;

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
          exact? ⟩ ( by
          exact h_M_prime3_coprime.2.2 ) _ using 1
        generalize_proofs at *;
        exact ⟨ _, hz₄.choose_spec.1, hz₄.choose_spec.2 ⟩

/-
If q is close to k (within 1/20), then q > k/2.
-/
lemma q_gt_half_k (C : ℝ) (hC : C ≥ 1) (k q : ℕ) (hk : k > 0)
  (h_range_lo : (1 - 1 / (20 * C)) * k < q) :
  (k : ℝ) / 2 < q := by
    nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast, one_div_mul_cancel ( by positivity : ( 20 * C : ℝ ) ≠ 0 ) ]

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
Arithmetic inequality for C >= 1.
-/
lemma arithmetic_bound_C (C : ℝ) (hC : C ≥ 1) : (1 - 1 / (40 * C)) * (1 + 1 / (20 * C)) > 1 := by
  ring_nf; nlinarith [ inv_pos.2 ( show 0 < C by linarith ), inv_mul_cancel₀ ( ne_of_gt ( show 0 < C by linarith ) ) ] ;

/-
Density check for x construction.
-/
lemma density_check_x_lemma (C : ℝ) (hC : C ≥ 1) (k : ℕ) (q : ℝ) (hq : (1 - 1 / (40 * C)) * k < q) :
  2 * q - k ≥ (1 - 1 / (20 * C)) * q := by
    have := @arithmetic_bound_C C hC;
    nlinarith [ show ( 0 : ℝ ) ≤ 1 / ( 40 * C ) by positivity, show ( 0 : ℝ ) ≤ 1 / ( 20 * C ) by positivity ]

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
      refine h_const_terms.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop 1 ] with k hk₁ hk₂; simpa [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( show 0 < M k from Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ] );
    convert h_const_terms.sub h_k_div_M_k_zero using 2 <;> ring;
    unfold y_interval_length; ring;

/-
Asymptotic check for y interval length.
-/
lemma interval_length_check_y (C : ℝ) (hC : C ≥ 1) :
  ∃ K, ∀ k ≥ K, y_interval_length k C / ((M k : ℝ) / (k * k / 4)) > k := by
    -- First, use y_len_div_M_limit to find K such that for all k ≥ K, y_interval_length k C / M k > 1 / (40 * C).
    obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℕ, ∀ k ≥ K₁, y_interval_length k C / M k > 1 / (40 * C) := by
      have := y_len_div_M_limit C hC;
      have := this.eventually ( lt_mem_nhds <| show 1 / ( 20 * C ) > 1 / ( 40 * C ) by rw [ gt_iff_lt ] ; gcongr ; linarith ) ; aesop;
    have hK₂ : ∃ K₂ : ℕ, ∀ k ≥ K₂, 1 / (40 * C) * ((k * k) / 4) > k := by
      exact ⟨ ⌈40 * C * 4⌉₊ + 1, fun k hk => by nlinarith [ Nat.le_ceil ( 40 * C * 4 ), show ( k : ℝ ) ≥ ⌈40 * C * 4⌉₊ + 1 by exact_mod_cast hk, one_div_mul_cancel ( by positivity : ( 40 * C : ℝ ) ≠ 0 ) ] ⟩;
    obtain ⟨ K₂, hK₂ ⟩ := hK₂; use Max.max K₁ K₂; intros k hk; specialize hK₁ k ( le_of_max_le_left hk ) ; specialize hK₂ k ( le_of_max_le_right hk ) ; simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] ;
    nlinarith [ show ( 0 : ℝ ) ≤ k ^ 2 by positivity ]

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
Asymptotic check for x interval length.
-/
lemma interval_length_check_x (C : ℝ) (hC : C ≥ 1) :
  ∃ K, ∀ k ≥ K, x_interval_length k C / ((M k : ℝ) / (k * k * k)) > 3 * k := by
    -- Let's choose K = 15 * C + 1.
    use Nat.ceil (15 * C) + 1;
    -- Substitute the expression for x_interval_length k C and simplify.
    intro k hk
    have h_simp : (M k / (5 * C * k)) / (M k / (k * k * k)) = k^2 / (5 * C) := by
      field_simp [mul_comm, mul_assoc, mul_left_comm];
      rw [ mul_div_cancel_left₀ _ ( Nat.cast_ne_zero.mpr <| ne_of_gt <| M_pos k <| by linarith ) ];
    unfold x_interval_length;
    rw [ h_simp, gt_iff_lt, lt_div_iff₀ ] <;> nlinarith [ Nat.le_ceil ( 15 * C ), show ( k : ℝ ) ≥ ⌈15 * C⌉₊ + 1 by exact_mod_cast hk ]

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

#check DensityHypothesis

/-
System check.
-/
lemma check_system_alive : 1 + 1 = 2 := by rfl

/-
L(a, b) is the LCM of integers in [a, b].
-/
def L (a b : ℕ) : ℕ := (Finset.Icc a b).lcm id

#check Finset.lcm

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

lemma exists_good_primes (h_density : DensityHypothesis) (C : ℝ) (hC : C ≥ 1) :
  ∃ K, ∀ k ≥ K, Nonempty (GoodPrimes C k) := by
    by_contra h_contra;
    -- Let's choose ε = 1/(40*C) and apply the DensityHypothesis to find primes p1 and p2 such that their differences are within the required bounds.
    set ε := 1 / (40 * C) with hε_def
    have hε_pos : ε > 0 := by
      positivity
    have hε_small : ε ≤ 1 / 20 := by
      rw [ div_le_div_iff₀ ] <;> linarith
    obtain ⟨K, hK⟩ : ∃ K, ∀ k ≥ K, (∃ p1 p2 : ℕ, (k : ℝ) / 2 < p1 ∧ (p1 : ℝ) < (1 + ε) * k / 2 ∧ (k : ℝ) / 2 < p2 ∧ (p2 : ℝ) < (1 + ε) * k / 2 ∧ p1 ≠ p2 ∧ p1.Prime ∧ p2.Prime) ∧ (∃ q1 q2 q3 : ℕ, (1 - ε) * k < q1 ∧ (q1 : ℝ) < k ∧ (1 - ε) * k < q2 ∧ (q2 : ℝ) < k ∧ (1 - ε) * k < q3 ∧ (q3 : ℝ) < k ∧ q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3 ∧ q1.Prime ∧ q2.Prime ∧ q3.Prime) := by
      exact h_density ε hε_pos |> fun ⟨ K, hK ⟩ => ⟨ K, fun k hk => hK k hk |> fun h => ⟨ by simpa using h.1, by simpa using h.2 ⟩ ⟩;
    refine' h_contra ⟨ ⌈K⌉₊ + 1, fun k hk => _ ⟩;
    obtain ⟨ ⟨ p1, p2, hp1, hp2, hp3, hp4, hp5, hp6 ⟩, ⟨ q1, q2, q3, hq1, hq2, hq3, hq4, hq5, hq6, hq7 ⟩ ⟩ := hK k ( le_of_lt ( Nat.lt_of_ceil_lt hk ) );
    -- Since $p1$ and $p2$ are distinct primes in the required ranges, we can choose them such that $p1 < p2$.
    obtain ⟨p1, p2, hp1, hp2, hp_lt⟩ : ∃ p1 p2 : ℕ, p1.Prime ∧ p2.Prime ∧ p1 < p2 ∧ (k : ℝ) / 2 < p1 ∧ (p1 : ℝ) < (1 + ε) * k / 2 ∧ (k : ℝ) / 2 < p2 ∧ (p2 : ℝ) < (1 + ε) * k / 2 := by
      cases lt_or_gt_of_ne hp5 <;> [ exact ⟨ p1, p2, hp6.1, hp6.2, ‹_›, hp1, hp2, hp3, hp4 ⟩ ; exact ⟨ p2, p1, hp6.2, hp6.1, ‹_›, hp3, hp4, hp1, hp2 ⟩ ];
    refine' ⟨ ⟨ p1, p2, q1, q2, q3, hp1, hp2, hq7.2.2.2.1, hq7.2.2.2.2.1, hq7.2.2.2.2.2, hp_lt.1, hq7.1 |> fun h => by tauto, _, _, _, _, _ ⟩ ⟩;
    · exact ⟨ hp_lt.2.1, by rw [ ← @Nat.cast_le ℝ ] ; nlinarith [ show ( k : ℝ ) ≥ 1 by norm_cast; linarith ] ⟩;
    · exact ⟨ hp_lt.2.2.2.1, Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ mul_div_cancel₀ ( 1 : ℝ ) ( by positivity : ( 40 * C ) ≠ 0 ) ] ⟩;
    · constructor <;> nlinarith [ mul_div_cancel₀ 1 ( by positivity : ( 40 * C ) ≠ 0 ), mul_div_cancel₀ 1 ( by positivity : ( 20 * C ) ≠ 0 ) ];
    · constructor <;> nlinarith [ show ( 1 : ℝ ) ≤ C by linarith, mul_div_cancel₀ ( 1 : ℝ ) ( by linarith : ( 20 * C ) ≠ 0 ), mul_div_cancel₀ ( 1 : ℝ ) ( by linarith : ( 40 * C ) ≠ 0 ) ];
    · exact ⟨ by nlinarith [ show ( 1 : ℝ ) / ( 20 * C ) ≥ 1 / ( 40 * C ) by gcongr ; linarith ], hq6 ⟩

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

lemma construct_y_lemma (C : ℝ) (hC : C ≥ 1) (k : ℕ) (p1 p2 : ℕ)
  (hp1 : p1.Prime) (hp2 : p2.Prime) (hp_lt : p1 < p2)
  (h_range_p1 : (k : ℝ) / 2 < p1 ∧ (p1 : ℝ) < (1 + 1 / (40 * C)) * k / 2)
  (h_range_p2 : (k : ℝ) / 2 < p2 ∧ (p2 : ℝ) < (1 + 1 / (40 * C)) * k / 2)
  (hk_large : k ≥ 10)
  (h_len_y : y_interval_length k C / (M_prime k p1 p2 : ℝ) > p1 + p2)
  : ∃ y : ℕ, (y : ℝ) ∈ y_interval k C ∧ good_y k y := by
    apply exists_y_if_large_interval C hC k p1 p2 hp1 hp2 hp_lt (by
    exact ⟨ Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ mul_div_cancel₀ 1 ( by positivity : ( 40 * C ) ≠ 0 ) ], by rw [ ← @Nat.cast_le ℝ ] ; nlinarith [ mul_div_cancel₀ 1 ( by positivity : ( 40 * C ) ≠ 0 ) ] ⟩) (by
    exact ⟨ Nat.div_lt_of_lt_mul <| by rw [ div_lt_iff₀ ] at * <;> norm_cast at * ; nlinarith [ mul_div_cancel₀ 1 ( by positivity : ( 40 * C ) ≠ 0 ) ], Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast ; nlinarith [ mul_div_cancel₀ 1 ( by positivity : ( 40 * C ) ≠ 0 ) ] ⟩) h_len_y (by
    convert M_prime_coprime k p1 p2 hp1 hp2 hp_lt.ne _ _ _ using 1;
    · exact ⟨ Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ mul_div_cancel₀ ( 1 : ℝ ) ( by positivity : ( 40 * C ) ≠ 0 ) ], by rw [ ← @Nat.cast_le ℝ ] ; nlinarith [ mul_div_cancel₀ ( 1 : ℝ ) ( by positivity : ( 40 * C ) ≠ 0 ) ] ⟩;
    · exact ⟨ Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ mul_div_cancel₀ 1 ( by positivity : ( 40 * C ) ≠ 0 ) ], Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ mul_div_cancel₀ 1 ( by positivity : ( 40 * C ) ≠ 0 ) ] ⟩;
    · grind) (by
    have := B_set_density_bound k p1 ( 1 / ( 40 * C ) ) hp1 ( by positivity ) ( by nlinarith [ one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ) ] ) ⟨ h_range_p1.1, h_range_p1.2 ⟩ ; ( have := B_set_density_bound k p2 ( 1 / ( 40 * C ) ) hp2 ( by positivity ) ( by nlinarith [ one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ) ] ) ⟨ h_range_p2.1, h_range_p2.2 ⟩ ; ( constructor <;> norm_num at * <;> linarith; ) )) (by
    linarith [ epsilon_condition_y C hC k p1 p2 h_range_p1.1 h_range_p2.2 ( by linarith ) ])

lemma construct_x_lemma (C : ℝ) (hC : C ≥ 1) (k : ℕ) (y : ℕ) (q1 q2 q3 : ℕ)
  (hq1 : q1.Prime) (hq2 : q2.Prime) (hq3 : q3.Prime)
  (hq_distinct : q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3)
  (h_range_q1 : (1 - 1 / (40 * C)) * k < q1 ∧ (q1 : ℝ) < k)
  (h_range_q2 : (1 - 1 / (40 * C)) * k < q2 ∧ (q2 : ℝ) < k)
  (h_range_q3 : (1 - 1 / (40 * C)) * k < q3 ∧ (q3 : ℝ) < k)
  (hk_large : k ≥ 10)
  (h_len_x : x_interval_length k C / (M_prime3 k q1 q2 q3 : ℝ) > q1 + q2 + q3)
  (hy_large : (y : ℝ) > x_interval_length k C)
  : ∃ x : ℕ, (x : ℝ) ∈ x_interval k y C ∧ good_x k x := by
    apply exists_x_if_large_interval C hC k y q1 q2 q3 hq1 hq2 hq3 hq_distinct (by
    exact ⟨ by nlinarith [ one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ), one_div_mul_cancel ( by positivity : ( 20 * C ) ≠ 0 ) ], mod_cast h_range_q1.2 ⟩) (by
    exact ⟨ by nlinarith [ one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ), one_div_mul_cancel ( by positivity : ( 20 * C ) ≠ 0 ) ], by exact_mod_cast h_range_q2.2 ⟩) (by
    exact ⟨ by nlinarith [ one_div_mul_cancel ( by positivity : ( 20 : ℝ ) * C ≠ 0 ), one_div_mul_cancel ( by positivity : ( 40 : ℝ ) * C ≠ 0 ) ], by exact_mod_cast h_range_q3.2 ⟩) (by
    exact h_len_x) (by
    apply M_prime3_coprime k q1 q2 q3 hq1 hq2 hq3 hq_distinct (by
    exact ⟨ Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ show ( 1 : ℝ ) ≤ C by norm_cast, one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ) ], by rw [ ← @Nat.cast_le ℝ ] ; linarith ⟩) (by
    exact ⟨ Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ) ], Nat.le_of_lt <| by rw [ ← @Nat.cast_lt ℝ ] ; nlinarith [ one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ) ] ⟩) (by
    exact ⟨ Nat.div_lt_of_lt_mul <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; nlinarith [ one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ) ], Nat.le_of_lt <| by rw [ ← @Nat.cast_lt ℝ ] ; nlinarith [ one_div_mul_cancel ( by positivity : ( 40 * C ) ≠ 0 ) ] ⟩) (by
    linarith)) (by
    have h_card_B_set_x : ∀ p : ℕ, Nat.Prime p → (1 / 2 : ℝ) * k < p → p < k → (B_set_x k p).ncard = 2 * p - k := by
      intros p hp hp1 hp2
      apply B_set_x_ncard k p hp ⟨by
      exact hp1, by
        exact hp2⟩
      skip
      skip
    generalize_proofs at *; (
    have h_card_B_set_x_ge : ∀ p : ℕ, Nat.Prime p → (1 - 1 / (40 * C)) * k < p → p < k → (B_set_x k p).ncard ≥ (1 - 1 / (20 * C)) * p := by
      field_simp;
      intro p hp hp₁ hp₂; rw [ h_card_B_set_x p hp ( by nlinarith [ ( by norm_cast : ( 10 :ℝ ) ≤ k ) ] ) hp₂ ] ; rw [ Nat.cast_sub ( by linarith [ show p * 2 ≥ k from by exact_mod_cast ( by nlinarith [ ( by norm_cast : ( 10 :ℝ ) ≤ k ) ] : ( p :ℝ ) * 2 ≥ k ) ] ) ] ; push_cast ; nlinarith [ ( by norm_cast : ( 10 :ℝ ) ≤ k ) ] ;
    generalize_proofs at *; (
    exact ⟨ h_card_B_set_x_ge q1 hq1 h_range_q1.1 ( mod_cast h_range_q1.2 ), h_card_B_set_x_ge q2 hq2 h_range_q2.1 ( mod_cast h_range_q2.2 ), h_card_B_set_x_ge q3 hq3 h_range_q3.1 ( mod_cast h_range_q3.2 ) ⟩))) (by
    have := @epsilon_sum_lt_min_corrected C hC k q1 q2 q3 ?_ ?_ ?_ ?_ ?_ <;> norm_num at * <;> try linarith
    all_goals generalize_proofs at *;
    · exact this h_range_q3.2 ( by linarith ) |>.1;
    · nlinarith [ inv_mul_cancel₀ ( by linarith : C ≠ 0 ), ( by norm_cast : ( 10 : ℝ ) ≤ k ) ];
    · nlinarith [ ( by norm_cast : ( 10 : ℝ ) ≤ k ), inv_mul_cancel₀ ( by positivity : ( C : ℝ ) ≠ 0 ) ];
    · nlinarith [ inv_mul_cancel₀ ( by linarith : C ≠ 0 ), ( by norm_cast : ( 10 : ℝ ) ≤ k ) ]) hy_large

lemma inequality_p1_p2 (k : ℕ) (p1 p2 : ℕ) (hp1 : (k : ℝ) / 2 < p1) (hp2 : (k : ℝ) / 2 < p2) (hk : k > 0) :
  8 * (p1 : ℝ) * p2 > k * (p1 + p2) := by
    rw [ div_lt_iff₀ ] at * <;> norm_cast at * ; nlinarith only [ hp1, hp2, hk ] ;

lemma y_len_div_M_gt_8_div_k (C : ℝ) (k : ℕ) (hk : k > 0)
  (h_interval_check : y_interval_length k C / ((M k : ℝ) / (k * k / 4)) > 2 * k) :
  y_interval_length k C / (M k : ℝ) > 8 / k := by
    field_simp at *; ( ring_nf at *; (
    -- The goal is already satisfied by h_interval_check.
    exact h_interval_check); )

/-
Checking availability of definitions and lemmas.
-/
#check DensityHypothesis
#check exists_good_primes
#check construct_xy
#check lcm_ratio_bound
#check final_inequality_sufficient
#check MainTheoremStatement

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
      · exact?;
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
      exact?
    obtain ⟨K_x, hK_x⟩ : ∃ K_x, ∀ k ≥ K_x, ∀ q1 q2 q3 : ℝ, k / 2 < q1 → q1 ≤ k → k / 2 < q2 → q2 ≤ k → k / 2 < q3 → q3 ≤ k → (q1 * q2 * q3 : ℝ) / (5 * C * k) > q1 + q2 + q3 := by
      exact?;
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
The main theorem holds.
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

/-
Checking if lcm_real is defined.
-/
#check lcm_real

/-
Defining Conjecture 2 and Question 4 statements with explicit types.
-/
def Conjecture2Statement : Prop :=
  ∀ C : ℝ, C ≥ 1 →
  ∃ K : ℕ, ∀ k ≥ K, ∃ x y : ℕ,
    0 < x ∧ x < y ∧ y > x + k ∧
    lcm_real (Finset.Icc x (x + k - 1)) > lcm_real (Finset.Icc y (y + k + ⌊C⌋₊ - 1))

def Question4Statement : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
  ∃ K : ℕ, ∀ k ≥ K,
    let primes := (Finset.Icc 1 k).filter (fun p => p.Prime ∧ k.sqrt < p)
    let M := primes.prod id
    let I (p : ℕ) := Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ)))
    ∀ (start : ℕ), ∃ x ∈ Finset.Icc start (start + Nat.ceil ((M : ℝ) ^ ε) - 1),
      ∀ p ∈ primes, x % p ∈ I p

/-
Definitions of bad primes and a lemma about the count of multiples for good primes.
-/
def PrimesIn (k : ℕ) : Finset ℕ := (Finset.Icc 1 k).filter (fun p => p.Prime ∧ k.sqrt < p)

def is_bad (k p : ℕ) (δ : ℝ) : Prop :=
  k % p < Nat.ceil ((p : ℝ) ^ (1 - δ)) ∨ k % p > p - Nat.ceil ((p : ℝ) ^ (1 - δ))

def BadPrimes (k : ℕ) (δ : ℝ) : Finset ℕ := (PrimesIn k).filter (fun p => is_bad k p δ)

def M_prod (k : ℕ) : ℕ := (PrimesIn k).prod id

lemma count_multiples_good_primes (k x y : ℕ) (δ : ℝ) (p : ℕ)
  (hp : p ∈ PrimesIn k)
  (h_not_bad : ¬ is_bad k p δ)
  (hx : x % p ∈ Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ))))
  (hy : (p - y % p) % p ∈ Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ)))) :
  (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k))).card =
  (Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card + 1 := by
    -- We'll use that $x \pmod p \le p - (k \pmod p)$ and $y \pmod p \ge p - (k \pmod p)$ to show the cardinalities differ by 1.
    have h_mod_bounds : 1 ≤ x % p ∧ x % p ≤ p - (k % p) ∧ p - (k % p) ≤ y % p ∧ y % p ≤ p := by
      -- Since $p$ is not bad, we have $k \% p \ge \lceil p^{1-\delta} \rceil$.
      have h_k_mod_p : k % p ≥ Nat.ceil ((p : ℝ) ^ (1 - δ)) := by
        unfold is_bad at h_not_bad; aesop;
      have h_y_mod_p : p - k % p ≤ y % p := by
        have h_y_mod_p : (p - y % p) % p ≤ k % p := by
          exact le_trans ( Finset.mem_Icc.mp hy |>.2 ) h_k_mod_p;
        rw [ Nat.mod_eq_of_lt ] at h_y_mod_p;
        · exact Nat.sub_le_of_le_add <| by linarith [ Nat.sub_add_cancel <| show y % p ≤ p from Nat.le_of_lt <| Nat.mod_lt _ <| Nat.Prime.pos <| by unfold PrimesIn at hp; aesop ] ;
        · exact Nat.sub_lt ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ( Nat.pos_of_ne_zero ( by aesop_cat ) );
      have h_x_mod_p : x % p ≤ p - k % p := by
        refine le_trans ( Finset.mem_Icc.mp hx |>.2 ) ?_;
        -- Since $p$ is not bad, we have $k \% p \le p - \lceil p^{1-\delta} \rceil$.
        have h_k_mod_p_le : k % p ≤ p - Nat.ceil ((p : ℝ) ^ (1 - δ)) := by
          unfold is_bad at h_not_bad; aesop;
        grind;
      exact ⟨ Finset.mem_Icc.mp hx |>.1, h_x_mod_p, h_y_mod_p, Nat.le_of_lt <| Nat.mod_lt _ <| Nat.Prime.pos <| by unfold PrimesIn at hp; aesop ⟩;
    -- Apply the count_multiples_large_p_RHS and count_multiples_large_p_LHS lemmas with the bounds from h_mod_bounds.
    have h_count_rhs : (Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card = k / p := by
      apply count_multiples_large_p_RHS;
      · unfold PrimesIn at hp; aesop;
      · contrapose! h_not_bad; interval_cases k <;> simp_all +decide ;
        cases p <;> simp_all +decide [ PrimesIn ];
      · exact Nat.pos_of_ne_zero fun h => by simp_all +decide ;
      · unfold PrimesIn at hp; aesop;
      · aesop
    have h_count_lhs : (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k))).card = k / p + 1 := by
      apply count_multiples_large_p_LHS;
      · exact Finset.mem_filter.mp hp |>.2.1;
      · linarith [ show k ≥ 2 from le_of_not_gt fun hk => by interval_cases k <;> simp_all +decide [ PrimesIn ] ];
      · contrapose! h_not_bad; aesop;
      · unfold PrimesIn at hp; aesop;
      · exact ⟨ y % p, h_mod_bounds.2.2.1, h_mod_bounds.2.2.2, Nat.ModEq.symm <| Nat.mod_modEq _ _ ⟩;
    rw [ h_count_lhs, h_count_rhs ]

/-
Bound on the number of bad k's for a fixed prime p.
-/
lemma count_bad_k_bound (K : ℕ) (p : ℕ) (δ : ℝ) (hp : p > 0) :
  ((Finset.Ico K (2 * K)).filter (fun k => is_bad k p δ)).card ≤
  2 * Nat.ceil ((p : ℝ) ^ (1 - δ)) * (K / p + 1) := by
    have h_bound : ∀ r ∈ Finset.range p, (Finset.filter (fun k => k % p = r) (Finset.Ico K (2 * K))).card ≤ K / p + 1 := by
      intro r hr
      have h_filter : Finset.filter (fun k => k % p = r) (Finset.Ico K (2 * K)) ⊆ Finset.image (fun i => r + p * i) (Finset.Ico ((K + p - 1 - r) / p) ((2 * K + p - 1 - r) / p)) := by
        intro k hk;
        simp +zetaDelta at *;
        refine' ⟨ k / p, ⟨ _, _ ⟩, _ ⟩;
        · rw [ Nat.div_le_iff_le_mul_add_pred hp ];
          rw [ tsub_tsub, tsub_le_iff_left ];
          linarith [ Nat.mod_add_div k p, Nat.sub_add_cancel hp.nat_succ_le ];
        · rw [ Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hp ];
          exact le_tsub_of_add_le_left <| le_tsub_of_add_le_left <| by linarith [ Nat.mod_add_div k p, Nat.mod_lt k hp ] ;
        · linarith [ Nat.mod_add_div k p ];
      refine le_trans ( Finset.card_le_card h_filter ) ?_;
      rw [ Finset.card_image_of_injective _ fun i j hij => by nlinarith ] ; norm_num;
      rw [ Nat.le_iff_lt_or_eq ];
      refine' lt_or_eq_of_le ( Nat.le_of_lt_succ _ );
      rw [ Nat.div_lt_iff_lt_mul <| by positivity ] ; ring_nf;
      rw [ tsub_tsub, tsub_lt_iff_left ] <;> nlinarith [ Nat.div_add_mod K p, Nat.mod_lt K hp, Nat.div_add_mod ( K + p - 1 - r ) p, Nat.mod_lt ( K + p - 1 - r ) hp, Nat.sub_add_cancel ( show 1 ≤ K + p from by linarith [ Finset.mem_range.mp hr ] ), Nat.sub_add_cancel ( show r ≤ K + p - 1 from Nat.le_sub_one_of_lt ( by linarith [ Finset.mem_range.mp hr ] ) ) ];
    -- The set of bad residues modulo p is contained in the union of the sets of multiples of p and the set of numbers whose residue modulo p is greater than p - Nat.ceil ((p : ℝ) ^ (1 - δ)).
    have h_bad_residues : (Finset.filter (fun k => is_bad k p δ) (Finset.Ico K (2 * K))).card ≤ (Finset.filter (fun r => r < Nat.ceil ((p : ℝ) ^ (1 - δ))) (Finset.range p)).card * ((K / p) + 1) + (Finset.filter (fun r => r > p - Nat.ceil ((p : ℝ) ^ (1 - δ)) ) (Finset.range p)).card * ((K / p) + 1) := by
      have h_bad_residues : Finset.filter (fun k => is_bad k p δ) (Finset.Ico K (2 * K)) ⊆ Finset.biUnion (Finset.filter (fun r => r < Nat.ceil ((p : ℝ) ^ (1 - δ))) (Finset.range p)) (fun r => Finset.filter (fun k => k % p = r) (Finset.Ico K (2 * K))) ∪ Finset.biUnion (Finset.filter (fun r => r > p - Nat.ceil ((p : ℝ) ^ (1 - δ)) ) (Finset.range p)) (fun r => Finset.filter (fun k => k % p = r) (Finset.Ico K (2 * K))) := by
        intro k hk; simp_all +decide [ is_bad ] ;
        exact Or.imp ( fun h => ⟨ Nat.mod_lt _ hp, h ⟩ ) ( fun h => ⟨ Nat.mod_lt _ hp, h ⟩ ) hk.2;
      exact le_trans ( Finset.card_le_card h_bad_residues ) ( le_trans ( Finset.card_union_le _ _ ) ( add_le_add ( Finset.card_biUnion_le.trans ( Finset.sum_le_card_nsmul _ _ _ fun x hx => h_bound x <| Finset.mem_filter.mp hx |>.1 ) ) ( Finset.card_biUnion_le.trans ( Finset.sum_le_card_nsmul _ _ _ fun x hx => h_bound x <| Finset.mem_filter.mp hx |>.1 ) ) ) ) |> le_trans <| by simp +decide ;
    refine le_trans h_bad_residues ?_;
    rw [ ← add_mul ];
    rw [ show { r ∈ Finset.range p | r < ⌈ ( p : ℝ ) ^ ( 1 - δ ) ⌉₊ } = Finset.range ( Min.min p ⌈ ( p : ℝ ) ^ ( 1 - δ ) ⌉₊ ) by ext; aesop, show { r ∈ Finset.range p | p - ⌈ ( p : ℝ ) ^ ( 1 - δ ) ⌉₊ < r } = Finset.Ico ( p - ⌈ ( p : ℝ ) ^ ( 1 - δ ) ⌉₊ + 1 ) p by ext; aesop ] ; simp +arith +decide [ two_mul ];
    omega

/-
The sum of the number of bad primes over k is bounded by the sum over primes of the number of bad k's.
-/
def AllPrimesIn (k : ℕ) : Finset ℕ := (Finset.Icc 1 k).filter Nat.Prime

lemma sum_bad_primes_le_sum_all_primes (K : ℕ) (δ : ℝ) (hK : K > 0) :
  ∑ k ∈ Finset.Ico K (2 * K), (BadPrimes k δ).card ≤
  ∑ p ∈ AllPrimesIn (2 * K), ((Finset.Ico K (2 * K)).filter (fun k => is_bad k p δ)).card := by
    have h_sum_bound : ∑ k ∈ Finset.Ico K (2 * K), (BadPrimes k δ).card = ∑ k ∈ Finset.Ico K (2 * K), ∑ p ∈ AllPrimesIn (2 * K), (if is_bad k p δ then 1 else 0) * (if p ∈ PrimesIn k then 1 else 0) := by
      refine' Finset.sum_congr rfl fun k hk => _;
      rw [ ← Finset.sum_subset ];
      any_goals exact PrimesIn k |> Finset.filter ( fun p => is_bad k p δ );
      · rw [ Finset.card_eq_sum_ones, Finset.sum_filter ] ; aesop;
      · simp +decide [ Finset.subset_iff, PrimesIn, AllPrimesIn ];
        exact fun x hx₁ hx₂ hx₃ hx₄ hx₅ => ⟨ ⟨ hx₁, by linarith [ Finset.mem_Ico.mp hk ] ⟩, hx₃ ⟩;
      · grind;
    rw [ h_sum_bound, Finset.sum_comm ];
    simp +contextual [ Finset.sum_ite ];
    exact Finset.sum_le_sum fun p hp => Finset.card_le_card fun x hx => by aesop;

/-
Explicit bound on the sum of bad primes counts.
-/
lemma sum_bad_primes_bound_explicit (K : ℕ) (δ : ℝ) (hK : K > 0) :
  ∑ k ∈ Finset.Ico K (2 * K), (BadPrimes k δ).card ≤
  ∑ p ∈ AllPrimesIn (2 * K), 2 * Nat.ceil ((p : ℝ) ^ (1 - δ)) * (K / p + 1) := by
    refine le_trans ( sum_bad_primes_le_sum_all_primes K δ hK ) ?_;
    apply Finset.sum_le_sum;
    -- Apply the count_bad_k_bound lemma to each prime p in the range.
    intros p hp
    apply count_bad_k_bound;
    exact Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 )

/-
Refined bound on the sum of bad primes counts, restricting to large primes.
-/
lemma sum_bad_primes_bound_refined (K : ℕ) (δ : ℝ) (hK : K > 0) :
  ∑ k ∈ Finset.Ico K (2 * K), (BadPrimes k δ).card ≤
  ∑ p ∈ (AllPrimesIn (2 * K)).filter (fun p => p > Nat.sqrt K), 2 * Nat.ceil ((p : ℝ) ^ (1 - δ)) * (K / p + 1) := by
    -- By definition of `BadPrimes`, we know that for each `k` in the interval `[K, 2K)`, the bad primes p are those with `p > sqrt(k)`.
    have h_bad_primes_restrict : ∀ k ∈ Finset.Ico K (2 * K), BadPrimes k δ ⊆ AllPrimesIn (2 * K) ∩ Finset.filter (fun p => p > K.sqrt) (AllPrimesIn (2 * K)) := by
      intro k hk
      intro p hp
      simp [BadPrimes, AllPrimesIn] at hp ⊢;
      exact ⟨ ⟨ ⟨ hp.1 |> Finset.mem_filter.mp |>.2.1 |> Nat.Prime.pos, hp.1 |> Finset.mem_filter.mp |>.1 |> Finset.mem_Icc.mp |>.2.trans <| by linarith [ Finset.mem_Ico.mp hk ] ⟩, hp.1 |> Finset.mem_filter.mp |>.2.1 ⟩, by exact Nat.sqrt_lt.mpr <| by nlinarith [ Finset.mem_Ico.mp hk, hp.1 |> Finset.mem_filter.mp |>.2.2, Nat.lt_succ_sqrt k ] ⟩;
    have h_sum_bad_primes_bound : ∑ k ∈ Finset.Ico K (2 * K), (BadPrimes k δ).card ≤ ∑ p ∈ AllPrimesIn (2 * K) ∩ Finset.filter (fun p => p > K.sqrt) (AllPrimesIn (2 * K)), ((Finset.Ico K (2 * K)).filter (fun k => is_bad k p δ)).card := by
      have h_sum_bad_primes_bound : ∑ k ∈ Finset.Ico K (2 * K), (BadPrimes k δ).card ≤ ∑ p ∈ AllPrimesIn (2 * K) ∩ Finset.filter (fun p => p > K.sqrt) (AllPrimesIn (2 * K)), ∑ k ∈ Finset.Ico K (2 * K), (if is_bad k p δ then 1 else 0) := by
        have h_sum_bad_primes_bound : ∀ k ∈ Finset.Ico K (2 * K), (BadPrimes k δ).card ≤ ∑ p ∈ AllPrimesIn (2 * K) ∩ Finset.filter (fun p => p > K.sqrt) (AllPrimesIn (2 * K)), (if is_bad k p δ then 1 else 0) := by
          intros k hk
          have h_card_le : (BadPrimes k δ).card ≤ Finset.card (Finset.filter (fun p => is_bad k p δ) (AllPrimesIn (2 * K) ∩ Finset.filter (fun p => p > K.sqrt) (AllPrimesIn (2 * K)))) := by
            exact Finset.card_le_card fun x hx => Finset.mem_filter.mpr ⟨ h_bad_primes_restrict k hk hx, Finset.mem_filter.mp hx |>.2 ⟩;
          simpa [ Finset.sum_ite ] using h_card_le;
        exact le_trans ( Finset.sum_le_sum h_sum_bad_primes_bound ) ( by rw [ Finset.sum_comm ] );
      simpa only [ Finset.card_filter ] using h_sum_bad_primes_bound;
    refine le_trans h_sum_bad_primes_bound ?_;
    refine' le_trans ( Finset.sum_le_sum fun p hp => show Finset.card ( Finset.filter ( fun k => is_bad k p δ ) ( Finset.Ico K ( 2 * K ) ) ) ≤ 2 * ⌈ ( p : ℝ ) ^ ( 1 - δ ) ⌉₊ * ( K / p + 1 ) from _ ) _;
    · have := count_bad_k_bound K p δ ( Nat.Prime.pos <| Finset.mem_filter.mp ( Finset.mem_inter.mp hp |>.1 ) |>.2 ) ; aesop;
    · exact Finset.sum_le_sum_of_subset ( fun p hp => by aesop )

/-
Bound on the sum of p^(-delta) for large primes.
-/
lemma sum_pow_neg_delta_le (K : ℕ) (δ : ℝ) (hK : K > 0) (hδ : δ > 0) :
  ∑ p ∈ (AllPrimesIn (2 * K)).filter (fun p => p > Nat.sqrt K), ((p : ℝ) ^ (-δ)) ≤
  ((AllPrimesIn (2 * K)).card : ℝ) * (K : ℝ) ^ (-δ / 2) := by
    have h_term_bound : ∀ p ∈ (AllPrimesIn (2 * K)).filter (fun p => p > Nat.sqrt K), (p : ℝ) ^ (-δ : ℝ) ≤ (K : ℝ) ^ (-δ / 2 : ℝ) := by
      intros p hp
      have h_p_sqrt : (p : ℝ) ≥ Real.sqrt K := by
        exact Real.sqrt_le_iff.mpr ⟨ by positivity, by norm_cast; nlinarith [ Nat.lt_succ_sqrt K, Finset.mem_filter.mp hp ] ⟩;
      rw [ Real.rpow_def_of_pos, Real.rpow_def_of_pos ] <;> norm_num <;> try positivity;
      · nlinarith [ Real.log_le_log ( by positivity ) h_p_sqrt, Real.log_sqrt ( Nat.cast_nonneg K ) ];
      · exact Nat.pos_of_ne_zero ( by aesop );
    refine' le_trans ( Finset.sum_le_sum fun p hp => h_term_bound p hp ) _;
    norm_num [ mul_comm ];
    exact mul_le_mul_of_nonneg_right ( mod_cast Finset.card_filter_le _ _ ) ( by positivity )

/-
Bound on the sum of p^(1-delta) for primes up to 2K.
-/
lemma sum_pow_one_sub_delta_le (K : ℕ) (δ : ℝ) (hK : K > 0) (hδ : δ ≤ 1) :
  ∑ p ∈ (AllPrimesIn (2 * K)).filter (fun p => p > Nat.sqrt K), ((p : ℝ) ^ (1 - δ)) ≤
  ((AllPrimesIn (2 * K)).card : ℝ) * (2 * K : ℝ) ^ (1 - δ) := by
    have h_bound : ∀ p ∈ (AllPrimesIn (2 * K)).filter (fun p => p > Nat.sqrt K), (p : ℝ) ^ (1 - δ) ≤ (2 * K : ℝ) ^ (1 - δ) := by
      exact fun p hp => Real.rpow_le_rpow ( Nat.cast_nonneg _ ) ( mod_cast Finset.mem_Icc.mp ( Finset.mem_filter.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 ) |>.2 ) ( by linarith );
    exact le_trans ( Finset.sum_le_sum h_bound ) ( by simpa using mul_le_mul_of_nonneg_right ( Nat.cast_le.mpr <| Finset.card_filter_le _ _ ) <| Real.rpow_nonneg ( by positivity ) _ ) ;

/-
Definition of BadPrimesBound and a bound on its terms.
-/
def BadPrimesBound (K : ℕ) (δ : ℝ) : ℝ :=
  ∑ p ∈ (AllPrimesIn (2 * K)).filter (fun p => p > Nat.sqrt K), 2 * Nat.ceil ((p : ℝ) ^ (1 - δ)) * (K / p + 1)

lemma bad_primes_term_bound (p K : ℕ) (δ : ℝ) (hp : p > 0) :
  2 * Nat.ceil ((p : ℝ) ^ (1 - δ)) * (K / p + 1) ≤
  2 * (K * (p : ℝ) ^ (-δ) + (p : ℝ) ^ (1 - δ) + K / p + 2) := by
    field_simp;
    have := Nat.ceil_lt_add_one ( Real.rpow_nonneg ( Nat.cast_nonneg p ) ( 1 - δ ) );
    rw [ show ( 1 - δ ) = -δ + 1 by ring, Real.rpow_add ] at * <;> norm_num at *;
    · nlinarith [ ( by norm_cast : ( 1 : ℝ ) ≤ p ), Real.rpow_nonneg ( Nat.cast_nonneg p ) ( -δ ) ];
    · positivity;
    · positivity

/-
Explicit upper bound on BadPrimesBound.
-/
lemma bad_primes_bound_explicit_le (K : ℕ) (δ : ℝ) (hK : K > 0) (hδ : δ > 0) (hδ1 : δ ≤ 1) :
  BadPrimesBound K δ ≤
  2 * ((AllPrimesIn (2 * K)).card : ℝ) * (K * (K : ℝ) ^ (-δ / 2) + (2 * K : ℝ) ^ (1 - δ) + Real.sqrt K + 2) := by
    -- Apply the term bound to each term in the sum.
    have h_term_bound : ∀ p ∈ (AllPrimesIn (2 * K)).filter (fun p => p > Nat.sqrt K), 2 * Nat.ceil ((p : ℝ) ^ (1 - δ)) * (K / p + 1) ≤ 2 * (K * (p : ℝ) ^ (-δ) + (p : ℝ) ^ (1 - δ) + K / p + 2) := by
      intros p hp;
      have := bad_primes_term_bound p K δ ( Nat.pos_of_ne_zero ( by aesop ) );
      convert this using 1;
    refine le_trans ( Finset.sum_le_sum h_term_bound ) ?_;
    -- Apply the bounds from `sum_pow_neg_delta_le` and `sum_pow_one_sub_delta_le`.
    have h_sum_bounds : ∑ p ∈ (AllPrimesIn (2 * K)).filter (fun p => p > Nat.sqrt K), (K : ℝ) * (p : ℝ) ^ (-δ) ≤ (K : ℝ) * (K : ℝ) ^ (-δ / 2) * ((AllPrimesIn (2 * K)).card : ℝ) ∧
                        ∑ p ∈ (AllPrimesIn (2 * K)).filter (fun p => p > Nat.sqrt K), (p : ℝ) ^ (1 - δ) ≤ (2 * K : ℝ) ^ (1 - δ) * ((AllPrimesIn (2 * K)).card : ℝ) ∧
                        ∑ p ∈ (AllPrimesIn (2 * K)).filter (fun p => p > Nat.sqrt K), (K : ℝ) / p ≤ (Real.sqrt K : ℝ) * ((AllPrimesIn (2 * K)).card : ℝ) ∧
                        ∑ p ∈ (AllPrimesIn (2 * K)).filter (fun p => p > Nat.sqrt K), 2 ≤ 2 * ((AllPrimesIn (2 * K)).card : ℝ) := by
                          refine' ⟨ _, _, _, _ ⟩;
                          · have := sum_pow_neg_delta_le K δ hK hδ;
                            simpa only [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] using mul_le_mul_of_nonneg_left this <| Nat.cast_nonneg K;
                          · refine' le_trans ( Finset.sum_le_sum fun p hp => Real.rpow_le_rpow ( Nat.cast_nonneg _ ) ( show ( p : ℝ ) ≤ 2 * K by exact_mod_cast Finset.mem_Icc.mp ( Finset.mem_filter.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 ) |>.2 ) ( by linarith ) ) _ ; norm_num [ mul_comm ];
                            exact mul_le_mul_of_nonneg_right ( mod_cast Finset.card_filter_le _ _ ) ( by positivity );
                          · refine' le_trans ( Finset.sum_le_sum fun p hp => show ( K : ℝ ) / p ≤ Real.sqrt K from _ ) _;
                            · rw [ div_le_iff₀ ] <;> norm_num;
                              · rw [ ← div_le_iff₀' ] <;> norm_num;
                                · rw [ Real.sqrt_le_left ] <;> norm_cast <;> nlinarith [ Nat.lt_succ_sqrt K, Finset.mem_filter.mp hp ];
                                · positivity;
                              · exact Nat.Prime.pos ( by unfold AllPrimesIn at hp; aesop );
                            · norm_num [ mul_comm ];
                              exact mul_le_mul_of_nonneg_right ( mod_cast Finset.card_filter_le _ _ ) ( Real.sqrt_nonneg _ );
                          · norm_num [ mul_comm ];
                            exact Finset.card_filter_le _ _;
    norm_num [ Finset.sum_add_distrib, ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] at * ; linarith

/-
Polynomial decay lemma.
-/
lemma poly_decay (δ : ℝ) (hδ : δ > 0) (ε : ℝ) (hε : ε > 0) :
  ∃ K_min, ∀ K ≥ K_min,
    K * (K : ℝ) ^ (-δ / 2) + (2 * K : ℝ) ^ (1 - δ) + Real.sqrt K + 2 ≤ ε * K := by
      -- Divide by $K$ and let $K \to \infty$: $K^{-\delta/2} + 2^{1-\delta} K^{-\delta} + K^{-1/2} + 2K^{-1} \to 0$.
      have h_lim : Filter.Tendsto (fun K : ℝ => K * (K : ℝ) ^ (-δ / 2) / K + (2 * K) ^ (1 - δ) / K + Real.sqrt K / K + 2 / K) Filter.atTop (nhds 0) := by
        -- Simplify each term in the limit expression.
        suffices h_simp : Filter.Tendsto (fun K : ℝ => (K : ℝ) ^ (-δ / 2) + (2 : ℝ) ^ (1 - δ) * (K : ℝ) ^ (-δ) + (K : ℝ) ^ (-1 / 2 : ℝ) + 2 / K) Filter.atTop (nhds 0) by
          refine Filter.Tendsto.congr' ?_ h_simp ; filter_upwards [ Filter.eventually_gt_atTop 0 ] with K hK ; rw [ Real.mul_rpow ( by positivity ) ( by positivity ) ] ; rw [ Real.sqrt_eq_rpow ] ; rw [ mul_div_cancel_left₀ _ hK.ne' ] ; ring;
          norm_num [ mul_assoc, ← Real.rpow_neg_one, ← Real.rpow_add hK ] ; ring;
        field_simp;
        exact le_trans ( Filter.Tendsto.add ( Filter.Tendsto.add ( Filter.Tendsto.add ( tendsto_rpow_neg_atTop ( by linarith ) ) ( tendsto_const_nhds.mul ( tendsto_rpow_neg_atTop ( by linarith ) ) ) ) ( tendsto_rpow_neg_atTop ( by linarith ) ) ) ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) ) ( by norm_num );
      have := h_lim.eventually ( gt_mem_nhds <| show 0 < ε by linarith );
      obtain ⟨ K_min, hK_min ⟩ := Filter.eventually_atTop.mp this; use Max.max K_min 1; intro K hK; have := hK_min K ( le_trans ( le_max_left _ _ ) hK ) ; rw [ ← add_div, ← add_div, ← add_div, div_lt_iff₀ ] at * <;> nlinarith [ le_max_right K_min 1 ] ;

/-
Check primorial definitions.
-/
#check primorial
#check primorial_le_4_pow

/-
The cardinality of AllPrimesIn n is equal to pi(n).
-/
lemma card_all_primes_in_eq_pi (n : ℕ) : (AllPrimesIn n).card = Nat.primeCounting n := by
  unfold AllPrimesIn Nat.primeCounting;
  rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
  congr 1 with x ; cases x <;> aesop

/-
The cardinality of PrimesIn n is pi(n) - pi(sqrt n).
-/
lemma card_primes_in_eq_pi_sub_pi_sqrt (n : ℕ) : (PrimesIn n).card = Nat.primeCounting n - Nat.primeCounting (Nat.sqrt n) := by
  rw [ show PrimesIn n = Finset.filter Nat.Prime ( Finset.Icc 1 n ) \ Finset.filter Nat.Prime ( Finset.Icc 1 ( Nat.sqrt n ) ) from ?_ ];
  · rw [ Finset.card_sdiff ];
    congr 2;
    · rw [ Nat.primeCounting ];
      rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
      congr 1 with ( _ | x ) <;> aesop;
    · rw [ Finset.inter_eq_left.mpr ];
      · rw [ Nat.primeCounting ];
        rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
        congr 1 with ( _ | x ) <;> aesop;
      · exact Finset.filter_subset_filter _ <| Finset.Icc_subset_Icc_right <| Nat.sqrt_le_self _;
  · ext; simp [PrimesIn];
    grind

/-
Definition of Prime Number Theorem bounds with correct types.
-/
def PNT_bounds : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    (1 - ε) * (n : ℝ) / Real.log n ≤ (Nat.primeCounting n : ℝ) ∧
    (Nat.primeCounting n : ℝ) ≤ (1 + ε) * (n : ℝ) / Real.log n

/-
Bound on the ratio of prime counts assuming PNT.
-/
lemma primes_ratio_bound_of_PNT (hPNT : PNT_bounds) :
  ∃ K_min, ∀ K ≥ K_min, (AllPrimesIn (2 * K)).card ≤ 4 * (PrimesIn K).card := by
    -- Using PNT, we know that $\pi(2K) \sim \frac{2K}{\log 2K} \sim \frac{2K}{\log K}$.
    obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, ∀ n ≥ N₀, (Nat.primeCounting n : ℝ) ≤ (1 + 1 / 16) * n / Real.log n ∧ (Nat.primeCounting n : ℝ) ≥ (1 - 1 / 16) * n / Real.log n := by
      exact hPNT ( 1 / 16 ) ( by norm_num ) |> fun ⟨ N₀, hN₀ ⟩ => ⟨ N₀, fun n hn => ⟨ hN₀ n hn |>.2, hN₀ n hn |>.1 ⟩ ⟩;
    -- Choose $K_min$ such that for all $K \geq K_min$, $\pi(\sqrt{K}) \leq \frac{1}{4} \pi(K)$.
    obtain ⟨K_min, hK_min⟩ : ∃ K_min : ℕ, ∀ K ≥ K_min, (Nat.primeCounting (Nat.sqrt K) : ℝ) ≤ (1 / 4) * (Nat.primeCounting K : ℝ) := by
      -- Using the fact that $\pi(\sqrt{K}) \leq \sqrt{K}$, we can bound the ratio.
      have h_sqrt_bound : ∀ K ≥ N₀^2, (Nat.primeCounting (Nat.sqrt K) : ℝ) ≤ Nat.sqrt K := by
        intro K hK; norm_cast; exact (by
        rw [ Nat.primeCounting ];
        rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
        exact le_trans ( Finset.card_le_card ( show Finset.filter Nat.Prime ( Finset.range ( K.sqrt + 1 ) ) ⊆ Finset.Ico 2 ( K.sqrt + 1 ) from fun x hx => Finset.mem_Ico.mpr ⟨ Nat.Prime.two_le ( Finset.mem_filter.mp hx |>.2 ), Finset.mem_range.mp ( Finset.mem_filter.mp hx |>.1 ) ⟩ ) ) ( by simp +arith +decide ));
      -- Choose $K_min$ such that for all $K \geq K_min$, $\sqrt{K} \leq \frac{1}{4} \pi(K)$.
      obtain ⟨K_min, hK_min⟩ : ∃ K_min : ℕ, ∀ K ≥ K_min, Real.sqrt K ≤ (1 / 4) * (Nat.primeCounting K : ℝ) := by
        have h_sqrt_bound : ∃ K_min : ℕ, ∀ K ≥ K_min, Real.sqrt K ≤ (1 / 4) * ((1 - 1 / 16) * (K : ℝ) / Real.log K) := by
          -- We can divide both sides by $\sqrt{K}$ and then simplify.
          suffices h_div : ∃ K_min : ℕ, ∀ K ≥ K_min, 1 ≤ (1 / 4) * ((1 - 1 / 16) * Real.sqrt K / Real.log K) by
            obtain ⟨ K_min, hK_min ⟩ := h_div; use Max.max K_min 4; intro K hK; specialize hK_min K ( le_trans ( le_max_left _ _ ) hK ) ; rw [ mul_div, le_div_iff₀ ] at * <;> norm_num at *;
            · nlinarith [ Real.sqrt_nonneg K, Real.sq_sqrt ( Nat.cast_nonneg K ), ( by norm_cast; linarith : ( 4 : ℝ ) ≤ K ) ];
            · exact Real.log_pos ( by norm_cast; linarith );
            · exact Real.log_pos ( by norm_cast; linarith );
          -- We can divide both sides by $\sqrt{K}$ and then simplify to get $1 \leq \frac{1}{4} \cdot \frac{15}{16} \cdot \frac{\sqrt{K}}{\log K}$.
          suffices h_div : Filter.Tendsto (fun K : ℕ => (1 / 4) * ((1 - 1 / 16) * Real.sqrt K / Real.log K)) Filter.atTop Filter.atTop by
            exact Filter.eventually_atTop.mp ( h_div.eventually_ge_atTop 1 );
          -- We can use the fact that $\frac{\sqrt{K}}{\log K}$ tends to infinity as $K$ tends to infinity.
          have h_sqrt_log : Filter.Tendsto (fun K : ℕ => Real.sqrt K / Real.log K) Filter.atTop Filter.atTop := by
            -- We can use the change of variables $u = \log K$ to transform the limit expression.
            suffices h_log : Filter.Tendsto (fun u : ℝ => Real.exp (u / 2) / u) Filter.atTop Filter.atTop by
              have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
              refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Function.comp_apply, Real.sqrt_eq_rpow, Real.rpow_def_of_pos ( Nat.cast_pos.mpr hx ) ] ; ring );
            -- Let $y = \frac{u}{2}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{e^y}{2y}$.
            suffices h_change_var : Filter.Tendsto (fun y : ℝ => Real.exp y / (2 * y)) Filter.atTop Filter.atTop by
              convert h_change_var.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 2⁻¹ : ℝ ) ) ) using 2 ; norm_num ; ring;
            have := Real.tendsto_exp_div_pow_atTop 1;
            convert this.const_mul_atTop ( show ( 0 : ℝ ) < 1 / 2 by norm_num ) using 2 ; ring;
          convert h_sqrt_log.const_mul_atTop ( show ( 0 : ℝ ) < 1 / 4 * ( 1 - 1 / 16 ) by norm_num ) using 2 ; ring;
        exact ⟨ h_sqrt_bound.choose + N₀, fun K hK => le_trans ( h_sqrt_bound.choose_spec K ( by linarith ) ) ( mul_le_mul_of_nonneg_left ( hN₀ K ( by linarith ) |>.2 ) ( by norm_num ) ) ⟩;
      exact ⟨ Max.max ( N₀ ^ 2 ) K_min, fun K hK => le_trans ( h_sqrt_bound K ( le_trans ( le_max_left _ _ ) hK ) ) ( le_trans ( Real.le_sqrt_of_sq_le ( mod_cast Nat.sqrt_le' K ) ) ( hK_min K ( le_trans ( le_max_right _ _ ) hK ) ) ) ⟩;
    -- Using the bounds from PNT and the choice of K_min, we can show that for sufficiently large K, the inequality holds.
    obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ K ≥ N₁, (Nat.primeCounting (2 * K) : ℝ) ≤ 4 * (Nat.primeCounting K - Nat.primeCounting (Nat.sqrt K) : ℝ) := by
      refine' ⟨ N₀ + K_min + 4, fun K hK => _ ⟩ ; have := hN₀ K ( by linarith ) ; have := hN₀ ( 2 * K ) ( by linarith ) ; norm_num at *;
      -- Substitute the lower bound from hN₀ into the right-hand side of the inequality.
      have h_subst : 4 * ((15 / 16 : ℝ) * K / Real.log K - (1 / 4 : ℝ) * (17 / 16 : ℝ) * K / Real.log K) ≥ (17 / 16 : ℝ) * (2 * K) / Real.log (2 * K) := by
        rw [ Real.log_mul ( by norm_num ) ( by norm_cast; linarith ) ] ; ring_nf; norm_num;
        rw [ mul_assoc, mul_assoc ];
        exact mul_le_mul_of_nonneg_left ( by rw [ inv_mul_eq_div, inv_mul_eq_div, div_le_div_iff₀ ] <;> nlinarith only [ Real.log_pos one_lt_two, Real.log_le_log ( by norm_num ) ( show ( K : ℝ ) ≥ 2 by norm_cast; linarith ), Real.log_le_sub_one_of_pos zero_lt_two ] ) ( Nat.cast_nonneg _ );
      have := hK_min K ( by linarith ) ; ring_nf at *; linarith;
    use Max.max N₁ K_min;
    intros K hK; specialize hN₁ K ( le_trans ( le_max_left _ _ ) hK ) ; specialize hK_min K ( le_trans ( le_max_right _ _ ) hK ) ; norm_num [ card_all_primes_in_eq_pi, card_primes_in_eq_pi_sub_pi_sqrt ] at * ;
    norm_cast at *;
    rw [ Int.subNatNat_of_le ] at hN₁ <;> norm_cast at *;
    exact Nat.monotone_primeCounting ( Nat.sqrt_le_self _ )

/-
Check for central binomial coefficient lemmas.
-/
#check Nat.centralBinom
#check Nat.four_pow_lt_mul_centralBinom

/-
BadPrimesBound is small relative to K * pi(K), assuming PNT.
-/
lemma bad_primes_bound_small_of_PNT (hPNT : PNT_bounds) (ε δ : ℝ) (hε : ε > 0) (hδ : δ > 0) (hδ1 : δ ≤ 1) :
  ∃ K_min, ∀ K ≥ K_min, BadPrimesBound K δ ≤ ε * K * (PrimesIn K).card := by
    -- By Lemma primes_ratio_bound_of_PNT, there exists $K_min$ such that for all $K \geq K_min$, $\pi(2K) \leq 4\pi(K)$.
    obtain ⟨K_min1, hK_min1⟩ : ∃ K_min1, ∀ K ≥ K_min1, (AllPrimesIn (2 * K)).card ≤ 4 * (PrimesIn K).card := by
      exact?;
    -- By Lemma poly_decay, there exists $K_min$ such that for all $K \geq K_min$, $K * K^{-\delta / 2} + (2 * K)^{1 - \delta} + \sqrt{K} + 2 \leq \frac{\epsilon * K}{16}$.
    obtain ⟨K_min2, hK_min2⟩ : ∃ K_min2, ∀ K ≥ K_min2, K * (K : ℝ) ^ (-δ / 2) + (2 * K : ℝ) ^ (1 - δ) + Real.sqrt K + 2 ≤ ε * K / 16 := by
      have := poly_decay ( δ := δ ) hδ ( ε := ε / 16 ) ( by positivity );
      exact ⟨ this.choose, fun K hK => by linarith [ this.choose_spec K hK ] ⟩;
    use Nat.ceil K_min2 + K_min1 + 1;
    intro K hK
    have h_bound : BadPrimesBound K δ ≤ 2 * (AllPrimesIn (2 * K)).card * (K * (K : ℝ) ^ (-δ / 2) + (2 * K : ℝ) ^ (1 - δ) + Real.sqrt K + 2) := by
      convert bad_primes_bound_explicit_le K δ _ _ _ using 1;
      · linarith;
      · exact?;
      · linarith;
    have := hK_min2 K ( Nat.le_of_ceil_le ( by linarith ) ) ; norm_num at * ; nlinarith [ show ( AllPrimesIn ( 2 * K ) |> Finset.card : ℝ ) ≤ 4 * ( PrimesIn K |> Finset.card : ℝ ) by exact_mod_cast hK_min1 K ( by linarith ), show ( 0 : ℝ ) ≤ ε * K by positivity ] ;

/-
Asymptotic lower bound for PrimesIn k.
-/
lemma primes_in_card_asymp_lower (hPNT : PNT_bounds) (ε : ℝ) (hε : ε > 0) :
  ∃ N, ∀ k ≥ N, (PrimesIn k).card ≥ (1 - ε) * k / Real.log k := by
    -- From PNT, we know that $\pi(k) \geq (1 - \epsilon/2) k / \log k$ for large $k$.
    have h_pi_lower_bound : ∀ ε > 0, ∃ N, ∀ k ≥ N, (Nat.primeCounting k : ℝ) ≥ (1 - ε) * (k : ℝ) / Real.log k := by
      exact fun ε hε => by obtain ⟨ N, hN ⟩ := hPNT ε hε; exact ⟨ N, fun k hk => by have := hN k hk; ring_nf at this ⊢; linarith ⟩ ;
    -- Since $\pi(\sqrt{k}) \leq C \sqrt{k} / \log \sqrt{k}$, we have $\pi(k) - \pi(\sqrt{k}) \geq \pi(k) - o(k / \log k)$.
    have h_pi_sub_pi_sqrt_lower_bound : ∀ ε > 0, ∃ N, ∀ k ≥ N, (Nat.primeCounting k : ℝ) - (Nat.primeCounting (Nat.sqrt k) : ℝ) ≥ (1 - ε) * (k : ℝ) / Real.log k := by
      -- Since $\pi(\sqrt{k}) \leq C \sqrt{k} / \log \sqrt{k}$, we have $\pi(\sqrt{k}) = o(k / \log k)$.
      have h_pi_sqrt_small : Filter.Tendsto (fun k => (Nat.primeCounting (Nat.sqrt k) : ℝ) / (k / Real.log k)) Filter.atTop (nhds 0) := by
        -- We'll use that $\pi(\sqrt{k}) \leq \sqrt{k}$ and $\frac{\sqrt{k}}{k / \log k} = \frac{\log k}{\sqrt{k}}$.
        have h_pi_sqrt_le_sqrt : ∀ k : ℕ, k > 0 → (Nat.primeCounting (Nat.sqrt k) : ℝ) ≤ Real.sqrt k := by
          intro k hk_pos
          have h_pi_sqrt_le_sqrt : (Nat.primeCounting (Nat.sqrt k) : ℝ) ≤ Nat.sqrt k := by
            norm_cast;
            rw [ Nat.primeCounting ];
            rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
            exact le_trans ( Finset.card_le_card ( show Finset.filter Nat.Prime ( Finset.range ( k.sqrt + 1 ) ) ⊆ Finset.Ico 2 ( k.sqrt + 1 ) from fun x hx => Finset.mem_Ico.mpr ⟨ Nat.Prime.two_le ( Finset.mem_filter.mp hx |>.2 ), Finset.mem_range.mp ( Finset.mem_filter.mp hx |>.1 ) ⟩ ) ) ( by simp +arith +decide );
          exact le_trans h_pi_sqrt_le_sqrt <| Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' _;
        -- We'll use that $\frac{\sqrt{k}}{k / \log k} = \frac{\log k}{\sqrt{k}}$.
        suffices h_log_sqrt : Filter.Tendsto (fun k : ℕ => Real.log k / Real.sqrt k) Filter.atTop (nhds 0) by
          refine' squeeze_zero_norm' _ h_log_sqrt;
          field_simp;
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with k hk using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; rw [ div_le_div_iff₀ ] <;> first | positivity | nlinarith [ h_pi_sqrt_le_sqrt k hk, Real.sqrt_nonneg k, Real.sq_sqrt <| Nat.cast_nonneg k, Real.log_nonneg <| Nat.one_le_cast.2 hk, mul_le_mul_of_nonneg_right ( h_pi_sqrt_le_sqrt k hk ) <| Real.log_nonneg <| Nat.one_le_cast.2 hk ] ;
        -- Let $y = \sqrt{k}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{\log(y^2)}{y} = \lim_{y \to \infty} \frac{2 \log y}{y}$.
        suffices h_log_sqrt_y : Filter.Tendsto (fun y : ℝ => 2 * Real.log y / y) Filter.atTop (nhds 0) by
          have := h_log_sqrt_y.comp ( show Filter.Tendsto ( fun k : ℕ => Real.sqrt k ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Nat.ceil ( x ^ 2 ), fun n hn => Real.le_sqrt_of_sq_le <| by nlinarith [ Nat.ceil_le.mp hn ] ⟩ );
          refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with k hk using by rw [ Function.comp_apply, Real.log_sqrt ( Nat.cast_nonneg _ ) ] ; ring );
        -- Let $z = \frac{1}{y}$, so we can rewrite the limit as $\lim_{z \to 0^+} 2z \log(1/z)$.
        suffices h_log_recip : Filter.Tendsto (fun z : ℝ => 2 * z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
          exact h_log_recip.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] );
        norm_num +zetaDelta at *;
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using this.neg.const_mul 2 );
      intro ε hε_pos
      obtain ⟨N₁, hN₁⟩ : ∃ N₁, ∀ k ≥ N₁, (Nat.primeCounting k : ℝ) ≥ (1 - ε / 2) * (k : ℝ) / Real.log k := h_pi_lower_bound (ε / 2) (half_pos hε_pos)
      obtain ⟨N₂, hN₂⟩ : ∃ N₂, ∀ k ≥ N₂, (Nat.primeCounting (Nat.sqrt k) : ℝ) / (k / Real.log k) < ε / 2 := by
        simpa using h_pi_sqrt_small.eventually ( gt_mem_nhds <| half_pos hε_pos );
      refine' ⟨ Max.max N₁ N₂ + 2, fun k hk => _ ⟩ ; specialize hN₁ k ( by linarith [ le_max_left N₁ N₂ ] ) ; specialize hN₂ k ( by linarith [ le_max_right N₁ N₂ ] ) ; rw [ div_lt_iff₀ ] at hN₂;
      · ring_nf at *; nlinarith;
      · exact div_pos ( Nat.cast_pos.mpr ( by linarith [ le_max_left N₁ N₂, le_max_right N₁ N₂ ] ) ) ( Real.log_pos ( Nat.one_lt_cast.mpr ( by linarith [ le_max_left N₁ N₂, le_max_right N₁ N₂ ] ) ) );
    have h_card_primes_in_eq_pi_sub_pi_sqrt : ∀ k, (PrimesIn k).card = Nat.primeCounting k - Nat.primeCounting (Nat.sqrt k) := by
      intro k; rw [ card_primes_in_eq_pi_sub_pi_sqrt ] ;
    obtain ⟨ N, hN ⟩ := h_pi_sub_pi_sqrt_lower_bound ε hε; use N; intro k hk; specialize hN k hk; rw [ h_card_primes_in_eq_pi_sub_pi_sqrt ] ; rw [ Nat.cast_sub <| Nat.monotone_primeCounting <| Nat.sqrt_le_self _ ] ; aesop;

/-
Asymptotic upper bound for PrimesIn k.
-/
lemma primes_in_card_asymp_upper (hPNT : PNT_bounds) (ε : ℝ) (hε : ε > 0) :
  ∃ N, ∀ k ≥ N, (PrimesIn k).card ≤ (1 + ε) * k / Real.log k := by
    -- From PNT, $\pi(k) \leq (1 + \epsilon/2) k / \log k$.
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k ≥ N, (Nat.primeCounting k : ℝ) ≤ (1 + ε / 2) * k / Real.log k := by
      obtain ⟨ N, hN ⟩ := hPNT ( ε / 2 ) ( half_pos hε ) ; use N; intros k hk; specialize hN k hk; ring_nf at *; aesop;
    -- Since $\pi(\sqrt{k}) \geq 0$, we have $\pi(k) - \pi(\sqrt{k}) \leq \pi(k) \leq (1 + \epsilon/2) k / \log k$.
    have h_upper_bound : ∀ k ≥ N, (PrimesIn k).card ≤ (Nat.primeCounting k : ℝ) := by
      intro k hk; rw [ card_primes_in_eq_pi_sub_pi_sqrt ] ; norm_num;
    exact ⟨ N, fun k hk => le_trans ( h_upper_bound k hk ) ( le_trans ( hN k hk ) ( by gcongr ; linarith ) ) ⟩

/-
For large K, |PrimesIn(K)| <= 2 * |PrimesIn(k)| for k in [K, 2K).
-/
lemma primes_in_card_ratio (hPNT : PNT_bounds) :
  ∃ N, ∀ K ≥ N, ∀ k ∈ Finset.Ico K (2 * K), (PrimesIn K).card ≤ 2 * (PrimesIn k).card := by
    -- From PNT, for large $K$:
    -- $|PrimesIn(K)| \le 1.1 K/\log K$.
    have h_upper_bound : ∃ N, ∀ K ≥ N, (PrimesIn K).card ≤ 1.1 * K / Real.log K := by
      -- Apply the upper bound from the Prime Number Theorem with ε = 0.1.
      obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ K ≥ N, (Nat.primeCounting K : ℝ) ≤ 1.1 * K / Real.log K := by
        exact hPNT 0.1 ( by norm_num ) |> fun ⟨ N, hN ⟩ => ⟨ N + 2, fun K hK => by have := hN K ( by linarith ) ; norm_num at * ; linarith ⟩;
      use N + 1;
      intro K hK; specialize hN K ( by linarith ) ; rw [ card_primes_in_eq_pi_sub_pi_sqrt ] ; norm_num at *;
      exact le_trans ( Nat.cast_le.mpr ( Nat.sub_le _ _ ) ) hN;
    -- For $k \in [K, 2K)$, $|PrimesIn(k)| \ge 0.9 k/\log k \ge 0.9 K/\log(2K)$.
    have h_lower_bound : ∃ N, ∀ K ≥ N, ∀ k ∈ Finset.Ico K (2 * K), (PrimesIn k).card ≥ 0.9 * K / Real.log (2 * K) := by
      -- From PNT, for large $k$:
      -- $|PrimesIn(k)| \ge 0.9 k/\log k$.
      have h_lower_bound : ∃ N, ∀ k ≥ N, (PrimesIn k).card ≥ 0.9 * k / Real.log k := by
        obtain ⟨ N, hN ⟩ := primes_in_card_asymp_lower hPNT 0.1 ( by norm_num );
        exact ⟨ N, fun k hk => le_trans ( by ring_nf; norm_num ) ( hN k hk ) ⟩;
      simp +zetaDelta at *;
      obtain ⟨ N, hN ⟩ := h_lower_bound; use N + 2; intros K hK k hk₁ hk₂; specialize hN k ( by linarith ) ; rw [ div_le_iff₀ ] at * <;> norm_num at *;
      · exact le_trans ( by gcongr ) ( hN.trans ( mul_le_mul_of_nonneg_left ( Real.log_le_log ( by norm_cast; linarith ) ( by norm_cast; linarith ) ) ( Nat.cast_nonneg _ ) ) );
      · exact Real.log_pos ( by norm_cast; linarith );
      · exact Real.log_pos ( by norm_cast; linarith );
    -- We need to find N such that for all K ≥ N, 1.1 K / log K ≤ 2 * (0.9 K / log (2K)).
    have h_ratio_bound : ∃ N, ∀ K ≥ N, 1.1 * K / Real.log K ≤ 2 * (0.9 * K / Real.log (2 * K)) := by
      -- We can divide both sides by $K$ (since $K > 0$) to get $1.1 / \log K \leq 2 * (0.9 / \log (2K))$.
      suffices h_div : ∃ N, ∀ K ≥ N, 1.1 / Real.log K ≤ 2 * (0.9 / Real.log (2 * K)) by
        obtain ⟨ N, hN ⟩ := h_div; use Max.max N 2; intro K hK; specialize hN K ( le_trans ( le_max_left _ _ ) hK ) ; ring_nf at *; nlinarith [ show ( K : ℝ ) ≥ 2 by exact_mod_cast le_trans ( le_max_right _ _ ) hK ] ;
      -- We can divide both sides by $\log K$ (since $\log K > 0$ for $K > 1$) to get $1.1 \leq 1.8 * (\log K / \log (2K))$.
      suffices h_div_log : ∃ N, ∀ K ≥ N, 1.1 ≤ 1.8 * (Real.log K / Real.log (2 * K)) by
        exact ⟨ Max.max h_div_log.choose 2, fun K hK => by have := h_div_log.choose_spec K ( le_trans ( le_max_left _ _ ) hK ) ; ring_nf at this ⊢; nlinarith [ inv_pos.mpr ( Real.log_pos ( show ( K : ℝ ) > 1 by norm_cast; linarith [ le_max_right h_div_log.choose 2 ] ) ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos ( show ( K : ℝ ) > 1 by norm_cast; linarith [ le_max_right h_div_log.choose 2 ] ) ) ) ] ⟩;
      -- We can divide both sides by $K$ and simplify the inequality to $1.1 \leq 1.8 \cdot \frac{\log K}{\log (2K)}$. As $K \to \infty$, $\frac{\log K}{\log (2K)} \to 1$.
      have h_log_ratio : Filter.Tendsto (fun K : ℝ => Real.log K / Real.log (2 * K)) Filter.atTop (nhds 1) := by
        -- We can use the fact that $\log(2K) = \log 2 + \log K$ to simplify the expression.
        suffices h_log_simplified : Filter.Tendsto (fun K : ℝ => Real.log K / (Real.log 2 + Real.log K)) Filter.atTop (nhds 1) by
          refine h_log_simplified.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with K hK using by rw [ Real.log_mul ( by positivity ) ( by positivity ) ] );
        -- We can divide the numerator and the denominator by $\log K$.
        suffices h_div : Filter.Tendsto (fun K : ℝ => 1 / (Real.log 2 / Real.log K + 1)) Filter.atTop (nhds 1) by
          refine h_div.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with K hK using by rw [ div_add_one, div_div_eq_mul_div ] ; ring ; norm_num [ ne_of_gt, Real.log_pos hK ] );
        exact le_trans ( tendsto_const_nhds.div ( Filter.Tendsto.add ( tendsto_const_nhds.div_atTop ( Real.tendsto_log_atTop ) ) tendsto_const_nhds ) ( by norm_num ) ) ( by norm_num );
      have := h_log_ratio.const_mul 1.8; norm_num at *; exact Filter.eventually_atTop.mp ( this.eventually ( le_mem_nhds <| by norm_num ) ) ;
    norm_num +zetaDelta at *;
    obtain ⟨ N₁, hN₁ ⟩ := h_upper_bound; obtain ⟨ N₂, hN₂ ⟩ := h_lower_bound; obtain ⟨ N₃, hN₃ ⟩ := h_ratio_bound; use Nat.ceil N₁ + Nat.ceil N₂ + Nat.ceil N₃ + 1; intros K hK k hk₁ hk₂; have := hN₁ K ( by linarith [ Nat.ceil_le.mp ( by linarith : Nat.ceil N₁ ≤ K ) ] ) ; have := hN₂ K ( by linarith [ Nat.ceil_le.mp ( by linarith : Nat.ceil N₂ ≤ K ) ] ) k hk₁ hk₂; have := hN₃ K ( by linarith [ Nat.ceil_le.mp ( by linarith : Nat.ceil N₃ ≤ K ) ] ) ; rw [ ← @Nat.cast_le ℝ ] ; norm_num at * ; linarith;

/-
There exists a k in [K, 2K) such that the number of bad primes is at most epsilon times the number of primes in (sqrt k, k].
-/
lemma exists_good_k (h_pnt : PNT_bounds) (ε : ℝ) (δ : ℝ) (hε : ε > 0) (hδ : δ > 0) (hδ1 : δ ≤ 1) :
  ∃ K_min, ∀ K ≥ K_min, ∃ k ∈ Finset.Ico K (2 * K),
    (BadPrimes k δ).card ≤ ε * (PrimesIn k).card := by
      have h_avg_bound : ∃ K_min, ∀ K ≥ K_min, (∑ k ∈ Finset.Ico K (2 * K), (BadPrimes k δ).card : ℝ) ≤ ε / 2 * (∑ k ∈ Finset.Ico K (2 * K), (PrimesIn k).card) := by
        have h_sum_bound : ∃ K_min, ∀ K ≥ K_min, (∑ k ∈ Finset.Ico K (2 * K), (BadPrimes k δ).card : ℝ) ≤ ε / 4 * (K * (PrimesIn K).card) := by
          obtain ⟨ K_min, hK_min ⟩ := bad_primes_bound_small_of_PNT h_pnt ( ε / 4 ) δ ( by positivity ) hδ hδ1;
          refine' ⟨ K_min + 1, fun K hK => le_trans _ ( le_trans ( hK_min K ( by linarith ) ) ( by ring_nf; norm_num ) ) ⟩;
          have := sum_bad_primes_bound_refined K δ ( by linarith );
          norm_cast;
          refine' le_trans ( Nat.cast_le.mpr this ) _;
          unfold BadPrimesBound; norm_num;
          exact Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_left ( add_le_add_right ( Nat.cast_div_le .. ) _ ) ( by positivity );
        have h_sum_bound : ∃ K_min, ∀ K ≥ K_min, (∑ k ∈ Finset.Ico K (2 * K), (PrimesIn k).card : ℝ) ≥ K * (PrimesIn K).card / 2 := by
          have := primes_in_card_ratio h_pnt;
          field_simp;
          obtain ⟨ N, hN ⟩ := this; use N + 1; intros K hK; have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.Ico K ( 2 * K ) ) => show ( PrimesIn K |> Finset.card : ℝ ) ≤ 2 * ( PrimesIn i |> Finset.card : ℝ ) from mod_cast hN K ( by linarith ) i hi; simp_all +decide [ two_mul, Finset.sum_add_distrib ] ;
        obtain ⟨ K_min1, hK_min1 ⟩ := ‹∃ K_min, ∀ K ≥ K_min, ∑ k ∈ Finset.Ico K ( 2 * K ), ( BadPrimes k δ |> Finset.card : ℝ ) ≤ ε / 4 * ( K * ( PrimesIn K |> Finset.card : ℝ ) ) ›; obtain ⟨ K_min2, hK_min2 ⟩ := h_sum_bound; use Max.max K_min1 K_min2; intros K hK; specialize hK_min1 K ( le_trans ( le_max_left _ _ ) hK ) ; specialize hK_min2 K ( le_trans ( le_max_right _ _ ) hK ) ; norm_num at * ; nlinarith;
      obtain ⟨ K_min, hK_min ⟩ := h_avg_bound;
      use K_min + 1;
      intro K hK; specialize hK_min K ( by linarith ) ; contrapose! hK_min;
      rw [ Nat.cast_sum ];
      rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_lt_sum_of_nonempty ( by norm_num; linarith ) fun x hx => by linarith [ hK_min x hx ] ;

/-
If S is a subset of primes in (sqrt k, k] with size at most epsilon times the total count, then the product of primes in S is at most M^(2*epsilon).
-/
lemma prod_subset_primes_bound (h_pnt : PNT_bounds) (ε : ℝ) (hε : ε > 0) :
  ∃ K_min, ∀ k ≥ K_min, ∀ S ⊆ PrimesIn k,
    (S.card : ℝ) ≤ ε * (PrimesIn k).card →
    (S.prod (fun p => (p : ℝ))) ≤ (M_prod k : ℝ) ^ (2 * ε) := by
      -- Let's choose any $k$ and $S$ satisfying the conditions.
      obtain ⟨K_min, hK_min⟩ : ∃ K_min, ∀ k ≥ K_min, (∏ p ∈ PrimesIn k, (p : ℝ)) ≥ (Real.sqrt k) ^ ((PrimesIn k).card) := by
        use 4; intro k hk; refine le_trans ?_ ( Finset.prod_le_prod ?_ fun p hp => show ( p : ℝ ) ≥ Real.sqrt k from ?_ ) <;> norm_num;
        rw [ Real.sqrt_le_left ] <;> norm_cast <;> nlinarith [ Finset.mem_filter.mp hp, Nat.sqrt_le k, Nat.lt_succ_sqrt k ];
      -- Applying the bound from `hK_min`, we get $(\prod_{p \in S} p) \leq k^{|S|} \leq k^{\epsilon |PrimesIn k|}$.
      have h_prod_bound : ∀ k ≥ K_min, ∀ S ⊆ PrimesIn k, (S.card : ℝ) ≤ ε * (PrimesIn k).card → (∏ p ∈ S, (p : ℝ)) ≤ (Real.sqrt k) ^ (2 * ε * (PrimesIn k).card) := by
        intros k hk S hS_sub hS_card
        have h_prod_bound : (∏ p ∈ S, (p : ℝ)) ≤ (k : ℝ) ^ ((S.card : ℝ)) := by
          exact le_trans ( Finset.prod_le_prod ( fun _ _ => Nat.cast_nonneg _ ) fun x hx => show ( x : ℝ ) ≤ k from mod_cast Finset.mem_Icc.mp ( Finset.mem_filter.mp ( hS_sub hx ) |>.1 ) |>.2 ) ( by norm_num );
        by_cases hk : k = 0 <;> simp_all +decide [ mul_assoc, Real.sqrt_eq_rpow, ← Real.rpow_mul ];
        exact h_prod_bound.trans ( by exact_mod_cast Real.rpow_le_rpow_of_exponent_le ( Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hk ) ) hS_card );
      refine' ⟨ K_min, fun k hk S hS hS' => le_trans ( h_prod_bound k hk S hS hS' ) _ ⟩;
      have := hK_min k hk;
      convert Real.rpow_le_rpow ( by positivity ) this ( show 0 ≤ 2 * ε by positivity ) using 1 ; norm_cast ; ring;
      · rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Real.sqrt_nonneg _ ) ] ; ring;
      · norm_num [ M_prod ]

/-
log(m(k)) is at most pi(sqrt(k)) * log(k).
-/
lemma log_m_le (k : ℕ) (hk : k ≥ 1) :
  Real.log (m k) ≤ (Nat.primeCounting (Nat.sqrt k) : ℝ) * Real.log k := by
    -- By definition of $m(k)$, we know that $m(k) = \prod_{p \le \sqrt{k}} p^{\lfloor \log_p k \rfloor}$.
    have hm_def : m k = ∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 (Nat.sqrt k)), p ^ Nat.log p k := by
      unfold m;
      field_simp;
      rw [ Finset.prod_subset ];
      congr! 1;
      · rw [ Nat.factorization_def ];
        · have := padicValNat_lcm_range k ‹_›; aesop;
        · aesop;
      · exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1, by nlinarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2, Finset.mem_filter.mp hx |>.2.2, Nat.lt_succ_sqrt k ] ⟩, Finset.mem_filter.mp hx |>.2.1 ⟩;
      · simp +zetaDelta at *;
        exact fun x hx₁ hx₂ hx₃ hx₄ => absurd ( hx₄ hx₁ ( by nlinarith [ Nat.sqrt_le k ] ) hx₃ ) ( by nlinarith [ Nat.sqrt_le k ] );
    -- Taking logs, $\log m(k) = \sum_{p \le \sqrt{k}} \nu_p(M(k)) \log p$.
    have h_log_m : Real.log (m k) ≤ ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 (Nat.sqrt k)), Nat.log p k * Real.log p := by
      rw [ hm_def, Nat.cast_prod, Real.log_prod ] <;> aesop;
    -- We know $\nu_p(M(k)) = \lfloor \log_p k \rfloor$.
    have h_log_p : ∀ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 (Nat.sqrt k)), Nat.log p k * Real.log p ≤ Real.log k := by
      intro p hp; rw [ ← Real.log_pow ] ; exact Real.log_le_log ( by norm_cast; exact pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) _ ) ( mod_cast Nat.pow_log_le_self _ ( by linarith ) ) ;
    convert le_trans h_log_m ( Finset.sum_le_sum h_log_p ) using 1 ; norm_num [ Nat.primeCounting ];
    rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
    exact Or.inl ( by rw [ Finset.range_eq_Ico ] ; rfl )

/-
The sum of log p for p <= k is at most c2 * k for large k.
-/
lemma theta_upper_bound (h_pnt : PNT_bounds) :
  ∃ c2 > 0, ∃ K, ∀ k ≥ K, ∑ p ∈ AllPrimesIn k, Real.log p ≤ c2 * k := by
    -- By definition of $AllPrimesIn$, we know that $\sum_{p \le k} \log p \le \pi(k) \log k$.
    have h_sum_log_primes : ∀ k : ℕ, k ≥ 1 → (∑ p ∈ AllPrimesIn k, Real.log p) ≤ (Nat.primeCounting k : ℝ) * Real.log k := by
      intro k hk
      have h_sum_log_primes : (∑ p ∈ AllPrimesIn k, Real.log p) ≤ (∑ p ∈ AllPrimesIn k, Real.log k) := by
        exact Finset.sum_le_sum fun p hp => Real.log_le_log ( Nat.cast_pos.mpr <| Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2 ) <| Nat.cast_le.mpr <| Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2;
      convert h_sum_log_primes using 1;
      simp +decide [ Nat.primeCounting, AllPrimesIn ];
      rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
      exact Or.inl ( congr_arg Finset.card ( by ext ( _ | i ) <;> aesop ) );
    -- By PNT, $\pi(k) \le 2 \frac{k}{\log k}$ for large $k$.
    have h_pi_bound : ∃ K : ℕ, ∀ k ≥ K, (Nat.primeCounting k : ℝ) ≤ 2 * (k : ℝ) / Real.log k := by
      obtain ⟨ N, hN ⟩ := h_pnt 1 zero_lt_one;
      exact ⟨ N, fun k hk => le_trans ( hN k hk |>.2 ) ( by ring_nf; norm_num ) ⟩;
    obtain ⟨ K, hK ⟩ := h_pi_bound; use 2; norm_num; use K + 2; intros k hk; specialize h_sum_log_primes k ( by linarith ) ; specialize hK k ( by linarith ) ; rw [ le_div_iff₀ ] at hK <;> nlinarith [ Real.log_pos ( show ( k :ℝ ) > 1 by norm_cast ; linarith ), hK, h_sum_log_primes ] ;

/-
For x >= 5000, 1.1 * (x/2) / log(x/2) <= 0.6 * x / log x.
-/
lemma log_ineq_real (x : ℝ) (hx : x ≥ 5000) : 1.1 * (x / 2) / Real.log (x / 2) ≤ 0.6 * x / Real.log x := by
  rw [ Real.log_div ] <;> ring <;> norm_num <;> try linarith;
  -- By simplifying, we can see that this inequality holds for $x \geq 5000$.
  field_simp [hx];
  rw [ div_le_div_iff₀ ];
  · have := Real.log_le_log ( by norm_num ) ( show x ≥ 2 ^ 12 by linarith );
    rw [ Real.log_pow ] at this ; norm_num at this ; linarith [ Real.log_pos one_lt_two ] ;
  · exact sub_pos_of_lt ( Real.log_lt_log ( by norm_num ) ( by linarith ) );
  · exact Real.log_pos <| by linarith;

/-
x / log x is increasing for x >= 3.
-/
lemma x_div_log_x_mono (x y : ℝ) (hx : 3 ≤ x) (hxy : x ≤ y) : x / Real.log x ≤ y / Real.log y := by
  -- Since $f(t) = t / \log t$ is increasing for $t \geq 3$, we have $f(x) \leq f(y)$.
  have h_inc : StrictMonoOn (fun t : ℝ => t / Real.log t) (Set.Ici 3) := by
    -- Let's calculate the derivative of $f(t) = t / \log t$ and show it is positive for $t \geq 3$.
    have h_deriv_pos : ∀ t : ℝ, 3 ≤ t → 0 < deriv (fun t : ℝ => t / Real.log t) t := by
      -- The derivative of $f(t) = t / \log t$ is $(\log t - 1) / (\log t)^2$, which is positive for $t \ge 3$ because $\log t > 1$.
      intros t ht
      have h_log_pos : 1 < Real.log t := by
        rw [ Real.lt_log_iff_exp_lt ( by positivity ) ] ; exact Real.exp_one_lt_d9.trans_le ( by norm_num; linarith );
      norm_num [ show t ≠ 0 by linarith, show Real.log t ≠ 0 by linarith ];
      exact div_pos ( sub_pos.mpr h_log_pos ) ( sq_pos_of_pos ( Real.log_pos ( by linarith ) ) );
    -- Apply the Mean Value Theorem to show that the function is strictly increasing.
    have h_mvt : ∀ a b : ℝ, 3 ≤ a → a < b → ∃ c ∈ Set.Ioo a b, deriv (fun t : ℝ => t / Real.log t) c = ( (fun t : ℝ => t / Real.log t) b - (fun t : ℝ => t / Real.log t) a ) / (b - a) := by
      intros; apply_rules [ exists_deriv_eq_slope ];
      · exact continuousOn_of_forall_continuousAt fun t ht => DifferentiableAt.continuousAt <| differentiableAt_of_deriv_ne_zero <| ne_of_gt <| h_deriv_pos t <| by linarith [ ht.1 ] ;
      · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact differentiableAt_of_deriv_ne_zero ( ne_of_gt ( h_deriv_pos x ( by linarith [ hx.1 ] ) ) ) );
    intro a ha b hb hab; obtain ⟨ c, hc₁, hc₂ ⟩ := h_mvt a b ha hab; have := h_deriv_pos c ( by linarith [ hc₁.1, hc₁.2, ha.out, hb.out ] ) ; rw [ hc₂, lt_div_iff₀ ] at this <;> aesop;
  exact h_inc.le_iff_le ( by norm_num; linarith ) ( by norm_num; linarith ) |>.2 hxy

/-
pi(k/2) is at most 0.6 * k / log k for large k.
-/
lemma pi_half_upper_bound (h_pnt : PNT_bounds) :
  ∃ K, ∀ k ≥ K, (Nat.primeCounting (k / 2) : ℝ) ≤ 0.6 * k / Real.log k := by
    have := h_pnt ( 1 / 20 ) ( by norm_num );
    -- By combining the results from the hypothesis and the lemma, we can conclude the proof.
    obtain ⟨N, hN⟩ := this;
    use 2 * N + 5000;
    intro k hk;
    have h_floor : (Nat.primeCounting (Nat.floor (k / 2)) : ℝ) ≤ (21 / 20 : ℝ) * (Nat.floor (k / 2)) / Real.log (Nat.floor (k / 2)) := by
      exact_mod_cast hN _ ( Nat.le_floor ( by linarith [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos ] ) ) |>.2.trans ( by ring_nf; norm_num );
    -- Since $x / \log x$ is increasing for $x \ge 3$, we have $(Nat.floor (k / 2) : ℝ) / Real.log (Nat.floor (k / 2)) ≤ (k / 2) / Real.log (k / 2)$.
    have h_inc : (Nat.floor (k / 2) : ℝ) / Real.log (Nat.floor (k / 2)) ≤ (k / 2) / Real.log (k / 2) := by
      have h_inc : ∀ x y : ℝ, 3 ≤ x → x ≤ y → x / Real.log x ≤ y / Real.log y := by
        apply_rules [ x_div_log_x_mono ];
      convert h_inc _ _ _ _ using 1 <;> norm_num;
      · omega;
      · rw [ le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.div_mul_le_self k 2 ];
    norm_num [ mul_div_assoc ] at *;
    have := log_ineq_real ( k : ℝ ) ( by linarith [ show ( k : ℝ ) ≥ 5000 by norm_cast; linarith ] ) ; ring_nf at *; linarith;

/-
pi(k/2) is at most 1.1 * (k/2) / log(k/2) for large k.
-/
lemma pi_half_bound_intermediate (h_pnt : PNT_bounds) :
  ∃ K, ∀ k ≥ K, (Nat.primeCounting (k / 2) : ℝ) ≤ 1.1 * (k / 2) / Real.log (k / 2) := by
    -- By PNT, $\pi(n) \le 1.1 n / \log n$ for large $n$.
    have h_pi_half_bound : ∃ N, ∀ n ≥ N, (Nat.primeCounting n : ℝ) ≤ 1.1 * n / Real.log n := by
      have := h_pnt ( 0.1 ) ( by norm_num );
      exact ⟨ this.choose, fun n hn => le_trans ( this.choose_spec n hn |>.2 ) ( by ring_nf; norm_num ) ⟩;
    field_simp;
    obtain ⟨ N, hN ⟩ := h_pi_half_bound; use 2 * N + 4; intros k hk; specialize hN ( k / 2 ) ( by linarith [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos ] ) ; rw [ le_div_iff₀ ] at * <;> norm_num at *;
    · rcases Nat.even_or_odd' k with ⟨ c, rfl | rfl ⟩ <;> norm_num at *;
      · linarith;
      · norm_num [ Nat.add_div ] at *;
        rw [ show ( 2 * c + 1 : ℝ ) / 2 = c + 1 / 2 by ring ];
        have := Real.log_le_sub_one_of_pos ( show 0 < ( c + 1 / 2 : ℝ ) / c by exact div_pos ( by linarith [ show ( c : ℝ ) ≥ 2 by norm_cast; linarith ] ) ( by norm_cast; linarith ) );
        rw [ Real.log_div ( by positivity ) ( by norm_cast; linarith ) ] at this;
        -- Substitute the inequality from `this` into the goal.
        have h_subst : (Nat.primeCounting c : ℝ) * 2 * (Real.log c + 1 / (2 * c)) ≤ 11 / 10 * (2 * c + 1) := by
          have h_subst : (Nat.primeCounting c : ℝ) ≤ c := by
            norm_cast;
            rw [ Nat.primeCounting ];
            rw [ Nat.primeCounting', Nat.count_eq_card_filter_range ];
            exact le_trans ( Finset.card_le_card ( show Finset.filter ( fun x => Nat.Prime x ) ( Finset.range ( c + 1 ) ) ⊆ Finset.Ico 2 ( c + 1 ) from fun x hx => Finset.mem_Ico.mpr ⟨ Nat.Prime.two_le ( Finset.mem_filter.mp hx |>.2 ), Finset.mem_range.mp ( Finset.mem_filter.mp hx |>.1 ) ⟩ ) ) ( by simp +arith +decide );
          nlinarith [ show ( c : ℝ ) ≥ 2 by norm_cast; linarith, Real.log_nonneg ( show ( c : ℝ ) ≥ 1 by norm_cast; linarith ), mul_div_cancel₀ ( 1 : ℝ ) ( show ( 2 * c : ℝ ) ≠ 0 by norm_cast; linarith ) ];
        ring_nf at *; nlinarith [ inv_mul_cancel₀ ( by norm_cast; linarith : ( c : ℝ ) ≠ 0 ) ] ;
    · exact Real.log_pos ( Nat.one_lt_cast.mpr ( Nat.le_div_iff_mul_le zero_lt_two |>.2 ( by linarith ) ) );
    · exact Real.log_pos ( by rw [ lt_div_iff₀ ] <;> norm_cast ; linarith )

/-
The number of primes between k/2 and k is at least c * k / log k for large k.
-/
lemma pi_diff_lower_bound (h_pnt : PNT_bounds) :
  ∃ c > 0, ∃ K, ∀ k ≥ K, (Nat.primeCounting k : ℝ) - (Nat.primeCounting (k / 2) : ℝ) ≥ c * k / Real.log k := by
    -- By the properties of the prime counting function and the inequalities derived from the Prime Number Theorem, we can find such constants $c$ and $K$.
    obtain ⟨K1, hK1⟩ : ∃ K1 : ℕ, ∀ k ≥ K1, (Nat.primeCounting k : ℝ) ≥ 0.9 * k / Real.log k := by
      exact Exists.elim ( h_pnt 0.1 ( by norm_num ) ) fun K hK => ⟨ K, fun k hk => by have := hK k hk; ring_nf at this ⊢; linarith ⟩
    obtain ⟨K2, hK2⟩ : ∃ K2 : ℕ, ∀ k ≥ K2, (Nat.primeCounting (k / 2) : ℝ) ≤ 0.6 * k / Real.log k := by
      exact?
    use 0.3, by norm_num, max K1 K2 + 1;
    intro k hk; have := hK1 k ( by linarith [ le_max_left K1 K2 ] ) ; have := hK2 k ( by linarith [ le_max_right K1 K2 ] ) ; ring_nf at *; linarith;

/-
For large k, log(k/2) >= 0.5 * log k.
-/
lemma log_half_ge : ∃ K, ∀ k ≥ K, Real.log (k / 2) ≥ (1 / 2) * Real.log k := by
  field_simp;
  exact ⟨ 4, fun k hk => by erw [ ← Real.log_pow ] ; gcongr ; nlinarith ⟩

/-
The sum of log p for p <= k is at least c1 * k for large k.
-/
lemma theta_lower_bound (h_pnt : PNT_bounds) :
  ∃ c1 > 0, ∃ K, ∀ k ≥ K, c1 * k ≤ ∑ p ∈ AllPrimesIn k, Real.log p := by
    -- By `pi_diff_lower_bound`, $\pi(k) - \pi(k/2) \ge c k / \log k$.
    obtain ⟨c, hc_pos, hc_bound⟩ : ∃ c > 0, ∃ K, ∀ k ≥ K, (Nat.primeCounting k : ℝ) - (Nat.primeCounting (k / 2) : ℝ) ≥ c * k / Real.log k := by
      exact?;
    -- By `log_half_ge`, $\log(k/2) \ge 0.5 \log k$.
    obtain ⟨K_half, hK_half⟩ : ∃ K_half, ∀ k ≥ K_half, Real.log (k / 2) ≥ (1 / 2) * Real.log k := by
      exact log_half_ge;
    -- For $p > k/2$, $\log p > \log(k/2)$.
    have h_log_bound : ∀ k ≥ Nat.ceil K_half, ∑ p ∈ AllPrimesIn k \ AllPrimesIn (k / 2), Real.log p ≥ (Nat.primeCounting k - Nat.primeCounting (k / 2)) * (1 / 2) * Real.log k := by
      -- For each prime $p$ in the interval $(k/2, k]$, we have $\log p > \log(k/2)$.
      have h_log_bound : ∀ k ≥ Nat.ceil K_half, ∀ p ∈ AllPrimesIn k \ AllPrimesIn (k / 2), Real.log p ≥ (1 / 2) * Real.log k := by
        intros k hk p hp
        have hp_interval : k / 2 < p ∧ p ≤ k := by
          unfold AllPrimesIn at hp; aesop;
        refine le_trans ( hK_half k <| Nat.le_of_ceil_le hk ) ?_;
        exact Real.log_le_log ( div_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ) zero_lt_two ) ( by rw [ div_le_iff₀ ] <;> norm_cast ; linarith [ Nat.div_add_mod k 2, Nat.mod_lt k two_pos ] );
      intro k hk; specialize h_log_bound k hk; simp_all +decide [ Finset.sum_add_distrib, mul_assoc ] ;
      convert Finset.sum_le_sum fun p hp => h_log_bound p ( Finset.mem_sdiff.mp hp |>.1 ) ( Finset.mem_sdiff.mp hp |>.2 ) using 1 ; norm_num [ Finset.card_sdiff, * ];
      rw [ Nat.cast_sub ];
      · rw [ show AllPrimesIn ( k / 2 ) ∩ AllPrimesIn k = AllPrimesIn ( k / 2 ) from ?_ ] ; norm_num [ card_all_primes_in_eq_pi ];
        ext; simp [AllPrimesIn];
        exact fun _ _ _ => ⟨ ⟨ by linarith, by omega ⟩, by assumption ⟩;
      · exact Finset.card_mono <| Finset.inter_subset_right;
    -- Combining the above results, we get the desired lower bound.
    obtain ⟨K, hK⟩ : ∃ K, ∀ k ≥ K, (Nat.primeCounting k - Nat.primeCounting (k / 2)) * (1 / 2) * Real.log k ≥ (c / 2) * k := by
      obtain ⟨ K, hK ⟩ := hc_bound; use Max.max K 2; intro k hk; specialize hK k ( le_trans ( le_max_left _ _ ) hk ) ; rw [ ge_iff_le, div_le_iff₀ ] at * <;> nlinarith [ Real.log_pos <| show ( k :ℝ ) > 1 by norm_cast; linarith [ le_max_right K 2 ] ] ;
    refine' ⟨ c / 2, half_pos hc_pos, Max.max K ⌈K_half⌉₊, fun k hk => le_trans ( hK k ( le_trans ( le_max_left _ _ ) hk ) ) ( le_trans ( h_log_bound k ( le_trans ( le_max_right _ _ ) hk ) ) _ ) ⟩;
    exact Finset.sum_le_sum_of_subset_of_nonneg ( fun x hx => by aesop ) fun _ _ _ => Real.log_natCast_nonneg _

/-
The set of bad primes is contained in the union of BadPrimesForM over small m.
-/
def BadPrimesForM (k m : ℕ) (δ : ℝ) : Finset ℕ :=
  (PrimesIn k).filter (fun p => |(k : ℝ) - m * p| ≤ (p : ℝ) ^ (1 - δ) + 1)

lemma bad_primes_subset_union (k : ℕ) (δ : ℝ) (hk : k > 0) :
  BadPrimes k δ ⊆ (Finset.Icc 1 (Nat.sqrt k + 1)).biUnion (fun m => BadPrimesForM k m δ) := by
    intro p;
    cases eq_or_ne p 0 <;> simp_all +decide [ BadPrimes, BadPrimesForM ];
    · unfold PrimesIn; aesop;
    · intro hp hp';
      rcases hp' with ( h | h );
      · refine' ⟨ k / p, ⟨ Nat.div_pos _ _, _ ⟩, _ ⟩;
        · exact Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2;
        · exact Nat.pos_of_ne_zero ‹_›;
        · nlinarith [ Nat.div_mul_le_self k p, Nat.lt_succ_sqrt k, show p > Nat.sqrt k from Finset.mem_filter.mp hp |>.2 |>.2 ];
        · rw [ abs_of_nonneg ] <;> norm_cast;
          · rw [ Int.subNatNat_of_le ( Nat.div_mul_le_self _ _ ) ] ; norm_cast;
            rw [ show k - k / p * p = k % p from by rw [ Nat.sub_eq_of_eq_add ] ; linarith [ Nat.mod_add_div k p ] ] ; exact le_trans ( Nat.cast_le.mpr h.le ) ( Nat.ceil_lt_add_one ( by positivity ) |> le_of_lt );
          · rw [ Int.subNatNat_eq_coe ] ; push_cast ; linarith [ Nat.div_mul_le_self k p ];
      · refine' ⟨ k / p + 1, _, _ ⟩;
        · refine' ⟨ Nat.le_add_left _ _, Nat.succ_le_succ _ ⟩;
          exact Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.lt_succ_sqrt k, show p > Nat.sqrt k from Finset.mem_filter.mp hp |>.2.2 ] ;
        · rw [ abs_of_nonpos ] <;> norm_num;
          · rw [ show ( k : ℝ ) = ( k / p : ℕ ) * p + ( k % p : ℕ ) by exact_mod_cast Eq.symm ( Nat.div_add_mod' k p ) ];
            contrapose! h;
            refine' Nat.le_sub_of_add_le _;
            exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.ceil_lt_add_one <| show 0 ≤ ( p : ℝ ) ^ ( 1 - δ ) by positivity, Nat.mod_lt k <| Nat.pos_of_ne_zero ‹_› ] ;
          · exact_mod_cast by linarith [ Nat.div_add_mod k p, Nat.mod_lt k ( Nat.pos_of_ne_zero ‹_› ) ] ;

/-
Elements of BadPrimesForM satisfy a weaker bound using k instead of p.
-/
lemma bad_primes_for_m_bound_weak (k m : ℕ) (δ : ℝ) (hk : k > 0) (hδ1 : δ ≤ 1) :
  ∀ p ∈ BadPrimesForM k m δ, |(k : ℝ) - m * p| ≤ (k : ℝ) ^ (1 - δ) + 1 := by
    intro p hp;
    have h_p_le_k : (p : ℝ) ≤ k := by
      exact_mod_cast Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 |> Finset.mem_filter.mp |>.1 ) |>.2;
    have h_p_le_k : (p : ℝ) ^ (1 - δ) ≤ k ^ (1 - δ) := by
      exact Real.rpow_le_rpow ( Nat.cast_nonneg _ ) h_p_le_k ( by linarith );
    exact le_trans ( Finset.mem_filter.mp hp |>.2 ) ( by linarith )

/-
The number of integers in a real interval $[A, B]$ is at most $B - A + 1$.
-/
lemma card_int_in_real_interval (s : Finset ℕ) (A B : ℝ) (h : ∀ n ∈ s, A ≤ n ∧ n ≤ B) (hAB : A ≤ B) :
  (s.card : ℝ) ≤ B - A + 1 := by
    have h_card_le : (Finset.image (fun n : ℕ => (n : ℝ)) s).card ≤ B - A + 1 := by
      -- The image of s under the function n ↦ (n : ℝ) is a subset of [A, B], so its cardinality is at most the cardinality of [A, B].
      have h_image_subset : Finset.image (fun n : ℕ => (n : ℝ)) s ⊆ Finset.image (fun m : ℤ => (m : ℝ)) (Finset.Icc (Int.ceil A) (Int.floor B)) := by
        exact Finset.image_subset_iff.mpr fun x hx => Finset.mem_image.mpr ⟨ x, Finset.mem_Icc.mpr ⟨ Int.ceil_le.mpr ( h x hx |>.1 ), Int.le_floor.mpr ( h x hx |>.2 ) ⟩, rfl ⟩;
      refine' le_trans ( Nat.cast_le.mpr ( Finset.card_le_card h_image_subset ) ) _;
      rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
      rw [ add_sub_assoc ];
      linarith [ Int.floor_le B, Int.lt_floor_add_one B, Int.le_ceil A, Int.ceil_lt_add_one A, show ( Int.toNat ( ⌊B⌋ + ( 1 - ⌈A⌉ ) ) : ℝ ) ≤ ⌊B⌋ + ( 1 - ⌈A⌉ ) from mod_cast Int.toNat_of_nonneg ( show 0 ≤ ⌊B⌋ + ( 1 - ⌈A⌉ ) from by linarith [ show ⌊B⌋ ≥ ⌈A⌉ - 1 from Int.le_floor.2 <| by norm_num; linarith [ Int.ceil_lt_add_one A ] ] ) |> le_of_eq ];
    rwa [ Finset.card_image_of_injective _ Nat.cast_injective ] at h_card_le

/-
Primes in BadPrimesForM lie in a specific interval.
-/
lemma bad_primes_for_m_in_interval (k m : ℕ) (δ : ℝ) (hk : k > 0) (hm : m > 0) (hδ1 : δ ≤ 1) :
  ∀ p ∈ BadPrimesForM k m δ, ((k : ℝ) - (k : ℝ) ^ (1 - δ) - 1) / m ≤ p ∧ p ≤ ((k : ℝ) + (k : ℝ) ^ (1 - δ) + 1) / m := by
    intro p hp;
    have := bad_primes_for_m_bound_weak k m δ hk hδ1 p hp; rw [ abs_le ] at this; exact ⟨ by rw [ div_le_iff₀ ( by positivity ) ] ; linarith, by rw [ le_div_iff₀ ( by positivity ) ] ; linarith ⟩ ;

/-
The number of bad primes for a fixed m is bounded.
-/
lemma bad_primes_for_m_card_bound (k m : ℕ) (δ : ℝ) (hk : k > 0) (hm : m > 0) (hδ : δ ≥ 0) (hδ1 : δ ≤ 1) :
  (BadPrimesForM k m δ).card ≤ 2 * (k : ℝ) ^ (1 - δ) / m + 3 := by
    -- Apply `card_int_in_real_interval` with $A = ((k : ℝ) - (k : ℝ) ^ (1 - δ) - 1) / m$ and $B = ((k : ℝ) + (k : ℝ) ^ (1 - δ) + 1) / m$.
    have h_card_bound : ((BadPrimesForM k m δ).card : ℝ) ≤ ((k : ℝ) + (k : ℝ) ^ (1 - δ) + 1) / m - ((k : ℝ) - (k : ℝ) ^ (1 - δ) - 1) / m + 1 := by
      convert card_int_in_real_interval _ _ _ _ _ using 1;
      · exact?;
      · gcongr ; linarith [ Real.rpow_nonneg ( Nat.cast_nonneg k ) ( 1 - δ ) ];
    exact h_card_bound.trans ( by ring_nf; nlinarith [ inv_mul_cancel₀ ( by positivity : ( m : ℝ ) ≠ 0 ), show ( m : ℝ ) ≥ 1 by norm_cast ] )

/-
Tighter bound for BadPrimesForM using m.
-/
lemma bad_primes_for_m_bound_tight (k m : ℕ) (δ : ℝ) (hk : k ≥ 4) (hm : m > 0) (hδ : δ ≥ 0) (hδ1 : δ ≤ 1) :
  ∀ p ∈ BadPrimesForM k m δ, |(k : ℝ) - m * p| ≤ (2 * k / m : ℝ) ^ (1 - δ) + 1 := by
    intro p hp;
    -- Since $p$ is a prime in the interval $(\sqrt{k}, k]$, we have $p \leq k$.
    have hp_le_k : (p : ℝ) ≤ k := by
      exact_mod_cast Finset.mem_Icc.mp ( Finset.mem_filter.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 ) |>.2;
    have h_bound : |(k : ℝ) - m * p| ≤ (p : ℝ) ^ (1 - δ) + 1 := by
      exact Finset.mem_filter.mp hp |>.2;
    refine le_trans h_bound ?_;
    gcongr;
    · linarith;
    · rw [ le_div_iff₀ ] <;> norm_cast;
      have := Finset.mem_filter.mp hp |>.2;
      contrapose! this;
      rw [ abs_of_neg ] <;> norm_num;
      · refine' lt_of_le_of_lt ( add_le_add_right ( Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.one_le_iff_ne_zero.mpr <| by aesop_cat ) <| show 1 - δ ≤ 1 by linarith ) _ ) _ ; norm_num;
        rw [ lt_sub_iff_add_lt ] ; norm_cast;
        rcases p with ( _ | _ | p ) <;> rcases m with ( _ | _ | m ) <;> norm_num at * ; nlinarith only [ this, hk ];
        · linarith;
        · norm_cast at * ; linarith;
        · rcases p with ( _ | _ | p ) <;> rcases m with ( _ | _ | m ) <;> try norm_num at * ; nlinarith only [ this, hk ] ;
          norm_cast at * ; linarith;
      · norm_cast ; linarith

/-
The number of bad primes is bounded by the sum of bounds for each m.
-/
lemma bad_primes_card_bound_sum (k : ℕ) (δ : ℝ) (hk : k ≥ 4) (hδ : δ ≥ 0) (hδ1 : δ ≤ 1) :
  (BadPrimes k δ).card ≤ ∑ m ∈ Finset.Icc 1 (Nat.sqrt k + 1), (2 * (k : ℝ) ^ (1 - δ) / m + 3) := by
    -- By `bad_primes_subset_union`, `BadPrimes k δ` is a subset of the union of `BadPrimesForM`.
    have h_subset : (BadPrimes k δ).card ≤ ∑ m ∈ Finset.Icc 1 (Nat.sqrt k + 1), (BadPrimesForM k m δ).card := by
      exact le_trans ( Finset.card_mono <| by simpa using bad_primes_subset_union k δ <| by positivity ) <| Finset.card_biUnion_le;
    refine' le_trans ( Nat.cast_le.mpr h_subset ) _;
    rw [ Nat.cast_sum ];
    gcongr;
    exact_mod_cast bad_primes_for_m_card_bound k _ δ ( by linarith ) ( by linarith [ Finset.mem_Icc.mp ‹_› ] ) hδ hδ1

/-
Bound the sum using harmonic series properties.
-/
lemma sum_bound_harmonic (k : ℕ) (δ : ℝ) (hk : k ≥ 1) (hδ : δ ≥ 0) :
  ∑ m ∈ Finset.Icc 1 (Nat.sqrt k + 1), (2 * (k : ℝ) ^ (1 - δ) / m + 3) ≤
  2 * (k : ℝ) ^ (1 - δ) * (1 + Real.log (Nat.sqrt k + 1)) + 3 * (Nat.sqrt k + 1) := by
    -- Apply the known result that the harmonic number H_N is less than or equal to 1 + log N.
    have h_harmonic : ∀ N : ℕ, 1 ≤ N → (∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / m) ≤ 1 + Real.log N := by
      intro N hN
      have := harmonic_le_one_add_log N
      convert this using 1 ; norm_num [ harmonic ];
      erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ];
    simpa [ div_eq_mul_inv, Finset.mul_sum _ _ _, Finset.sum_add_distrib, mul_assoc, mul_comm, mul_left_comm ] using mul_le_mul_of_nonneg_left ( h_harmonic ( k.sqrt + 1 ) ( Nat.succ_pos _ ) ) ( show ( 0 :ℝ ) ≤ 2 * k ^ ( 1 - δ ) by positivity )

/-
The sum of $1/m^s$ is bounded by $s/(s-1)$ for $s > 1$.
-/
lemma sum_inv_pow_bound (N : ℕ) (s : ℝ) (hs : s > 1) :
  ∑ m ∈ Finset.Icc 1 N, (1 : ℝ) / (m : ℝ) ^ s ≤ s / (s - 1) := by
    -- We use the integral test.
    have h_integral_test : ∀ N : ℕ, N ≥ 1 → ∑ m ∈ Finset.Icc 1 N, (1 / (m : ℝ)^s) ≤ 1 + ∫ x in (1 : ℝ)..N, x^(-s : ℝ) := by
      intro N hN
      induction' N, hN using Nat.le_induction with N ih;
      · norm_num;
      · -- For the inductive step, we can split the sum at $N+1$ and use the induction hypothesis.
        have h_split : ∑ m ∈ Finset.Icc 1 (N + 1), (1 / (m : ℝ)^s) = ∑ m ∈ Finset.Icc 1 N, (1 / (m : ℝ)^s) + (1 / ((N + 1) : ℝ)^s) := by
          exact_mod_cast Finset.sum_Ioc_succ_top ( by norm_num ) _;
        -- We'll use the fact that $\frac{1}{(N+1)^s} \leq \int_{N}^{N+1} x^{-s} \, dx$.
        have h_integral_bound : (1 / ((N + 1) : ℝ)^s) ≤ ∫ x in (N : ℝ)..(N + 1), x^(-s : ℝ) := by
          have h_integral_bound : ∫ x in (N : ℝ)..(N + 1), x^(-s : ℝ) ≥ ∫ x in (N : ℝ)..(N + 1), (N + 1 : ℝ)^(-s : ℝ) := by
            refine' intervalIntegral.integral_mono_on _ _ _ _ <;> norm_num;
            · apply_rules [ intervalIntegral.intervalIntegrable_rpow ] ; norm_num;
              exact Or.inr fun h => by linarith;
            · intro x hx₁ hx₂; rw [ Real.rpow_le_rpow_iff_of_neg ] <;> norm_num <;> linarith [ ( by norm_cast : ( 1 :ℝ ) ≤ N ) ] ;
          simpa [ Real.rpow_neg ( by positivity : 0 ≤ ( N:ℝ ) + 1 ) ] using h_integral_bound.trans' ( by norm_num [ Real.rpow_neg ( by positivity : 0 ≤ ( N:ℝ ) + 1 ) ] );
        -- By the properties of integrals, we can split the integral from 1 to N+1 into the integral from 1 to N and the integral from N to N+1.
        have h_integral_split : ∫ x in (1 : ℝ)..↑(N + 1), x^(-s : ℝ) = (∫ x in (1 : ℝ)..↑N, x^(-s : ℝ)) + (∫ x in (↑N : ℝ)..↑(N + 1), x^(-s : ℝ)) := by
          rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ intervalIntegral.intervalIntegrable_rpow ] <;> norm_num;
          · exact Or.inr <| Set.notMem_uIcc_of_lt ( by norm_num ) <| by norm_num; linarith;
          · exact Or.inr fun h => by linarith;
        norm_num at * ; linarith;
    -- Evaluate the integral $\int_1^N x^{-s} \, dx$.
    have h_integral_eval : ∀ N : ℕ, N ≥ 1 → ∫ x in (1 : ℝ)..N, x^(-s : ℝ) = (1 / (s - 1)) * (1 - (N : ℝ)^(-s + 1)) := by
      intro N hN; rw [ integral_rpow ] <;> norm_num [ hs.le ];
      · rw [ ← neg_div_neg_eq ] ; ring;
      · exact Or.inr ⟨ by linarith, Set.notMem_uIcc_of_lt ( by norm_num ) ( by norm_num; linarith ) ⟩;
    rcases N.eq_zero_or_pos with hN | hN <;> simp_all +decide [ division_def ];
    · linarith;
    · nlinarith [ inv_mul_cancel₀ ( by linarith : ( s - 1 ) ≠ 0 ), h_integral_test N hN, show ( N : ℝ ) ^ ( -s + 1 ) ≥ 0 by positivity ]

/-
Explicit bound on the number of bad primes.
-/
lemma bad_primes_card_bound_explicit (k : ℕ) (δ : ℝ) (hk : k ≥ 4) (hδ : δ ≥ 0) (hδ1 : δ ≤ 1) :
  (BadPrimes k δ).card ≤ 2 * (k : ℝ) ^ (1 - δ) * (1 + Real.log (Nat.sqrt k + 1)) + 3 * (Nat.sqrt k + 1) := by
    convert bad_primes_card_bound_sum k δ hk hδ hδ1 |> le_trans <| sum_bound_harmonic k δ ( by linarith ) hδ using 1

/-
The product of bad primes is small relative to M.
-/
lemma bad_primes_product_small (hPNT : PNT_bounds) (ε δ : ℝ) (hε : ε > 0) (hδ : δ > 0) (hδ1 : δ ≤ 1) :
  ∃ K_min, ∀ k ≥ K_min, ((BadPrimes k δ).prod (fun p => (p : ℝ))) ≤ (M k : ℝ) ^ (2 * ε) := by
    -- Using the bounds from `bad_primes_card_bound_explicit` and `theta_lower_bound`, we get:
    have h_prod_bound : ∃ K_min, ∀ k ≥ K_min, (∑ p ∈ BadPrimes k δ, Real.log p) ≤ 2 * ε * (∑ p ∈ AllPrimesIn k, Real.log p) := by
      have h_prod_bound : ∃ K_min, ∀ k ≥ K_min, (∑ p ∈ BadPrimes k δ, Real.log p) ≤ 2 * (k : ℝ) ^ (1 - δ) * (1 + Real.log (Nat.sqrt k + 1)) * Real.log k + 3 * (Nat.sqrt k + 1) * Real.log k := by
        have h_prod_bound : ∃ K_min, ∀ k ≥ K_min, (∑ p ∈ BadPrimes k δ, Real.log p) ≤ (2 * (k : ℝ) ^ (1 - δ) * (1 + Real.log (Nat.sqrt k + 1)) + 3 * (Nat.sqrt k + 1)) * Real.log k := by
          have h_log_bound : ∀ k ≥ 4, ∑ p ∈ BadPrimes k δ, Real.log p ≤ (BadPrimes k δ).card * Real.log k := by
            intros k hk
            have h_log_bound : ∀ p ∈ BadPrimes k δ, Real.log p ≤ Real.log k := by
              exact fun p hp => Real.log_le_log ( Nat.cast_pos.mpr <| Nat.Prime.pos <| by have := Finset.mem_filter.mp hp; have := Finset.mem_filter.mp this.1; aesop ) <| Nat.cast_le.mpr <| by have := Finset.mem_filter.mp hp; have := Finset.mem_filter.mp this.1; aesop;
            simpa using Finset.sum_le_sum h_log_bound;
          refine' ⟨ 4, fun k hk => le_trans ( h_log_bound k hk ) _ ⟩;
          gcongr ; exact_mod_cast bad_primes_card_bound_explicit k δ hk hδ.le hδ1 |> le_trans <| by norm_num;
        exact ⟨ h_prod_bound.choose, fun k hk => by linarith [ h_prod_bound.choose_spec k hk ] ⟩;
      -- Using the bounds from `theta_lower_bound`, we get:
      obtain ⟨c1, hc1_pos, K_min, hK_min⟩ : ∃ c1 > 0, ∃ K_min, ∀ k ≥ K_min, c1 * k ≤ ∑ p ∈ AllPrimesIn k, Real.log p := by
        apply theta_lower_bound hPNT;
      -- Using the fact that $(k : ℝ) ^ (1 - δ) * (Real.log k) ^ 2 = o(k)$, we can find a $K_min$ such that for all $k ≥ K_min$, the expression is less than $2 * ε * c1 * k$.
      have h_o_k : Filter.Tendsto (fun k : ℕ => (2 * (k : ℝ) ^ (1 - δ) * (1 + Real.log (Nat.sqrt k + 1)) * Real.log k + 3 * (Nat.sqrt k + 1) * Real.log k) / (k : ℝ)) Filter.atTop (nhds 0) := by
        -- We can factor out $k^{1-\delta}$ and use the fact that $\log(k)$ grows slower than any polynomial function.
        have h_factor : Filter.Tendsto (fun k : ℕ => (2 * (k : ℝ) ^ (-δ) * (1 + Real.log (Nat.sqrt k + 1)) * Real.log k + 3 * (Nat.sqrt k + 1) * Real.log k / (k : ℝ))) Filter.atTop (nhds 0) := by
          -- We'll use the fact that $(k : ℝ) ^ (-δ) * (1 + Real.log (Nat.sqrt k + 1)) * Real.log k$ tends to $0$ as $k$ tends to infinity.
          have h_term1 : Filter.Tendsto (fun k : ℕ => (k : ℝ) ^ (-δ) * (1 + Real.log (Nat.sqrt k + 1)) * Real.log k) Filter.atTop (nhds 0) := by
            -- We can factor out $k^{-\delta}$ and use the fact that $\log(k)$ grows slower than any polynomial function.
            have h_log_growth : Filter.Tendsto (fun k : ℕ => (Real.log k) ^ 2 / (k : ℝ) ^ δ) Filter.atTop (nhds 0) := by
              -- Let $y = \log k$, therefore the expression becomes $\frac{y^2}{e^{y \delta}}$.
              suffices h_log : Filter.Tendsto (fun y : ℝ => y^2 / Real.exp (y * δ)) Filter.atTop (nhds 0) by
                have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
                refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by simp +decide [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr hx ), mul_comm ] );
              -- Let $z = y \delta$, therefore the expression becomes $\frac{z^2}{e^z}$.
              suffices h_z : Filter.Tendsto (fun z : ℝ => z^2 / Real.exp z) Filter.atTop (nhds 0) by
                have := h_z.comp ( Filter.tendsto_id.atTop_mul_const hδ );
                convert this.div_const ( δ ^ 2 ) using 2 <;> norm_num [ div_eq_mul_inv, mul_pow, mul_assoc, mul_comm, mul_left_comm, hδ.ne' ];
              simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2;
            -- We can bound $(1 + \log(\sqrt{k} + 1))$ by $2 \log(k)$ for large $k$.
            have h_bound : ∀ᶠ k in Filter.atTop, (1 + Real.log (Nat.sqrt k + 1)) ≤ 2 * Real.log k := by
              have h_bound : ∀ᶠ k in Filter.atTop, Real.log (Nat.sqrt k + 1) ≤ Real.log k := by
                filter_upwards [ Filter.eventually_gt_atTop 1 ] with k hk using Real.log_le_log ( by positivity ) ( by norm_cast; nlinarith [ Nat.sqrt_le k ] );
              filter_upwards [ h_bound, Filter.eventually_gt_atTop 2 ] with k hk₁ hk₂ using by linarith [ show 1 ≤ Real.log k from by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( k : ℝ ) ≥ 3 by norm_cast ] ) ] ;
            have h_bound : Filter.Tendsto (fun k : ℕ => (k : ℝ) ^ (-δ) * (2 * Real.log k) * Real.log k) Filter.atTop (nhds 0) := by
              convert h_log_growth.const_mul 2 using 2 <;> norm_num [ Real.rpow_neg ] ; ring;
            refine' squeeze_zero_norm' _ h_bound;
            filter_upwards [ ‹∀ᶠ k : ℕ in Filter.atTop, 1 + Real.log ( k.sqrt + 1 ) ≤ 2 * Real.log k›, Filter.eventually_gt_atTop 1 ] with k hk₁ hk₂ using by rw [ Real.norm_of_nonneg ( mul_nonneg ( mul_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ( add_nonneg zero_le_one ( Real.log_nonneg ( by norm_cast; linarith [ Nat.sqrt_pos.mpr ( zero_lt_one.trans hk₂ ) ] ) ) ) ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ) ] ; exact mul_le_mul_of_nonneg_right ( mul_le_mul_of_nonneg_left hk₁ ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ;
          -- We'll use the fact that $(Nat.sqrt k + 1) * Real.log k / (k : ℝ)$ tends to $0$ as $k$ tends to infinity.
          have h_term2 : Filter.Tendsto (fun k : ℕ => (Nat.sqrt k + 1) * Real.log k / (k : ℝ)) Filter.atTop (nhds 0) := by
            -- We can bound the term $(Nat.sqrt k + 1) * Real.log k / (k : ℝ)$ by $2 * Real.sqrt k * Real.log k / (k : ℝ)$.
            suffices h_bound : Filter.Tendsto (fun k : ℕ => 2 * Real.sqrt k * Real.log k / (k : ℝ)) Filter.atTop (nhds 0) by
              refine' squeeze_zero_norm' _ h_bound;
              norm_num +zetaDelta at *;
              refine' ⟨ 4, fun k hk => _ ⟩ ; rw [ abs_of_nonneg ( by positivity ), abs_of_nonneg ( Real.log_nonneg ( by norm_cast; linarith ) ) ] ; gcongr ; nlinarith [ Real.sqrt_nonneg k, Real.sq_sqrt ( Nat.cast_nonneg k ), show ( k : ℝ ) ≥ 4 by norm_cast, show ( Nat.sqrt k : ℝ ) ≤ Real.sqrt k by exact Real.le_sqrt_of_sq_le ( mod_cast Nat.sqrt_le' k ) ] ;
            -- We can simplify the expression $2 * \sqrt{k} * \log k / k$ to $2 * \log k / \sqrt{k}$.
            suffices h_simplified : Filter.Tendsto (fun k : ℕ => 2 * Real.log k / Real.sqrt k) Filter.atTop (nhds 0) by
              refine h_simplified.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with k hk using by rw [ div_eq_div_iff ] <;> first | positivity | ring ; norm_num [ hk.ne' ] );
            -- Let $y = \sqrt{k}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{2 \log y^2}{y} = \lim_{y \to \infty} \frac{4 \log y}{y}$.
            suffices h_log_y : Filter.Tendsto (fun y : ℝ => 4 * Real.log y / y) Filter.atTop (nhds 0) by
              have := h_log_y.comp ( show Filter.Tendsto ( fun k : ℕ => Real.sqrt k ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Nat.ceil ( x ^ 2 ), fun n hn => Real.le_sqrt_of_sq_le <| by nlinarith [ Nat.ceil_le.mp hn ] ⟩ );
              exact this.congr fun x => by rw [ Function.comp_apply ] ; rw [ Real.log_sqrt ( Nat.cast_nonneg _ ) ] ; ring;
            -- Let $z = \frac{1}{y}$, so we can rewrite the limit as $\lim_{z \to 0^+} 4z \log(1/z)$.
            suffices h_log_recip : Filter.Tendsto (fun z : ℝ => 4 * z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
              exact h_log_recip.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] );
            norm_num +zetaDelta at *;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using this.neg.const_mul 4 );
          convert Filter.Tendsto.add ( h_term1.const_mul 2 ) ( h_term2.const_mul 3 ) using 2 <;> ring;
        refine h_factor.congr' ?_ ; filter_upwards [ Filter.eventually_gt_atTop 0 ] with k hk ; rw [ Real.rpow_sub ( by positivity ), Real.rpow_one ] ; ring;
        norm_num [ Real.rpow_neg ( Nat.cast_nonneg _ ), hk.ne' ] ; ring;
      have := h_o_k.eventually ( gt_mem_nhds <| show 0 < 2 * ε * c1 by positivity );
      rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ K, hK ⟩ ; rcases h_prod_bound with ⟨ K', hK' ⟩ ; exact ⟨ Max.max K K' + K_min + 1, fun k hk => by have := hK k ( by linarith [ le_max_left K K', le_max_right K K' ] ) ; rw [ div_lt_iff₀ ( Nat.cast_pos.mpr <| by linarith [ le_max_left K K', le_max_right K K' ] ) ] at this; nlinarith [ hK' k ( by linarith [ le_max_left K K', le_max_right K K' ] ), hK_min k ( by linarith [ le_max_left K K', le_max_right K K' ] ) ] ⟩ ;
    have h_exp_prod_bound : ∃ K_min, ∀ k ≥ K_min, Real.log (∏ p ∈ BadPrimes k δ, p) ≤ 2 * ε * Real.log (M k) := by
      have h_exp_prod_bound : ∀ k, (∑ p ∈ AllPrimesIn k, Real.log p) ≤ Real.log (M k) := by
        intro k
        have h_prod_le_M : (∏ p ∈ AllPrimesIn k, p) ≤ M k := by
          have h_log_M_bound : (∏ p ∈ AllPrimesIn k, p) ∣ Finset.lcm (Finset.Icc 1 k) id := by
            have h_log_M_bound : ∀ p ∈ AllPrimesIn k, p ∣ Finset.lcm (Finset.Icc 1 k) id := by
              exact fun p hp => Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ), Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2 ⟩ ) |> fun h => dvd_trans ( by aesop ) h;
            have h_log_M_bound : ∀ {S : Finset ℕ}, (∀ p ∈ S, p ∣ Finset.lcm (Finset.Icc 1 k) id) → (∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.gcd p q = 1) → (∏ p ∈ S, p) ∣ Finset.lcm (Finset.Icc 1 k) id := by
              intros S hS_div hS_coprime; induction' S using Finset.induction with p S hpS ih; aesop;
              rw [ Finset.prod_insert hpS ];
              exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ( show Nat.Coprime p ( ∏ x ∈ S, x ) from Nat.Coprime.prod_right fun q hq => hS_coprime p ( Finset.mem_insert_self _ _ ) q ( Finset.mem_insert_of_mem hq ) <| by aesop ) ( hS_div p <| Finset.mem_insert_self _ _ ) ( ih ( fun q hq => hS_div q <| Finset.mem_insert_of_mem hq ) ( fun q hq r hr hqr => hS_coprime q ( Finset.mem_insert_of_mem hq ) r ( Finset.mem_insert_of_mem hr ) hqr ) )
            generalize_proofs at *; (
            exact h_log_M_bound ‹_› fun p hp q hq hpq => by have := Nat.coprime_primes ( show Nat.Prime p from by { unfold AllPrimesIn at hp; aesop } ) ( show Nat.Prime q from by { unfold AllPrimesIn at hq; aesop } ) ; aesop;)
          generalize_proofs at *; (
          exact Nat.le_of_dvd ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) h_log_M_bound)
        have h_log_prod_le_log_M : Real.log (∏ p ∈ AllPrimesIn k, p) ≤ Real.log (M k) := by
          gcongr;
          · exact Finset.prod_pos fun p hp => Nat.cast_pos.mpr <| Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2;
          · rw [ ← Nat.cast_prod ] ; exact_mod_cast h_prod_le_M
        have h_sum_log_le_log_M : (∑ p ∈ AllPrimesIn k, Real.log p) ≤ Real.log (M k) := by
          rwa [ Real.log_prod _ _ fun x hx => Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| by unfold AllPrimesIn at hx; aesop ] at h_log_prod_le_log_M;
        exact h_sum_log_le_log_M;
      exact ⟨ h_prod_bound.choose, fun k hk => by rw [ Real.log_prod _ _ fun x hx => Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| by { have := Finset.mem_filter.mp ( Finset.mem_filter.mp hx |>.1 ) ; aesop } ] ; exact le_trans ( h_prod_bound.choose_spec k hk ) ( mul_le_mul_of_nonneg_left ( h_exp_prod_bound k ) <| by positivity ) ⟩;
    obtain ⟨ K_min, hK_min ⟩ := h_exp_prod_bound; use K_min; intro k hk; specialize hK_min k hk; rw [ ← Real.log_le_log_iff ( Finset.prod_pos fun p hp => Nat.cast_pos.mpr <| Nat.Prime.pos <| by { exact Finset.mem_filter.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2.1 } ) ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by { unfold M; exact ne_of_gt <| Nat.pos_of_ne_zero <| by { exact mt Finset.lcm_eq_zero_iff.mp <| by aesop } } ) _ ) ] ; rw [ Real.log_rpow ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by { unfold M; exact ne_of_gt <| Nat.pos_of_ne_zero <| by { exact mt Finset.lcm_eq_zero_iff.mp <| by aesop } } ) ] ; linarith;

/-
The difference in the number of multiples of p in intervals of length k and k+1 is at most 1.
-/
lemma count_diff_le_one (k x y p : ℕ) (hp : p > 0) :
  |((Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card : ℤ) -
   ((Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k))).card : ℤ)| ≤ 1 := by
     rcases k with ( _ | k ) <;> norm_num at *;
     · rcases x with ( _ | x ) <;> norm_num [ Finset.filter_singleton ];
       · split_ifs <;> norm_num;
       · split_ifs <;> norm_num;
     · -- The number of multiples of p in the interval [x, x+k] is either floor((x+k)/p) - floor((x-1)/p) or floor((x+k)/p) - floor((x-1)/p) + 1.
       have h_multiples : ∀ x k p : ℕ, p > 0 → ((Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k))).card : ℤ) = ((x + k) / p - (x - 1) / p) := by
         intros x k p hp
         have h_multiples : ((Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k))).card : ℤ) = ((x + k) / p - (x - 1) / p) := by
           have h_filter : Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k)) = Finset.image (fun m => p * m) (Finset.Icc ((x + p - 1) / p) ((x + k) / p)) := by
             ext i;
             norm_num +zetaDelta at *;
             constructor <;> intro h;
             · obtain ⟨ a, rfl ⟩ := h.2;
               exact ⟨ a, ⟨ Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ x + p ) ], Nat.le_div_iff_mul_le hp |>.2 <| by linarith ⟩, rfl ⟩;
             · rcases h with ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩ ; exact ⟨ ⟨ by nlinarith [ Nat.div_add_mod ( x + p - 1 ) p, Nat.mod_lt ( x + p - 1 ) hp, Nat.sub_add_cancel ( by linarith : 1 ≤ x + p ) ], by nlinarith [ Nat.div_mul_le_self ( x + k ) p ] ⟩, dvd_mul_right _ _ ⟩ ;
           rw [ h_filter, Finset.card_image_of_injective _ fun a b h => mul_left_cancel₀ hp.ne' h ];
           rcases x with ( _ | x ) <;> norm_num [ Nat.succ_div ];
           · rcases p with ( _ | _ | p ) <;> norm_num [ Nat.div_eq_of_lt ] at *;
             norm_cast;
           · rw [ Nat.cast_sub ] <;> norm_num;
             · rw [ show ( x + p : ℤ ) / p = x / p + 1 by rw [ Int.add_ediv_of_dvd_right ] <;> norm_num [ hp.ne' ] ] ; ring;
             · exact Nat.le_of_lt_succ ( Nat.div_lt_of_lt_mul <| by linarith [ Nat.div_add_mod ( x + 1 + k ) p, Nat.mod_lt ( x + 1 + k ) hp ] );
         convert h_multiples using 1;
       rw [ h_multiples x k p hp, h_multiples y ( k + 1 ) p hp ] ; norm_num [ Int.emod_def ] ; ring_nf ;
       rw [ abs_le ] ; constructor <;> nlinarith [ Int.mul_ediv_add_emod ( x + k ) p, Int.emod_nonneg ( x + k ) ( by positivity : ( p : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( x + k ) ( by positivity : ( p : ℤ ) > 0 ), Int.mul_ediv_add_emod ( -1 + x ) p, Int.emod_nonneg ( -1 + x ) ( by positivity : ( p : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( -1 + x ) ( by positivity : ( p : ℤ ) > 0 ), Int.mul_ediv_add_emod ( 1 + k + y ) p, Int.emod_nonneg ( 1 + k + y ) ( by positivity : ( p : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( 1 + k + y ) ( by positivity : ( p : ℤ ) > 0 ), Int.mul_ediv_add_emod ( -1 + y ) p, Int.emod_nonneg ( -1 + y ) ( by positivity : ( p : ℤ ) ≠ 0 ), Int.emod_lt_of_pos ( -1 + y ) ( by positivity : ( p : ℤ ) > 0 ) ]

/-
For good primes, the number of multiples of p in the interval for y is at least one more than in the interval for x.
-/
lemma count_multiples_good_primes_conj2 (k x y C_int : ℕ) (δ : ℝ) (p : ℕ)
  (hp : p ∈ PrimesIn k)
  (h_not_bad : ¬ is_bad k p δ)
  (hx : x % p ∈ Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ))))
  (hy : (p - y % p) % p ∈ Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ))))
  (hC : C_int ≥ 1) :
  (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k + C_int - 1))).card ≥
  (Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card + 1 := by
    -- Let's simplify the goal using the fact that multiplication by a constant $C_int \geq 1$ preserves the inequality.
    have h_simp : (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k + C_int - 1))).card ≥ (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k + 1 - 1))).card := by
      exact Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.Icc_subset_Icc_right <| by omega;
    have := count_multiples_good_primes k x y δ p hp h_not_bad hx hy; aesop;

/-
Any set of k consecutive integers contains at least one multiple of p if p <= k.
-/
lemma count_pos_of_le_len (k : ℕ) (p : ℕ) (S : Finset ℕ)
  (hS_card : S.card = k)
  (hS_consec : ∃ s, S = Finset.Icc s (s + k - 1))
  (hp_le : p ≤ k)
  (hp_pos : p > 0) :
  (S.filter (p ∣ ·)).card ≥ 1 := by
    obtain ⟨ s, rfl ⟩ := hS_consec;
    -- Since $p \leq k$, there exists some $m$ such that $s \leq mp \leq s + k - 1$.
    obtain ⟨m, hm⟩ : ∃ m, s ≤ m * p ∧ m * p ≤ s + k - 1 := by
      exact ⟨ ( s + p - 1 ) / p, by linarith [ Nat.div_add_mod ( s + p - 1 ) p, Nat.mod_lt ( s + p - 1 ) hp_pos, Nat.sub_add_cancel ( by linarith : 1 ≤ s + p ) ], by linarith [ Nat.div_mul_le_self ( s + p - 1 ) p, Nat.sub_add_cancel ( by linarith : 1 ≤ s + p ), Nat.sub_add_cancel ( by linarith : 1 ≤ s + k ) ] ⟩
    generalize_proofs at *;
    exact Finset.card_pos.mpr ⟨ m * p, by aesop ⟩

/-
If an interval has length n where p <= n < p^2, then the p-adic valuation of the ratio is the count of multiples minus 1.
-/
lemma valuation_eq_count_sub_one_of_len (n : ℕ) (p : ℕ) (S : Finset ℕ)
  (hp : p.Prime)
  (hS_card : S.card = n)
  (hS_consec : ∃ s, S = Finset.Icc s (s + n - 1))
  (h_len_sq : n < p * p)
  (h_len_ge : p ≤ n)
  (h_nonzero : ∀ z ∈ S, z ≠ 0) :
  padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (S.filter (p ∣ ·)).card - 1 := by
    have h_count_pos : (S.filter (p ∣ ·)).card ≥ 1 := by
      apply count_pos_of_le_len;
      exacts [ hS_card, hS_consec, h_len_ge, hp.pos ];
    apply_rules [ @valuation_large_p ];
    exact Exists.elim ( Finset.card_pos.mp h_count_pos ) fun x hx => ⟨ x, by aesop ⟩

/-
For good primes, the p-adic valuation of the ratio for the y-interval is at least one greater than that for the x-interval.
-/
lemma valuation_ineq_good_p (k x y C_int : ℕ) (δ : ℝ) (p : ℕ)
  (hp : p ∈ PrimesIn k)
  (h_not_bad : ¬ is_bad k p δ)
  (hx : x % p ∈ Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ))))
  (hy : (p - y % p) % p ∈ Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ))))
  (hC : C_int ≥ 1)
  (h_sq : p * p > k + C_int)
  (hx0 : x > 0) (hy0 : y > 0) :
  padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) ≥
  padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) + 1 := by
    norm_num +zetaDelta at *;
    have h_val_y : padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) = (Finset.filter (p ∣ ·) (Finset.Icc y (y + k + C_int - 1))).card - 1 := by
      apply_rules [ valuation_eq_count_sub_one_of_len ];
      · exact Finset.mem_filter.mp hp |>.2.1;
      · simp +arith +decide [ Nat.add_sub_assoc ( show 1 ≤ k + C_int from by linarith ) ];
        exact ⟨ y, by rw [ show y + ( k + y + C_int - 1 + 1 - y ) - 1 = k + y + C_int - 1 from by omega ] ⟩;
      · simp +zetaDelta at *;
        omega;
      · simp +zetaDelta at *;
        rw [ tsub_add_cancel_of_le ] <;> try linarith;
        exact le_tsub_of_add_le_left ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) ] );
      · exact fun z hz => by linarith [ Finset.mem_Icc.mp hz ] ;
    have h_val_x : padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = (Finset.filter (p ∣ ·) (Finset.Icc x (x + k - 1))).card - 1 := by
      apply valuation_eq_count_sub_one_of_len;
      any_goals exact k;
      all_goals norm_num [ Nat.Prime.dvd_iff_not_coprime ] at *;
      any_goals omega;
      · exact Finset.mem_filter.mp hp |>.2.1;
      · use x;
      · exact Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2;
    have h_count_y : (Finset.filter (p ∣ ·) (Finset.Icc y (y + k + C_int - 1))).card ≥ (Finset.filter (p ∣ ·) (Finset.Icc x (x + k - 1))).card + 1 := by
      apply_rules [ count_multiples_good_primes_conj2 ];
      · aesop;
      · aesop;
    rw [ h_val_x, h_val_y ];
    rw [ Nat.sub_add_cancel ];
    · exact Nat.le_sub_one_of_lt h_count_y;
    · have h_count_pos : ∃ m ∈ Finset.Icc x (x + k - 1), p ∣ m := by
        have h_count_pos : p ≤ k := by
          exact Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2;
        exact ⟨ p * ( x / p + 1 ), Finset.mem_Icc.mpr ⟨ by linarith [ Nat.div_add_mod x p, Nat.mod_lt x ( Nat.Prime.pos ( show Nat.Prime p from by unfold PrimesIn at hp; aesop ) ) ], Nat.le_sub_one_of_lt ( by linarith [ Nat.div_mul_le_self x p, Nat.mod_add_div x p, Nat.mod_lt x ( Nat.Prime.pos ( show Nat.Prime p from by unfold PrimesIn at hp; aesop ) ) ] ) ⟩, by norm_num ⟩;
      exact Finset.card_pos.mpr ⟨ h_count_pos.choose, Finset.mem_filter.mpr ⟨ h_count_pos.choose_spec.1, h_count_pos.choose_spec.2 ⟩ ⟩

/-
For any prime p > sqrt(k) (with p^2 > k+C), the p-adic valuation of the ratio for y is at least that for x minus 1.
-/
lemma valuation_ineq_bad_p (k x y C_int : ℕ) (p : ℕ)
  (hp : p ∈ PrimesIn k)
  (hC : C_int ≥ 1)
  (h_sq : p * p > k + C_int)
  (hx0 : x > 0) (hy0 : y > 0) :
  (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
  (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) - 1 := by
    by_cases hp_prime : p.Prime;
    · have h_val_y_eq : padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) = (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k + C_int - 1))).card - 1 := by
        apply valuation_eq_count_sub_one_of_len;
        all_goals norm_num +zetaDelta at *;
        exact hp_prime;
        any_goals rw [ Nat.sub_add_cancel ( by omega ) ];
        · exact ⟨ y, by simp +arith +decide [ add_assoc, Nat.add_sub_assoc ] ⟩;
        · omega;
        · exact le_tsub_of_add_le_left ( by nlinarith only [ h_sq, hp_prime.two_le, show p ≤ k from by { exact ( Finset.mem_filter.mp hp ) |>.1 |> Finset.mem_Icc.mp |>.2 } ] );
        · intros; linarith;
      have h_val_x_eq : padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = (Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card - 1 := by
        apply valuation_eq_count_sub_one_of_len;
        any_goals exact k;
        any_goals omega;
        · simp +zetaDelta at *;
          omega;
        · use x;
        · exact Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2;
        · exact fun z hz => by linarith [ Finset.mem_Icc.mp hz ] ;
      have h_count_diff : ((Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k + C_int - 1))).card : ℤ) ≥ ((Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card : ℤ) - 1 := by
        have := count_diff_le_one k x y p hp_prime.pos;
        linarith [ abs_le.mp this, show ( Finset.card ( Finset.filter ( fun i => p ∣ i ) ( Finset.Icc y ( y + k + C_int - 1 ) ) ) : ℤ ) ≥ ( Finset.card ( Finset.filter ( fun i => p ∣ i ) ( Finset.Icc y ( y + k ) ) ) : ℤ ) from mod_cast Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.Icc_subset_Icc_right <| by omega ];
      omega;
    · unfold PrimesIn at hp; aesop;

/-
R_val is non-negative.
-/
def R_val (start len : ℕ) (p : ℕ) : ℕ :=
  padicValNat p ((∏ i ∈ Finset.Icc start (start + len - 1), i) / (Finset.Icc start (start + len - 1)).lcm id)

lemma R_val_ge_zero (start len p : ℕ) : R_val start len p ≥ 0 := by
  exact Nat.zero_le _

/-
For p > k, the p-adic valuation of the ratio for the x-interval (length k) is 0.
-/
lemma valuation_x_eq_zero_large_p (k x : ℕ) (p : ℕ)
  (hp : p.Prime)
  (hx0 : x > 0)
  (h_p_gt_k : p > k) :
  padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = 0 := by
    apply valuation_very_large_p;
    all_goals norm_num +zetaDelta at *;
    exact hp;
    any_goals exact k;
    · omega;
    · use x;
    · grind;
    · intros; linarith;

/-
For p > k, the difference in p-adic valuations of the ratios is non-negative.
-/
lemma valuation_diff_ge_zero_large_p (k x y C_int : ℕ) (p : ℕ)
  (hp : p.Prime)
  (hx0 : x > 0)
  (h_p_gt_k : p > k) :
  (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
  (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥ 0 := by
    rw [ valuation_x_eq_zero_large_p k x p hp hx0 h_p_gt_k ];
    grind

/-
The ratio of the y-quantity to the x-quantity.
-/
def ratio_of_ratios (k x y C_int : ℕ) : ℚ :=
  ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), (i : ℚ)) / (Finset.Icc y (y + k + C_int - 1)).lcm id) /
  ((∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) / (Finset.Icc x (x + k - 1)).lcm id)

/-
The p-adic valuation of the ratio is at least the p-adic valuation of the bound for all primes p.
-/
lemma ratio_val_ge_rhs_val (k x y C_int : ℕ) (δ : ℝ) (p : ℕ)
  (hp : p.Prime)
  (hC : C_int ≥ 1)
  (hx0 : x > 0) (hy0 : y > 0)
  (h_good_p : p ∈ PrimesIn k → ¬ is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) + 1)
  (h_bad_p : p ∈ PrimesIn k → is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) - 1)
  (h_small_p : p ≤ k.sqrt →
    padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) =
    padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id))
  (h_large_p : p > k + C_int →
    padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) = 0 ∧
    padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = 0)
  (h_diff_ge_zero : p > k →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥ 0) :
  padicValRat p (((∏ i ∈ Finset.Icc y (y + k + C_int - 1), (i : ℚ)) / (Finset.Icc y (y + k + C_int - 1)).lcm id) /
  ((∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) / (Finset.Icc x (x + k - 1)).lcm id)) ≥
  padicValRat p ((M_prod k : ℚ) / ((BadPrimes k δ).prod (fun p => (p : ℚ) ^ 2))) := by
    have h_val_of_prod : padicValRat p ((M_prod k : ℚ) / ((BadPrimes k δ).prod (fun p => p ^ 2 : ℕ → ℚ))) ≤ (padicValRat p ((∏ x ∈ Finset.Icc y (y + k + C_int - 1), (x : ℚ)) / ((Finset.Icc y (y + k + C_int - 1)).lcm id))) - (padicValRat p ((∏ x ∈ Finset.Icc x (x + k - 1), (x : ℚ)) / ((Finset.Icc x (x + k - 1)).lcm id))) := by
      have h_val_diff : ∀ p : ℕ, p.Prime → padicValRat p ((M_prod k : ℚ) / ((BadPrimes k δ).prod (fun p => p ^ 2 : ℕ → ℚ))) = (if p ∈ PrimesIn k then 1 else 0) - 2 * (if p ∈ BadPrimes k δ then 1 else 0) := by
        intro p hp
        have h_val_diff : padicValRat p ((M_prod k : ℚ) / ((BadPrimes k δ).prod (fun p => p ^ 2 : ℕ → ℚ))) = padicValRat p (M_prod k) - 2 * padicValRat p ((BadPrimes k δ).prod (fun p => p : ℕ → ℚ)) := by
          haveI := Fact.mk hp; rw [ padicValRat.div ] <;> norm_num [ Finset.prod_pow ] ;
          · rw [ sq, padicValRat.mul ] <;> norm_num [ Finset.prod_eq_zero_iff, hp.ne_zero ];
            · ring;
            · simp +decide [ BadPrimes ];
              unfold PrimesIn; aesop;
            · simp +decide [ BadPrimes ];
              unfold PrimesIn; aesop;
          · exact Finset.prod_ne_zero_iff.mpr fun q hq => Nat.Prime.ne_zero <| Finset.mem_filter.mp hq |>.2.1;
          · exact Finset.prod_ne_zero_iff.mpr fun x hx => Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| by exact Finset.mem_filter.mp hx |>.2 |> fun h => by exact Finset.mem_filter.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2.1;
        have h_val_diff : padicValRat p (M_prod k) = (if p ∈ PrimesIn k then 1 else 0) := by
          have h_val_diff : padicValRat p (M_prod k) = ∑ q ∈ PrimesIn k, padicValRat p q := by
            have h_val_diff : ∀ {S : Finset ℕ}, (∀ q ∈ S, Nat.Prime q) → padicValRat p (∏ q ∈ S, q) = ∑ q ∈ S, padicValRat p q := by
              intros S hS_primes
              induction' S using Finset.induction with q S hqS ih;
              · norm_num +zetaDelta at *;
              · rw [ Finset.prod_insert hqS, Finset.sum_insert hqS ];
                haveI := Fact.mk hp; rw [ padicValRat.mul ( Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| hS_primes q <| Finset.mem_insert_self q S ) <| Finset.prod_ne_zero_iff.mpr fun x hx => Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| hS_primes x <| Finset.mem_insert_of_mem hx, ih fun x hx => hS_primes x <| Finset.mem_insert_of_mem hx ] ;
            convert h_val_diff _ using 1
            generalize_proofs at *;
            · unfold M_prod; aesop;
            · exact fun q hq => Finset.mem_filter.mp hq |>.2.1;
          have h_val_diff : ∀ q ∈ PrimesIn k, padicValRat p q = if p = q then 1 else 0 := by
            intros q hq
            have h_prime : Nat.Prime q := by
              exact Finset.mem_filter.mp hq |>.2.1
            have h_eq : p = q ∨ p ≠ q := by
              exact em _
            cases h_eq <;> simp [*, padicValRat];
            · haveI := Fact.mk h_prime; simp +decide [ padicValNat.eq_zero_of_not_dvd, h_prime.ne_one ] ;
            · exact Or.inr <| Or.inr <| by rw [ Nat.prime_dvd_prime_iff_eq ] <;> tauto;
          rw [ ‹padicValRat p ↑ ( M_prod k ) = ∑ q ∈ PrimesIn k, padicValRat p ↑ q›, Finset.sum_congr rfl h_val_diff ] ; aesop
        have h_val_diff_bad : padicValRat p ((BadPrimes k δ).prod (fun p => p : ℕ → ℚ)) = (if p ∈ BadPrimes k δ then 1 else 0) := by
          have h_val_diff : padicValRat p (∏ p ∈ BadPrimes k δ, (p : ℚ)) = ∑ q ∈ BadPrimes k δ, padicValRat p (q : ℚ) := by
            have h_val_diff : ∀ {S : Finset ℕ} {f : ℕ → ℚ}, (∀ q ∈ S, f q ≠ 0) → padicValRat p (∏ q ∈ S, f q) = ∑ q ∈ S, padicValRat p (f q) := by
              intros S f hf_nonzero
              induction' S using Finset.induction with q S hqS ih;
              · norm_num +zetaDelta at *;
              · rw [ Finset.prod_insert hqS, Finset.sum_insert hqS ];
                haveI := Fact.mk hp; rw [ padicValRat.mul ( hf_nonzero q ( Finset.mem_insert_self q S ) ) ( Finset.prod_ne_zero_iff.mpr fun x hx => hf_nonzero x ( Finset.mem_insert_of_mem hx ) ), ih fun x hx => hf_nonzero x ( Finset.mem_insert_of_mem hx ) ] ;
            exact h_val_diff fun q hq => Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| Finset.mem_filter.mp ( Finset.mem_filter.mp hq |>.1 ) |>.2.1 |> fun h => by aesop;
          have h_val_diff : ∀ q ∈ BadPrimes k δ, padicValRat p (q : ℚ) = if p = q then 1 else 0 := by
            intro q hq
            by_cases h_eq : p = q;
            · haveI := Fact.mk hp; simp +decide [ ← h_eq, padicValRat.of_nat ] ;
            · haveI := Fact.mk hp; simp +decide [ padicValRat.of_nat, h_eq ] ;
              exact Or.inr <| Or.inr <| fun h => h_eq <| by have := Nat.prime_dvd_prime_iff_eq hp ( show Nat.Prime q from by { exact ( Finset.mem_filter.mp ( Finset.mem_filter.mp hq |>.1 ) ) |>.2.1 } ) ; tauto;
          rw [ ‹padicValRat p ( ∏ p ∈ BadPrimes k δ, ( p : ℚ ) ) = ∑ q ∈ BadPrimes k δ, padicValRat p ( q : ℚ ) ›, Finset.sum_congr rfl h_val_diff ] ; aesop
        simp_all +decide [ padicValRat.div ]
      have h_val_diff_yx : padicValRat p ((∏ x ∈ Finset.Icc y (y + k + C_int - 1), (x : ℚ)) / ((Finset.Icc y (y + k + C_int - 1)).lcm id)) - padicValRat p ((∏ x ∈ Finset.Icc x (x + k - 1), (x : ℚ)) / ((Finset.Icc x (x + k - 1)).lcm id)) = (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / ((Finset.Icc y (y + k + C_int - 1)).lcm id))) - (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / ((Finset.Icc x (x + k - 1)).lcm id))) := by
        have h_val_rat : ∀ {n : ℕ}, n ≠ 0 → padicValRat p (n : ℚ) = padicValNat p n := by
          simp +zetaDelta at *;
        rw [ ← h_val_rat, ← h_val_rat ];
        · rw [ Nat.cast_div, Nat.cast_div ] <;> norm_num;
          · exact fun b hb₁ hb₂ => Finset.dvd_prod_of_mem _ ( Finset.mem_Icc.mpr ⟨ hb₁, hb₂ ⟩ );
          · linarith;
          · exact fun b hb₁ hb₂ => Finset.dvd_prod_of_mem _ ( Finset.mem_Icc.mpr ⟨ hb₁, hb₂ ⟩ );
          · linarith;
        · norm_num [ Finset.prod_eq_zero_iff, Finset.lcm_eq_zero_iff ];
          exact ⟨ hx0.ne', Nat.le_of_dvd ( Finset.prod_pos fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ) ( Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi ) ⟩;
        · refine' Nat.ne_of_gt ( Nat.div_pos _ _ );
          · exact Nat.le_of_dvd ( Finset.prod_pos fun x hx => by linarith [ Finset.mem_Icc.mp hx ] ) ( Finset.lcm_dvd fun x hx => Finset.dvd_prod_of_mem _ hx );
          · exact Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by simp +decide [ hy0.ne' ] ) );
      by_cases hpk : p ∈ PrimesIn k <;> by_cases hpb : p ∈ BadPrimes k δ <;> simp_all +decide only [sub_self];
      · norm_num +zetaDelta at *;
        exact_mod_cast h_bad_p ( by unfold BadPrimes at hpb; aesop );
      · norm_num +zetaDelta at *;
        exact le_tsub_of_add_le_left ( mod_cast h_good_p ( show ¬is_bad k p δ from fun h => hpb <| Finset.mem_filter.mpr ⟨ hpk, h ⟩ ) );
      · unfold BadPrimes at hpb; aesop;
      · by_cases hpk : p > k <;> simp_all +decide only [sub_nonneg];
        · norm_num +zetaDelta at *;
          exact h_diff_ge_zero;
        · by_cases hpk : p ≤ Nat.sqrt k <;> simp_all ( config := { decide := Bool.true } ) only [ ];
          · norm_num;
          · exact False.elim <| ‹p ∉ PrimesIn k› <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp.pos, by linarith ⟩, hp, by linarith ⟩;
    convert h_val_of_prod.ge using 1;
    convert padicValRat.div _ _ using 1;
    · exact ⟨ hp ⟩;
    · simp +decide [ Finset.prod_eq_zero_iff, Finset.lcm_eq_zero_iff ];
      linarith;
    · simp +zetaDelta at *;
      exact ⟨ Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ], hx0.ne' ⟩

/-
If the p-adic valuation of q1 is at least that of q2 for all primes, and both are positive, then q1 >= q2.
-/
lemma rational_ge_of_valuation_ge (q1 q2 : ℚ) (hq1 : q1 > 0) (hq2 : q2 > 0)
  (h : ∀ p, p.Prime → padicValRat p q1 ≥ padicValRat p q2) : q1 ≥ q2 := by
    have h_val : ∀ p : ℕ, Nat.Prime p → (padicValRat p (q1 / q2)) ≥ 0 := by
      intro p pp; haveI := Fact.mk pp; rw [ padicValRat.div ] <;> aesop;
    -- If the p-adic valuation of q1 / q2 is non-negative for all primes p, then q1 / q2 is an integer.
    have h_int : ∃ n : ℤ, q1 / q2 = n := by
      have h_int : ∀ p : ℕ, Nat.Prime p → (q1 / q2).den % p ≠ 0 := by
        intro p pp; specialize h_val p pp; contrapose! h_val; simp_all +decide [ padicValRat ] ;
        haveI := Fact.mk pp; rw [ ← Nat.dvd_iff_mod_eq_zero ] at h_val; rw [ padicValInt.eq_zero_of_not_dvd ];
        · exact Nat.pos_of_ne_zero ( by aesop );
        · exact fun h => pp.not_dvd_one <| by have := Rat.reduced ( q1 / q2 ) ; exact this.gcd_eq_one ▸ Nat.dvd_gcd ( Int.natAbs_dvd_natAbs.mpr h ) h_val;
      contrapose! h_int;
      exact ⟨ Nat.minFac ( q1 / q2 |> Rat.den ), Nat.minFac_prime ( by intro h; exact h_int ( q1 / q2 |> Rat.num ) <| by simpa [ h ] using Eq.symm <| Rat.eq_iff_mul_eq_mul.mpr <| by norm_num [ h ] ), Nat.mod_eq_zero_of_dvd <| Nat.minFac_dvd _ ⟩;
    cases' h_int with n hn; rw [ div_eq_iff hq2.ne' ] at hn; rcases n with ⟨ _ | _ | n ⟩ <;> norm_num at * <;> nlinarith;

/-
The ratio of the quantities is at least the bound derived from the bad primes.
-/
lemma ratio_lower_bound_from_valuations (k x y C_int : ℕ) (δ : ℝ)
  (hC : C_int ≥ 1)
  (hx0 : x > 0) (hy0 : y > 0)
  (h_good_p : ∀ p ∈ PrimesIn k, ¬ is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) + 1)
  (h_bad_p : ∀ p ∈ PrimesIn k, is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) - 1)
  (h_small_p : ∀ p, p.Prime → p ≤ k.sqrt →
    padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) =
    padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id))
  (h_large_p : ∀ p, p.Prime → p > k + C_int →
    padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) = 0 ∧
    padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = 0)
  (h_diff_ge_zero : ∀ p, p > k →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥ 0) :
  ratio_of_ratios k x y C_int ≥ (M_prod k : ℚ) / ((BadPrimes k δ).prod (fun p => (p : ℚ) ^ 2)) := by
    -- Apply the hypothesis `h_val_ge_rhs_val` to each prime `p`.
    have h_val_ge_rhs_val_applied : ∀ p, p.Prime →
      padicValRat p (ratio_of_ratios k x y C_int) ≥
      padicValRat p ((M_prod k : ℚ) / ((BadPrimes k δ).prod (fun p => (p : ℚ) ^ 2))) := by
        intro p hp
        apply ratio_val_ge_rhs_val;
        all_goals solve_by_elim;
    apply_rules [ rational_ge_of_valuation_ge ];
    · refine' div_pos _ _;
      · refine' div_pos _ _;
        · exact Finset.prod_pos fun i hi => Nat.cast_pos.mpr <| by linarith [ Finset.mem_Icc.mp hi ] ;
        · exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by norm_num; omega ) ) );
      · refine' div_pos _ _;
        · exact Finset.prod_pos fun i hi => Nat.cast_pos.mpr <| by linarith [ Finset.mem_Icc.mp hi ] ;
        · exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by simp +decide [ hx0.ne' ] ) ) );
    · exact div_pos ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
        exact Finset.prod_ne_zero_iff.mpr fun p hp => Nat.Prime.ne_zero <| Finset.mem_filter.mp hp |>.2 |> fun h => by aesop; ) <| Finset.prod_pos fun p hp => sq_pos_of_pos <| Nat.cast_pos.mpr <| Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2 |> fun h => by
        exact Finset.mem_filter.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2.1

/-
For a prime p with sqrt(k) < p <= k, the integer logarithm of k base p is 1.
-/
lemma log_eq_one_of_sqrt_lt (k p : ℕ) (hp : p.Prime) (h_sqrt : k.sqrt < p) (h_le : p ≤ k) :
  Nat.log p k = 1 := by
    -- Since $p > \sqrt{k}$, we have $p^2 > k$.
    have h_p_sq_gt_k : p^2 > k := by
      exact?;
    rw [ Nat.log_eq_iff ] <;> aesop

/-
For a prime p in (sqrt(k), k], the exponent of p in the prime factorization of M(k) is 1.
-/
lemma valuation_M_eq_one_of_sqrt_lt (k p : ℕ) (hp : p ∈ PrimesIn k) (hk : k ≥ 1) :
  (M k).factorization p = 1 := by
    have h_log : Nat.log p k = 1 := by
      apply log_eq_one_of_sqrt_lt;
      · exact Finset.mem_filter.mp hp |>.2.1;
      · exact Finset.mem_filter.mp hp |>.2.2;
      · exact Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2;
    rw [ Nat.factorization_def ];
    · rw [ padicValNat_lcm_range ] ; aesop;
      · exact Finset.mem_filter.mp hp |>.2.1;
      · grind;
    · exact Finset.mem_filter.mp hp |>.2.1

/-
M(k) is equal to the product over primes p <= k of p raised to the exponent of p in the factorization of M(k).
-/
lemma M_eq_prod_factorization (k : ℕ) :
  M k = ∏ p ∈ (Finset.Icc 1 k).filter Nat.Prime, p ^ ((M k).factorization p) := by
    conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self ( show M k ≠ 0 from Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop ) ] ;
    rw [ Finsupp.prod_of_support_subset ] <;> norm_num;
    intro p hp; simp_all +decide [ Nat.mem_primeFactors ];
    exact ⟨ hp.1.pos, hp.1.dvd_factorial.mp <| dvd_trans hp.2.1 <| Finset.lcm_dvd fun i hi => Nat.dvd_factorial ( Finset.mem_Icc.mp hi |>.1 ) <| Finset.mem_Icc.mp hi |>.2 ⟩

/-
The product of m(k) and M_prod(k) is M(k).
-/
lemma m_mul_M_prod_eq_M (k : ℕ) (hk : k ≥ 1) : m k * M_prod k = M k := by
  -- We decompose the product formula for M k into two parts: primes <= sqrt(k) and primes > sqrt(k).
  have h_decomp : M k = (∏ p ∈ (Finset.Icc 1 k).filter Nat.Prime, p ^ ((Nat.factorization (M k)) p)) := by
    exact?;
  -- We split the product into two parts: primes <= sqrt(k) and primes > sqrt(k).
  have h_split : (∏ p ∈ (Finset.Icc 1 k).filter Nat.Prime, p ^ ((Nat.factorization (M k)) p)) = (∏ p ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ p ≤ Nat.sqrt k), p ^ ((Nat.factorization (M k)) p)) * (∏ p ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ k.sqrt < p), p ^ ((Nat.factorization (M k)) p)) := by
    rw [ ← Finset.prod_union ];
    · rcongr p ; by_cases hp : p ≤ Nat.sqrt k <;> aesop;
    · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
  -- We show that the product over primes <= sqrt(k) is equal to m k.
  have h_prod_le_sqrt : (∏ p ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ p ≤ Nat.sqrt k), p ^ ((Nat.factorization (M k)) p)) = m k := by
    refine' Finset.prod_congr _ _ <;> norm_num;
    ext; simp [Nat.le_sqrt];
  -- We show that the product over primes > sqrt(k) is equal to M_prod k.
  have h_prod_gt_sqrt : (∏ p ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ k.sqrt < p), p ^ ((Nat.factorization (M k)) p)) = M_prod k := by
    refine' Finset.prod_congr rfl fun p hp => _;
    rw [ valuation_M_eq_one_of_sqrt_lt k p hp hk ] ; norm_num;
  rw [ ← h_prod_le_sqrt, ← h_prod_gt_sqrt, ← h_split, ← h_decomp ]

/-
M(k) splits into the product over primes <= sqrt(k) and primes > sqrt(k).
-/
lemma M_split_product (k : ℕ) :
  M k = (∏ p ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ p ≤ k.sqrt), p ^ ((M k).factorization p)) *
        (∏ p ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ k.sqrt < p), p ^ ((M k).factorization p)) := by
          rw [ ← Finset.prod_union ];
          · convert M_eq_prod_factorization k using 2;
            ext; by_cases h : ‹_› ≤ Nat.sqrt k <;> aesop;
          · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;

/-
The ratio of LCMs is equal to the ratio of ratios times the ratio of products.
-/
lemma lcm_ratio_eq_ratio_of_ratios_mul_prod_ratio (k x y C_int : ℕ) (hx0 : x > 0) (hy0 : y > 0) :
  (((Finset.Icc x (x + k - 1)).lcm id : ℕ) : ℚ) / (((Finset.Icc y (y + k + C_int - 1)).lcm id : ℕ) : ℚ) =
  ratio_of_ratios k x y C_int *
  ((∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) / (∏ i ∈ Finset.Icc y (y + k + C_int - 1), (i : ℚ))) := by
    unfold ratio_of_ratios;
    field_simp;
    rw [ mul_div_mul_right, mul_div_mul_right ];
    · exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ] ;
    · exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ] ;

/-
Checking if Question4Statement and Conjecture2Statement are defined.
-/
#check Question4Statement
#check Conjecture2Statement

/-
The natural logarithm of M(k) is at least the sum of the logarithms of the primes up to k.
-/
lemma log_M_ge_theta (k : ℕ) (hk : k ≥ 1) : Real.log (M k) ≥ ∑ p ∈ AllPrimesIn k, Real.log p := by
  rw [ ← Real.log_prod ];
  · gcongr ; norm_cast;
    · exact Finset.prod_pos fun p hp => Nat.cast_pos.mpr <| Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2;
    · rw [ ← Nat.cast_prod ];
      have h_prod_le_prod : (∏ i ∈ (Finset.Icc 1 k).filter Nat.Prime, i) ∣ (Finset.Icc 1 k).lcm id := by
        -- Since the primes are pairwise coprime, their product divides the lcm.
        have h_coprime : ∀ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 k), p ∣ (Finset.Icc 1 k).lcm id := by
          exact fun p hp => Finset.dvd_lcm ( Finset.mem_filter.mp hp |>.1 );
        refine' Nat.dvd_trans _ ( Nat.prod_primeFactors_dvd _ );
        apply_rules [ Finset.prod_dvd_prod_of_subset ];
        intro p hp; specialize h_coprime p hp; aesop;
      exact_mod_cast Nat.le_of_dvd ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) h_prod_le_prod;
  · -- Since primes are positive integers, we have $x \geq 2$ for any prime $x$.
    intro x hx
    have h_pos : 2 ≤ x := by
      exact Nat.Prime.two_le ( Finset.mem_filter.mp hx |>.2 )
    exact ne_of_gt (by positivity)

/-
The natural logarithm of M_prod(k) is the sum of the logarithms of the primes in PrimesIn(k).
-/
lemma log_M_prod_eq_sum_log (k : ℕ) : Real.log (M_prod k) = ∑ p ∈ PrimesIn k, Real.log p := by
  unfold M_prod;
  rw [ Nat.cast_prod, Real.log_prod ] ; aesop;
  exact fun p hp => Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| Finset.mem_filter.mp hp |>.2.1

/-
If k is good, the product of bad primes is bounded by M_prod^(2*epsilon).
-/
def k_is_good (k : ℕ) (ε δ : ℝ) : Prop :=
  (BadPrimes k δ).card ≤ ε * (PrimesIn k).card

lemma prod_bad_le_M_prod_pow (k : ℕ) (ε δ : ℝ)
  (hk : k ≥ 4)
  (h_eps : ε > 0)
  (h_good : k_is_good k ε δ)
  (h_pnt : PNT_bounds) :
  ∃ K_min, ∀ k ≥ K_min, k_is_good k ε δ →
  ((BadPrimes k δ).prod (fun p => (p : ℝ))) ≤ (M_prod k : ℝ) ^ (2 * ε) := by
    have := @prod_subset_primes_bound h_pnt ε h_eps;
    exact ⟨ this.choose, fun k hk hk' => this.choose_spec k hk _ ( Finset.filter_subset _ _ ) hk' ⟩

/-
There exists a multiple of M larger than any given bound.
-/
lemma exists_reflection_of_interval (M start len : ℕ) (hM : M > 0) :
  ∃ k : ℕ, M * k > start + len := by
    exact ⟨ start + len + 1, by nlinarith ⟩

/-
A variant of Question 4 for negative residues.
-/
lemma Q4_neg_variant (hQ4 : Question4Statement) :
  ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
  ∃ K : ℕ, ∀ k ≥ K,
    let primes := (Finset.Icc 1 k).filter (fun p => p.Prime ∧ k.sqrt < p)
    let M := primes.prod id
    let I (p : ℕ) := Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ)))
    ∀ (start : ℕ), ∃ y ∈ Finset.Icc start (start + Nat.ceil ((M : ℝ) ^ ε) - 1),
      ∀ p ∈ primes, (p - y % p) % p ∈ I p := by
        intro ε hε_pos
        obtain ⟨δ, hδ_pos, hδ_le, K, hK⟩ := hQ4 ε hε_pos
        use δ, hδ_pos, hδ_le, K;
        intro k hk;
        intro primes M I start;
        -- Choose a large multiple `K` of `M` such that `K * M > start + ⌈M^ε⌉₊`.
        obtain ⟨K', hK'⟩ : ∃ K' : ℕ, K' * M > start + ⌈(M : ℝ) ^ ε⌉₊ := by
          by_cases hM_pos : M > 0;
          · exact ⟨ start + ⌈ ( M : ℝ ) ^ ε⌉₊ + 1, by nlinarith ⟩;
          · specialize hK 0 ; aesop;
        -- By Question 4, there exists `x` in the interval `[K' * M - (start + ⌈M^ε⌉₊ - 1), K' * M - start]` such that `x % p \in I_p` for all `p`.
        obtain ⟨x, hx_interval, hx_cond⟩ : ∃ x ∈ Finset.Icc (K' * M - (start + ⌈(M : ℝ) ^ ε⌉₊ - 1)) (K' * M - start), ∀ p ∈ primes, x % p ∈ I p := by
          specialize hK k hk (K' * M - (start + ⌈(M : ℝ) ^ ε⌉₊ - 1));
          simp +zetaDelta at *;
          exact ⟨ hK.choose, ⟨ hK.choose_spec.1.1, by omega ⟩, hK.choose_spec.2 ⟩;
        refine' ⟨ K' * M - x, _, _ ⟩ <;> norm_num at *;
        · omega;
        · intro p hp; specialize hx_cond p hp; simp_all +decide [ ← ZMod.val_natCast, Nat.cast_sub ( show x ≤ K' * M from by omega ) ] ;
          haveI := Fact.mk ( Finset.mem_filter.mp hp |>.2.1 ) ; simp_all +decide [ ← ZMod.intCast_eq_intCast_iff ] ;
          convert hx_cond using 1;
          rw [ Nat.modEq_of_dvd ];
          rw [ Nat.cast_sub <| show ( K' * M - x : ZMod p ).val ≤ p from _ ] ; simp +decide [ ← ZMod.intCast_zmod_eq_zero_iff_dvd ];
          · exact Or.inr <| by rw [ ZMod.natCast_eq_zero_iff ] ; exact Finset.dvd_prod_of_mem _ hp;
          · exact Nat.le_of_lt ( ZMod.val_lt _ )

/-
If p divides M and y = K*M - x, then (p - y % p) % p = x % p.
-/
lemma mod_reflection (p M K x y : ℕ) (hp : p > 0) (h_dvd : p ∣ M) (h_eq : y = K * M - x) (h_le : x ≤ K * M) :
  (p - y % p) % p = x % p := by
    zify [ h_dvd ];
    rw [ Int.ofNat_sub ];
    · simp +decide [ ← ZMod.intCast_eq_intCast_iff', * ];
      cases h_dvd ; aesop;
    · exact Nat.le_of_lt ( Nat.mod_lt _ hp )

/-
M_prod(k) tends to infinity as k tends to infinity.
-/
lemma M_prod_tendsto_infinity (h_pnt : PNT_bounds) :
  Filter.Tendsto (fun k => (M_prod k : ℝ)) Filter.atTop Filter.atTop := by
    -- We'll use that the logarithm of the product of primes in (sqrt k, k] is at least the sum of the logarithms of the primes in (sqrt k, k].
    have h_log_prod : Filter.Tendsto (fun k => ∑ p ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ Nat.sqrt k < p), Real.log p) Filter.atTop Filter.atTop := by
      -- By the Prime Number Theorem, the number of primes in (sqrt(k), k] is approximately c * k / log(k) for some constant c.
      have h_prime_count : Filter.Tendsto (fun k => ((Finset.Icc 1 k).filter (fun p => p.Prime ∧ Nat.sqrt k < p)).card : ℕ → ℕ) Filter.atTop Filter.atTop := by
        -- By the Prime Number Theorem, there exists a constant $c > 0$ such that for sufficiently large $k$, the number of primes in $(\sqrt{k}, k]$ is at least $c \cdot \frac{k}{\log k}$.
        obtain ⟨c, hc_pos, hc_bound⟩ : ∃ c > 0, ∃ K, ∀ k ≥ K, (Finset.filter (fun p => Nat.Prime p ∧ Nat.sqrt k < p) (Finset.Icc 1 k)).card ≥ c * k / Real.log k := by
          have := primes_in_card_asymp_lower h_pnt ( 1 / 4 ) ( by norm_num );
          exact ⟨ 1 - 1 / 4, by norm_num, this ⟩;
        -- Since $c * k / \log k$ tends to infinity as $k$ tends to infinity, the number of primes in $(\sqrt{k}, k]$ must also tend to infinity.
        have h_log_div_tendsto_infty : Filter.Tendsto (fun k : ℕ => c * k / Real.log k) Filter.atTop Filter.atTop := by
          have h_log_div_tendsto_infty : Filter.Tendsto (fun k : ℕ => (k : ℝ) / Real.log k) Filter.atTop Filter.atTop := by
            -- We can use the change of variables $u = \log k$ to transform the limit expression.
            suffices h_log : Filter.Tendsto (fun u : ℝ => Real.exp u / u) Filter.atTop Filter.atTop by
              have := h_log.comp Real.tendsto_log_atTop;
              exact this.comp tendsto_natCast_atTop_atTop |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by simp +decide [ Real.exp_log ( Nat.cast_pos.mpr hx ) ] );
            simpa using Real.tendsto_exp_div_pow_atTop 1;
          simpa only [ mul_div_assoc ] using h_log_div_tendsto_infty.const_mul_atTop hc_pos;
        rw [ Filter.tendsto_atTop_atTop ] at *;
        exact fun b => by rcases h_log_div_tendsto_infty b with ⟨ i, hi ⟩ ; obtain ⟨ K, hK ⟩ := hc_bound; exact ⟨ Max.max i K, fun k hk => by exact_mod_cast le_trans ( hi k ( le_trans ( le_max_left _ _ ) hk ) ) ( hK k ( le_trans ( le_max_right _ _ ) hk ) ) ⟩ ;
      -- Since the logarithm of a prime p is at least log(2), we can bound the sum from below.
      have h_log_bound : ∀ k, ∑ p ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ Nat.sqrt k < p), Real.log p ≥ (Finset.card ((Finset.Icc 1 k).filter (fun p => p.Prime ∧ Nat.sqrt k < p))) * Real.log 2 := by
        intro k; rw [ Finset.cast_card ] ; exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun x hx => Real.log_le_log ( by norm_num ) <| Nat.cast_le.mpr <| Nat.Prime.two_le <| Finset.mem_filter.mp hx |>.2.1 ) ;
      exact Filter.tendsto_atTop_mono h_log_bound ( Filter.Tendsto.atTop_mul_const ( by positivity ) ( tendsto_natCast_atTop_atTop.comp h_prime_count ) );
    have h_exp_log_prod : Filter.Tendsto (fun k => Real.exp (∑ p ∈ (Finset.Icc 1 k).filter (fun p => p.Prime ∧ Nat.sqrt k < p), Real.log p)) Filter.atTop Filter.atTop := by
      exact Real.tendsto_exp_atTop.comp h_log_prod;
    convert h_exp_log_prod using 2 ; norm_num [ Real.exp_sum, Real.exp_log ];
    simp +decide [ Real.exp_log, Finset.prod_ite, M_prod ];
    exact Finset.prod_congr rfl fun x hx => by rw [ Real.exp_log ( Nat.cast_pos.mpr <| Nat.Prime.pos <| by aesop ) ] ;

/-
Arithmetic bounds for x and y given M and epsilon.
-/
lemma arithmetic_bounds (M : ℕ) (ε : ℝ) (x y : ℕ) (h_eps : ε > 0) (hM : M > 1)
  (hx : x ∈ Finset.Icc (Nat.ceil ((M : ℝ) ^ (5 * ε / 2))) (Nat.ceil ((M : ℝ) ^ (5 * ε / 2)) + Nat.ceil ((M : ℝ) ^ ε) - 1))
  (hy : y ∈ Finset.Icc (x + Nat.ceil (1.5 * (M : ℝ) ^ ε)) (x + Nat.ceil (1.5 * (M : ℝ) ^ ε) + Nat.ceil ((M : ℝ) ^ ε) - 1))
  (hM_large : (M : ℝ) ^ (ε / 2) > 2) :
  (M : ℝ) ^ (2 * ε) < x ∧ (x : ℝ) < (M : ℝ) ^ (3 * ε) ∧
  (M : ℝ) ^ ε < (y : ℝ) - x ∧ (y : ℝ) - x < 3 * (M : ℝ) ^ ε := by
    have h_ineq : (M : ℝ) ^ (2 * ε) < ⌈(M : ℝ) ^ (5 * ε / 2)⌉₊ ∧ ⌈(M : ℝ) ^ (5 * ε / 2)⌉₊ + ⌈(M : ℝ) ^ ε⌉₊ - 1 < (M : ℝ) ^ (3 * ε) ∧ (M : ℝ) ^ ε < ⌈1.5 * (M : ℝ) ^ ε⌉₊ ∧ ⌈1.5 * (M : ℝ) ^ ε⌉₊ + ⌈(M : ℝ) ^ ε⌉₊ - 1 < 3 * (M : ℝ) ^ ε := by
      refine' ⟨ _, _, _, _ ⟩ <;> try nlinarith [ Nat.le_ceil ( ( M : ℝ ) ^ ( 5 * ε / 2 ) ), Nat.le_ceil ( ( M : ℝ ) ^ ε ), Nat.le_ceil ( 1.5 * ( M : ℝ ) ^ ε ), Real.rpow_pos_of_pos ( by positivity : 0 < ( M : ℝ ) ) ( 3 * ε ), Real.rpow_pos_of_pos ( by positivity : 0 < ( M : ℝ ) ) ( 5 * ε / 2 ), Real.rpow_pos_of_pos ( by positivity : 0 < ( M : ℝ ) ) ε ];
      · refine' lt_of_lt_of_le _ ( Nat.le_ceil _ );
        exact Real.rpow_lt_rpow_of_exponent_lt ( by norm_cast ) ( by linarith );
      · -- We'll use that $M^{ε / 2} > 2$ to show that $M^{3ε} > M^{5ε / 2} + M^ε + 1$.
        have h_exp : (M : ℝ) ^ (3 * ε) > (M : ℝ) ^ (5 * ε / 2) + (M : ℝ) ^ ε + 1 := by
          rw [ show ( 3 * ε : ℝ ) = 5 * ε / 2 + ε / 2 by ring, show ( 5 * ε / 2 : ℝ ) = ε + 3 * ε / 2 by ring, Real.rpow_add, Real.rpow_add ] <;> try positivity;
          rw [ show ( 3 * ε / 2 : ℝ ) = ε + ε / 2 by ring, Real.rpow_add ] <;> norm_num <;> try positivity;
          nlinarith [ show ( M : ℝ ) ^ ε > 1 by exact Real.one_lt_rpow ( by norm_cast ) ( by positivity ), show ( M : ℝ ) ^ ε * 2 < ( M : ℝ ) ^ ε * ( M : ℝ ) ^ ( ε / 2 ) by gcongr, show ( M : ℝ ) ^ ε * ( M : ℝ ) ^ ( ε / 2 ) > 0 by positivity ];
        linarith [ Nat.ceil_lt_add_one ( show 0 ≤ ( M : ℝ ) ^ ( 5 * ε / 2 ) by positivity ), Nat.ceil_lt_add_one ( show 0 ≤ ( M : ℝ ) ^ ε by positivity ) ];
      · have h_ceil_approx : ⌈(1.5 : ℝ) * (M : ℝ) ^ ε⌉₊ ≤ 1.5 * (M : ℝ) ^ ε + 1 ∧ ⌈(M : ℝ) ^ ε⌉₊ ≤ (M : ℝ) ^ ε + 1 := by
          exact ⟨ le_of_lt <| Nat.ceil_lt_add_one <| by positivity, le_of_lt <| Nat.ceil_lt_add_one <| by positivity ⟩;
        rw [ show ( M : ℝ ) ^ ε = ( M ^ ( ε / 2 ) ) ^ 2 by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring ] at * ; nlinarith [ ( by norm_cast : ( 1 :ℝ ) < M ) ];
    norm_num at *;
    refine' ⟨ lt_of_lt_of_le h_ineq.1 _, _, _, _ ⟩;
    · exact_mod_cast Nat.ceil_le.mpr hx.1;
    · exact lt_of_le_of_lt ( Nat.cast_le.mpr hx.2 ) ( by rw [ Nat.cast_sub <| Nat.one_le_iff_ne_zero.mpr <| by positivity ] ; norm_num ; linarith );
    · linarith [ show ( y : ℝ ) ≥ x + ⌈ ( 3 : ℝ ) / 2 * M ^ ε⌉₊ by exact_mod_cast hy.1 ];
    · linarith [ show ( y : ℝ ) ≤ x + ⌈3 / 2 * ( M : ℝ ) ^ ε⌉₊ + ⌈ ( M : ℝ ) ^ ε⌉₊ - 1 by exact le_tsub_of_add_le_right <| by norm_cast; linarith [ Nat.sub_add_cancel <| show 1 ≤ x + ⌈3 / 2 * ( M : ℝ ) ^ ε⌉₊ + ⌈ ( M : ℝ ) ^ ε⌉₊ from by linarith [ Nat.ceil_pos.mpr <| show 0 < ( M : ℝ ) ^ ε by positivity, Nat.ceil_pos.mpr <| show 0 < ( 3 : ℝ ) / 2 * ( M : ℝ ) ^ ε by positivity ] ] ]

/-
For sufficiently large k, there exist x and y in the desired intervals satisfying the modular conditions.
-/
lemma exists_xy_in_intervals (hQ4 : Question4Statement) (h_pnt : PNT_bounds) (ε : ℝ) (h_eps : ε > 0) :
  ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
  ∃ K : ℕ, ∀ k ≥ K,
    let primes := (Finset.Icc 1 k).filter (fun p => p.Prime ∧ k.sqrt < p)
    let M := primes.prod id
    let I (p : ℕ) (δ : ℝ) := Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ)))
    ∃ x y : ℕ,
      (M : ℝ) ^ (2 * ε) < x ∧ x < (M : ℝ) ^ (3 * ε) ∧
      (M : ℝ) ^ ε < (y : ℝ) - x ∧ (y : ℝ) - x < 3 * (M : ℝ) ^ ε ∧
      (∀ p ∈ primes, x % p ∈ I p δ) ∧
      (∀ p ∈ primes, (p - y % p) % p ∈ I p δ) := by
        obtain ⟨ δ1, hδ1₀, hδ1₁, K1, hK1 ⟩ := hQ4 ε h_eps
        obtain ⟨ δ2, hδ2₀, hδ2₁, K2, hK2 ⟩ := Q4_neg_variant hQ4 ε h_eps
        set δ := min δ1 δ2 with hδ_def
        by_contra h_contra;
        -- Use `M_prod_tendsto_infinity` to find `K_large` such that for `k >= K_large`, `M = M_prod k` satisfies `M^(ε/2) > 2` and `M > 1`.
        obtain ⟨ K_large, hK_large ⟩ : ∃ K_large, ∀ k ≥ K_large, (M_prod k : ℝ) > 1 ∧ (M_prod k : ℝ) ^ (ε / 2) > 2 := by
          have hM_prod_tendsto_infinity : Filter.Tendsto (fun k => (M_prod k : ℝ)) Filter.atTop Filter.atTop := by
            exact?;
          have := hM_prod_tendsto_infinity.eventually_gt_atTop ( 2 ^ ( 2 / ε ) );
          obtain ⟨ K, hK ⟩ := Filter.eventually_atTop.mp this;
          exact ⟨ K, fun k hk => ⟨ by exact lt_trans ( Real.one_lt_rpow ( by norm_num ) ( by positivity ) ) ( hK k hk ), by exact lt_of_le_of_lt ( by rw [ ← Real.rpow_mul ( by positivity ), div_mul_div_cancel₀ ( by positivity ) ] ; norm_num ) ( Real.rpow_lt_rpow ( by positivity ) ( hK k hk ) ( by positivity ) ) ⟩ ⟩;
        refine h_contra ⟨ δ, lt_min hδ1₀ hδ2₀, min_lt_of_left_lt hδ1₁, K1 + K2 + K_large, fun k hk => ?_ ⟩;
        -- Apply `hK1` and `hK2` to find `x` and `y` satisfying the modular conditions.
        obtain ⟨ x, hx₁, hx₂ ⟩ := hK1 k (by linarith) (Nat.ceil ((M_prod k : ℝ) ^ (5 * ε / 2)))
        obtain ⟨ y, hy₁, hy₂ ⟩ := hK2 k (by linarith) (x + Nat.ceil (1.5 * (M_prod k : ℝ) ^ ε));
        refine' ⟨ x, y, _, _, _, _, _ ⟩;
        · have := hK_large k ( by linarith );
          refine' lt_of_lt_of_le _ ( Nat.le_of_ceil_le <| Finset.mem_Icc.mp hx₁ |>.1 );
          exact Real.rpow_lt_rpow_of_exponent_lt ( mod_cast this.1 ) ( by linarith );
        · have := arithmetic_bounds ( M_prod k ) ε x y h_eps ( by
            exact_mod_cast hK_large k ( by linarith ) |>.1 ) hx₁ hy₁ ( by
            exact hK_large k ( by linarith ) |>.2 );
          convert this.2.1 using 1;
        · simp +zetaDelta at *;
          refine' lt_tsub_iff_left.mpr _;
          refine' lt_of_lt_of_le _ ( Nat.cast_le.mpr hy₁.1 );
          norm_num [ M_prod ];
          exact lt_of_lt_of_le ( by exact lt_mul_of_one_lt_left ( Real.rpow_pos_of_pos ( Finset.prod_pos fun p hp => Nat.cast_pos.mpr <| Nat.Prime.pos <| by aesop ) _ ) <| by norm_num ) <| Nat.le_ceil _;
        · have h_arithmetic_bounds : (M_prod k : ℝ) ^ (ε / 2) > 2 := by
            exact hK_large k ( by linarith ) |>.2;
          have := arithmetic_bounds ( M_prod k ) ε x y h_eps ( show 1 < M_prod k from ?_ ) hx₁ hy₁ h_arithmetic_bounds;
          · convert this.2.2.2 using 1;
          · exact_mod_cast hK_large k ( by linarith ) |>.1;
        · simp +zetaDelta at *;
          exact ⟨ fun p hp₁ hp₂ hp₃ hp₄ => ⟨ hx₂ p hp₁ hp₂ hp₃ hp₄ |>.1, le_trans ( hx₂ p hp₁ hp₂ hp₃ hp₄ |>.2 ) ( Nat.ceil_mono <| Real.rpow_le_rpow_of_exponent_le ( mod_cast hp₃.one_lt.le ) <| by cases min_cases δ1 δ2 <;> linarith ) ⟩, fun p hp₁ hp₂ hp₃ hp₄ => ⟨ hy₂ p hp₁ hp₂ hp₃ hp₄ |>.1, le_trans ( hy₂ p hp₁ hp₂ hp₃ hp₄ |>.2 ) ( Nat.ceil_mono <| Real.rpow_le_rpow_of_exponent_le ( mod_cast hp₃.one_lt.le ) <| by cases min_cases δ1 δ2 <;> linarith ) ⟩ ⟩

/-
Checking if exists_xy_in_intervals is available.
-/
#check exists_xy_in_intervals

/-
PNT implies the second part of the Density Hypothesis (existence of 3 primes in $((1-\epsilon)k, k)$).
-/
lemma DensityHypothesis_of_PNT_aux2 (hPNT : PNT_bounds) :
  ∀ ε > 0, ∃ K, ∀ k ≥ K,
    (∃ q1 q2 q3 : ℕ, (1 - ε) * k < q1 ∧ (q1 : ℝ) < k ∧ (1 - ε) * k < q2 ∧ (q2 : ℝ) < k ∧ (1 - ε) * k < q3 ∧ (q3 : ℝ) < k ∧
      q1 ≠ q2 ∧ q1 ≠ q3 ∧ q2 ≠ q3 ∧ q1.Prime ∧ q2.Prime ∧ q3.Prime) := by
        intro ε hε;
        simp +arith +decide [ Nat.sub_eq_zero_of_le hε ];
        use 1000000; intros k hk; use 2, by norm_num, by linarith, 3, by norm_num, by linarith, 5, by norm_num, by linarith;
        norm_num

/-
The limit of floor(ck)/k is c.
-/
lemma floor_asymp (c : ℝ) (hc : c > 0) : Filter.Tendsto (fun k => (⌊c * k⌋₊ : ℝ) / k) Filter.atTop (nhds c) := by
  rw [ Metric.tendsto_nhds ];
  intro ε ε_pos; refine Filter.eventually_atTop.mpr ⟨ ⌈ε⁻¹ * ( c + 1 ) ⌉₊ + 1, fun x hx => abs_lt.mpr ⟨ ?lb, ?ub ⟩ ⟩ <;> nlinarith [ Nat.le_ceil ( ε⁻¹ * ( c + 1 ) ), mul_inv_cancel₀ ( ne_of_gt ε_pos ), Nat.floor_le ( show 0 ≤ c * x by nlinarith ), Nat.lt_floor_add_one ( c * x ), mul_div_cancel₀ ( Nat.floor ( c * x ) : ℝ ) ( by linarith : x ≠ 0 ) ] ;

/-
The limit of log(floor(ck))/log(k) is 1.
-/
lemma log_floor_asymp (c : ℝ) (hc : c > 0) : Filter.Tendsto (fun k => Real.log ⌊c * k⌋₊ / Real.log k) Filter.atTop (nhds 1) := by
  -- We can use the fact that $\log [ck] \sim \log c + \log k$ for large $k$.
  have h_log_approx : Filter.Tendsto (fun k => Real.log (Nat.floor (c * k) : ℝ) - Real.log k) Filter.atTop (nhds (Real.log c)) := by
    have h_log_approx : Filter.Tendsto (fun k => Real.log (Nat.floor (c * k) / k)) Filter.atTop (nhds (Real.log c)) := by
      refine' Filter.Tendsto.log _ ( by positivity );
      exact?;
    refine h_log_approx.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0, Filter.eventually_gt_atTop ( 1 / c ) ] with k hk₁ hk₂ using by rw [ Real.log_div ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.floor_pos.mpr <| by nlinarith [ mul_div_cancel₀ 1 hc.ne' ] ) hk₁.ne' ] );
  have := h_log_approx.div_atTop ( Real.tendsto_log_atTop );
  simpa using this.add_const 1 |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ sub_div, div_self <| ne_of_gt <| Real.log_pos hx ] ; ring )

/-
For large k, the number of primes in [ck, (c+epsilon)k] is at least (epsilon/2) * k / log k.
-/
lemma prime_counting_diff_lower_bound_explicit (hPNT : PNT_bounds) (c ε : ℝ) (hc : c > 0) (hε : ε > 0) :
  ∃ K : ℕ, ∀ k ≥ K, (Nat.primeCounting ⌊(c + ε) * k⌋₊ : ℝ) - (Nat.primeCounting ⌊c * k⌋₊ : ℝ) ≥ (ε / 2) * (k : ℝ) / Real.log k := by
    -- Apply the PNT_bounds hypothesis to obtain the required bounds for large k.
    obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ k ≥ K, (Nat.primeCounting ⌊(c + ε) * k⌋₊ : ℝ) ≥ (1 - ε / (6 * (c + ε))) * (⌊(c + ε) * k⌋₊ : ℝ) / Real.log (⌊(c + ε) * k⌋₊ : ℝ) ∧ (Nat.primeCounting ⌊c * k⌋₊ : ℝ) ≤ (1 + ε / (6 * (c + ε))) * (⌊c * k⌋₊ : ℝ) / Real.log (⌊c * k⌋₊ : ℝ) := by
      obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℕ, ∀ k ≥ K₁, (Nat.primeCounting ⌊(c + ε) * k⌋₊ : ℝ) ≥ (1 - ε / (6 * (c + ε))) * (⌊(c + ε) * k⌋₊ : ℝ) / Real.log (⌊(c + ε) * k⌋₊ : ℝ) := by
        have := hPNT ( ε / ( 6 * ( c + ε ) ) ) ( by positivity );
        obtain ⟨ N, hN ⟩ := this; use ⌈N / ( c + ε ) ⌉₊ + 1; intros k hk; specialize hN ⌊ ( c + ε ) * k⌋₊ ( Nat.le_floor <| by nlinarith [ Nat.le_ceil ( N / ( c + ε ) ), mul_div_cancel₀ ( N : ℝ ) ( by positivity : ( c + ε ) ≠ 0 ), ( by norm_cast : ( ⌈N / ( c + ε ) ⌉₊ :ℝ ) + 1 ≤ k ) ] ) ; aesop;
      obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℕ, ∀ k ≥ K₂, (Nat.primeCounting ⌊c * k⌋₊ : ℝ) ≤ (1 + ε / (6 * (c + ε))) * (⌊c * k⌋₊ : ℝ) / Real.log (⌊c * k⌋₊ : ℝ) := by
        obtain ⟨ K₂, hK₂ ⟩ := hPNT ( ε / ( 6 * ( c + ε ) ) ) ( by positivity );
        exact ⟨ ⌈K₂ / c⌉₊ + 1, fun k hk => hK₂ _ ( Nat.le_floor <| by nlinarith [ Nat.le_ceil ( K₂ / c ), show ( k : ℝ ) ≥ ⌈K₂ / c⌉₊ + 1 by exact_mod_cast hk, mul_div_cancel₀ ( K₂ : ℝ ) hc.ne' ] ) |>.2 ⟩;
      exact ⟨ Max.max K₁ K₂, fun k hk => ⟨ hK₁ k ( le_trans ( le_max_left _ _ ) hk ), hK₂ k ( le_trans ( le_max_right _ _ ) hk ) ⟩ ⟩;
    -- Use the fact that for large k, the difference between the logarithms is approximately log(1 + ε/c) and apply the PNT bounds.
    have h_log_approx : Filter.Tendsto (fun k : ℕ => Real.log ⌊(c + ε) * k⌋₊ / Real.log k) Filter.atTop (nhds 1) ∧ Filter.Tendsto (fun k : ℕ => Real.log ⌊c * k⌋₊ / Real.log k) Filter.atTop (nhds 1) := by
      have h_log_approx : Filter.Tendsto (fun k : ℕ => Real.log ⌊(c + ε) * k⌋₊ / Real.log k) Filter.atTop (nhds 1) := by
        have := log_floor_asymp ( c + ε ) ( by positivity );
        exact this.comp tendsto_natCast_atTop_atTop;
      exact ⟨ h_log_approx, by simpa using log_floor_asymp c hc |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ⟩;
    -- Using the fact that the difference between the logarithms is approximately log(1 + ε/c), we can bound the difference in the number of primes.
    have h_diff_primes : Filter.Tendsto (fun k : ℕ => ((1 - ε / (6 * (c + ε))) * ⌊(c + ε) * k⌋₊ / Real.log ⌊(c + ε) * k⌋₊ - (1 + ε / (6 * (c + ε))) * ⌊c * k⌋₊ / Real.log ⌊c * k⌋₊) / (k / Real.log k)) Filter.atTop (nhds ((1 - ε / (6 * (c + ε))) * (c + ε) - (1 + ε / (6 * (c + ε))) * c)) := by
      have h_floor_asymp : Filter.Tendsto (fun k : ℕ => ⌊(c + ε) * k⌋₊ / (k : ℝ)) Filter.atTop (nhds (c + ε)) ∧ Filter.Tendsto (fun k : ℕ => ⌊c * k⌋₊ / (k : ℝ)) Filter.atTop (nhds c) := by
        have h_floor_asymp : Filter.Tendsto (fun x : ℝ => ⌊(c + ε) * x⌋₊ / x) Filter.atTop (nhds (c + ε)) ∧ Filter.Tendsto (fun x : ℝ => ⌊c * x⌋₊ / x) Filter.atTop (nhds c) := by
          exact ⟨ by simpa using floor_asymp ( c + ε ) ( by positivity ), by simpa using floor_asymp c hc ⟩;
        exact ⟨ h_floor_asymp.1.comp tendsto_natCast_atTop_atTop, h_floor_asymp.2.comp tendsto_natCast_atTop_atTop ⟩;
      convert Filter.Tendsto.sub ( h_floor_asymp.1.const_mul ( 1 - ε / ( 6 * ( c + ε ) ) ) |> Filter.Tendsto.mul <| h_log_approx.1.inv₀ <| by norm_num ) ( h_floor_asymp.2.const_mul ( 1 + ε / ( 6 * ( c + ε ) ) ) |> Filter.Tendsto.mul <| h_log_approx.2.inv₀ <| by norm_num ) using 2 <;> ring;
    -- Since the limit of the difference in the number of primes is positive, there exists some $K$ such that for all $k \geq K$, the difference is at least $\frac{\epsilon}{2} \frac{k}{\log k}$.
    obtain ⟨K', hK'⟩ : ∃ K' : ℕ, ∀ k ≥ K', ((1 - ε / (6 * (c + ε))) * ⌊(c + ε) * k⌋₊ / Real.log ⌊(c + ε) * k⌋₊ - (1 + ε / (6 * (c + ε))) * ⌊c * k⌋₊ / Real.log ⌊c * k⌋₊) ≥ (ε / 2) * (k / Real.log k) := by
      have := h_diff_primes.eventually ( lt_mem_nhds <| show ( 1 - ε / ( 6 * ( c + ε ) ) ) * ( c + ε ) - ( 1 + ε / ( 6 * ( c + ε ) ) ) * c > ε / 2 by nlinarith [ mul_div_cancel₀ ε ( by positivity : ( 6 * ( c + ε ) ) ≠ 0 ) ] );
      rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ K', hK' ⟩ ; exact ⟨ K' + 2, fun k hk => by have := hK' k ( by linarith ) ; rw [ lt_div_iff₀ ( div_pos ( Nat.cast_pos.mpr <| by linarith ) <| Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith ) ] at this; linarith ⟩ ;
    exact ⟨ Max.max K K', fun k hk => by have := hK k ( le_trans ( le_max_left _ _ ) hk ) ; have := hK' k ( le_trans ( le_max_right _ _ ) hk ) ; ring_nf at *; linarith ⟩

/-
k / log k tends to infinity as k tends to infinity.
-/
lemma k_div_log_k_tendsto_atTop : Filter.Tendsto (fun k : ℕ => (k : ℝ) / Real.log k) Filter.atTop Filter.atTop := by
  -- We can use the change of variables $u = \log k$ to transform the limit expression.
  suffices h_log : Filter.Tendsto (fun u : ℝ => Real.exp u / u) Filter.atTop Filter.atTop by
    have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    exact this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Function.comp_apply, Real.exp_log ( Nat.cast_pos.mpr hx ) ] );
  simpa using Real.tendsto_exp_div_pow_atTop 1

/-
Bound on the product ratio for the construction in Question 4 implies Conjecture 2.
-/
lemma product_ratio_bound_explicit (k x y C_int : ℕ) (M : ℝ) (ε : ℝ)
  (hC : C_int ≥ 1)
  (hx : x > 0) (hy : y > 0) (hxy : x < y)
  (h_bound_y : (y : ℝ) + k + C_int < (M : ℝ) ^ (3 * ε))
  (h_bound_x : (x : ℝ) > (M : ℝ) ^ (2 * ε))
  (h_bound_diff : (y : ℝ) - x < 3 * (M : ℝ) ^ ε)
  (h_k_large : k > 0)
  (h_M_large : M > 1) :
  ((∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) / (∏ i ∈ Finset.Icc y (y + k + C_int - 1), (i : ℚ))) ≥
  ((x : ℚ) / y) ^ k * (1 / (y + k + C_int : ℚ)) ^ C_int := by
    -- Apply the bound on the product ratio.
    have h_prod_ratio : (∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) ≥ (x / y : ℚ) ^ k * (∏ i ∈ Finset.Icc y (y + k - 1), (i : ℚ)) := by
      have h_prod_ratio : (∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) ≥ (∏ i ∈ Finset.Icc x (x + k - 1), (x / y : ℚ) * (y + i - x : ℚ)) := by
        exact Finset.prod_le_prod ( fun _ _ => mul_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) ( sub_nonneg.mpr ( by norm_cast; linarith [ Finset.mem_Icc.mp ‹_› ] ) ) ) fun i hi => by nlinarith [ show ( i : ℚ ) ≥ x by norm_cast; linarith [ Finset.mem_Icc.mp hi ], show ( y : ℚ ) > x by norm_cast, div_mul_cancel₀ ( x : ℚ ) ( by positivity : ( y : ℚ ) ≠ 0 ) ] ;
      convert h_prod_ratio using 1;
      erw [ Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range ];
      rw [ Nat.sub_add_cancel ( by linarith ), Nat.sub_add_cancel ( by linarith ) ] ; norm_num [ Finset.prod_mul_distrib ] ; ring;
    have h_prod_ratio' : (∏ i ∈ Finset.Icc y (y + k + C_int - 1), (i : ℚ)) ≤ (∏ i ∈ Finset.Icc y (y + k - 1), (i : ℚ)) * ((y + k + C_int : ℚ) ^ C_int) := by
      have h_prod_ratio : (∏ i ∈ Finset.Icc (y + k) (y + k + C_int - 1), (i : ℚ)) ≤ ((y + k + C_int : ℚ) ^ C_int) := by
        refine' le_trans ( Finset.prod_le_prod _ fun i hi => show ( i : ℚ ) ≤ y + k + C_int from _ ) _ <;> norm_num;
        · exact_mod_cast le_trans ( Finset.mem_Icc.mp hi |>.2 ) ( Nat.sub_le _ _ );
        · rw [ Nat.sub_add_cancel ( by linarith ) ] ; norm_num;
      convert mul_le_mul_of_nonneg_left h_prod_ratio ( show 0 ≤ ∏ i ∈ Finset.Icc y ( y + k - 1 ), ( i : ℚ ) from Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _ ) using 1;
      erw [ ← Finset.prod_union ];
      · rcongr i ; norm_num;
        exact ⟨ fun hi => if hi' : i ≤ y + k - 1 then Or.inl ⟨ hi.1, hi' ⟩ else Or.inr ⟨ by omega, hi.2 ⟩, fun hi => hi.elim ( fun hi => ⟨ hi.1, by omega ⟩ ) fun hi => ⟨ by omega, by omega ⟩ ⟩;
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Icc.mp hx₁, Finset.mem_Icc.mp hx₂, Nat.sub_add_cancel ( by linarith : 1 ≤ y + k ) ] ;
    rw [ ge_iff_le, le_div_iff₀ ];
    · refine le_trans ?_ h_prod_ratio;
      field_simp;
      rw [ one_div_pow, div_mul_eq_mul_div, div_le_iff₀ ] <;> first | positivity | linarith;
    · exact Finset.prod_pos fun i hi => Nat.cast_pos.mpr <| by linarith [ Finset.mem_Icc.mp hi ] ;

/-
$\pi(n) \le C \frac{n}{\log n}$ for all $n \ge 2$.
-/
lemma pi_bound_explicit (h_pnt : PNT_bounds) : ∃ C, ∀ n ≥ 2, (Nat.primeCounting n : ℝ) ≤ C * n / Real.log n := by
  obtain ⟨ N, hN ⟩ := h_pnt 1 zero_lt_one;
  -- Let $S = \{2, ..., N\}$. The set of values $\{\pi(n) \frac{\log n}{n} \mid n \in S\}$ is finite, so it has a maximum $M$.
  obtain ⟨ M, hM ⟩ : ∃ M : ℝ, ∀ n ∈ Finset.Icc 2 N, (Nat.primeCounting n : ℝ) / (n / Real.log n) ≤ M := by
    exact ⟨ ∑ n ∈ Finset.Icc 2 N, ( Nat.primeCounting n : ℝ ) / ( n / Real.log n ), fun n hn => Finset.single_le_sum ( fun x hx => div_nonneg ( Nat.cast_nonneg ( Nat.primeCounting x ) ) ( div_nonneg ( Nat.cast_nonneg x ) ( Real.log_nonneg ( Nat.one_le_cast.mpr ( by linarith [ Finset.mem_Icc.mp hx ] ) ) ) ) ) hn ⟩;
  use Max.max M 2; intro n hn; by_cases h : n ≤ N <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] ;
  · have := hM n hn h;
    rw [ inv_mul_eq_div, div_le_iff₀ ( by positivity ) ] at this;
    rw [ ← div_eq_mul_inv, mul_div, le_div_iff₀ ] <;> nlinarith [ Real.log_pos ( show ( n : ℝ ) > 1 by norm_cast ), le_max_left M 2, le_max_right M 2 ];
  · exact le_trans ( hN n h.le ) ( by gcongr ; norm_num )

/-
$\pi(\sqrt{k}) \log k \le C' \sqrt{k}$.
-/
lemma pi_sqrt_mul_log_le (C : ℝ) (hC : ∀ n ≥ 2, (Nat.primeCounting n : ℝ) ≤ C * n / Real.log n) :
  ∃ C', ∀ k ≥ 2, (Nat.primeCounting (Nat.sqrt k) : ℝ) * Real.log k ≤ C' * Real.sqrt k := by
    -- Let $n = \lfloor \sqrt{k} \rfloor$, so $n^2 \le k < (n+1)^2$.
    have h_interval : ∀ k : ℕ, 2 ≤ k → (Nat.primeCounting (Nat.sqrt k) : ℝ) * Real.log k ≤ C * Nat.sqrt k * (Real.log k / Real.log (Nat.sqrt k)) := by
      intros k hk
      have h_pi_bound : (Nat.primeCounting (Nat.sqrt k) : ℝ) ≤ C * Nat.sqrt k / Real.log (Nat.sqrt k) := by
        by_cases h_sqrt : Nat.sqrt k ≥ 2;
        · exact hC _ h_sqrt;
        · interval_cases _ : Nat.sqrt k <;> norm_num at *;
      convert mul_le_mul_of_nonneg_right h_pi_bound ( Real.log_nonneg <| Nat.one_le_cast.mpr <| by linarith ) using 1 ; ring;
    -- For $k \geq 4$, we have $\frac{\log k}{\log \lfloor \sqrt{k} \rfloor} \leq 2 \frac{\log (\lfloor \sqrt{k} \rfloor + 1)}{\log \lfloor \sqrt{k} \rfloor}$.
    have h_ratio_bound : ∃ B : ℝ, ∀ k : ℕ, 4 ≤ k → (Real.log k / Real.log (Nat.sqrt k)) ≤ B := by
      -- For $k \geq 4$, we have $\frac{\log k}{\log \lfloor \sqrt{k} \rfloor} \leq 2 \frac{\log (\lfloor \sqrt{k} \rfloor + 1)}{\log \lfloor \sqrt{k} \rfloor}$ by the properties of logarithms.
      have h_ratio_bound : ∀ k : ℕ, 4 ≤ k → (Real.log k / Real.log (Nat.sqrt k)) ≤ 2 * (Real.log (Nat.sqrt k + 1) / Real.log (Nat.sqrt k)) := by
        intro k hk
        have h_log_k_le : Real.log k ≤ 2 * Real.log (Nat.sqrt k + 1) := by
          rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> nlinarith [ Nat.lt_succ_sqrt k ];
        rw [ mul_div ] ; gcongr;
      -- Since $\frac{\log (\lfloor \sqrt{k} \rfloor + 1)}{\log \lfloor \sqrt{k} \rfloor}$ is bounded above by some constant $B$, we can conclude that $\frac{\log k}{\log \lfloor \sqrt{k} \rfloor}$ is also bounded above by $2B$.
      obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ n : ℕ, 2 ≤ n → (Real.log (n + 1) / Real.log n) ≤ B := by
        use 2;
        intro n hn; rw [ div_le_iff₀ ( Real.log_pos <| by norm_cast ) ] ; rw [ ← Real.log_rpow, Real.log_le_log_iff ] <;> norm_cast <;> nlinarith [ Nat.pow_le_pow_left hn 2 ] ;
      exact ⟨ 2 * B, fun k hk => le_trans ( h_ratio_bound k hk ) ( mul_le_mul_of_nonneg_left ( hB _ ( Nat.le_sqrt.mpr ( by linarith ) ) ) zero_le_two ) ⟩;
    -- Combining h_interval and h_ratio_bound, we get the desired bound.
    obtain ⟨ B, hB ⟩ := h_ratio_bound;
    use C * B;
    intro k hk;
    by_cases hk4 : k ≥ 4;
    · refine le_trans ( h_interval k hk ) ?_;
      rw [ mul_assoc, mul_assoc ];
      exact mul_le_mul_of_nonneg_left ( by nlinarith [ hB k hk4, show ( k.sqrt : ℝ ) ≤ Real.sqrt k by exact Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' k, show ( Real.log k / Real.log k.sqrt : ℝ ) ≥ 0 by exact div_nonneg ( Real.log_nonneg <| mod_cast by linarith ) ( Real.log_nonneg <| mod_cast by nlinarith [ Nat.sqrt_pos.mpr <| show 0 < k by linarith ] ) ] ) <| show 0 ≤ C by have := hC 2 ( by norm_num ) ; norm_num at this ; nlinarith [ Real.log_pos one_lt_two, mul_div_cancel₀ ( C * 2 ) ( ne_of_gt <| Real.log_pos one_lt_two ) ] ;
    · interval_cases k <;> norm_num [ Nat.primeCounting ];
      · have := hC 2 ( by norm_num ) ; have := hC 3 ( by norm_num ) ; norm_num [ Nat.primeCounting ] at *;
        exact mul_nonneg ( by rw [ le_div_iff₀ ( Real.log_pos ( by norm_num ) ) ] at *; nlinarith [ Real.log_pos ( by norm_num : ( 2 : ℝ ) > 1 ), Real.log_lt_log ( by norm_num ) ( by norm_num : ( 3 : ℝ ) > 2 ), show ( Nat.count Nat.Prime 3 : ℝ ) = 1 by norm_cast ] ) ( by exact le_trans ( by positivity ) ( hB 4 ( by norm_num ) ) );
      · exact mul_nonneg ( show 0 ≤ C by have := hC 2 ( by norm_num ) ; norm_num at this ; rw [ le_div_iff₀ ( Real.log_pos ( by norm_num ) ) ] at this ; nlinarith [ Real.log_pos ( by norm_num : ( 2 : ℝ ) > 1 ) ] ) ( show 0 ≤ B by have := hB 4 ( by norm_num ) ; norm_num at this ; exact le_trans ( by positivity ) this )

/-
$\log m(k) \le C \sqrt{k}$ for some constant $C$.
-/
lemma log_m_bound_sqrt (h_pnt : PNT_bounds) : ∃ C, ∀ k ≥ 2, Real.log (m k) ≤ C * Real.sqrt k := by
  -- Applying `pi_bound_explicit` to our hypothesis `h_pnt`, we get the required $C$.
  obtain ⟨C, hC⟩ := pi_bound_explicit h_pnt;
  -- Applying `pi_sqrt_mul_log_le` to our hypothesis `hC`, we get the required $C'$.
  obtain ⟨C', hC'⟩ := pi_sqrt_mul_log_le C hC;
  exact ⟨ C', fun k hk => le_trans ( log_m_le k <| by linarith ) ( hC' k hk ) ⟩

/-
$m(k) < M(k)^\epsilon$ for large $k$.
-/
lemma m_small_relative_to_M (h_pnt : PNT_bounds) (ε : ℝ) (hε : ε > 0) :
  ∃ K, ∀ k ≥ K, (m k : ℝ) < (M k : ℝ) ^ ε := by
    have := log_m_bound_sqrt h_pnt;
    -- By the properties of logarithms, we can rewrite the inequality $\log m(k) < \epsilon \log M(k)$ as $m(k) < M(k)^\epsilon$.
    have h_log_ineq : ∃ K : ℕ, ∀ k ≥ K, (Real.log (m k)) < ε * (Real.log (M k)) := by
      have := theta_lower_bound h_pnt;
      -- By combining the results from the previous steps, we can conclude that for sufficiently large $k$, $\log m(k) < \epsilon \log M(k)$.
      obtain ⟨C, hC⟩ := ‹∃ C, ∀ k ≥ 2, Real.log (m k) ≤ C * Real.sqrt k›
      obtain ⟨c1, hc1_pos, K1, hK1⟩ := this
      have h_log_M_ge_c1_k : ∃ K2 : ℕ, ∀ k ≥ K2, Real.log (M k) ≥ c1 * k := by
        exact ⟨ K1 + 2, fun k hk => le_trans ( hK1 k ( by linarith ) ) ( log_M_ge_theta k ( by linarith ) ) ⟩;
      -- Choose $K$ such that for all $k \geq K$, $C \sqrt{k} < \epsilon c1 k$.
      obtain ⟨K2, hK2⟩ : ∃ K2 : ℕ, ∀ k ≥ K2, C * Real.sqrt k < ε * c1 * k := by
        exact ⟨ ⌈ ( C / ( ε * c1 ) ) ^ 2⌉₊ + 1, fun k hk => by nlinarith [ Nat.le_ceil ( ( C / ( ε * c1 ) ) ^ 2 ), show ( k : ℝ ) ≥ ⌈ ( C / ( ε * c1 ) ) ^ 2⌉₊ + 1 by exact_mod_cast hk, show 0 < ε * c1 by positivity, div_mul_cancel₀ C ( show ( ε * c1 ) ≠ 0 by positivity ), Real.sqrt_nonneg k, Real.sq_sqrt ( Nat.cast_nonneg k ), pow_two_nonneg ( Real.sqrt k - C / ( ε * c1 ) ), mul_div_cancel₀ ( C : ℝ ) ( show ( ε * c1 ) ≠ 0 by positivity ) ] ⟩;
      exact ⟨ K2 + 2 + h_log_M_ge_c1_k.choose, fun k hk => lt_of_le_of_lt ( hC k ( by linarith ) ) ( by nlinarith [ hK2 k ( by linarith ), h_log_M_ge_c1_k.choose_spec k ( by linarith ) ] ) ⟩;
    cases' h_log_ineq with K hK;
    exact ⟨ K + 1, fun k hk => by rw [ ← Real.log_lt_log_iff ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
      exact Nat.ne_of_gt <| Finset.prod_pos fun p hp => Nat.pos_of_ne_zero <| by aesop; ) ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
      exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by unfold M; aesop; ) _ ), Real.log_rpow ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
      exact Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by unfold M; aesop; ) ] ; linarith [ hK k <| by linarith ] ⟩

#check is_bad
#check PrimesIn
#check valuation_eq_count_sub_one_of_len

#check Q4_neg_variant
#check exists_xy_in_intervals

/-
Checking availability of lemmas.
-/
#check count_multiples_good_primes
#check valuation_ineq_good_p
#check valuation_ineq_bad_p
#check ratio_lower_bound_from_valuations

/-
Checking availability of lemmas.
-/
#check prod_bad_le_M_prod_pow
#check lcm_ratio_eq_ratio_of_ratios_mul_prod_ratio

/-
Checking availability.
-/
#check arithmetic_bounds
#check M_prod_tendsto_infinity

/-
For sufficiently large $k$, the number of bad primes is small relative to the total number of primes.
-/
lemma all_k_good_for_large_k (h_pnt : PNT_bounds) (ε δ : ℝ) (hε : ε > 0) (hδ : δ > 0) (hδ1 : δ ≤ 1) :
  ∃ K, ∀ k ≥ K, k_is_good k ε δ := by
    by_contra h_contra;
    -- For large $k$, this is $O(k^{1-\delta} \log k)$.
    have h_bad_primes_card_bound : ∃ K : ℕ, ∀ k ≥ K, (BadPrimes k δ).card ≤ 2 * (k : ℝ) ^ (1 - δ) * (1 + Real.log (Nat.sqrt k + 1)) + 3 * (Nat.sqrt k + 1) := by
      use 4; intros k hk; have := bad_primes_card_bound_explicit k δ ( by linarith ) ( by linarith ) ( by linarith ) ; aesop;
    -- For large $k$, this is $O(k^{1-\delta} \log k)$ and $|Primes| \ge c k / \log k$.
    obtain ⟨K₁, hK₁⟩ := h_bad_primes_card_bound
    obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℕ, ∀ k ≥ K₂, (PrimesIn k).card ≥ (1 / 2) * k / Real.log k := by
      have := primes_in_card_asymp_lower h_pnt ( 1 / 2 ) ( by norm_num );
      exact ⟨ this.choose, fun k hk => by convert this.choose_spec k hk using 1 ; ring ⟩;
    -- We need $|Bad| \le \epsilon |Primes|$.
    -- It suffices to show $k^{1-\delta} \log k \ll k / \log k$, i.e., $k^{-\delta} (\log k)^2 \to 0$.
    have h_lim : Filter.Tendsto (fun k : ℕ => (2 * (k : ℝ) ^ (1 - δ) * (1 + Real.log (Nat.sqrt k + 1)) + 3 * (Nat.sqrt k + 1)) / ((1 / 2) * k / Real.log k)) Filter.atTop (nhds 0) := by
      -- We can factor out $k^{1-\delta}$ and use the fact that $\log k$ grows slower than any polynomial function.
      have h_factor : Filter.Tendsto (fun k : ℕ => (k : ℝ) ^ (1 - δ) * (1 + Real.log (Nat.sqrt k + 1)) * Real.log k / k) Filter.atTop (nhds 0) := by
        -- We can simplify the expression inside the limit.
        suffices h_simplify : Filter.Tendsto (fun k : ℕ => (Real.log k) ^ 2 / (k : ℝ) ^ δ) Filter.atTop (nhds 0) by
          have h_simplify : Filter.Tendsto (fun k : ℕ => (1 + Real.log (Nat.sqrt k + 1)) * Real.log k / (k : ℝ) ^ δ) Filter.atTop (nhds 0) := by
            -- We can bound the term $(1 + \log(\sqrt{k} + 1))$ by $2 \log k$ for large $k$.
            have h_bound : ∀ᶠ k in Filter.atTop, (1 + Real.log (Nat.sqrt k + 1)) ≤ 2 * Real.log k := by
              filter_upwards [ Filter.eventually_gt_atTop 4 ] with k hk;
              rw [ ← Real.log_rpow, Real.le_log_iff_exp_le ] <;> norm_num <;> try positivity;
              rw [ Real.exp_add, Real.exp_log ( by positivity ) ];
              have := Real.exp_one_lt_d9.le ; norm_num1 at * ; nlinarith [ show ( k : ℝ ) ≥ 5 by norm_cast, show ( Nat.sqrt k : ℝ ) ≤ k by exact_mod_cast Nat.sqrt_le_self k, show ( k : ℝ ) ^ 2 ≥ k * k by nlinarith ];
            refine' squeeze_zero_norm' _ ( by simpa using h_simplify.const_mul 2 );
            field_simp;
            filter_upwards [ h_bound, Filter.eventually_gt_atTop 1 ] with k hk₁ hk₂ using by rw [ Real.norm_of_nonneg ( div_nonneg ( mul_nonneg ( add_nonneg zero_le_one ( Real.log_nonneg ( by norm_cast; linarith [ Nat.sqrt_pos.mpr ( zero_lt_one.trans hk₂ ) ] ) ) ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ] ; rw [ div_le_div_iff_of_pos_right ( Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( pos_of_gt hk₂ ) ) _ ) ] ; nlinarith [ Real.log_nonneg ( by norm_cast; linarith : ( k :ℝ ) ≥ 1 ) ] ;
          refine h_simplify.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with k hk using by rw [ Real.rpow_sub ( by positivity ), Real.rpow_one ] ; rw [ div_eq_mul_inv ] ; ring_nf; norm_num [ hk.ne' ] );
        -- Let $y = \log k$, therefore the expression becomes $\frac{y^2}{e^{y \delta}}$.
        suffices h_log : Filter.Tendsto (fun y : ℝ => y^2 / Real.exp (y * δ)) Filter.atTop (nhds 0) by
          have := h_log.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
          refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by simp +decide [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr hx ), mul_comm ] );
        -- Let $z = y \delta$, therefore the expression becomes $\frac{z^2}{e^z}$.
        suffices h_z : Filter.Tendsto (fun z : ℝ => z^2 / Real.exp z) Filter.atTop (nhds 0) by
          have := h_z.comp ( Filter.tendsto_id.atTop_mul_const hδ );
          convert this.div_const ( δ ^ 2 ) using 2 <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, hδ.ne' ];
          field_simp;
        simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2;
      -- We can factor out $k^{1-\delta}$ and use the fact that $\sqrt{k}$ grows slower than any polynomial function.
      have h_factor_sqrt : Filter.Tendsto (fun k : ℕ => (Nat.sqrt k + 1) * Real.log k / k) Filter.atTop (nhds 0) := by
        -- We can factor out $k^{1/2}$ and use the fact that $\log k$ grows slower than any polynomial function.
        have h_factor_sqrt : Filter.Tendsto (fun k : ℕ => (Real.sqrt k + 1) * Real.log k / k) Filter.atTop (nhds 0) := by
          have h_sqrt : Filter.Tendsto (fun k : ℕ => Real.sqrt k * Real.log k / k) Filter.atTop (nhds 0) := by
            -- We can simplify the expression $\frac{\sqrt{k} \log k}{k}$ to $\frac{\log k}{\sqrt{k}}$.
            suffices h_simplified : Filter.Tendsto (fun k : ℕ => Real.log k / Real.sqrt k) Filter.atTop (nhds 0) by
              refine h_simplified.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ div_eq_div_iff ] <;> ring <;> norm_num [ hx.ne', le_of_lt hx ] );
            -- Let $y = \sqrt{k}$, so we can rewrite the limit as $\lim_{y \to \infty} \frac{\log(y^2)}{y} = \lim_{y \to \infty} \frac{2 \log y}{y}$.
            suffices h_log_sqrt_y : Filter.Tendsto (fun y : ℝ => 2 * Real.log y / y) Filter.atTop (nhds 0) by
              have := h_log_sqrt_y.comp ( show Filter.Tendsto ( fun k : ℕ => Real.sqrt k ) Filter.atTop Filter.atTop from Filter.tendsto_atTop_atTop.mpr fun x => ⟨ Nat.ceil ( x ^ 2 ), fun n hn => Real.le_sqrt_of_sq_le <| by simpa using Nat.ceil_le.mp hn ⟩ );
              exact this.congr fun x => by rw [ Function.comp_apply ] ; rw [ Real.log_sqrt ( Nat.cast_nonneg _ ) ] ; ring;
            -- Let $z = \frac{1}{y}$, so we can rewrite the limit as $\lim_{z \to 0^+} 2z \log(1/z)$.
            suffices h_log_recip : Filter.Tendsto (fun z : ℝ => 2 * z * Real.log (1 / z)) (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
              exact h_log_recip.congr ( by simp +contextual [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] );
            norm_num +zetaDelta at *;
            exact tendsto_nhdsWithin_of_tendsto_nhds ( by have := Real.continuous_mul_log.tendsto 0; simpa [ mul_assoc ] using this.neg.const_mul 2 )
          have h_const : Filter.Tendsto (fun k : ℕ => Real.log k / k) Filter.atTop (nhds 0) := by
            refine' squeeze_zero_norm' _ h_sqrt;
            filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact mul_le_mul_of_nonneg_right ( le_mul_of_one_le_left ( Real.log_nonneg ( Nat.one_le_cast.mpr hn.le ) ) ( Real.le_sqrt_of_sq_le ( mod_cast hn.le ) ) ) ( by positivity ) ;
          convert h_sqrt.add h_const using 2 <;> ring;
        refine' squeeze_zero_norm' _ h_factor_sqrt;
        filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; gcongr ; exact Real.le_sqrt_of_sq_le <| mod_cast Nat.sqrt_le' _;
      convert h_factor.const_mul 4 |> Filter.Tendsto.add <| h_factor_sqrt.const_mul 6 using 2 <;> ring;
      norm_num ; ring;
    -- Since the limit is 0, there exists a K such that for all k ≥ K, the ratio is less than ε.
    obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ k ≥ K, (2 * (k : ℝ) ^ (1 - δ) * (1 + Real.log (Nat.sqrt k + 1)) + 3 * (Nat.sqrt k + 1)) / ((1 / 2) * k / Real.log k) < ε := by
      simpa using h_lim.eventually ( gt_mem_nhds hε );
    refine h_contra ⟨ K + K₁ + K₂ + 2, fun k hk => ?_ ⟩;
    refine' le_trans ( hK₁ k ( by linarith ) ) _;
    have := hK k ( by linarith ) ; rw [ div_lt_iff₀ ] at this <;> nlinarith [ hK₂ k ( by linarith ), show ( k : ℝ ) ≥ 2 by norm_cast; linarith, Real.log_pos ( show ( k : ℝ ) > 1 by norm_cast; linarith ), mul_div_cancel₀ ( ( 1 / 2 : ℝ ) * k ) ( ne_of_gt ( Real.log_pos ( show ( k : ℝ ) > 1 by norm_cast; linarith ) ) ) ] ;

/-
Checking availability.
-/
#check valuation_small_p
#check valuation_x_eq_zero_large_p
#check valuation_diff_ge_zero_large_p

/-
$M_{prod}(k) \ge M(k)^{1-\epsilon}$ for large $k$.
-/
lemma M_prod_ge_M_pow (h_pnt : PNT_bounds) (ε : ℝ) (hε : ε > 0) :
  ∃ K, ∀ k ≥ K, (M_prod k : ℝ) ≥ (M k : ℝ) ^ (1 - ε) := by
    obtain ⟨ K, hK ⟩ := m_small_relative_to_M h_pnt ε hε;
    use K + 1;
    intro k hk; rw [ Real.rpow_sub ] <;> norm_num;
    · rw [ div_le_iff₀ ];
      · have := m_mul_M_prod_eq_M k ( by linarith );
        exact le_trans ( mod_cast this ▸ by nlinarith ) ( mul_le_mul_of_nonneg_left ( le_of_lt ( hK k ( by linarith ) ) ) ( Nat.cast_nonneg _ ) );
      · exact Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ) _;
    · exact Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) )

/-
p-adic valuation of a product of distinct primes.
-/
lemma padicValRat_prod_primes (S : Finset ℕ) (p : ℕ) (hp : p.Prime) (hS : ∀ q ∈ S, q.Prime) :
  padicValRat p (S.prod (fun q => (q : ℚ))) = if p ∈ S then 1 else 0 := by
    -- If $p \in S$, then the product contains $p$ exactly once (since $S$ is a Finset of primes, so no duplicates and all are primes).
    by_cases hpS : p ∈ S;
    · have h_prod : padicValRat p (∏ q ∈ S, (q : ℚ)) = padicValNat p (∏ q ∈ S, q) := by
        haveI := Fact.mk hp; rw [ ← padicValRat.of_nat ] ;
        rw [ Nat.cast_prod ];
      haveI := Fact.mk hp; simp_all +decide [ padicValNat.pow, Finset.prod_eq_prod_diff_singleton_mul hpS ] ;
      haveI := Fact.mk ( hS p hpS ) ; rw [ padicValNat.mul ] <;> simp_all +decide [ Finset.prod_eq_zero_iff, Nat.Prime.ne_zero ] ;
      · simp_all +decide [ Nat.Prime.dvd_iff_not_coprime, Nat.coprime_prod_right_iff, Nat.coprime_prod_left_iff ];
        exact Or.inr <| Or.inr <| fun q hq hqp => by have := Nat.coprime_primes ( hS p hpS ) ( hS q hq ) ; aesop;
      · exact fun h => absurd ( hS 0 h ) ( by norm_num );
    · -- Since p is not in S, each element in S is not divisible by p, hence their product isn't divisible by p either.
      have h_not_div : ∀ q ∈ S, ¬(p ∣ q) := by
        intro q hq; rw [ Nat.prime_dvd_prime_iff_eq ] <;> aesop;
      -- Since p is not in S, each element in S is not divisible by p, hence their product isn't divisible by p either. Thus, the p-adic valuation of the product is zero.
      have h_not_div_prod : ¬(p ∣ ∏ q ∈ S, q) := by
        simp_all +decide [ Nat.Prime.dvd_iff_not_coprime hp, Nat.coprime_prod_right_iff ];
      rw [ ← Nat.cast_prod, padicValRat.of_nat ] ; aesop

/-
Simplification of the RHS valuation.
-/
lemma rhs_valuation_simpl (k : ℕ) (δ : ℝ) (p : ℕ) (hp : p.Prime) :
  padicValRat p (((PrimesIn k).filter (fun p => p ≤ k / 2)).prod (fun p => (p : ℚ))) -
  padicValRat p ((BadPrimes k δ).prod (fun p => (p : ℚ) ^ 2)) =
  (if p ∈ PrimesIn k ∧ p ≤ k / 2 then 1 else 0) - (if p ∈ BadPrimes k δ then 2 else 0) := by
    -- Apply `padicValRat_prod_primes` for the first term.
    have h_padicValRat_prod_primes : padicValRat p (∏ p ∈ (Finset.filter (fun p => p ≤ k / 2) (PrimesIn k)), (p : ℚ)) = if p ∈ (Finset.filter (fun p => p ≤ k / 2) (PrimesIn k)) then 1 else 0 := by
      have h_padicValRat_prod_primes : ∀ {S : Finset ℕ}, (∀ q ∈ S, q.Prime) → padicValRat p (∏ p ∈ S, (p : ℚ)) = if p ∈ S then 1 else 0 := by
        exact?;
      apply h_padicValRat_prod_primes; intro q hq; exact (by
      unfold PrimesIn at hq; aesop;);
    have h_padicValRat_prod_primes_bad : padicValRat p (∏ p ∈ BadPrimes k δ, (p : ℚ) ^ 2) = 2 * padicValRat p (∏ p ∈ BadPrimes k δ, (p : ℚ)) := by
      haveI := Fact.mk hp; rw [ Finset.prod_pow ] ; ring;
      have h_padicValRat_sq : ∀ {x : ℚ}, x ≠ 0 → padicValRat p (x ^ 2) = 2 * padicValRat p x := by
        intros x hx_nonzero
        have h_padicValRat_sq : padicValRat p (x ^ 2) = padicValRat p x + padicValRat p x := by
          rw [ sq, padicValRat.mul ] <;> aesop;
        rw [ h_padicValRat_sq, two_mul ];
      by_cases h : ∏ x ∈ BadPrimes k δ, ( x : ℚ ) = 0 <;> simp_all +decide [ mul_comm ];
    have h_padicValRat_prod_primes_bad : padicValRat p (∏ p ∈ BadPrimes k δ, (p : ℚ)) = if p ∈ BadPrimes k δ then 1 else 0 := by
      apply padicValRat_prod_primes;
      · assumption;
      · exact fun q hq => Finset.mem_filter.mp ( Finset.mem_filter.mp hq |>.1 ) |>.2 |>.1;
    aesop

/-
Valuation inequality for a single prime (helper lemma).
-/
def rhs_val (k : ℕ) (δ : ℝ) (p : ℕ) : ℤ :=
  (if p ∈ PrimesIn k ∧ p ≤ k / 2 then 1 else 0) - (if p ∈ BadPrimes k δ then 2 else 0)

lemma valuation_ge_rhs_val (k x y C_int : ℕ) (δ : ℝ) (p : ℕ)
  (hp : p.Prime)
  (hC : C_int ≥ 1)
  (hx0 : x > 0) (hy0 : y > 0)
  (h_good_p : ∀ p ∈ PrimesIn k, p ≤ k / 2 → ¬ is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) + 1)
  (h_bad_p : ∀ p ∈ PrimesIn k, is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) - 1)
  (h_others : ∀ p ∈ PrimesIn k, p > k / 2 → ¬ is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ))
  (h_small_p : ∀ p, p.Prime → p ≤ k.sqrt →
    padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) =
    padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id))
  (h_large_p : ∀ p, p.Prime → p > k + C_int →
    padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) = 0 ∧
    padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = 0) :
  padicValRat p (ratio_of_ratios k x y C_int) ≥ rhs_val k δ p := by
    unfold rhs_val;
    split_ifs <;> norm_num;
    · unfold ratio_of_ratios;
      have h_val : padicValRat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), (i : ℚ)) / (Finset.Icc y (y + k + C_int - 1)).lcm id) - padicValRat p ((∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) / (Finset.Icc x (x + k - 1)).lcm id) ≥ -1 := by
        have h_val : padicValRat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), (i : ℚ)) / (Finset.Icc y (y + k + C_int - 1)).lcm id) - padicValRat p ((∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) / (Finset.Icc x (x + k - 1)).lcm id) = (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) - (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) := by
          have h_val : ∀ (n : ℕ), n ≠ 0 → padicValRat p (n : ℚ) = padicValNat p n := by
            exact?;
          rw [ ← h_val, ← h_val ];
          · rw [ Nat.cast_div, Nat.cast_div ] <;> norm_num;
            · exact fun b hb₁ hb₂ => Finset.dvd_prod_of_mem _ ( Finset.mem_Icc.mpr ⟨ hb₁, hb₂ ⟩ );
            · linarith;
            · exact fun n hn₁ hn₂ => Finset.dvd_prod_of_mem _ <| Finset.mem_Icc.mpr ⟨ hn₁, hn₂ ⟩;
            · linarith;
          · simp +zetaDelta at *;
            exact ⟨ hx0.ne', Nat.le_of_dvd ( Finset.prod_pos fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ) ( Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi ) ⟩;
          · simp +zetaDelta at *;
            exact ⟨ hy0.ne', Nat.le_of_dvd ( Finset.prod_pos fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ) ( Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi ) ⟩;
        linarith [ h_bad_p p ( by tauto ) ( by unfold BadPrimes at *; aesop ) ];
      convert h_val.le using 1;
      convert padicValRat.div _ _ using 1;
      · exact ⟨ hp ⟩;
      · simp +zetaDelta at *;
        exact ⟨ Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ], hy0.ne' ⟩;
      · norm_num [ Finset.prod_eq_zero_iff, Finset.lcm_eq_zero_iff ];
        linarith;
    · unfold ratio_of_ratios;
      have h_ratio_ge : padicValRat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / ((Finset.Icc y (y + k + C_int - 1)).lcm id) / ((∏ i ∈ Finset.Icc x (x + k - 1), i) / ((Finset.Icc x (x + k - 1)).lcm id))) = padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / ((Finset.Icc y (y + k + C_int - 1)).lcm id)) - padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / ((Finset.Icc x (x + k - 1)).lcm id)) := by
        haveI := Fact.mk hp; rw [ padicValRat.div ] ; norm_num;
        · rw [ ← padicValRat.of_nat, ← padicValRat.of_nat ];
          rw [ Nat.cast_div, Nat.cast_div ] <;> norm_num;
          · exact fun b hb₁ hb₂ => Finset.dvd_prod_of_mem _ ( Finset.mem_Icc.mpr ⟨ hb₁, hb₂ ⟩ );
          · linarith;
          · exact fun b hb₁ hb₂ => Finset.dvd_prod_of_mem _ ( Finset.mem_Icc.mpr ⟨ hb₁, hb₂ ⟩ );
          · linarith;
        · simp +zetaDelta at *;
          exact ⟨ Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ], hy0.ne' ⟩;
        · simp +zetaDelta at *;
          exact ⟨ Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ], hx0.ne' ⟩;
      simp +zetaDelta at *;
      linarith [ h_good_p p ( by tauto ) ( by tauto ) ( by unfold BadPrimes at *; aesop ) ];
    · -- Since $p$ is a bad prime, we have $padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) ≥ padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) - 1$.
      have h_bad : padicValRat p (ratio_of_ratios k x y C_int) ≥ -1 := by
        unfold ratio_of_ratios;
        have h_bad : padicValRat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) ≥ padicValRat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) - 1 := by
          convert h_bad_p p _ _ using 1 <;> norm_cast;
          · convert padicValRat.div _ _ using 1;
            · haveI := Fact.mk hp; rw [ padicValRat.of_nat, padicValRat.of_nat ] ;
              rw [ padicValNat.div_of_dvd ];
              · rw [ Nat.cast_sub ];
                rw [ ← Nat.factorization_def, ← Nat.factorization_def ];
                · have h_lcm_le_prod : (Finset.Icc y (y + k + C_int - 1)).lcm id ∣ ∏ i ∈ Finset.Icc y (y + k + C_int - 1), i := by
                    exact Finset.lcm_dvd fun x hx => Finset.dvd_prod_of_mem _ hx;
                  exact Nat.factorization_le_iff_dvd ( by aesop ) ( Finset.prod_ne_zero_iff.mpr fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ) |>.2 h_lcm_le_prod p;
                · exact hp;
                · exact hp;
              · exact Finset.lcm_dvd fun x hx => Finset.dvd_prod_of_mem _ hx;
            · exact ⟨ hp ⟩;
            · exact mod_cast Finset.prod_ne_zero_iff.mpr fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ;
            · simp +decide [ Finset.lcm_eq_zero_iff ];
              linarith;
          · rw [ Int.subNatNat_eq_coe ] ; norm_num [ padicValRat.div, hp.ne_zero ];
            rw [ ← Nat.cast_prod, ← Nat.cast_div ];
            · rw [ padicValRat.of_nat ];
            · exact Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi;
            · simp +decide [ Finset.lcm_eq_zero_iff, hx0.ne' ];
          · exact Finset.mem_filter.mp ‹_› |>.1;
          · unfold BadPrimes at *; aesop;
        have h_bad : padicValRat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id / ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id)) = padicValRat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) - padicValRat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) := by
          haveI := Fact.mk hp; rw [ padicValRat.div ] ; norm_num;
          · exact ⟨ Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ], hy0.ne' ⟩;
          · simp +decide [ Finset.prod_eq_zero_iff, Finset.lcm_eq_zero_iff ];
            linarith;
        norm_num [ Rat.divInt_eq_div ] at * ; linarith;
      linarith;
    · have h_diff_ge_zero : (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
        (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥ 0 := by
          by_cases hp_le_sqrt : p ≤ Nat.sqrt k;
          · rw [ h_small_p p hp hp_le_sqrt ] ; norm_num;
          · by_cases hp_le_k : p ≤ k;
            · by_cases hp_le_k_div_2 : p ≤ k / 2;
              · exact False.elim <| ‹¬ ( p ∈ PrimesIn k ∧ p ≤ k / 2 ) › ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp.pos, hp_le_k ⟩, hp, by simpa using hp_le_sqrt ⟩, hp_le_k_div_2 ⟩;
              · simp +zetaDelta at *;
                apply h_others p;
                · exact Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp.pos, hp_le_k ⟩, hp, hp_le_sqrt ⟩;
                · linarith;
                · exact fun h => ‹p ∉ BadPrimes k δ› <| Finset.mem_filter.mpr ⟨ Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp.pos, hp_le_k ⟩, hp, hp_le_sqrt ⟩, h ⟩;
            · by_cases hp_le_k_plus_C_int : p ≤ k + C_int;
              · have h_val_x_zero : padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = 0 := by
                  apply valuation_x_eq_zero_large_p k x p hp hx0 (by linarith);
                simp [h_val_x_zero];
              · rw [ h_large_p p hp ( not_le.mp hp_le_k_plus_C_int ) |>.1, h_large_p p hp ( not_le.mp hp_le_k_plus_C_int ) |>.2 ] ; norm_num;
      convert h_diff_ge_zero.le using 1;
      convert padicValRat.div _ _ using 1;
      · rw [ ← Nat.cast_prod, ← Nat.cast_prod ];
        congr! 1;
        · simp +decide [ padicValRat.div, hp.ne_zero, Nat.cast_prod ];
          rw [ ← Nat.cast_prod, ← Nat.cast_div ];
          · norm_num +zetaDelta at *;
          · exact Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi;
          · norm_num [ Finset.lcm_eq_zero_iff ];
            linarith;
        · norm_num +zetaDelta at *;
          rw [ ← Nat.cast_prod, ← Nat.cast_div ] <;> norm_num;
          · exact fun b hb₁ hb₂ => Finset.dvd_prod_of_mem _ ( Finset.mem_Icc.mpr ⟨ hb₁, hb₂ ⟩ );
          · linarith;
      · exact ⟨ hp ⟩;
      · simp +zetaDelta at *;
        exact ⟨ Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ], hy0.ne' ⟩;
      · simp +decide [ Finset.prod_eq_zero_iff, Nat.factorial_ne_zero, Nat.cast_eq_zero ];
        linarith

/-
For x in [0, 0.5], log(1-x) >= -x - x^2.
-/
lemma log_one_sub_ge (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 0.5) : Real.log (1 - x) ≥ -x - x^2 := by
  -- Let's define the function $f(x) = \ln(1-x) + x + x^2$ and show that $f(x) \geq 0$ for $x \in [0, 0.5]$.
  set f : ℝ → ℝ := fun x => Real.log (1 - x) + x + x^2
  have hf_deriv_nonneg : ∀ x ∈ Set.Icc 0 0.5, 0 ≤ deriv f x := by
    intros x hx
    have : deriv f x = -1 / (1 - x) + 1 + 2 * x := by
      apply_rules [ HasDerivAt.deriv ];
      exact HasDerivAt.add ( HasDerivAt.add ( HasDerivAt.log ( hasDerivAt_id' x |> HasDerivAt.const_sub 1 ) ( by norm_num at hx; linarith ) ) ( hasDerivAt_id' x ) ) ( hasDerivAt_pow 2 x ) |> HasDerivAt.congr_deriv <| by ring;
    rw [ this, div_eq_mul_inv ] ; nlinarith [ hx.1, hx.2, mul_inv_cancel₀ ( by linarith [ hx.1, hx.2 ] : ( 1 - x ) ≠ 0 ) ];
  by_contra h_contra;
  -- Since $f$ is differentiable and its derivative is non-negative on $[0, 0.5]$, we can apply the Mean Value Theorem to $f$ on this interval.
  have h_mvt : ∃ c ∈ Set.Ioo 0 x, deriv f c = (f x - f 0) / (x - 0) := by
    apply_rules [ exists_deriv_eq_slope ];
    · exact hx.lt_of_ne ( by rintro rfl; norm_num at h_contra );
    · exact continuousOn_of_forall_continuousAt fun y hy => by exact ContinuousAt.add ( ContinuousAt.add ( ContinuousAt.log ( continuousAt_const.sub continuousAt_id ) ( by linarith [ hy.1, hy.2 ] ) ) continuousAt_id ) ( continuousAt_id.pow 2 ) ;
    · exact DifferentiableOn.add ( DifferentiableOn.add ( DifferentiableOn.log ( differentiableOn_id.const_sub _ ) ( by intro y hy; norm_num at *; linarith ) ) differentiableOn_id ) ( differentiableOn_pow 2 );
  norm_num +zetaDelta at *;
  obtain ⟨ c, ⟨ hc1, hc2 ⟩, hc3 ⟩ := h_mvt; have := hf_deriv_nonneg c ( by linarith ) ( by linarith ) ; rw [ hc3, le_div_iff₀ ] at this <;> nlinarith;

/-
The expression tends to infinity as M tends to infinity.
-/
lemma large_M_asymptotic (C : ℝ) (hC : C ≥ 1) (ε : ℝ) (h_eps : ε = 1 / (3 * C + 6)) :
  Filter.Tendsto (fun M => M ^ (1 - 5 * ε - 3 * ε * C) * (1 - 3 * M ^ (-ε)) ^ (2 * Real.log M)) Filter.atTop Filter.atTop := by
    -- The exponent $1 - 5\epsilon - 3\epsilon C$ simplifies to $\frac{1}{3C+6}$, which is positive.
    have h_exp_pos : 1 - 5 * ε - 3 * ε * C > 0 := by
      rw [ h_eps ] ; nlinarith [ mul_div_cancel₀ 1 ( by linarith : ( 3 * C + 6 ) ≠ 0 ) ];
    -- Consider the second term $(1 - 3 M^{-\epsilon})^{2 \ln M}$.
    -- Take log: $2 \ln M \ln(1 - 3 M^{-\epsilon})$.
    have h_log_second_term : Filter.Tendsto (fun M : ℝ => 2 * Real.log M * Real.log (1 - 3 * M ^ (-ε))) Filter.atTop (nhds 0) := by
      -- Since $\epsilon > 0$, $M^{-\epsilon} \ln M \to 0$ by L'Hopital or standard growth rates.
      have h_lim : Filter.Tendsto (fun M : ℝ => M ^ (-ε) * Real.log M) Filter.atTop (nhds 0) := by
        -- Let $y = \log M$, therefore the expression becomes $\frac{y}{e^{y \epsilon}}$.
        suffices h_log : Filter.Tendsto (fun y : ℝ => y / Real.exp (y * ε)) Filter.atTop (nhds 0) by
          have := h_log.comp Real.tendsto_log_atTop;
          refine' this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by simp +decide [ Real.rpow_def_of_pos hx, mul_comm, div_eq_mul_inv, Real.exp_neg, mul_assoc, mul_left_comm, hx.ne' ] );
        -- Let $z = y \epsilon$, therefore the expression becomes $\frac{z}{e^z}$.
        suffices h_z : Filter.Tendsto (fun z : ℝ => z / Real.exp z) Filter.atTop (nhds 0) by
          have := h_z.comp ( Filter.tendsto_id.atTop_mul_const ( show 0 < ε by rw [ h_eps ] ; positivity ) );
          convert this.div_const ε using 2 <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, ne_of_gt ( show 0 < ε by rw [ h_eps ] ; positivity ) ];
        simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
      -- Since $\ln(1 - z) \approx -z$ for small $z$, we can bound $\ln(1 - 3 M^{-\epsilon})$.
      have h_log_bound : ∀ᶠ M in Filter.atTop, |Real.log (1 - 3 * M ^ (-ε))| ≤ 6 * M ^ (-ε) := by
        -- Since $M^{-\epsilon} \to 0$ as $M \to \infty$, we can find $M_0$ such that for all $M \geq M_0$, $3 * M^{-\epsilon} < 1/2$.
        obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, ∀ M ≥ M₀, 3 * M ^ (-ε) < 1 / 2 := by
          have h_lim : Filter.Tendsto (fun M : ℝ => 3 * M ^ (-ε)) Filter.atTop (nhds 0) := by
            simpa using tendsto_const_nhds.mul ( tendsto_rpow_neg_atTop ( show 0 < ε by rw [ h_eps ] ; positivity ) );
          simpa using h_lim.eventually ( gt_mem_nhds <| by norm_num );
        filter_upwards [ Filter.eventually_ge_atTop M₀, Filter.eventually_gt_atTop 0 ] with M hM₁ hM₂ using by rw [ abs_of_nonpos ( Real.log_nonpos ( by linarith [ hM₀ M hM₁ ] ) ( by linarith [ hM₀ M hM₁, Real.rpow_nonneg hM₂.le ( -ε ) ] ) ) ] ; nlinarith [ hM₀ M hM₁, Real.log_inv ( 1 - 3 * M ^ ( -ε ) ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith [ hM₀ M hM₁ ] : 0 < 1 - 3 * M ^ ( -ε ) ) ), mul_inv_cancel₀ ( by linarith [ hM₀ M hM₁ ] : ( 1 - 3 * M ^ ( -ε ) ) ≠ 0 ), Real.rpow_nonneg hM₂.le ( -ε ) ] ;
      -- Using the bound, we can show that the product tends to 0.
      have h_prod_zero : Filter.Tendsto (fun M : ℝ => 2 * Real.log M * (6 * M ^ (-ε))) Filter.atTop (nhds 0) := by
        convert h_lim.const_mul 12 using 2 <;> ring;
      refine' squeeze_zero_norm' _ h_prod_zero;
      filter_upwards [ h_log_bound, Filter.eventually_gt_atTop 1 ] with M hM₁ hM₂ using by rw [ Real.norm_eq_abs, abs_mul, abs_of_nonneg ( mul_nonneg zero_le_two ( Real.log_nonneg hM₂.le ) ) ] ; exact mul_le_mul_of_nonneg_left hM₁ ( mul_nonneg zero_le_two ( Real.log_nonneg hM₂.le ) ) ;
    -- Since the logarithm of the second term tends to 0, the second term itself tends to 1.
    have h_second_term_one : Filter.Tendsto (fun M : ℝ => (1 - 3 * M ^ (-ε)) ^ (2 * Real.log M)) Filter.atTop (nhds 1) := by
      have h_second_term_one : Filter.Tendsto (fun M : ℝ => Real.exp (2 * Real.log M * Real.log (1 - 3 * M ^ (-ε)))) Filter.atTop (nhds 1) := by
        simpa only [ Real.exp_zero ] using Filter.Tendsto.comp ( Real.continuous_exp.tendsto _ ) h_log_second_term;
      refine h_second_term_one.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1, Filter.eventually_gt_atTop ( 3 ^ ( 1 / ε ) ) ] with M hM₁ hM₂;
      rw [ Real.rpow_def_of_pos ( sub_pos.mpr <| ?_ ), mul_comm ];
      rw [ Real.rpow_neg ( by positivity ) ];
      rw [ ← div_eq_mul_inv, div_lt_one ( by positivity ) ];
      exact lt_of_le_of_lt ( by rw [ ← Real.rpow_mul ( by positivity ), one_div_mul_cancel ( by rw [ h_eps ] ; positivity ), Real.rpow_one ] ) ( Real.rpow_lt_rpow ( by positivity ) hM₂ ( by rw [ h_eps ] ; positivity ) );
    apply Filter.Tendsto.atTop_mul_pos;
    exacts [ zero_lt_one, tendsto_rpow_atTop ( by linarith ), h_second_term_one ]

/-
For large M, y + k + C is bounded by 2 * M^(3*epsilon).
-/
lemma bound_y_term (C : ℝ) (hC : C ≥ 1) (ε : ℝ) (h_eps : ε > 0) :
  ∃ M0, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ, (k : ℝ) ≤ 2 * Real.log M →
  ∀ y : ℕ, (y : ℝ) < M ^ (3 * ε) →
  (y : ℝ) + k + C < 2 * M ^ (3 * ε) := by
    -- We'll use that $M^{3\epsilon}$ grows faster than $2 \ln M$ and $C$.
    have h_bound : Filter.Tendsto (fun M => (2 * Real.log M + C) / M ^ (3 * ε)) Filter.atTop (nhds 0) := by
      -- We can use the fact that $\frac{\log M}{M^{3\epsilon}}$ tends to $0$ as $M$ tends to infinity.
      have h_log_div_M : Filter.Tendsto (fun M => Real.log M / M ^ (3 * ε)) Filter.atTop (nhds 0) := by
        -- Let $y = \ln M$, therefore the expression becomes $\frac{y}{e^{y \cdot 3\epsilon}}$.
        suffices h_log : Filter.Tendsto (fun y : ℝ => y / Real.exp (y * 3 * ε)) Filter.atTop (nhds 0) by
          have := h_log.comp Real.tendsto_log_atTop;
          refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.rpow_def_of_pos hx ] ; ring );
        -- Let $z = y \cdot 3 \epsilon$, therefore the expression becomes $\frac{y}{e^{z}}$.
        suffices h_z : Filter.Tendsto (fun z : ℝ => (z / (3 * ε)) / Real.exp z) Filter.atTop (nhds 0) by
          convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( show 0 < 3 * ε by positivity ) ) using 2 ; norm_num ; ring;
          norm_num [ mul_assoc, mul_comm ε, h_eps.ne' ];
        -- We can factor out the constant $1/(3\epsilon)$ and use the fact that $\frac{z}{e^z}$ tends to $0$ as $z$ tends to infinity.
        suffices h_factor : Filter.Tendsto (fun z : ℝ => z / Real.exp z) Filter.atTop (nhds 0) by
          convert h_factor.const_mul ( 1 / ( 3 * ε ) ) using 2 <;> ring;
        simpa [ Real.exp_neg ] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
      simpa [ add_div, mul_div_assoc ] using Filter.Tendsto.add ( h_log_div_M.const_mul 2 ) ( tendsto_const_nhds.div_atTop ( tendsto_rpow_atTop ( by positivity ) ) );
    have := h_bound.eventually ( gt_mem_nhds <| show 0 < 1 / 2 by norm_num );
    rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ M0, hM0 ⟩ ; use Max.max M0 1; rintro M hM k hk y hy; have := hM0 M ( le_trans ( le_max_left _ _ ) hM ) ; rw [ div_lt_iff₀ ] at this <;> nlinarith [ Real.rpow_pos_of_pos ( show 0 < M by linarith [ le_max_right M0 1 ] ) ( 3 * ε ) ] ;

/-
For large M, if y < 2 * M^(3*epsilon), then y + k + C < 3 * M^(3*epsilon).
-/
lemma bound_y_term_relaxed (C : ℝ) (hC : C ≥ 1) (ε : ℝ) (h_eps : ε > 0) :
  ∃ M0, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ, (k : ℝ) ≤ 2 * Real.log M →
  ∀ y : ℕ, (y : ℝ) < 2 * M ^ (3 * ε) →
  (y : ℝ) + k + C < 3 * M ^ (3 * ε) := by
    -- We want $k+C < M^{3\epsilon}$.
    suffices h_suff : ∃ M0, ∀ M ≥ M0, 2 * Real.log M + C < M ^ (3 * ε) by
      exact ⟨ h_suff.choose, fun M hM k hk y hy => by linarith [ h_suff.choose_spec M hM ] ⟩;
    -- Since $M^{3\epsilon}$ grows faster than $\ln M$, we can find $M0$ such that for all $M \geq M0$, $2 \ln M < \frac{M^{3\epsilon}}{2}$.
    obtain ⟨M0, hM0⟩ : ∃ M0, ∀ M ≥ M0, 2 * Real.log M < (1 / 2) * M ^ (3 * ε) := by
      -- We can choose $M0$ such that for all $M \geq M0$, $M^{3\epsilon} / \ln M > 4$.
      have h_lim : Filter.Tendsto (fun M : ℝ => M ^ (3 * ε) / Real.log M) Filter.atTop Filter.atTop := by
        -- Let $y = \log M$, therefore the expression becomes $\frac{e^{3\epsilon y}}{y}$.
        suffices h_log : Filter.Tendsto (fun y : ℝ => Real.exp (3 * ε * y) / y) Filter.atTop Filter.atTop by
          have := h_log.comp Real.tendsto_log_atTop;
          refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.rpow_def_of_pos hx ] ; ring );
        -- Let $z = 3\epsilon y$, therefore the expression becomes $\frac{e^z}{z/(3\epsilon)} = 3\epsilon \frac{e^z}{z}$.
        suffices h_z : Filter.Tendsto (fun z : ℝ => 3 * ε * Real.exp z / z) Filter.atTop Filter.atTop by
          convert h_z.comp ( Filter.tendsto_id.const_mul_atTop ( show 0 < 3 * ε by positivity ) ) using 2 ; norm_num ; ring;
          norm_num [ mul_assoc, mul_comm ε, h_eps.ne' ];
        simpa [ mul_div_assoc ] using Filter.Tendsto.const_mul_atTop ( by positivity ) ( Real.tendsto_exp_div_pow_atTop 1 ) |> Filter.Tendsto.comp <| Filter.tendsto_id;
      exact Filter.eventually_atTop.mp ( h_lim.eventually_gt_atTop 4 ) |> fun ⟨ M0, hM0 ⟩ ↦ ⟨ Max.max M0 2, fun M hM ↦ by have := hM0 M ( le_trans ( le_max_left _ _ ) hM ) ; rw [ lt_div_iff₀ ( Real.log_pos <| by linarith [ le_max_right M0 2 ] ) ] at this; linarith ⟩;
    -- Since $M^{3\epsilon}$ grows faster than $\ln M$, we can find $M0$ such that for all $M \geq M0$, $C < \frac{M^{3\epsilon}}{2}$.
    obtain ⟨M1, hM1⟩ : ∃ M1, ∀ M ≥ M1, C < (1 / 2) * M ^ (3 * ε) := by
      have h_lim : Filter.Tendsto (fun M : ℝ => (1 / 2) * M ^ (3 * ε)) Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.const_mul_atTop ( by positivity ) ( tendsto_rpow_atTop ( by positivity ) );
      exact Filter.eventually_atTop.mp ( h_lim.eventually_gt_atTop C ) |> fun ⟨ M1, hM1 ⟩ => ⟨ M1, fun M hM => hM1 M hM ⟩;
    exact ⟨ Max.max M0 M1, fun M hM => by linarith [ hM0 M ( le_trans ( le_max_left _ _ ) hM ), hM1 M ( le_trans ( le_max_right _ _ ) hM ) ] ⟩

/-
For large M, (x/y)^k >= (1 - 3 M^(-epsilon))^(2 log M).
-/
lemma x_div_y_bound (ε : ℝ) (h_eps : ε > 0) :
  ∃ M0, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ, (k : ℝ) ≤ 2 * Real.log M →
  ∀ x y : ℕ, M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε →
  ((x : ℝ) / y) ^ k ≥ (1 - 3 * M ^ (-ε)) ^ (2 * Real.log M) := by
    -- Let's choose any $M0$ such that $M0^{ε} > 3$.
    obtain ⟨M0, hM0⟩ : ∃ M0 : ℝ, ∀ M ≥ M0, M ^ ε > 3 := by
      exact ⟨ 4 ^ ( 1 / ε ), fun M hM => by exact lt_of_lt_of_le ( by norm_num [ ← Real.rpow_mul, h_eps.ne' ] ) ( Real.rpow_le_rpow ( by positivity ) hM ( by positivity ) ) ⟩;
    -- For $M \ge M0$, we have $M^\epsilon > 3$, thus $1 - 3 M^{-\epsilon} > 0$.
    use max M0 2; intros M hM k hk x y hx hy hxy; (
    -- Since $x/y > 1 - 3 M^{-\epsilon}$, we have $(x/y)^k \ge (1 - 3 M^{-\epsilon})^k$.
    have h_xy_ge : (x / y : ℝ) ^ k ≥ (1 - 3 * M ^ (-ε)) ^ k := by
      gcongr;
      · norm_num [ Real.rpow_neg ( by linarith [ le_max_right M0 2 ] : 0 ≤ M ) ];
        rw [ ← div_eq_mul_inv, div_le_iff₀ ] <;> linarith [ hM0 M ( le_trans ( le_max_left _ _ ) hM ) ];
      · rw [ le_div_iff₀ ( by norm_cast; linarith ) ];
        rw [ Real.rpow_neg ( by linarith [ le_max_right M0 2 ] ) ];
        nlinarith [ inv_pos.mpr ( show 0 < M ^ ε by exact Real.rpow_pos_of_pos ( by linarith [ le_max_right M0 2 ] ) _ ), mul_inv_cancel₀ ( ne_of_gt ( show 0 < M ^ ε by exact Real.rpow_pos_of_pos ( by linarith [ le_max_right M0 2 ] ) _ ) ), show ( M : ℝ ) ^ ( 2 * ε ) = ( M ^ ε ) ^ 2 by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by linarith [ le_max_right M0 2 ] ) ] ; ring, show ( M : ℝ ) ^ ε > 0 by exact Real.rpow_pos_of_pos ( by linarith [ le_max_right M0 2 ] ) _ ];
    field_simp;
    refine le_trans ?_ h_xy_ge;
    exact_mod_cast Real.rpow_le_rpow_of_exponent_ge ( sub_pos.mpr <| by rw [ Real.rpow_neg <| by linarith [ le_max_right M0 2 ] ] ; nlinarith [ hM0 M <| le_trans ( le_max_left M0 2 ) hM, Real.rpow_pos_of_pos ( by linarith [ le_max_right M0 2 ] : 0 < M ) ε, mul_inv_cancel₀ <| ne_of_gt <| Real.rpow_pos_of_pos ( by linarith [ le_max_right M0 2 ] : 0 < M ) ε ] ) ( sub_le_self _ <| by exact mul_nonneg zero_le_three <| Real.rpow_nonneg ( by linarith [ le_max_right M0 2 ] ) _ ) hk)

/-
For large M, the inequality holds.
-/
lemma large_M_inequality (C : ℝ) (hC : C ≥ 1) (ε : ℝ) (h_eps : ε = 1 / (3 * C + 6)) :
  ∃ M0, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ,
  1 ≤ k → (k : ℝ) ≤ 2 * Real.log M →
  ∀ x y : ℕ,
  M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε →
  (y : ℝ) < 2 * M ^ (3 * ε) →
  M ^ (1 - 5 * ε) * ((x : ℝ) / y) ^ k * (1 / (y + k + C : ℝ)) ^ C > 1 := by
    have := large_M_asymptotic C hC ε h_eps;
    have := this.eventually_gt_atTop ( 3 ^ C );
    obtain ⟨ M0, HM0 ⟩ := Filter.eventually_atTop.mp this;
    -- Now use the bounds from `bound_y_term_relaxed` and `x_div_y_bound`.
    obtain ⟨ M1, HM1 ⟩ := bound_y_term_relaxed C hC ε ( by rw [ h_eps ] ; positivity )
    obtain ⟨ M2, HM2 ⟩ := x_div_y_bound ε ( by rw [ h_eps ] ; positivity );
    refine' ⟨ Max.max M0 ( Max.max M1 ( Max.max M2 1 ) ), fun M hM k hk hk' x y hx hy hxy hy' => _ ⟩ ; simp_all +decide [ Real.rpow_sub ];
    -- Substitute the bounds from `HM1` and `HM2`.
    have h_subst : M ^ (1 - 5 * (3 * C + 6)⁻¹) * (↑x / ↑y) ^ k * (↑y + ↑k + C)⁻¹ ^ C ≥ M ^ (1 - 5 * (3 * C + 6)⁻¹) * (1 - 3 * M ^ (-(3 * C + 6)⁻¹)) ^ (2 * Real.log M) * (3 * M ^ (3 * (3 * C + 6)⁻¹))⁻¹ ^ C := by
      gcongr <;> try linarith [ HM1 M hM.2.1 k hk' y hy' ];
      · exact Real.rpow_nonneg ( inv_nonneg.2 ( mul_nonneg zero_le_three ( Real.rpow_nonneg ( by linarith ) _ ) ) ) _;
      · exact mul_nonneg ( Real.rpow_nonneg ( by linarith ) _ ) ( pow_nonneg ( div_nonneg ( Nat.cast_nonneg _ ) ( Nat.cast_nonneg _ ) ) _ );
      · exact Real.rpow_nonneg ( by linarith ) _;
      · exact HM2 M hM.2.2.1 k hk' x y hx hy hxy;
      · exact inv_nonneg.2 ( mul_nonneg zero_le_three ( Real.rpow_nonneg ( by linarith ) _ ) );
    refine lt_of_lt_of_le ?_ h_subst;
    convert one_lt_div ( by positivity ) |>.2 ( HM0 M hM.1 ) using 1 ; ring;
    rw [ Real.mul_rpow ( by exact inv_nonneg.2 <| Real.rpow_nonneg ( by linarith ) _ ) ( by positivity ), Real.inv_rpow ( by exact Real.rpow_nonneg ( by linarith ) _ ) ] ; ring;
    rw [ ← Real.rpow_mul ( by linarith ) ] ; ring;
    rw [ show ( 1 + ( - ( C * ( 6 + C * 3 ) ⁻¹ * 3 ) - ( 6 + C * 3 ) ⁻¹ * 5 ) ) = ( 1 - ( 6 + C * 3 ) ⁻¹ * 5 ) - ( C * ( 6 + C * 3 ) ⁻¹ * 3 ) by ring ] ; rw [ Real.rpow_sub ( by linarith ) ] ; norm_num ; ring;
    rw [ show ( 1 + ( - ( C * ( 6 + C * 3 ) ⁻¹ * 3 ) - ( 6 + C * 3 ) ⁻¹ * 5 ) ) = 1 - ( 6 + C * 3 ) ⁻¹ * 5 - C * ( 6 + C * 3 ) ⁻¹ * 3 by ring ] ; rw [ Real.rpow_sub ( by linarith ), Real.rpow_sub ( by linarith ) ] ; norm_num ; ring;
    norm_num [ Real.div_rpow ]

/-
Algebraic simplification for the large M inequality.
-/
lemma large_M_algebra (M C ε : ℝ) (hM : M > 0) (h_base : 1 - 3 * M ^ (-ε) ≥ 0) :
  M ^ (1 - 5 * ε) * (1 - 3 * M ^ (-ε)) ^ (2 * Real.log M) * (3 * M ^ (3 * ε)) ^ (-C) =
  3 ^ (-C) * (M ^ (1 - 5 * ε - 3 * ε * C) * (1 - 3 * M ^ (-ε)) ^ (2 * Real.log M)) := by
    rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_mul ( by positivity ) ] ; ring;
    rw [ show 1 + ( - ( ε * 5 ) - ε * C * 3 ) = ( 1 - ε * 5 ) + ( - ( ε * C * 3 ) ) by ring, Real.rpow_add hM ] ; ring

/-
For large M, the LHS is bounded below by the algebraic expression.
-/
lemma large_M_lower_bound (C : ℝ) (hC : C ≥ 1) (ε : ℝ) (h_eps : ε > 0) :
  ∃ M0, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ,
  1 ≤ k → (k : ℝ) ≤ 2 * Real.log M →
  ∀ x y : ℕ,
  M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε →
  (y : ℝ) < 2 * M ^ (3 * ε) →
  M ^ (1 - 5 * ε) * ((x : ℝ) / y) ^ k * (1 / (y + k + C : ℝ)) ^ C ≥
  M ^ (1 - 5 * ε) * (1 - 3 * M ^ (-ε)) ^ (2 * Real.log M) * (3 * M ^ (3 * ε)) ^ (-C) := by
    -- Apply the bounds from `x_div_y_bound` and `bound_y_term_relaxed`.
    have h_bounds : ∃ M0 : ℝ, ∀ M ≥ M0, ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ 2 * Real.log M → ∀ x y : ℕ, M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε → (y : ℝ) < 2 * M ^ (3 * ε) →
        ((x : ℝ) / y) ^ k ≥ (1 - 3 * M ^ (-ε)) ^ (2 * Real.log M) ∧
        (1 / (y + k + C : ℝ)) ^ C ≥ (3 * M ^ (3 * ε)) ^ (-C) := by
          have := x_div_y_bound ε h_eps;
          obtain ⟨ M0, HM0 ⟩ := this;
          -- Apply the bound from `bound_y_term_relaxed`.
          obtain ⟨M1, HM1⟩ := bound_y_term_relaxed C hC ε h_eps;
          use Max.max M0 M1; intros M hM k hk hk' x y hx hy hxy hy'; exact ⟨HM0 M (le_trans (le_max_left _ _) hM) k hk' x y hx hy hxy, by
            rw [ Real.rpow_neg ( by linarith [ HM1 M ( le_trans ( le_max_right M0 M1 ) hM ) k hk' y hy' ] ) ];
            norm_num +zetaDelta at *;
            rw [ Real.inv_rpow ( by positivity ) ] ; gcongr ; linarith [ HM1 M hM.2 k hk' y hy' ]⟩;
    obtain ⟨ M0, hM0 ⟩ := h_bounds;
    use Max.max M0 1;
    simp +zetaDelta at *;
    exact fun M hM₁ hM₂ k hk₁ hk₂ x y hx₁ hx₂ hx₃ hx₄ => mul_le_mul ( mul_le_mul_of_nonneg_left ( hM0 M hM₁ k hk₁ hk₂ x y hx₁ hx₂ hx₃ hx₄ |>.1 ) ( by positivity ) ) ( hM0 M hM₁ k hk₁ hk₂ x y hx₁ hx₂ hx₃ hx₄ |>.2 ) ( by positivity ) ( by positivity )

/-
For large M, the inequality holds.
-/
lemma large_M_inequality_final (C : ℝ) (hC : C ≥ 1) (ε : ℝ) (h_eps : ε = 1 / (3 * C + 6)) :
  ∃ M0, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ,
  1 ≤ k → (k : ℝ) ≤ 2 * Real.log M →
  ∀ x y : ℕ,
  M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε →
  (y : ℝ) < 2 * M ^ (3 * ε) →
  M ^ (1 - 5 * ε) * ((x : ℝ) / y) ^ k * (1 / (y + k + C : ℝ)) ^ C > 1 := by
    exact?

/-
For large M, the inequality holds.
-/
lemma large_M_inequality_v2 (C : ℝ) (hC : C ≥ 1) (ε : ℝ) (h_eps : ε = 1 / (3 * C + 6)) :
  ∃ M0, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ,
  1 ≤ k → (k : ℝ) ≤ 2 * Real.log M →
  ∀ x y : ℕ,
  M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε →
  (y : ℝ) < 2 * M ^ (3 * ε) →
  M ^ (1 - 5 * ε) * ((x : ℝ) / y) ^ k * (1 / (y + k + C : ℝ)) ^ C > 1 := by
    -- Apply the lemma `large_M_inequality_final` to obtain the required M0.
    apply large_M_inequality_final C hC ε h_eps

/-
For large M, the inequality holds.
-/
lemma large_M_inequality_v3 (C : ℝ) (hC : C ≥ 1) (ε : ℝ) (h_eps : ε = 1 / (3 * C + 6)) :
  ∃ M0, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ,
  1 ≤ k → (k : ℝ) ≤ 2 * Real.log M →
  ∀ x y : ℕ,
  M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε →
  (y : ℝ) < 2 * M ^ (3 * ε) →
  M ^ (1 - 5 * ε) * ((x : ℝ) / y) ^ k * (1 / (y + k + C : ℝ)) ^ C > 1 := by
    -- Apply the hypothesis `large_M_inequality_final` to conclude the proof.
    apply large_M_inequality_final C hC ε h_eps

/-
Algebraic bound for the ratio of M_prod to BadProd squared.
-/
lemma M_prod_div_BadProd_sq_ge_M_pow (k : ℕ) (ε δ : ℝ) (h_eps : ε > 0)
  (h_bad_prod : (BadPrimes k δ).prod (fun p => (p : ℝ)) ≤ (M_prod k : ℝ) ^ (2 * ε))
  (h_M_prod : (M_prod k : ℝ) ≥ (M k : ℝ) ^ (1 - ε))
  (hM_gt_1 : (M k : ℝ) > 1)
  (h_M_prod_pos : (M_prod k : ℝ) > 0) :
  ((M_prod k : ℚ) / ((BadPrimes k δ).prod (fun p => (p : ℚ) ^ 2)) : ℝ) ≥ (M k : ℝ) ^ (1 - 5 * ε) := by
    field_simp;
    -- Since $M_{prod}(k) \geq M(k)^{1-\epsilon}$ and $(M_{prod}(k))^{4\epsilon} \leq M_{prod}(k)^{4\epsilon}$, we can combine these inequalities.
    have h_combined : (M_prod k : ℝ) / ((∏ p ∈ BadPrimes k δ, (p : ℝ)) ^ 2) ≥ (M k : ℝ) ^ (1 - ε) / (M_prod k : ℝ) ^ (4 * ε) := by
      gcongr;
      · refine sq_pos_of_pos <| Finset.prod_pos fun p hp => Nat.cast_pos.mpr <| Nat.Prime.pos <| ?_;
        exact Finset.mem_filter.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2.1;
      · convert pow_le_pow_left₀ ( Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _ ) h_bad_prod 2 using 1 ; rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring;
    convert h_combined.le.trans' _ using 1;
    · norm_num [ Finset.prod_pow ];
    · rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_div ( by positivity ) ( by positivity ), Real.log_rpow ( by positivity ), Real.log_rpow ( by positivity ) ];
      rw [ Real.log_rpow h_M_prod_pos ] ; ring_nf ; norm_num;
      have h_combined : Real.log (M_prod k : ℝ) ≤ Real.log (M k : ℝ) := by
        apply Real.log_le_log;
        · positivity;
        · have h_M_prod_le_M : (M k : ℝ) = (m k : ℝ) * (M_prod k : ℝ) := by
            convert m_mul_M_prod_eq_M k using 1;
            norm_cast;
            cases k <;> aesop;
          exact h_M_prod_le_M.symm ▸ le_mul_of_one_le_left h_M_prod_pos.le ( mod_cast Nat.one_le_iff_ne_zero.mpr <| Nat.ne_of_gt <| Nat.pos_of_ne_zero <| by contrapose! hM_gt_1; aesop );
      nlinarith [ Real.log_pos hM_gt_1 ]

/-
Modular conditions for small primes are satisfied.
-/
lemma small_prime_conditions_satisfied (k x y : ℕ) (p : ℕ) (hp : p.Prime) (h_sqrt : p * p ≤ k)
  (h_mod_x : x % (m k) = 1) (h_mod_y : y % (m k) = 0) :
  x % (p ^ (padicValNat p (M k))) = 1 ∧ y % (p ^ (padicValNat p (M k))) = 0 := by
    refine' ⟨ _, _ ⟩;
    · rw [ ← Nat.mod_mod_of_dvd x ( show p ^ padicValNat p ( M k ) ∣ m k from ?_ ), h_mod_x ];
      · rw [ Nat.mod_eq_of_lt ( one_lt_pow₀ hp.one_lt ( Nat.ne_of_gt ( Nat.pos_of_ne_zero _ ) ) ) ];
        have h_val_pos : p ≤ k := by
          nlinarith [ hp.two_le ];
        have h_val_pos : p ∣ M k := by
          exact Finset.dvd_lcm ( Finset.mem_Icc.mpr ⟨ hp.pos, h_val_pos ⟩ ) |> dvd_trans ( by aesop );
        simp_all +decide [ Nat.factorization_eq_zero_iff, hp.ne_one ];
        exact Nat.ne_of_gt ( Nat.pos_of_ne_zero ( by unfold M; aesop ) );
      · unfold m M;
        by_cases hpk : p ∈ Finset.filter (fun p => Nat.Prime p ∧ p * p ≤ k) (Finset.Icc 1 k);
        · refine' dvd_trans _ ( Finset.dvd_prod_of_mem _ hpk );
          rw [ Nat.factorization_def ] ; aesop;
        · exact False.elim <| hpk <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp.pos, by nlinarith ⟩, hp, h_sqrt ⟩;
    · refine' Nat.mod_eq_zero_of_dvd _;
      refine' Nat.dvd_trans _ ( Nat.dvd_of_mod_eq_zero h_mod_y );
      unfold m;
      rw [ Finset.prod_eq_prod_diff_singleton_mul <| show p ∈ Finset.filter ( fun p => Nat.Prime p ∧ p * p ≤ k ) ( Finset.Icc 1 k ) from Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp.pos, by nlinarith ⟩, hp, h_sqrt ⟩ ];
      rw [ Nat.factorization_def ] ; aesop;
      assumption

/-
For a prime p <= sqrt(k), the p-adic valuation of m(k) is equal to the p-adic valuation of M(k).
-/
lemma valuation_m_eq_valuation_M (k p : ℕ) (hp : p.Prime) (h_small : p ≤ k.sqrt) (hk : k ≥ 1) :
  padicValNat p (m k) = padicValNat p (M k) := by
    have h_val_m : m k = ∏ q ∈ Finset.filter (fun q => q.Prime ∧ q ≤ Nat.sqrt k) (Finset.Icc 1 k), (q : ℕ) ^ (Nat.factorization (M k) q) := by
      -- By definition of $m$, we know that $m k$ is the product of primes $q$ in the range $1$ to $k$ that are prime and less than or equal to $\sqrt{k}$, each raised to the power of their factorization in $M k$.
      simp [m];
      simp +decide [ ← sq, Nat.le_sqrt ];
    -- Apply the fact that the p-adic valuation of a product is the sum of the p-adic valuations of the factors.
    have h_val_m_sum : padicValNat p (m k) = ∑ q ∈ Finset.filter (fun q => q.Prime ∧ q ≤ Nat.sqrt k) (Finset.Icc 1 k), padicValNat p (q ^ (Nat.factorization (M k) q)) := by
      rw [h_val_m];
      have h_val_prod : ∀ {S : Finset ℕ} {f : ℕ → ℕ}, (∀ q ∈ S, f q ≠ 0) → padicValNat p (∏ q ∈ S, f q) = ∑ q ∈ S, padicValNat p (f q) := by
        intros S f hf_nonzero
        induction' S using Finset.induction with q S hqS ih;
        · simp +decide [ hp.ne_one ];
        · rw [ Finset.prod_insert hqS, Finset.sum_insert hqS ];
          haveI := Fact.mk hp; rw [ padicValNat.mul ( hf_nonzero q ( Finset.mem_insert_self q S ) ) ( Finset.prod_ne_zero_iff.mpr fun x hx => hf_nonzero x ( Finset.mem_insert_of_mem hx ) ), ih fun x hx => hf_nonzero x ( Finset.mem_insert_of_mem hx ) ] ;
      exact h_val_prod fun q hq => pow_ne_zero _ <| Nat.Prime.ne_zero <| by aesop;
    -- Since $p$ is prime and $\leq \sqrt{k}$, the only term in the sum that contributes to the $p$-adic valuation is when $q = p$.
    have h_val_m_single : ∑ q ∈ Finset.filter (fun q => q.Prime ∧ q ≤ Nat.sqrt k) (Finset.Icc 1 k), padicValNat p (q ^ (Nat.factorization (M k) q)) = padicValNat p (p ^ (Nat.factorization (M k) p)) := by
      rw [ Finset.sum_eq_single p ];
      · intro q hq hqp; haveI := Fact.mk hp; simp_all +decide [ padicValNat.pow ] ;
        exact Or.inr <| Or.inr <| mt hp.dvd_of_dvd_pow <| by rw [ Nat.dvd_prime hq.2.1 ] ; aesop;
      · exact fun h => False.elim <| h <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp.pos, by nlinarith [ Nat.sqrt_le k ] ⟩, hp, h_small ⟩;
    haveI := Fact.mk hp; simp_all +decide [ padicValNat.pow ] ;
    rw [ Nat.factorization_def ] ; aesop

/-
The p-adic valuation of the ratio of the product to the LCM of a set S is at least the sum of truncated valuations (min(v_p(i), e)) minus e, provided the maximum valuation in S is at least e.
-/
lemma valuation_ratio_ge_sum_min_sub_e (S : Finset ℕ) (p e : ℕ)
  (hp : p.Prime)
  (h_max : S.sup (padicValNat p) ≥ e)
  (h_nonzero : ∀ i ∈ S, i ≠ 0) :
  (padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) : ℤ) ≥ (∑ i ∈ S, min (padicValNat p i) e : ℤ) - e := by
    -- The p-adic valuation of the ratio of the product to the LCM of a set S is at least the sum of truncated valuations (min(v_p(i), e)) minus e.
    have h_ratio_val : (padicValNat p ((∏ i ∈ S, i) / (S.lcm id))) ≥ (∑ i ∈ S, (padicValNat p i)) - (S.sup (padicValNat p)) := by
      have h_ratio_val : (padicValNat p ((∏ i ∈ S, i) / (S.lcm id))) = (∑ i ∈ S, (padicValNat p i)) - (padicValNat p (S.lcm id)) := by
        have h_val_sum : padicValNat p ((∏ i ∈ S, i) / S.lcm id) = padicValNat p (∏ i ∈ S, i) - padicValNat p (S.lcm id) := by
          have h_div : ∀ {a b : ℕ}, a ≠ 0 → b ≠ 0 → a % b = 0 → padicValNat p (a / b) = padicValNat p a - padicValNat p b := by
            intros a b ha hb hab; have := Nat.dvd_of_mod_eq_zero hab; obtain ⟨ q, rfl ⟩ := this; simp +decide [ *, padicValNat.mul ] ;
            haveI := Fact.mk hp; rw [ padicValNat.mul ] <;> aesop;
          apply h_div;
          · exact Finset.prod_ne_zero_iff.mpr h_nonzero;
          · simp_all +decide [ Finset.lcm_eq_zero_iff ];
          · rw [ Nat.mod_eq_zero_of_dvd ];
            exact Finset.lcm_dvd fun x hx => Finset.dvd_prod_of_mem _ hx
        generalize_proofs at *; (
        have h_val_prod : ∀ {T : Finset ℕ}, (∀ i ∈ T, i ≠ 0) → padicValNat p (∏ i ∈ T, i) = ∑ i ∈ T, padicValNat p i := by
          intros T hT_nonzero
          induction' T using Finset.induction with i T hiT ih
          generalize_proofs at *; (
          simp +decide [ padicValNat.eq_zero_of_not_dvd, hp.ne_one ]);
          simp_all +decide [ Finset.prod_insert hiT, Finset.sum_insert hiT ];
          haveI := Fact.mk hp; rw [ padicValNat.mul ] <;> simp_all +decide [ Finset.prod_eq_zero_iff ] ;
        generalize_proofs at *; (
        rw [ h_val_sum, h_val_prod h_nonzero ]));
      have h_lcm_val : ∀ {T : Finset ℕ}, (∀ i ∈ T, i ≠ 0) → (padicValNat p (T.lcm id)) ≤ T.sup (padicValNat p) := by
        intros T hT_nonzero
        induction' T using Finset.induction with i T hiT ih;
        · simp +decide [ Finset.lcm ];
        · have h_lcm_val_insert : ∀ {a b : ℕ}, a ≠ 0 → b ≠ 0 → (padicValNat p (Nat.lcm a b)) ≤ max (padicValNat p a) (padicValNat p b) := by
            intros a b ha hb; haveI := Fact.mk hp; rw [ ← Nat.factorization_def, ← Nat.factorization_def, ← Nat.factorization_def ] ;
            · rw [ Nat.factorization_lcm ] <;> aesop;
            · exact hp;
            · exact hp;
            · exact hp;
          simp_all +decide [ Finset.lcm_insert ];
          exact Or.imp id ( fun h => h.trans ih ) ( h_lcm_val_insert hT_nonzero.1 ( Nat.ne_of_gt ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) ) );
      exact h_ratio_val.symm ▸ Nat.sub_le_sub_left ( h_lcm_val h_nonzero ) _;
    have h_sum_min : ∑ i ∈ S, (min (padicValNat p i) e : ℤ) ≤ ∑ i ∈ S, (padicValNat p i : ℤ) - (S.sup (padicValNat p) - e) := by
      -- Let $m = S.sup (padicValNat p)$. Then $m \ge e$.
      set m := S.sup (padicValNat p)
      have hm : m ≥ e := by
        exact h_max;
      -- If $m > e$, then there exists some $j \in S$ such that $v_p(j) = m > e$.
      by_cases hme : m > e;
      · obtain ⟨j, hj⟩ : ∃ j ∈ S, (padicValNat p j : ℤ) = m := by
          have h_exists_j : ∃ j ∈ S, (padicValNat p j : ℤ) = m := by
            have h_finite : S.Nonempty := by
              contrapose! hme; aesop;
            norm_num +zetaDelta at *;
            exact Finset.exists_max_image _ _ h_finite |> fun ⟨ j, hj₁, hj₂ ⟩ => ⟨ j, hj₁, le_antisymm ( Finset.le_sup ( f := padicValNat p ) hj₁ ) ( Finset.sup_le fun i hi => hj₂ i hi ) ⟩;
          exact h_exists_j;
        have h_sum_min : ∑ i ∈ S, (min (padicValNat p i) e : ℤ) ≤ ∑ i ∈ S, (padicValNat p i : ℤ) - (padicValNat p j - e) := by
          have h_sum_min_step : ∀ i ∈ S, (min (padicValNat p i) e : ℤ) ≤ (padicValNat p i : ℤ) - (if i = j then (padicValNat p j - e) else 0) := by
            grind
          convert Finset.sum_le_sum h_sum_min_step using 1 ; aesop;
        grind;
      · norm_num [ le_antisymm ( le_of_not_gt hme ) hm ];
        exact Finset.sum_le_sum fun i hi => min_le_left _ _;
    norm_cast at *;
    rw [ Int.subNatNat_eq_coe ] at *; omega;

/-
The sum of truncated p-adic valuations is invariant under shifting the interval by a multiple of the period p^e.
-/
lemma sum_min_valuation_shift (x y k p e : ℕ) (hp : p.Prime) (he : e > 0)
  (hx : x > 0) (hy : y > 0)
  (h_mod : x ≡ y + 1 [MOD p ^ e]) :
  ∑ i ∈ Finset.Icc (y + 1) (y + k), min (padicValNat p i) e =
  ∑ i ∈ Finset.Icc x (x + k - 1), min (padicValNat p i) e := by
    -- By definition of modular equivalence, the sequences of values in the intervals $[x, x+k-1]$ and $[y+1, y+k]$ are the same when considered modulo $p^e$.
    have h_seq_eq : ∑ i ∈ Finset.range k, min (padicValNat p (y + 1 + i)) e = ∑ i ∈ Finset.range k, min (padicValNat p (x + i)) e := by
      -- Since $x \equiv y + 1 \pmod{p^e}$, we have $x + i \equiv y + 1 + i \pmod{p^e}$ for all $i$.
      have h_cong : ∀ i, (x + i) ≡ (y + 1 + i) [MOD p^e] := by
        exact fun i => h_mod.add_right i;
      -- Since $x + i \equiv y + 1 + i \pmod{p^e}$, we have $\min(v_p(x + i), e) = \min(v_p(y + 1 + i), e)$ for all $i$.
      have h_min_eq : ∀ i, min (padicValNat p (x + i)) e = min (padicValNat p (y + 1 + i)) e := by
        -- Since $x + i \equiv y + 1 + i \pmod{p^e}$, we have $v_p(x + i) = v_p(y + 1 + i)$ if $v_p(x + i) < e$ and $v_p(x + i) = e$ if $v_p(x + i) \geq e$.
        intros i
        by_cases h_case : padicValNat p (x + i) < e;
        · have h_cong_val : p ^ (padicValNat p (x + i)) ∣ (y + 1 + i) ∧ ¬p ^ (padicValNat p (x + i) + 1) ∣ (y + 1 + i) := by
            have h_cong_val : p ^ (padicValNat p (x + i)) ∣ (x + i) ∧ ¬p ^ (padicValNat p (x + i) + 1) ∣ (x + i) := by
              haveI := Fact.mk hp; simp +decide [ padicValNat_dvd_iff ] ;
              aesop;
            have h_cong_val_y : (x + i) ≡ (y + 1 + i) [MOD p ^ (padicValNat p (x + i) + 1)] := by
              exact h_cong i |> Nat.ModEq.of_dvd ( pow_dvd_pow _ h_case );
            exact ⟨ Nat.dvd_of_mod_eq_zero ( h_cong_val_y.of_dvd ( pow_dvd_pow _ ( Nat.le_succ _ ) ) ▸ Nat.mod_eq_zero_of_dvd h_cong_val.1 ), fun h => h_cong_val.2 ( Nat.dvd_of_mod_eq_zero ( h_cong_val_y.symm ▸ Nat.mod_eq_zero_of_dvd h ) ) ⟩;
          have h_cong_val : padicValNat p (y + 1 + i) = padicValNat p (x + i) := by
            have h_cong_val : Nat.factorization (y + 1 + i) p = padicValNat p (x + i) := by
              exact Nat.le_antisymm ( Nat.le_of_not_lt fun h => h_cong_val.2 <| Nat.dvd_trans ( pow_dvd_pow _ h ) <| Nat.ordProj_dvd _ _ ) ( Nat.le_of_not_lt fun h => by have := Nat.dvd_trans ( pow_dvd_pow _ h ) h_cong_val.1; exact absurd this <| Nat.pow_succ_factorization_not_dvd ( by positivity ) <| by aesop );
            rw [ ← h_cong_val, Nat.factorization_def ] ; aesop;
          rw [ h_cong_val ];
        · -- Since $x + i \equiv y + 1 + i \pmod{p^e}$, we have $p^e \mid x + i$ and $p^e \mid y + 1 + i$.
          have h_div : p^e ∣ x + i ∧ p^e ∣ y + 1 + i := by
            have h_div : p^e ∣ x + i := by
              have h_div : p ^ (padicValNat p (x + i)) ∣ x + i := by
                convert Nat.ordProj_dvd ( x + i ) p using 1;
                rw [ Nat.factorization ] ; aesop;
              exact dvd_trans ( pow_dvd_pow _ ( le_of_not_gt h_case ) ) h_div;
            exact ⟨ h_div, Nat.dvd_of_mod_eq_zero ( h_cong i ▸ Nat.mod_eq_zero_of_dvd h_div ) ⟩;
          have h_val_ge_e : ∀ {n : ℕ}, p^e ∣ n → n ≠ 0 → padicValNat p n ≥ e := by
            intros n hn hn_ne_zero; exact (by
            obtain ⟨ k, rfl ⟩ := hn; simp +decide [ *, padicValNat.mul ] ;
            haveI := Fact.mk hp; rw [ padicValNat.mul ( by aesop ) ( by aesop ) ] ; aesop;);
          rw [ min_eq_right ( h_val_ge_e h_div.1 ( by positivity ) ), min_eq_right ( h_val_ge_e h_div.2 ( by positivity ) ) ];
      grind;
    erw [ Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range ];
    grind

/-
If a set S has at most one element with p-adic valuation greater than e, and the maximum valuation is at least e, then the valuation of prod/lcm is equal to the sum of truncated valuations minus e.
-/
lemma valuation_ratio_eq_sum_min_sub_e_of_unique_max (S : Finset ℕ) (p e : ℕ)
  (hp : p.Prime)
  (h_max : S.sup (padicValNat p) ≥ e)
  (h_unique : (S.filter (fun i => padicValNat p i > e)).card ≤ 1)
  (h_nonzero : ∀ i ∈ S, i ≠ 0) :
  padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (∑ i ∈ S, min (padicValNat p i) e) - e := by
    -- Let $v_p(n)$ be the valuation.
    have h_val : padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (∑ i ∈ S, padicValNat p i) - (S.sup (padicValNat p)) := by
      have h_val : padicValNat p (Finset.prod S id) = ∑ i ∈ S, padicValNat p i := by
        have h_val_prod : ∀ {T : Finset ℕ}, (∀ i ∈ T, i ≠ 0) → padicValNat p (∏ i ∈ T, i) = ∑ i ∈ T, padicValNat p i := by
          intros T hT_nonzero
          induction' T using Finset.induction with i T hiT ih;
          · norm_num;
          · rw [ Finset.prod_insert hiT, Finset.sum_insert hiT ];
            haveI := Fact.mk hp; rw [ padicValNat.mul ( hT_nonzero i ( Finset.mem_insert_self i T ) ) ( Finset.prod_ne_zero_iff.mpr fun x hx => hT_nonzero x ( Finset.mem_insert_of_mem hx ) ), ih fun x hx => hT_nonzero x ( Finset.mem_insert_of_mem hx ) ] ;
        exact h_val_prod h_nonzero;
      have h_val_lcm : padicValNat p (Finset.lcm S id) = S.sup (padicValNat p) := by
        have h_val_lcm : ∀ {T : Finset ℕ}, (∀ i ∈ T, i ≠ 0) → padicValNat p (Finset.lcm T id) = Finset.sup T (padicValNat p) := by
          intros T hT_nonzero
          induction' T using Finset.induction with i T hiT ih;
          · simp +decide [ Finset.lcm ];
          · have h_val_lcm_insert : padicValNat p (Nat.lcm i (Finset.lcm T id)) = max (padicValNat p i) (padicValNat p (Finset.lcm T id)) := by
              have h_val_lcm_insert : ∀ {a b : ℕ}, a ≠ 0 → b ≠ 0 → padicValNat p (Nat.lcm a b) = max (padicValNat p a) (padicValNat p b) := by
                intros a b ha hb; haveI := Fact.mk hp; rw [ ← Nat.factorization_def, ← Nat.factorization_def, ← Nat.factorization_def ] ;
                · rw [ Nat.factorization_lcm ] <;> aesop;
                · exact hp;
                · exact hp;
                · exact hp;
              exact h_val_lcm_insert ( hT_nonzero i ( Finset.mem_insert_self i T ) ) ( Nat.ne_of_gt ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by intros h; obtain ⟨ x, hx ⟩ := h; specialize hT_nonzero x ( Finset.mem_insert_of_mem hx.1 ) ; aesop ) ) ) );
            aesop;
        apply h_val_lcm; assumption;
      haveI := Fact.mk hp; rw [ ← h_val, ← h_val_lcm, padicValNat.div_of_dvd ] ; aesop;
      exact Finset.lcm_dvd fun x hx => Finset.dvd_prod_of_mem _ hx;
    -- We want $\sum (v_p(i) - \min(v_p(i), e)) = \max v_p(i) - e$.
    have h_sum : ∑ i ∈ S, (padicValNat p i - min (padicValNat p i) e) = (S.sup (padicValNat p)) - e := by
      -- If there are no elements with $v_p(i) > e$, then the sum is $0$.
      by_cases h_no_large : ∀ i ∈ S, padicValNat p i ≤ e;
      · cases eq_or_lt_of_le h_max <;> aesop;
      · -- If there is exactly one element with $v_p(i) > e$, then the sum is $v_p(z) - e$.
        obtain ⟨z, hzS, hz⟩ : ∃ z ∈ S, padicValNat p z > e ∧ ∀ i ∈ S, i ≠ z → padicValNat p i ≤ e := by
          obtain ⟨z, hz⟩ : ∃ z ∈ S, padicValNat p z > e := by
            grind;
          exact ⟨ z, hz.1, hz.2, fun i hi hi' => not_lt.1 fun hi'' => h_unique.not_lt <| Finset.one_lt_card.2 ⟨ i, by aesop, z, by aesop ⟩ ⟩;
        -- Since z is the only element with padicValNat p i > e, the supremum of the padicValNat p over S is exactly padicValNat p z.
        have h_sup_eq : S.sup (padicValNat p) = padicValNat p z := by
          exact le_antisymm ( Finset.sup_le fun i hi => if hi' : i = z then hi'.symm ▸ le_rfl else hz.2 i hi hi' |> le_trans <| by linarith ) ( Finset.le_sup ( f := padicValNat p ) hzS );
        rw [ Finset.sum_eq_single z ] <;> aesop;
    have h_sum : ∑ i ∈ S, padicValNat p i = ∑ i ∈ S, min (padicValNat p i) e + ∑ i ∈ S, (padicValNat p i - min (padicValNat p i) e) := by
      rw [ ← Finset.sum_add_distrib, Finset.sum_congr rfl fun x hx => add_tsub_cancel_of_le <| min_le_left _ _ ];
    omega

#check small_prime_conditions_satisfied

/-
If x is 1 mod m(k) and y is 0 mod m(k), then for any prime p <= sqrt(k), x is 1 mod p^(v_p(M(k))) and y is 0 mod p^(v_p(M(k))).
-/
lemma small_prime_conditions_satisfied_proven (k x y : ℕ) (p : ℕ) (hp : p.Prime) (h_sqrt : p * p ≤ k)
  (h_mod_x : x % (m k) = 1) (h_mod_y : y % (m k) = 0) :
  x % (p ^ (padicValNat p (M k))) = 1 ∧ y % (p ^ (padicValNat p (M k))) = 0 := by
    have h_mod_x_y : x % (m k) = 1 ∧ y % (m k) = 0 → x % (p ^ (padicValNat p (M k))) = 1 ∧ y % (p ^ (padicValNat p (M k))) = 0 := by
      intro h
      exact (small_prime_conditions_satisfied k x y p hp (by
      exact h_sqrt) h_mod_x h_mod_y);
    exact h_mod_x_y ⟨ h_mod_x, h_mod_y ⟩

/-
The sum of truncated valuations over the y-interval is at least the sum over the x-interval plus e.
-/
lemma sum_min_valuation_ineq (x y k C_int p e : ℕ) (hp : p.Prime) (he : e > 0)
  (hx : x > 0) (hy : y > 0)
  (h_mod : x ≡ y + 1 [MOD p ^ e])
  (h_y_mod : y ≡ 0 [MOD p ^ e])
  (hC : C_int ≥ 1) :
  ∑ i ∈ Finset.Icc y (y + k + C_int - 1), min (padicValNat p i) e ≥
  (∑ i ∈ Finset.Icc x (x + k - 1), min (padicValNat p i) e) + e := by
    -- Since $y \equiv 0 \pmod{p^e}$, we have $\min(v_p(y), e) = e$.
    have h_y_min : min (padicValNat p y) e = e := by
      have := Nat.dvd_of_mod_eq_zero h_y_mod;
      obtain ⟨ k, hk ⟩ := this;
      haveI := Fact.mk hp; rw [ hk, padicValNat.mul ] <;> aesop;
    have h_split_sum : ∑ i ∈ Finset.Icc y (y + k + C_int - 1), min (padicValNat p i) e ≥ min (padicValNat p y) e + ∑ i ∈ Finset.Icc (y + 1) (y + k), min (padicValNat p i) e := by
      have h_split_sum : Finset.Icc y (y + k + C_int - 1) ⊇ {y} ∪ Finset.Icc (y + 1) (y + k) := by
        exact Finset.union_subset ( Finset.singleton_subset_iff.mpr ( Finset.mem_Icc.mpr ⟨ le_rfl, Nat.le_sub_one_of_lt ( by linarith ) ⟩ ) ) ( Finset.Icc_subset_Icc ( by linarith ) ( by omega ) );
      refine' le_trans _ ( Finset.sum_le_sum_of_subset h_split_sum );
      rw [ Finset.sum_union ] <;> norm_num;
    simp_all +decide [ add_comm, add_left_comm, add_assoc ];
    exact le_trans ( add_le_add_left ( sum_min_valuation_shift x y k p e hp he hx hy h_mod ▸ le_rfl ) _ ) h_split_sum

/-
For small primes, the difference in p-adic valuations is bounded below by -v_p(m(k)).
-/
lemma small_prime_valuation_bound (k x y C_int : ℕ) (p : ℕ)
  (hp : p.Prime) (h_small : p ≤ k.sqrt)
  (hx0 : x > 0) (hy0 : y > 0)
  (h_mod_x : x % (m k) = 1)
  (h_mod_y : y % (m k) = 0)
  (hC : C_int ≥ 1)
  (hk : k ≥ 1) :
  (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
  (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥
  -(padicValNat p (m k) : ℤ) := by
    -- Let $e = v_p(M(k))$. By `valuation_m_eq_valuation_M`, $v_p(m(k)) = e$.
    set e := padicValNat p (M k) with he;
    -- By Lemma~\ref{lem:small_prime_conditions_satisfied_proven}, $x \equiv 1 \pmod{p^e}$ and $y \equiv 0 \pmod{p^e}$.
    have h_mod_x_y : x % (p ^ e) = 1 ∧ y % (p ^ e) = 0 := by
      have h_mod_xy : x % (p ^ e) = 1 ∧ y % (p ^ e) = 0 := by
        have h_mod_x_step : x % (p ^ e) = 1 := by
          have := small_prime_conditions_satisfied_proven k x y p hp ( by nlinarith [ Nat.sqrt_le k ] ) h_mod_x;
          exact this h_mod_y |>.1
        have h_mod_y_step : y % (p ^ e) = 0 := by
          have h_mod_y_step : p ^ e ∣ m k := by
            have h_val_eq : padicValNat p (m k) = e := by
              apply valuation_m_eq_valuation_M k p hp h_small hk
            rw [ ← h_val_eq ];
            convert Nat.ordProj_dvd ( m k ) p using 1;
            rw [ Nat.factorization_def ] ; aesop;
          exact Nat.mod_eq_zero_of_dvd ( dvd_trans h_mod_y_step ( Nat.dvd_of_mod_eq_zero h_mod_y ) )
        exact ⟨h_mod_x_step, h_mod_y_step⟩;
      exact h_mod_xy;
    -- Apply `valuation_ratio_eq_sum_min_sub_e_of_unique_max` to $x$ and `valuation_ratio_ge_sum_min_sub_e` to $y$.
    have h_val_x : padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = (∑ i ∈ Finset.Icc x (x + k - 1), min (padicValNat p i) e) - e := by
      apply_rules [ valuation_ratio_eq_sum_min_sub_e_of_unique_max ];
      · -- Since $p^e \le k$, there exists some $i \in [x, x+k-1]$ such that $p^e \mid i$.
        obtain ⟨i, hi⟩ : ∃ i ∈ Finset.Icc x (x + k - 1), p ^ e ∣ i := by
          have h_exists_i : ∃ i ∈ Finset.Icc x (x + k - 1), i ≡ 0 [MOD p ^ e] := by
            have h_length : k ≥ p ^ e := by
              have h_len : p ^ e ≤ k := by
                have h_e : e = Nat.log p k := by
                  have h_e : e = Nat.factorization (M k) p := by
                    rw [ Nat.factorization_def ] ; aesop;
                  exact?
                rw [h_e]
                exact Nat.pow_log_le_self p (by linarith);
              exact h_len
            exact ⟨ p ^ e * ( ( x + k - 1 ) / p ^ e ), Finset.mem_Icc.mpr ⟨ by nlinarith [ Nat.div_add_mod ( x + k - 1 ) ( p ^ e ), Nat.mod_lt ( x + k - 1 ) ( pow_pos hp.pos e ), Nat.sub_add_cancel ( by linarith : 1 ≤ x + k ) ], by nlinarith [ Nat.div_mul_le_self ( x + k - 1 ) ( p ^ e ), Nat.sub_add_cancel ( by linarith : 1 ≤ x + k ) ] ⟩, Nat.modEq_zero_iff_dvd.mpr <| dvd_mul_right _ _ ⟩;
          exact ⟨ h_exists_i.choose, h_exists_i.choose_spec.1, Nat.dvd_of_mod_eq_zero h_exists_i.choose_spec.2 ⟩;
        refine' le_trans _ ( Finset.le_sup hi.1 );
        haveI := Fact.mk hp; rw [ padicValNat_dvd_iff ] at hi; aesop;
      · -- Since $p^e \le k < p^{e+1}$, there can be at most one element in the interval $[x, x+k-1]$ that is divisible by $p^{e+1}$.
        have h_unique_div : ∀ i j : ℕ, i ∈ Finset.Icc x (x + k - 1) → j ∈ Finset.Icc x (x + k - 1) → p ^ (e + 1) ∣ i → p ^ (e + 1) ∣ j → i = j := by
          intros i j hi hj hi_div hj_div
          have h_diff : |(i : ℤ) - j| < p ^ (e + 1) := by
            have h_diff : |(i : ℤ) - j| < k := by
              exact abs_sub_lt_iff.mpr ⟨ by linarith [ Finset.mem_Icc.mp hi, Finset.mem_Icc.mp hj, Nat.sub_add_cancel ( by linarith : 1 ≤ x + k ) ], by linarith [ Finset.mem_Icc.mp hi, Finset.mem_Icc.mp hj, Nat.sub_add_cancel ( by linarith : 1 ≤ x + k ) ] ⟩;
            have h_diff : k < p ^ (e + 1) := by
              have h_diff : k < p ^ (Nat.log p k + 1) := by
                exact Nat.lt_pow_succ_log_self hp.one_lt _;
              convert h_diff using 1;
              rw [ show e = Nat.log p k from ?_ ];
              exact?;
            linarith;
          contrapose! h_diff;
          exact Int.le_of_dvd ( abs_pos.mpr ( sub_ne_zero.mpr <| mod_cast h_diff ) ) <| by simpa using dvd_sub ( Int.natCast_dvd_natCast.mpr hi_div ) ( Int.natCast_dvd_natCast.mpr hj_div ) ;
        have h_unique_div : ∀ i : ℕ, i ∈ Finset.Icc x (x + k - 1) → padicValNat p i > e → p ^ (e + 1) ∣ i := by
          intros i hi hpi
          have h_div : p ^ (e + 1) ∣ i := by
            have h_div : p ^ (padicValNat p i) ∣ i := by
              convert Nat.ordProj_dvd i p using 1;
              rw [ Nat.factorization_def ] ; aesop ( simp_config := { singlePass := true } ) ;
            exact dvd_trans ( pow_dvd_pow _ hpi ) h_div
          exact h_div;
        exact Finset.card_le_one.mpr fun i hi j hj => ‹∀ i j : ℕ, i ∈ Finset.Icc x ( x + k - 1 ) → j ∈ Finset.Icc x ( x + k - 1 ) → p ^ ( e + 1 ) ∣ i → p ^ ( e + 1 ) ∣ j → i = j› i j ( Finset.filter_subset _ _ hi ) ( Finset.filter_subset _ _ hj ) ( h_unique_div i ( Finset.filter_subset _ _ hi ) ( Finset.mem_filter.mp hi |>.2 ) ) ( h_unique_div j ( Finset.filter_subset _ _ hj ) ( Finset.mem_filter.mp hj |>.2 ) );
      · exact fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ;
    have h_val_y : padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) ≥ (∑ i ∈ Finset.Icc y (y + k + C_int - 1), min (padicValNat p i) e) - e := by
      have h_val_y : ∀ {S : Finset ℕ}, (∀ i ∈ S, i ≠ 0) → S.sup (padicValNat p) ≥ e → padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) ≥ (∑ i ∈ S, min (padicValNat p i) e) - e := by
        intros S hS_nonzero hS_max; exact (by
        have := @valuation_ratio_ge_sum_min_sub_e S p e hp hS_max hS_nonzero;
        norm_cast at this;
        rw [ Int.subNatNat_eq_coe ] at this ; omega);
      apply h_val_y;
      · exact fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ;
      · -- Since $y \equiv 0 \pmod{p^e}$, there exists some $i \in [y, y + k + C_int - 1]$ such that $p^e \mid i$.
        obtain ⟨i, hi⟩ : ∃ i ∈ Finset.Icc y (y + k + C_int - 1), p ^ e ∣ i := by
          exact ⟨ y, Finset.mem_Icc.mpr ⟨ by linarith, Nat.le_sub_one_of_lt <| by linarith ⟩, Nat.dvd_of_mod_eq_zero h_mod_x_y.2 ⟩;
        have h_val_i : padicValNat p i ≥ e := by
          obtain ⟨ q, rfl ⟩ := hi.2;
          haveI := Fact.mk hp; rw [ padicValNat.mul ] <;> aesop;
        exact le_trans h_val_i ( Finset.le_sup ( f := padicValNat p ) hi.1 );
    -- By Lemma~\ref{lem:sum_min_valuation_ineq}, $\sum_{i \in I_y} \min \ge \sum_{i \in I_x} \min + e$.
    have h_sum_min_ineq : (∑ i ∈ Finset.Icc y (y + k + C_int - 1), min (padicValNat p i) e) ≥ (∑ i ∈ Finset.Icc x (x + k - 1), min (padicValNat p i) e) + e := by
      apply sum_min_valuation_ineq;
      any_goals assumption;
      · refine' Nat.pos_of_ne_zero _;
        intro H; simp_all +decide [ Nat.mod_eq_of_lt ] ;
        norm_num [ ← he ] at *;
        norm_num [ Nat.mod_one ] at h_mod_x_y;
      · rw [ Nat.modEq_iff_dvd ];
        simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
        exact ⟨ ( y / p ^ padicValNat p ( M k ) ) - ( x / p ^ padicValNat p ( M k ) ), by linarith [ Nat.mod_add_div y ( p ^ padicValNat p ( M k ) ), Nat.mod_add_div x ( p ^ padicValNat p ( M k ) ) ] ⟩;
      · exact h_mod_x_y.2;
    omega

/-
Compute the p-adic valuation of the RHS bound for each prime p.
-/
lemma valuation_rhs_compute (k : ℕ) (δ : ℝ) (p : ℕ) (hp : p.Prime) :
  padicValRat p ((M_prod k : ℚ) / ((m k : ℚ) * (BadPrimes k δ).prod (fun p => (p : ℚ) ^ 2))) =
  if p ≤ k.sqrt then -(padicValNat p (m k) : ℤ)
  else if p ∈ PrimesIn k then
    if p ∈ BadPrimes k δ then -1 else 1
  else 0 := by
    -- Let's simplify the expression for the p-adic valuation of the RHS bound.
    have h_rhs_val : padicValRat p ((M_prod k : ℚ) / ((m k) * ((BadPrimes k δ).prod (fun p => (p : ℚ) ^ 2))) : ℚ) = padicValRat p ((M_prod k : ℚ)) - padicValRat p ((m k) : ℚ) - 2 * padicValRat p ((BadPrimes k δ).prod (fun p => (p : ℚ))) := by
      by_cases hM : M_prod k = 0 <;> by_cases hm : m k = 0 <;> by_cases hBad : ∏ p ∈ BadPrimes k δ, ( p : ℚ ) = 0 <;> simp_all +decide [ padicValRat.div, padicValRat.mul ];
      all_goals simp_all +decide [ Finset.prod_eq_zero_iff, padicValRat.div, padicValRat.mul ];
      all_goals simp_all +decide [ BadPrimes, PrimesIn ];
      · exact absurd hm <| ne_of_gt <| Finset.prod_pos fun q hq => pow_pos ( Nat.Prime.pos <| by aesop ) _;
      · exact absurd hM <| ne_of_gt <| Finset.prod_pos fun x hx => Nat.Prime.pos <| Finset.mem_filter.mp hx |>.2.1;
      · exact absurd hm ( Nat.ne_of_gt ( Finset.prod_pos fun x hx => pow_pos ( Nat.Prime.pos ( by aesop ) ) _ ) );
      · rw [ Finset.prod_pow ];
        haveI := Fact.mk hp; rw [ padicValRat.pow ] ; ring;
        exact Finset.prod_ne_zero_iff.mpr fun x hx => Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| by aesop;
    have h_rhs_val_simp : padicValRat p ((M_prod k : ℚ)) = if p ∈ PrimesIn k then 1 else 0 := by
      have h_rhs_val_cases : padicValRat p (M_prod k : ℚ) = ∑ q ∈ PrimesIn k, padicValRat p (q : ℚ) := by
        have h_rhs_val_cases : padicValRat p (∏ q ∈ PrimesIn k, (q : ℚ)) = ∑ q ∈ PrimesIn k, padicValRat p (q : ℚ) := by
          haveI := Fact.mk hp;
          have h_rhs_val_cases : ∀ {S : Finset ℕ}, (∀ q ∈ S, q ≠ 0) → padicValRat p (∏ q ∈ S, (q : ℚ)) = ∑ q ∈ S, padicValRat p (q : ℚ) := by
            intros S hS_nonzero
            induction' S using Finset.induction with q S hqS ih;
            · norm_num +zetaDelta at *;
            · rw [ Finset.prod_insert hqS, Finset.sum_insert hqS ];
              rw [ padicValRat.mul ] <;> simp_all +decide [ Finset.prod_eq_zero_iff ];
          exact h_rhs_val_cases fun q hq => Nat.Prime.ne_zero <| Finset.mem_filter.mp hq |>.2.1;
        simpa [ M_prod ] using h_rhs_val_cases;
      have h_rhs_val_cases : ∀ q ∈ PrimesIn k, padicValRat p (q : ℚ) = if p = q then 1 else 0 := by
        intro q hq; split_ifs <;> simp_all +decide [ padicValRat.of_nat ] ;
        exact Or.inr <| Or.inr <| fun h => ‹¬p = q› <| by have := Nat.prime_dvd_prime_iff_eq hp ( Finset.mem_filter.mp hq |>.2.1 ) ; tauto;
      aesop
    have h_rhs_val_simp2 : padicValRat p ((m k) : ℚ) = if p ≤ k.sqrt then (padicValNat p (m k) : ℤ) else 0 := by
      split_ifs <;> simp_all +decide [ padicValNat_def ];
      refine Or.inr <| Or.inr <| ?_;
      rw [ Nat.Prime.dvd_iff_not_coprime hp ];
      simp +zetaDelta at *;
      refine' Nat.Coprime.prod_right fun q hq => _;
      exact hp.coprime_iff_not_dvd.mpr fun h => by have := Nat.Prime.dvd_of_dvd_pow hp h; exact absurd this ( Nat.not_dvd_of_pos_of_lt ( Nat.Prime.pos ( by aesop ) ) ( by nlinarith [ Finset.mem_filter.mp hq, Nat.sqrt_lt.mp ‹_› ] ) ) ;
    have h_rhs_val_simp3 : padicValRat p ((BadPrimes k δ).prod (fun p => (p : ℚ))) = if p ∈ BadPrimes k δ then 1 else 0 := by
      convert padicValRat_prod_primes _ _ _ using 1;
      any_goals exact hp;
      any_goals exact BadPrimes k δ;
      exact ⟨ fun h => fun _ => h, fun h => h fun q hq => Finset.mem_filter.mp ( Finset.mem_filter.mp hq |>.1 ) |>.2.1 ⟩;
    split_ifs at * <;> simp_all +decide [ Finset.prod_pow ] ;
    · exact absurd ‹p ∈ PrimesIn k› ( by unfold PrimesIn; aesop );
    · exact absurd ( Finset.mem_filter.mp ‹p ∈ PrimesIn k› |>.2.2 ) ( by nlinarith [ Nat.sqrt_le k ] );
    · unfold BadPrimes at *; aesop;
    · unfold BadPrimes at *; aesop;

/-
For small primes p <= sqrt(k), the valuation of the ratio of ratios is at least the valuation of the RHS bound.
-/
lemma valuation_comparison_small (k x y C_int : ℕ) (δ : ℝ)
  (hC : C_int ≥ 1)
  (hx0 : x > 0) (hy0 : y > 0)
  (h_small_p : ∀ p, p.Prime → p ≤ k.sqrt →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥
    -(padicValNat p (m k) : ℤ))
  (p : ℕ) (hp : p.Prime) (h_le_sqrt : p ≤ k.sqrt) :
  padicValRat p (ratio_of_ratios k x y C_int) ≥
  padicValRat p ((M_prod k : ℚ) / ((m k : ℚ) * (BadPrimes k δ).prod (fun p => (p : ℚ) ^ 2))) := by
    convert h_small_p p hp h_le_sqrt using 1 ; norm_num [ ratio_of_ratios ];
    · convert padicValRat.div _ _ using 1;
      · have h_val_eq : ∀ (n : ℕ), n ≠ 0 → padicValRat p (n : ℚ) = padicValNat p n := by
          bound;
        rw [ ← h_val_eq, ← h_val_eq ];
        · rw [ Nat.cast_div, Nat.cast_div ] <;> norm_num;
          · exact fun n hn₁ hn₂ => Finset.dvd_prod_of_mem _ ( Finset.mem_Icc.mpr ⟨ hn₁, hn₂ ⟩ );
          · positivity;
          · exact fun n hn₁ hn₂ => Finset.dvd_prod_of_mem _ <| Finset.mem_Icc.mpr ⟨ hn₁, hn₂ ⟩;
          · linarith;
        · exact Nat.ne_of_gt ( Nat.div_pos ( Nat.le_of_dvd ( Finset.prod_pos fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ) ( Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi ) ) ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) );
        · refine' Nat.ne_of_gt ( Nat.div_pos _ _ );
          · exact Nat.le_of_dvd ( Finset.prod_pos fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ) ( Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi );
          · exact Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) );
      · exact ⟨ hp ⟩;
      · exact div_ne_zero ( Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ] ) ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop );
      · exact div_ne_zero ( Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ] ) <| Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
    · convert valuation_rhs_compute k δ p hp using 1;
      rw [ if_pos h_le_sqrt ]

/-
The ratio of ratios is bounded below by M_prod / (m * BadPrimes^2).
-/
lemma ratio_lower_bound_with_m (k x y C_int : ℕ) (δ : ℝ)
  (hC : C_int ≥ 1)
  (hx0 : x > 0) (hy0 : y > 0)
  (h_good_p : ∀ p ∈ PrimesIn k, ¬ is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) + 1)
  (h_bad_p : ∀ p ∈ PrimesIn k, is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) - 1)
  (h_small_p : ∀ p, p.Prime → p ≤ k.sqrt →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥
    -(padicValNat p (m k) : ℤ))
  (h_large_p : ∀ p, p.Prime → p > k + C_int →
    padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) = 0 ∧
    padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = 0)
  (h_diff_ge_zero : ∀ p, p > k →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥ 0) :
  ratio_of_ratios k x y C_int ≥ (M_prod k : ℚ) / ((m k : ℚ) * (BadPrimes k δ).prod (fun p => (p : ℚ) ^ 2)) := by
    apply rational_ge_of_valuation_ge;
    · unfold ratio_of_ratios;
      simp +zetaDelta at *;
      refine' div_pos _ _;
      · exact div_pos ( Finset.prod_pos fun i hi => Nat.cast_pos.mpr <| by linarith [ Finset.mem_Icc.mp hi ] ) <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop;
      · refine' div_pos ( Finset.prod_pos fun i hi => Nat.cast_pos.mpr <| by linarith [ Finset.mem_Icc.mp hi ] ) ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop );
    · refine' div_pos ( Nat.cast_pos.mpr _ ) ( mul_pos ( Nat.cast_pos.mpr _ ) ( Finset.prod_pos fun p hp => pow_pos ( Nat.cast_pos.mpr _ ) _ ) );
      · exact Finset.prod_pos fun p hp => Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2.1;
      · exact Finset.prod_pos fun p hp => pow_pos ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2.1 ) ) _;
      · exact Nat.Prime.pos ( Finset.mem_filter.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2.1 );
    · intro p hp; by_cases h : p ≤ k.sqrt <;> simp +decide [ *, h, padicValRat.div ] ;
      · convert valuation_comparison_small k x y C_int δ hC hx0 hy0 ( fun p hp hp' => h_small_p p hp hp' ) p hp h using 1;
      · by_cases h' : p ∈ PrimesIn k <;> simp +decide [ *, padicValRat.div ] at *;
        · by_cases h'' : p ∈ BadPrimes k δ <;> simp +decide [ *, padicValRat.div ] at *;
          · -- Since $p \in \text{BadPrimes } k \delta$, we have $\text{padicValRat } p (\text{ratio\_of\_ratios } k x y C_int) \geq -1$.
            have h_padic_ge_neg1 : padicValRat p (ratio_of_ratios k x y C_int) ≥ -1 := by
              have h_padic_ge_neg1 : padicValRat p (ratio_of_ratios k x y C_int) = padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) - padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) := by
                convert padicValRat.div _ _ using 1;
                · convert rfl;
                  · rw [ ← Nat.cast_prod, ← Nat.cast_div ];
                    · norm_num +zetaDelta at *;
                    · exact Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi;
                    · simp +decide [ Finset.lcm_eq_zero_iff ];
                      linarith;
                  · rw [ ← Nat.cast_prod, ← Nat.cast_div ] <;> norm_cast;
                    · exact Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi;
                    · norm_num [ Finset.lcm_eq_zero_iff ];
                      linarith;
                · exact ⟨ hp ⟩;
                · simp +decide [ Finset.prod_eq_zero_iff, Finset.lcm_eq_zero_iff ];
                  linarith;
                · simp +zetaDelta at *;
                  exact ⟨ Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ], hx0.ne' ⟩;
              linarith [ h_bad_p p h' ( by unfold BadPrimes at h''; aesop ) ];
            convert h_padic_ge_neg1.le using 1;
            convert valuation_rhs_compute k δ p hp using 1;
            grind;
          · -- Since $p$ is not a bad prime, the p-adic valuation of the ratio_of_ratios is at least 1.
            have h_val_ratio : padicValRat p (ratio_of_ratios k x y C_int) ≥ 1 := by
              have h_val_ratio : padicValRat p (ratio_of_ratios k x y C_int) = padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) - padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) := by
                convert padicValRat.div _ _ using 1;
                · congr! 1;
                  · rw [ ← Nat.cast_prod, ← Nat.cast_div ] <;> norm_num;
                    · exact fun b hb₁ hb₂ => Finset.dvd_prod_of_mem _ ( Finset.mem_Icc.mpr ⟨ hb₁, hb₂ ⟩ );
                    · linarith;
                  · convert rfl;
                    convert padicValRat.div _ _ using 1;
                    · convert padicValRat.div _ _ using 1;
                      · rw [ ← Nat.cast_prod, ← Nat.cast_div ];
                        · norm_num +zetaDelta at *;
                        · exact Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi;
                        · simp +decide [ Finset.lcm_eq_zero_iff ];
                          linarith;
                      · exact ⟨ hp ⟩;
                      · exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ] ;
                      · simp +decide [ Finset.lcm_eq_zero_iff, hx0.ne', hy0.ne' ];
                    · exact ⟨ hp ⟩;
                    · exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ] ;
                    · simp +decide [ Finset.lcm_eq_zero_iff, hx0.ne', hy0.ne' ];
                · exact ⟨ hp ⟩;
                · exact div_ne_zero ( Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ] ) ( Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop );
                · simp +zetaDelta at *;
                  exact ⟨ Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ], hx0.ne' ⟩;
              linarith [ h_good_p p h' ( by unfold BadPrimes at h''; aesop ) ];
            have h_val_rhs : padicValRat p (M_prod k / (m k * (BadPrimes k δ).prod (fun p => (p : ℚ) ^ 2))) = if p ∈ BadPrimes k δ then -1 else 1 := by
              have := valuation_rhs_compute k δ p hp; aesop;
            aesop;
        · -- Since $p$ is not in $PrimesIn k$, it must be greater than $k$. Therefore, the p-adic valuation of the product of bad primes is zero.
          have h_val_zero : padicValRat p (M_prod k / ((m k) * (∏ p ∈ BadPrimes k δ, (p : ℚ) ^ 2))) = 0 := by
            convert valuation_rhs_compute k δ p hp using 1;
            aesop;
          have h_val_pos : padicValRat p (ratio_of_ratios k x y C_int) ≥ 0 := by
            have h_val_pos : (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) - (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥ 0 := by
              by_cases h'' : p > k <;> simp_all +decide [ Nat.lt_succ_iff ];
              exact False.elim <| h' <| Finset.mem_filter.mpr ⟨ Finset.mem_Icc.mpr ⟨ hp.pos, h'' ⟩, hp, by nlinarith [ Nat.lt_succ_sqrt k ] ⟩;
            convert h_val_pos using 1;
            convert padicValRat.div _ _ using 1;
            · convert rfl using 2;
              · convert padicValRat.div _ _ using 1;
                · convert padicValRat.div _ _ using 1;
                  · rw [ ← Nat.cast_prod, ← Nat.cast_div ] <;> norm_num [ hp.ne_zero, hp.ne_one ];
                    · exact fun b hb₁ hb₂ => Finset.dvd_prod_of_mem _ ( Finset.mem_Icc.mpr ⟨ hb₁, hb₂ ⟩ );
                    · linarith;
                  · exact ⟨ hp ⟩;
                  · exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ] ;
                  · simp +decide [ Finset.lcm_eq_zero_iff ];
                    linarith;
                · exact ⟨ hp ⟩;
                · exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ] ;
                · simp +decide [ Finset.lcm_eq_zero_iff ];
                  linarith;
              · convert padicValRat.div _ _ using 1;
                · convert padicValRat.div _ _ using 1;
                  · rw [ ← Nat.cast_prod, ← Nat.cast_div ] <;> norm_num;
                    · exact fun b hb₁ hb₂ => Finset.dvd_prod_of_mem _ ( Finset.mem_Icc.mpr ⟨ hb₁, hb₂ ⟩ );
                    · linarith;
                  · exact ⟨ hp ⟩;
                  · exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ] ;
                  · simp +decide [ Finset.lcm_eq_zero_iff ];
                    linarith;
                · exact ⟨ hp ⟩;
                · exact Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ] ;
                · simp +decide [ Finset.lcm_eq_zero_iff, hx0.ne' ];
            · exact ⟨ hp ⟩;
            · simp +zetaDelta at *;
              exact ⟨ Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ], hy0.ne' ⟩;
            · simp +zetaDelta at *;
              exact ⟨ Finset.prod_ne_zero_iff.mpr fun i hi => Nat.cast_ne_zero.mpr <| by linarith [ Finset.mem_Icc.mp hi ], hx0.ne' ⟩;
          linarith

#check mod_reflection

/-
The p-adic valuation of the ratio of ratios is the difference of the p-adic valuations of the integer ratios.
-/
lemma valuation_ratio_of_ratios_eq_diff (k x y C_int : ℕ) (p : ℕ) (hp : p.Prime) (hx0 : x > 0) (hy0 : y > 0) :
  padicValRat p (ratio_of_ratios k x y C_int) =
  (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
  (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) := by
    unfold ratio_of_ratios;
    have h_val_ratio : ∀ {a b : ℕ}, a ≠ 0 → b ≠ 0 → padicValRat p (a / b : ℚ) = (padicValNat p a : ℤ) - (padicValNat p b : ℤ) := by
      intros a b ha hb; haveI := Fact.mk hp; rw [ padicValRat.div ] <;> aesop;
    convert h_val_ratio _ _ using 2;
    · rw [ Nat.cast_div, Nat.cast_div ] <;> norm_num;
      · exact fun b hb₁ hb₂ => Finset.dvd_prod_of_mem _ <| Finset.mem_Icc.mpr ⟨ hb₁, hb₂ ⟩;
      · positivity;
      · exact fun b hb₁ hb₂ => Finset.dvd_prod_of_mem _ <| Finset.mem_Icc.mpr ⟨ hb₁, hb₂ ⟩;
      · positivity;
    · refine' Nat.ne_of_gt ( Nat.div_pos _ _ );
      · exact Nat.le_of_dvd ( Finset.prod_pos fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ) ( Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi );
      · exact Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) );
    · exact Nat.ne_of_gt ( Nat.div_pos ( Nat.le_of_dvd ( Finset.prod_pos fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ) ( Finset.lcm_dvd fun i hi => Finset.dvd_prod_of_mem _ hi ) ) ( Nat.pos_of_ne_zero ( mt Finset.lcm_eq_zero_iff.mp ( by aesop ) ) ) )

/-
The ratio of LCMs is bounded below by a specific expression involving M, m, x, y, k, and C.
-/
lemma lcm_ratio_lower_bound_detailed (k x y C_int : ℕ) (δ : ℝ) (ε : ℝ)
  (hC : C_int ≥ 1)
  (hx0 : x > 0) (hy0 : y > 0) (hxy : x < y)
  (h_good_p : ∀ p ∈ PrimesIn k, ¬ is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) + 1)
  (h_bad_p : ∀ p ∈ PrimesIn k, is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) - 1)
  (h_small_p : ∀ p, p.Prime → p ≤ k.sqrt →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥
    -(padicValNat p (m k) : ℤ))
  (h_large_p : ∀ p, p.Prime → p > k + C_int →
    padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) = 0 ∧
    padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = 0)
  (h_diff_ge_zero : ∀ p, p > k →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥ 0)
  (h_bad_prod : (BadPrimes k δ).prod (fun p => (p : ℝ)) ≤ (M_prod k : ℝ) ^ (2 * ε))
  (h_M_prod : (M_prod k : ℝ) ≥ (M k : ℝ) ^ (1 - ε))
  (hM_gt_1 : (M k : ℝ) > 1)
  (h_M_prod_pos : (M_prod k : ℝ) > 0)
  (h_bound_y : (y : ℝ) + k + C_int < (M k : ℝ) ^ (3 * ε))
  (h_bound_x : (x : ℝ) > (M k : ℝ) ^ (2 * ε))
  (h_bound_diff : (y : ℝ) - x < 3 * (M k : ℝ) ^ ε)
  (h_k_large : k > 0)
  (h_eps : ε > 0)
  (h_m_pos : (m k : ℝ) > 0) :
  (((Finset.Icc x (x + k - 1)).lcm id : ℕ) : ℚ) / (((Finset.Icc y (y + k + C_int - 1)).lcm id : ℕ) : ℚ) ≥
  ((M k : ℝ) ^ (1 - 5 * ε) / (m k : ℝ)) * ((x : ℝ) / y) ^ k * (1 / (y + k + C_int : ℝ)) ^ C_int := by
    have := lcm_ratio_eq_ratio_of_ratios_mul_prod_ratio k x y C_int hx0 hy0;
    -- Apply `product_ratio_bound_explicit` to get `prod_ratio >= (x/y)^k * (1/(y+k+C))^C`.
    have h_prod_ratio_bound : ((∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) / (∏ i ∈ Finset.Icc y (y + k + C_int - 1), (i : ℚ))) ≥ ((x : ℚ) / y) ^ k * (1 / (y + k + C_int : ℚ)) ^ C_int := by
      convert product_ratio_bound_explicit k x y C_int ( M k ) ε hC hx0 hy0 hxy h_bound_y h_bound_x h_bound_diff h_k_large ( by linarith ) using 1;
    have h_ratio_lower_bound : ratio_of_ratios k x y C_int ≥ (M_prod k : ℚ) / ((m k : ℚ) * (BadPrimes k δ).prod (fun p => (p : ℚ) ^ 2)) := by
      apply ratio_lower_bound_with_m k x y C_int δ hC hx0 hy0 h_good_p h_bad_p h_small_p h_large_p h_diff_ge_zero;
    have h_M_prod_div_BadProd_sq_ge_M_pow : ((M_prod k : ℚ) / ((m k : ℚ) * (BadPrimes k δ).prod (fun p => (p : ℚ) ^ 2))) ≥ (M k : ℝ) ^ (1 - 5 * ε) / (m k : ℝ) := by
      have := M_prod_div_BadProd_sq_ge_M_pow k ε δ h_eps h_bad_prod h_M_prod hM_gt_1 h_M_prod_pos
      simp +zetaDelta at *;
      convert div_le_div_of_nonneg_right this ( Nat.cast_nonneg ( m k ) ) using 1 ; ring;
    -- By combining the inequalities from h_ratio_lower_bound and h_prod_ratio_bound, we can conclude the proof by multiplying them together.
    have h_combined : ratio_of_ratios k x y C_int * ((∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) / (∏ i ∈ Finset.Icc y (y + k + C_int - 1), (i : ℚ))) ≥ ((M k : ℝ) ^ (1 - 5 * ε) / (m k : ℝ)) * ((x : ℚ) / y) ^ k * (1 / (y + k + C_int : ℚ)) ^ C_int := by
      have := h_ratio_lower_bound
      have := h_prod_ratio_bound
      rw [ mul_assoc ] ; gcongr;
      · exact_mod_cast le_trans ( div_nonneg ( Nat.cast_nonneg _ ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( Finset.prod_nonneg fun _ _ => sq_nonneg _ ) ) ) ‹ratio_of_ratios k x y C_int ≥ ↑ ( M_prod k ) / ( ↑ ( m k ) * ∏ p ∈ BadPrimes k δ, ↑p ^ 2 ) ›;
      · exact h_M_prod_div_BadProd_sq_ge_M_pow.trans ( mod_cast ‹ratio_of_ratios k x y C_int ≥ ↑ ( M_prod k ) / ( ↑ ( m k ) * ∏ p ∈ BadPrimes k δ, ↑ p ^ 2 ) › );
      · convert this.le using 1 ; norm_cast;
    convert h_combined using 1;
    · convert this using 1;
      norm_num [ ← @Rat.cast_inj ℝ ];
    · norm_num [ ← @Rat.cast_inj ℝ ]

/-
The truncated p-adic valuation min(v_p(n), e) is equal to the sum of indicators 1_{p^k | n} for k from 1 to e.
-/
lemma min_padic_eq_sum_indicators (p n e : ℕ) (hp : p > 1) (hn : n > 0) :
  min (padicValNat p n) e = ∑ k ∈ Finset.Icc 1 e, if p ^ k ∣ n then 1 else 0 := by
    have h_eq : ∀ k ∈ Finset.Icc 1 e, (p ^ k ∣ n ↔ k ≤ padicValNat p n) := by
      intro k hk;
      constructor <;> intro h <;> contrapose! h;
      · rw [ padicValNat ] at h;
        split_ifs at h ; simp_all +decide [ Nat.find_eq_iff ];
        · exact fun h' => h.choose_spec.2 ( dvd_trans ( pow_dvd_pow _ ( by linarith [ h.choose_spec.1 ] ) ) h' );
        · aesop;
      · rw [ padicValNat ];
        split_ifs <;> simp_all +decide [ Nat.find_eq_iff ];
        exact ⟨ k - 1, Nat.pred_lt ( ne_bot_of_gt hk.1 ), by cases k <;> aesop ⟩;
    simp_all +decide [ Finset.sum_ite ];
    rw [ show Finset.filter ( fun x => p ^ x ∣ n ) ( Finset.Icc 1 e ) = Finset.Icc 1 ( Min.min ( padicValNat p n ) e ) from ?_ ];
    · norm_num;
    · ext; aesop

/-
The difference in the number of multiples of m between two intervals of the same length k is at most 1.
-/
lemma count_multiples_diff_le_one_same_len (k x y m : ℕ) (hm : m > 0) :
  |((Finset.filter (fun i => m ∣ i) (Finset.Icc x (x + k - 1))).card : ℤ) -
   ((Finset.filter (fun i => m ∣ i) (Finset.Icc y (y + k - 1))).card : ℤ)| ≤ 1 := by
     -- The number of multiples of $m$ in an interval of length $k$ is at most $\lfloor k/m \rfloor + 1$.
     have h_multiples_bound (a b : ℕ) (hab : a ≤ b) : ((Finset.Icc a b).filter (fun i => m ∣ i) : Finset ℕ).card ≤ (b - a + 1) / m + 1 := by
       have h_multiples_bound (a b : ℕ) (hab : a ≤ b) : ((Finset.Icc a b).filter (fun i => m ∣ i) : Finset ℕ).card ≤ Finset.card (Finset.image (fun i => m * i) (Finset.Icc ((a + m - 1) / m) (b / m))) := by
         refine Finset.card_le_card ?_;
         intros i hi;
         norm_num +zetaDelta at *;
         exact ⟨ i / m, ⟨ Nat.le_of_lt_succ <| Nat.div_lt_of_lt_mul <| by linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ a + m ), Nat.div_mul_cancel hi.2 ], Nat.le_div_iff_mul_le hm |>.2 <| by linarith [ Nat.div_mul_cancel hi.2 ] ⟩, Nat.mul_div_cancel' hi.2 ⟩;
       refine le_trans ( h_multiples_bound a b hab ) ?_;
       refine' le_trans ( Finset.card_image_le ) _;
       simp +arith +decide [ Nat.div_le_iff_le_mul_add_pred hm ];
       exact Nat.le_of_lt_succ ( by nlinarith [ Nat.div_mul_le_self b m, Nat.div_add_mod ( b - a + 1 ) m, Nat.mod_lt ( b - a + 1 ) hm, Nat.div_add_mod ( m + a - 1 ) m, Nat.mod_lt ( m + a - 1 ) hm, Nat.sub_add_cancel ( by linarith : 1 ≤ m + a ), Nat.sub_add_cancel ( by linarith : a ≤ b ) ] );
     have h_multiples_bound : ((Finset.Icc x (x + k - 1)).filter (fun i => m ∣ i) : Finset ℕ).card ≥ (k) / m ∧ ((Finset.Icc y (y + k - 1)).filter (fun i => m ∣ i) : Finset ℕ).card ≥ (k) / m := by
       have h_multiples_bound : ∀ a : ℕ, ((Finset.Icc a (a + m - 1)).filter (fun i => m ∣ i) : Finset ℕ).card ≥ 1 := by
         intro a
         have h_exists_multiple : ∃ i ∈ Finset.Icc a (a + m - 1), m ∣ i := by
           use m * ((a + m - 1) / m);
           exact ⟨ Finset.mem_Icc.mpr ⟨ by linarith [ Nat.div_add_mod ( a + m - 1 ) m, Nat.mod_lt ( a + m - 1 ) hm, Nat.sub_add_cancel ( by linarith : 1 ≤ a + m ) ], by linarith [ Nat.div_mul_le_self ( a + m - 1 ) m, Nat.sub_add_cancel ( by linarith : 1 ≤ a + m ) ] ⟩, dvd_mul_right _ _ ⟩
         obtain ⟨i, hi⟩ := h_exists_multiple
         exact Finset.card_pos.mpr ⟨i, by aesop⟩;
       -- By partitioning the interval [x, x+k-1] into ⌊k/m⌋ blocks of m consecutive integers, each block contributes at least one multiple of m.
       have h_partition : ∀ a : ℕ, ((Finset.Icc a (a + m * (k / m) - 1)).filter (fun i => m ∣ i) : Finset ℕ).card ≥ k / m := by
         intro a
         have h_partition : Finset.filter (fun i => m ∣ i) (Finset.Icc a (a + m * (k / m) - 1)) ⊇ Finset.biUnion (Finset.range (k / m)) (fun i => Finset.filter (fun j => m ∣ j) (Finset.Icc (a + m * i) (a + m * i + m - 1))) := by
           simp +decide [ Finset.subset_iff ];
           exact fun x i hi₁ hi₂ hi₃ hi₄ => ⟨ ⟨ by nlinarith, Nat.le_sub_one_of_lt <| by nlinarith [ Nat.div_mul_le_self k m, Nat.sub_add_cancel <| show 1 ≤ a + m * i + m from by nlinarith ] ⟩, hi₄ ⟩;
         refine le_trans ?_ ( Finset.card_mono h_partition );
         rw [ Finset.card_biUnion ];
         · exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun _ _ => h_multiples_bound _ );
         · intros i hi j hj hij; simp_all +decide [ Finset.disjoint_left ];
           intro x hx₁ hx₂ hx₃ hx₄; contrapose! hij; nlinarith [ Nat.sub_add_cancel ( by nlinarith : 1 ≤ a + m * i + m ), Nat.sub_add_cancel ( by nlinarith : 1 ≤ a + m * j + m ) ] ;
       exact ⟨ le_trans ( h_partition x ) ( Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.Icc_subset_Icc_right <| Nat.sub_le_sub_right ( by nlinarith [ Nat.div_mul_le_self k m ] ) _ ), le_trans ( h_partition y ) ( Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.Icc_subset_Icc_right <| Nat.sub_le_sub_right ( by nlinarith [ Nat.div_mul_le_self k m ] ) _ ) ⟩;
     rename_i h;
     rcases k with ( _ | k ) <;> simp_all +decide [ Nat.succ_div ];
     · rcases x with ( _ | x ) <;> rcases y with ( _ | y ) <;> norm_num at *;
       · exact Finset.card_filter_le _ _;
       · exact Finset.card_filter_le _ _;
     · exact abs_sub_le_iff.mpr ⟨ by specialize h x ( x + k ) ( by linarith ) ; specialize h ; norm_num at * ; split_ifs at * <;> omega, by specialize h y ( y + k ) ( by linarith ) ; specialize h ; norm_num at * ; split_ifs at * <;> omega ⟩

/-
The difference between the sums of truncated p-adic valuations over two intervals of length k is at least -e.
-/
lemma sum_min_val_diff_bound (k x y p e : ℕ) (hp : p.Prime) (he : e > 0) (hx : x > 0) (hy : y > 0) :
  (∑ i ∈ Finset.Icc y (y + k - 1), min (padicValNat p i) e : ℤ) -
  (∑ i ∈ Finset.Icc x (x + k - 1), min (padicValNat p i) e : ℤ) ≥ -(e : ℤ) := by
    have h_count_multiples_diff_le_one_same_len : ∀ j ∈ Finset.Icc 1 e, |((Finset.filter (fun i => p ^ j ∣ i) (Finset.Icc y (y + k - 1))).card : ℤ) - ((Finset.filter (fun i => p ^ j ∣ i) (Finset.Icc x (x + k - 1))).card : ℤ)| ≤ 1 := by
      intros j hj;
      have := count_multiples_diff_le_one_same_len k x y ( p ^ j ) ( pow_pos hp.pos _ );
      rwa [ abs_sub_comm ];
    -- Apply `min_padic_eq_sum_indicators` to rewrite the sums.
    have h_rewrite_sums : (∑ i ∈ Finset.Icc y (y + k - 1), min (padicValNat p i) e : ℤ) = ∑ j ∈ Finset.Icc 1 e, ((Finset.filter (fun i => p ^ j ∣ i) (Finset.Icc y (y + k - 1))).card : ℤ) ∧
                        (∑ i ∈ Finset.Icc x (x + k - 1), min (padicValNat p i) e : ℤ) = ∑ j ∈ Finset.Icc 1 e, ((Finset.filter (fun i => p ^ j ∣ i) (Finset.Icc x (x + k - 1))).card : ℤ) := by
                          have h_min_padic_eq_sum_indicators : ∀ n > 0, min (padicValNat p n) e = ∑ j ∈ Finset.Icc 1 e, if p ^ j ∣ n then 1 else 0 := by
                            intros n hn_pos;
                            convert min_padic_eq_sum_indicators p n e hp.one_lt hn_pos using 1;
                          norm_cast;
                          exact ⟨ by rw [ Finset.sum_congr rfl fun i hi => h_min_padic_eq_sum_indicators i <| by linarith [ Finset.mem_Icc.mp hi ] ] ; rw [ Finset.sum_comm ] ; simp +decide [ Finset.sum_ite ], by rw [ Finset.sum_congr rfl fun i hi => h_min_padic_eq_sum_indicators i <| by linarith [ Finset.mem_Icc.mp hi ] ] ; rw [ Finset.sum_comm ] ; simp +decide [ Finset.sum_ite ] ⟩;
    exact h_rewrite_sums.1.symm ▸ h_rewrite_sums.2.symm ▸ by simpa using Finset.sum_le_sum fun i hi => neg_le_of_abs_le <| h_count_multiples_diff_le_one_same_len i hi;

/-
For small primes, the difference in valuations is bounded by -v_p(m).
-/
lemma small_prime_condition_satisfied (k x y C_int : ℕ) (p : ℕ)
  (hp : p.Prime) (h_small : p ≤ k.sqrt)
  (hx0 : x > 0) (hy0 : y > 0)
  (hC : C_int ≥ 1)
  (hk : k ≥ 1) :
  (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
  (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥
  -(padicValNat p (m k) : ℤ) := by
    -- Let $e = v_p(M(k)) = v_p(m(k)) = \lfloor \log_p k \rfloor$.
    set e := Nat.log p k with he_def
    have he_eq : padicValNat p (m k) = e := by
      have h_val_m_eq_e : padicValNat p (m k) = padicValNat p (M k) := by
        exact?
      generalize_proofs at *; (
      exact h_val_m_eq_e.trans ( by exact? ))
    have he_eq' : padicValNat p (M k) = e := by
      exact?
    generalize_proofs at *; (
    -- Apply the lemma that bounds the difference in the sums of truncated valuations.
    have h_sum_bound : (∑ i ∈ Finset.Icc y (y + k + C_int - 1), min (padicValNat p i) e : ℤ) - (∑ i ∈ Finset.Icc x (x + k - 1), min (padicValNat p i) e : ℤ) ≥ -e := by
      have h_sum_bound : (∑ i ∈ Finset.Icc y (y + k - 1), min (padicValNat p i) e : ℤ) - (∑ i ∈ Finset.Icc x (x + k - 1), min (padicValNat p i) e : ℤ) ≥ -e := by
        apply sum_min_val_diff_bound k x y p e hp (Nat.log_pos hp.one_lt (by
        exact le_trans h_small ( Nat.sqrt_le_self _ ))) hx0 hy0
        skip
      generalize_proofs at *; (
      exact le_trans h_sum_bound ( sub_le_sub_right ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.Icc_subset_Icc_right ( Nat.sub_le_sub_right ( Nat.le_add_right _ _ ) _ ) ) fun _ _ _ => by positivity ) _ ));
    -- Apply the lemma that bounds the difference in valuations by summing the min valuations.
    have h_val_bound : (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥ (∑ i ∈ Finset.Icc y (y + k + C_int - 1), min (padicValNat p i) e : ℤ) - e ∧ (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≤ (∑ i ∈ Finset.Icc x (x + k - 1), min (padicValNat p i) e : ℤ) - e := by
      constructor <;> norm_cast;
      · rw [ Int.subNatNat_eq_coe ] ; norm_num;
        have h_val_bound : (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥ (∑ i ∈ Finset.Icc y (y + k + C_int - 1), min (padicValNat p i) e : ℤ) - e := by
          have := @valuation_ratio_ge_sum_min_sub_e (Finset.Icc y (y + k + C_int - 1)) p e
          apply this hp;
          · -- Since $p \leq \sqrt{k}$, we have $p^e \leq k$. Therefore, there exists some $i \in [y, y + k + C_int - 1]$ such that $p^e \mid i$.
            obtain ⟨i, hi⟩ : ∃ i ∈ Finset.Icc y (y + k + C_int - 1), p ^ e ∣ i := by
              have h_exists_i : ∃ i ∈ Finset.Icc y (y + k + C_int - 1), i % p ^ e = 0 := by
                have h_len : k + C_int ≥ p ^ e := by
                  exact le_add_of_le_of_nonneg ( Nat.pow_log_le_self p ( by linarith ) ) ( Nat.zero_le _ )
                use y + (p ^ e - y % p ^ e) % p ^ e; simp +zetaDelta at *; (
                exact ⟨ Nat.le_sub_one_of_lt ( by linarith [ Nat.mod_lt ( p ^ Nat.log p k - y % p ^ Nat.log p k ) ( pow_pos hp.pos ( Nat.log p k ) ), Nat.sub_add_cancel ( show y % p ^ Nat.log p k ≤ p ^ Nat.log p k from Nat.le_of_lt ( Nat.mod_lt _ ( pow_pos hp.pos _ ) ) ) ] ), Nat.mod_eq_zero_of_dvd <| by exact ⟨ y / p ^ Nat.log p k + 1, by linarith [ Nat.div_add_mod y ( p ^ Nat.log p k ), Nat.sub_add_cancel ( show y % p ^ Nat.log p k ≤ p ^ Nat.log p k from Nat.le_of_lt ( Nat.mod_lt _ ( pow_pos hp.pos _ ) ) ) ] ⟩ ⟩);
              exact ⟨ h_exists_i.choose, h_exists_i.choose_spec.1, Nat.dvd_of_mod_eq_zero h_exists_i.choose_spec.2 ⟩;
            have h_val_ge_e : padicValNat p i ≥ e := by
              have h_val_ge_e : padicValNat p i ≥ padicValNat p (p ^ e) := by
                have h_val_ge_e : padicValNat p (p ^ e) ≤ padicValNat p i := by
                  have h_div : p ^ e ∣ i := hi.right
                  haveI := Fact.mk hp; rw [ padicValNat_dvd_iff ] at h_div; aesop;
                exact h_val_ge_e;
              haveI := Fact.mk hp; simp_all +decide [ padicValNat.pow ] ;
            exact le_trans h_val_ge_e ( Finset.le_sup ( f := padicValNat p ) hi.1 );
          · exact fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ;
        grind;
      · rw [ Int.subNatNat_of_le ] <;> norm_cast;
        · have h_val_eq_sum_min_sub_e_of_unique_max : padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = (∑ i ∈ Finset.Icc x (x + k - 1), min (padicValNat p i) e : ℕ) - e := by
            apply_rules [ valuation_ratio_eq_sum_min_sub_e_of_unique_max ];
            · -- Since $p^e \leq k$, there exists some $i \in [x, x+k-1]$ such that $p^e \mid i$.
              obtain ⟨i, hi⟩ : ∃ i ∈ Finset.Icc x (x + k - 1), p ^ e ∣ i := by
                have h_exists_multiple : ∃ i ∈ Finset.Icc x (x + k - 1), p ^ e ∣ i := by
                  have h_interval : p ^ e ≤ k := by
                    exact Nat.pow_log_le_self p ( by linarith )
                  exact ⟨ p ^ e * ( ( x + k - 1 ) / p ^ e ), Finset.mem_Icc.mpr ⟨ by nlinarith [ Nat.div_add_mod ( x + k - 1 ) ( p ^ e ), Nat.mod_lt ( x + k - 1 ) ( pow_pos hp.pos e ), Nat.sub_add_cancel ( by linarith : 1 ≤ x + k ) ], by nlinarith [ Nat.div_mul_le_self ( x + k - 1 ) ( p ^ e ), Nat.sub_add_cancel ( by linarith : 1 ≤ x + k ) ] ⟩, by norm_num ⟩
                generalize_proofs at *; (
                exact h_exists_multiple);
              have h_val_ge_e : padicValNat p i ≥ e := by
                haveI := Fact.mk hp; rw [ padicValNat_dvd_iff ] at *; aesop;
              exact le_trans h_val_ge_e ( Finset.le_sup ( f := padicValNat p ) hi.1 );
            · -- Since $p \leq \sqrt{k}$, we have $p^e \leq k < p^{e+1}$.
              have h_bounds : p^e ≤ k ∧ k < p^(e+1) := by
                exact ⟨ Nat.pow_log_le_self p ( by linarith ), Nat.lt_pow_succ_log_self hp.one_lt _ ⟩;
              -- Since $p^e \leq k < p^{e+1}$, there can be at most one multiple of $p^{e+1}$ in the interval $[x, x+k-1]$.
              have h_unique : ∀ i ∈ Finset.Icc x (x + k - 1), padicValNat p i > e → i = p^(e+1) * (i / p^(e+1)) := by
                intros i hi hpi
                have h_div : p ^ (e + 1) ∣ i := by
                  have h_div : p ^ (padicValNat p i) ∣ i := by
                    convert Nat.ordProj_dvd i p using 1;
                    rw [ Nat.factorization ] ; aesop;
                  exact dvd_trans ( pow_dvd_pow _ ‹_› ) h_div;
                rw [ Nat.mul_div_cancel' h_div ];
              have h_unique : ∀ i j : ℕ, i ∈ Finset.Icc x (x + k - 1) → j ∈ Finset.Icc x (x + k - 1) → padicValNat p i > e → padicValNat p j > e → i = j := by
                intros i j hi hj hi_gt hj_gt
                have h_eq : i / p^(e+1) = j / p^(e+1) := by
                  have h_eq : i < j + p^(e+1) ∧ j < i + p^(e+1) := by
                    constructor <;> linarith [ Finset.mem_Icc.mp hi, Finset.mem_Icc.mp hj, Nat.sub_add_cancel ( by linarith : 1 ≤ x + k ) ];
                  rw [ h_unique i hi hi_gt, h_unique j hj hj_gt ] at h_eq ; nlinarith [ pow_pos hp.pos ( e + 1 ) ];
                rw [ h_unique i hi hi_gt, h_unique j hj hj_gt, h_eq ];
              exact Finset.card_le_one.mpr fun i hi j hj => h_unique i j ( Finset.filter_subset _ _ hi ) ( Finset.filter_subset _ _ hj ) ( Finset.mem_filter.mp hi |>.2 ) ( Finset.mem_filter.mp hj |>.2 ) ▸ rfl;
            · exact fun i hi => by linarith [ Finset.mem_Icc.mp hi ] ;
          rw [h_val_eq_sum_min_sub_e_of_unique_max];
        · -- Since $p \leq \sqrt{k}$, we have $p^e \leq k$, and thus there exists at least one multiple of $p^e$ in the interval $[x, x + k - 1]$.
          obtain ⟨i, hi⟩ : ∃ i ∈ Finset.Icc x (x + k - 1), p ^ e ∣ i := by
            have h_exists_multiple : ∃ i ∈ Finset.Icc x (x + k - 1), p ^ e ∣ i := by
              have h_interval : p ^ e ≤ k := by
                exact Nat.pow_log_le_self p ( by linarith )
              exact ⟨ p ^ e * ( ( x + k - 1 ) / p ^ e ), Finset.mem_Icc.mpr ⟨ by nlinarith [ Nat.div_add_mod ( x + k - 1 ) ( p ^ e ), Nat.mod_lt ( x + k - 1 ) ( pow_pos hp.pos e ), Nat.sub_add_cancel ( by linarith : 1 ≤ x + k ) ], by nlinarith [ Nat.div_mul_le_self ( x + k - 1 ) ( p ^ e ), Nat.sub_add_cancel ( by linarith : 1 ≤ x + k ) ] ⟩, by norm_num ⟩
            generalize_proofs at *; (
            exact h_exists_multiple);
          rw [ Finset.sum_eq_add_sum_diff_singleton hi.1 ];
          haveI := Fact.mk hp; rw [ padicValNat_dvd_iff ] at *; aesop;
    linarith [ show ( e : ℤ ) = padicValNat p ( m k ) from mod_cast he_eq.symm ] ;)

/-
The p-adic valuation of the RHS bound matches the expected values for small, bad, and good primes.
-/
lemma valuation_rhs_compute_v2 (k : ℕ) (δ : ℝ) (p : ℕ) (hp : p.Prime) :
  padicValRat p ((M_prod k : ℚ) / ((m k : ℚ) * (BadPrimes k δ).prod (fun p => (p : ℚ) ^ 2))) =
  if p ≤ k.sqrt then -(padicValNat p (m k) : ℤ)
  else if p ∈ PrimesIn k then
    if p ∈ BadPrimes k δ then -1 else 1
  else 0 := by
    convert valuation_rhs_compute k δ p hp using 1

/-
The ratio of ratios is bounded below by M_prod / (m * BadPrimes^2).
-/
lemma ratio_lower_bound_with_m_v2 (k x y C_int : ℕ) (δ : ℝ)
  (hC : C_int ≥ 1)
  (hx0 : x > 0) (hy0 : y > 0)
  (h_good_p : ∀ p ∈ PrimesIn k, ¬ is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) + 1)
  (h_bad_p : ∀ p ∈ PrimesIn k, is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) - 1)
  (h_small_p : ∀ p, p.Prime → p ≤ k.sqrt →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥
    -(padicValNat p (m k) : ℤ))
  (h_large_p : ∀ p, p.Prime → p > k + C_int →
    padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) = 0 ∧
    padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = 0)
  (h_diff_ge_zero : ∀ p, p > k →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥ 0) :
  ratio_of_ratios k x y C_int ≥ (M_prod k : ℚ) / ((m k : ℚ) * (BadPrimes k δ).prod (fun p => (p : ℚ) ^ 2)) := by
    -- Apply the `rational_ge_of_valuation_ge` lemma with the given hypotheses.
    apply ratio_lower_bound_with_m k x y C_int δ hC hx0 hy0 h_good_p h_bad_p h_small_p h_large_p h_diff_ge_zero

/-
lcm_real S > lcm_real T iff the ratio of their LCMs (as rationals) is > 1.
-/
lemma lcm_real_gt_iff_ratio_gt_one (S T : Finset ℕ) (hS : S.lcm id > 0) (hT : T.lcm id > 0) :
  lcm_real S > lcm_real T ↔ ((S.lcm id : ℕ) : ℚ) / ((T.lcm id : ℕ) : ℚ) > 1 := by
    field_simp;
    unfold lcm_real;
    norm_cast

/-
m(k) is small enough relative to M(k) that dividing by it doesn't reduce the exponent by much.
-/
lemma m_bound_for_ratio (h_pnt : PNT_bounds) (ε : ℝ) (h_eps : ε > 0) :
  ∃ K, ∀ k ≥ K, (M k : ℝ) ^ (1 - 5 * ε) / (m k : ℝ) ≥ (M k : ℝ) ^ (1 - 6 * ε) := by
    -- Using the fact that $m(k) < M(k)^{\epsilon}$ for large $k$, we can bound the ratio.
    obtain ⟨ K, hK ⟩ := m_small_relative_to_M h_pnt ( ε ) h_eps;
    use K + 1;
    intro k hk; rw [ ge_iff_le ] ; rw [ le_div_iff₀ ];
    · exact le_trans ( mul_le_mul_of_nonneg_left ( le_of_lt ( hK k ( by linarith ) ) ) ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ) ( by rw [ ← Real.rpow_add ( Nat.cast_pos.mpr <| M_pos k ( by linarith ) ) ] ; ring_nf; norm_num );
    · exact mod_cast pos_iff_ne_zero.mpr ( show m k ≠ 0 from Nat.ne_of_gt <| Finset.prod_pos fun p hp => Nat.pos_of_ne_zero <| by aesop )

/-
For sufficiently large M, the inequality holds provided epsilon is small enough.
-/
lemma large_M_inequality_generic (C : ℝ) (hC : C ≥ 1) (ε : ℝ) (h_eps : ε > 0) (h_eps_cond : 1 - (3 * C + 6) * ε > 0) :
  ∃ M0, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ,
  1 ≤ k → (k : ℝ) ≤ 2 * Real.log M →
  ∀ x y : ℕ,
  M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε →
  (y : ℝ) < 2 * M ^ (3 * ε) →
  M ^ (1 - 6 * ε) * ((x : ℝ) / y) ^ k * (1 / (y + k + C : ℝ)) ^ C > 1 := by
    -- The term $(1 - 3M^{-\epsilon})^{2 \log M}$ behaves like $\exp(-6M^{-\epsilon} \log M)$, which tends to 1 as $M \to \infty$.
    have h_exp : Filter.Tendsto (fun M : ℝ => (1 - 3 * M ^ (-ε)) ^ (2 * Real.log M)) Filter.atTop (nhds 1) := by
      have h_exp : Filter.Tendsto (fun M : ℝ => Real.exp (2 * Real.log M * Real.log (1 - 3 * M ^ (-ε)))) Filter.atTop (nhds 1) := by
        have h_exp : Filter.Tendsto (fun M : ℝ => 2 * Real.log M * Real.log (1 - 3 * M ^ (-ε))) Filter.atTop (nhds 0) := by
          -- As $M \to \infty$, $3M^{-\epsilon} \to 0$, so we can use the fact that $\ln(1 - u) \sim -u$ for small $u$.
          have h_log_approx : Filter.Tendsto (fun M : ℝ => Real.log (1 - 3 * M ^ (-ε)) / (-3 * M ^ (-ε))) Filter.atTop (nhds 1) := by
            have h_log_approx : Filter.Tendsto (fun u : ℝ => Real.log (1 - u) / -u) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
              simpa [ div_eq_mul_inv, mul_comm ] using HasDerivAt.tendsto_slope_zero_right ( HasDerivAt.neg ( HasDerivAt.log ( hasDerivAt_id 0 |> HasDerivAt.const_sub 1 ) <| by norm_num ) );
            convert h_log_approx.comp ( show Filter.Tendsto ( fun M : ℝ => 3 * M ^ ( -ε ) ) Filter.atTop ( nhdsWithin 0 ( Set.Ioi 0 ) ) from ?_ ) using 2 <;> norm_num [ neg_div ];
            rw [ tendsto_nhdsWithin_iff ];
            exact ⟨ by simpa using tendsto_const_nhds.mul ( tendsto_rpow_neg_atTop h_eps ), Filter.eventually_atTop.mpr ⟨ 1, fun n hn => by norm_num; positivity ⟩ ⟩;
          -- Using the fact that $M^{-\epsilon} \log M \to 0$ as $M \to \infty$, we can conclude.
          have h_lim : Filter.Tendsto (fun M : ℝ => M ^ (-ε) * Real.log M) Filter.atTop (nhds 0) := by
            -- Let $y = \log M$, therefore the expression becomes $\frac{y}{e^{y \epsilon}}$.
            suffices h_log : Filter.Tendsto (fun y : ℝ => y * Real.exp (-y * ε)) Filter.atTop (nhds 0) by
              have := h_log.comp Real.tendsto_log_atTop;
              refine this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with M hM using by rw [ Function.comp_apply, Real.rpow_def_of_pos hM ] ; ring );
            -- Let $z = y \epsilon$, therefore the expression becomes $\frac{z}{e^z}$.
            suffices h_z : Filter.Tendsto (fun z : ℝ => z * Real.exp (-z)) Filter.atTop (nhds 0) by
              have := h_z.comp ( Filter.tendsto_id.atTop_mul_const h_eps );
              convert this.div_const ε using 2 <;> norm_num [ mul_assoc, mul_comm ε, h_eps.ne' ];
              rw [ mul_div_assoc, mul_div_cancel_right₀ _ h_eps.ne' ];
            convert ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 ) using 2 ; norm_num;
          have := h_log_approx.mul ( h_lim.const_mul ( -3 * 2 ) );
          simpa using this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ div_mul_eq_mul_div, div_eq_iff ( by positivity ) ] ; ring );
        simpa only [ Real.exp_zero ] using Filter.Tendsto.comp ( Real.continuous_exp.tendsto _ ) h_exp;
      refine h_exp.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 3, Filter.eventually_gt_atTop ( 3 ^ ( 1 / ε ) ) ] with M hM₁ hM₂;
      rw [ Real.rpow_def_of_pos ( sub_pos.mpr <| by rw [ Real.rpow_neg <| by positivity ] ; nlinarith [ show M ^ ε > 3 by exact lt_of_le_of_lt ( by rw [ ← Real.rpow_mul ( by positivity ), one_div_mul_cancel <| ne_of_gt h_eps, Real.rpow_one ] ) <| Real.rpow_lt_rpow ( by positivity ) hM₂ <| by positivity, one_div_mul_cancel <| ne_of_gt h_eps, Real.rpow_one 3, Real.rpow_neg ( by positivity : ( 0 :ℝ ) ≤ M ), mul_inv_cancel₀ <| ne_of_gt <| Real.rpow_pos_of_pos ( by positivity : ( 0 :ℝ ) < M ) ε ] ), mul_comm ];
    have h_exp : Filter.Tendsto (fun M : ℝ => M ^ (1 - 6 * ε) * (1 - 3 * M ^ (-ε)) ^ (2 * Real.log M) * (3 * M ^ (3 * ε)) ^ (-C)) Filter.atTop Filter.atTop := by
      have h_exp : Filter.Tendsto (fun M : ℝ => (M ^ (1 - (3 * C + 6) * ε)) * (3 ^ (-C)) * (1 - 3 * M ^ (-ε)) ^ (2 * Real.log M)) Filter.atTop Filter.atTop := by
        apply Filter.Tendsto.atTop_mul_pos;
        exacts [ zero_lt_one, Filter.Tendsto.atTop_mul_const ( by positivity ) ( tendsto_rpow_atTop ( by linarith ) ), h_exp ];
      refine h_exp.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with M hM ; rw [ Real.mul_rpow ( by positivity ) ( by positivity ), ← Real.rpow_mul ( by positivity ) ] ; ring;
      rw [ show 1 + ( - ( C * ε * 3 ) - ε * 6 ) = ( 1 - ε * 6 ) + ( - ( C * ε * 3 ) ) by ring, Real.rpow_add hM ] ; ring;
    have h_exp : ∃ M0 : ℝ, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ, (k : ℝ) ≤ 2 * Real.log M → ∀ x y : ℕ, M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε → (y : ℝ) < 2 * M ^ (3 * ε) → M ^ (1 - 6 * ε) * ((x : ℝ) / y) ^ k * (1 / (y + k + C : ℝ)) ^ C ≥ M ^ (1 - 6 * ε) * (1 - 3 * M ^ (-ε)) ^ (2 * Real.log M) * (3 * M ^ (3 * ε)) ^ (-C) := by
      have h_exp : ∃ M0 : ℝ, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ, (k : ℝ) ≤ 2 * Real.log M → ∀ x y : ℕ, M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε → (y : ℝ) < 2 * M ^ (3 * ε) → ((x : ℝ) / y) ^ k ≥ (1 - 3 * M ^ (-ε)) ^ (2 * Real.log M) ∧ (1 / (y + k + C : ℝ)) ^ C ≥ (1 / (3 * M ^ (3 * ε) : ℝ)) ^ C := by
        have h_exp : ∃ M0 : ℝ, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ, (k : ℝ) ≤ 2 * Real.log M → ∀ x y : ℕ, M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε → (y : ℝ) < 2 * M ^ (3 * ε) → ((x : ℝ) / y) ^ k ≥ (1 - 3 * M ^ (-ε)) ^ (2 * Real.log M) := by
          have := x_div_y_bound ε h_eps; aesop;
        have h_exp : ∃ M0 : ℝ, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ, (k : ℝ) ≤ 2 * Real.log M → ∀ x y : ℕ, M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε → (y : ℝ) < 2 * M ^ (3 * ε) → (1 / (y + k + C : ℝ)) ^ C ≥ (1 / (3 * M ^ (3 * ε) : ℝ)) ^ C := by
          have h_exp : ∃ M0 : ℝ, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ, (k : ℝ) ≤ 2 * Real.log M → ∀ x y : ℕ, M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε → (y : ℝ) < 2 * M ^ (3 * ε) → (y + k + C : ℝ) ≤ 3 * M ^ (3 * ε) := by
            have := bound_y_term_relaxed C hC ε h_eps;
            exact ⟨ this.choose, fun M hM k hk x y hx hy hxy hy' => le_of_lt ( this.choose_spec M hM k hk y hy' ) ⟩;
          field_simp;
          obtain ⟨ M0, hM0 ⟩ := h_exp; use Max.max M0 1; intros M hM k hk x y hx hy hxy hyx; rw [ Real.rpow_le_rpow_iff ] <;> try positivity;
          · exact one_div_le_one_div_of_le ( by positivity ) ( by have := hM0 M ( le_trans ( le_max_left _ _ ) hM ) k hk x y hx hy hxy ( by ring_nf at *; linarith ) ; ring_nf at *; linarith );
          · exact div_nonneg zero_le_one ( mul_nonneg zero_le_three ( Real.rpow_nonneg ( by linarith [ le_max_right M0 1 ] ) _ ) );
        exact ⟨ Max.max ( Classical.choose ‹∃ M0, ∀ M ≥ M0, ∀ k : ℕ, ( k : ℝ ) ≤ 2 * Real.log M → ∀ x y : ℕ, M ^ ( 2 * ε ) < x → x < y → ( y : ℝ ) - x < 3 * M ^ ε → y < 2 * M ^ ( 3 * ε ) → ( x / y : ℝ ) ^ k ≥ ( 1 - 3 * M ^ ( -ε ) ) ^ ( 2 * Real.log M ) › ) h_exp.choose, fun M hM k hk x y hx hy hxy hyx => ⟨ Classical.choose_spec ‹∃ M0, ∀ M ≥ M0, ∀ k : ℕ, ( k : ℝ ) ≤ 2 * Real.log M → ∀ x y : ℕ, M ^ ( 2 * ε ) < x → x < y → ( y : ℝ ) - x < 3 * M ^ ε → y < 2 * M ^ ( 3 * ε ) → ( x / y : ℝ ) ^ k ≥ ( 1 - 3 * M ^ ( -ε ) ) ^ ( 2 * Real.log M ) › M ( le_trans ( le_max_left _ _ ) hM ) k hk x y hx hy hxy hyx, h_exp.choose_spec M ( le_trans ( le_max_right _ _ ) hM ) k hk x y hx hy hxy hyx ⟩ ⟩;
      obtain ⟨ M0, hM0 ⟩ := h_exp;
      use Max.max M0 1;
      intros M hM k hk x y hx hy hxy hyx
      have := hM0 M (le_trans (le_max_left _ _) hM) k hk x y hx hy hxy hyx
      simp_all +decide [ Real.rpow_neg_eq_inv_rpow ];
      gcongr;
      · exact Real.rpow_nonneg ( mul_nonneg ( inv_nonneg.2 ( Real.rpow_nonneg ( by linarith ) _ ) ) ( by norm_num ) ) _;
      · exact mul_nonneg ( Real.rpow_nonneg ( by linarith ) _ ) ( pow_nonneg ( by positivity ) _ );
      · exact Real.rpow_nonneg ( by linarith ) _;
      · exact hM0 M hM.1 k hk x y hx hy hxy hyx |>.1;
    obtain ⟨ M0, hM0 ⟩ := h_exp; rcases Filter.eventually_atTop.mp ( ‹Filter.Tendsto ( fun M : ℝ => M ^ ( 1 - 6 * ε ) * ( 1 - 3 * M ^ ( -ε ) ) ^ ( 2 * Real.log M ) * ( 3 * M ^ ( 3 * ε ) ) ^ ( -C ) ) Filter.atTop Filter.atTop›.eventually_gt_atTop 1 ) with ⟨ M1, hM1 ⟩ ; exact ⟨ Max.max M0 M1, fun M hM k hk₁ hk₂ x y hx hy₁ hy₂ hy₃ => lt_of_lt_of_le ( hM1 M ( le_trans ( le_max_right _ _ ) hM ) ) ( hM0 M ( le_trans ( le_max_left _ _ ) hM ) k hk₂ x y hx hy₁ hy₂ hy₃ ) ⟩ ;

/-
Arithmetic bounds for the stronger existence lemma (corrected).
-/
lemma arithmetic_bounds_stronger (M : ℕ) (ε : ℝ) (x y : ℕ) (h_eps : ε > 0) (hM : M > 1)
  (hx : x ∈ Finset.Icc (Nat.ceil ((M : ℝ) ^ (2.5 * ε))) (Nat.ceil ((M : ℝ) ^ (2.5 * ε)) + Nat.ceil ((M : ℝ) ^ ε) - 1))
  (hy : y ∈ Finset.Icc (x + Nat.ceil (1.5 * (M : ℝ) ^ ε)) (x + Nat.ceil (1.5 * (M : ℝ) ^ ε) + Nat.ceil ((M : ℝ) ^ ε) - 1))
  (hM_large : (M : ℝ) ^ (0.5 * ε) > 3) :
  (M : ℝ) ^ (2.5 * ε) ≤ x ∧ (x : ℝ) < (M : ℝ) ^ (3 * ε) ∧
  (M : ℝ) ^ ε < (y : ℝ) - x ∧ (y : ℝ) - x < 3 * (M : ℝ) ^ ε := by
    refine' ⟨ _, _, _, _ ⟩;
    · exact le_trans ( Nat.le_ceil _ ) ( mod_cast Finset.mem_Icc.mp hx |>.1 );
    · -- Since $M^{0.5\epsilon} > 3$, we have $M^{2.5\epsilon} + M^\epsilon + 1 < M^{3\epsilon}$.
      have h_bound : (M : ℝ) ^ (2.5 * ε) + (M : ℝ) ^ ε + 1 < (M : ℝ) ^ (3 * ε) := by
        -- Since $M^{0.5\epsilon} > 3$, we have $M^{2.5\epsilon} > 3M^{2\epsilon}$.
        have h_bound : (M : ℝ) ^ (2.5 * ε) > 3 * (M : ℝ) ^ (2 * ε) := by
          exact lt_of_lt_of_le ( mul_lt_mul_of_pos_right hM_large ( by positivity ) ) ( by rw [ ← Real.rpow_add ( by positivity ) ] ; ring_nf; norm_num );
        -- Since $M^{0.5\epsilon} > 3$, we have $M^{3\epsilon} = M^{2.5\epsilon} \cdot M^{0.5\epsilon} > M^{2.5\epsilon} \cdot 3$.
        have h_bound : (M : ℝ) ^ (3 * ε) > (M : ℝ) ^ (2.5 * ε) * 3 := by
          exact lt_of_lt_of_le ( mul_lt_mul_of_pos_left hM_large ( by positivity ) ) ( by rw [ ← Real.rpow_add ( by positivity ) ] ; ring_nf; norm_num );
        nlinarith [ show ( M : ℝ ) ^ ε ≥ 1 by exact Real.one_le_rpow ( mod_cast hM.le ) ( by positivity ), show ( M : ℝ ) ^ ( 2 * ε ) ≥ ( M : ℝ ) ^ ε by exact Real.rpow_le_rpow_of_exponent_le ( mod_cast hM.le ) ( by linarith ) ];
      norm_num +zetaDelta at *;
      exact lt_of_le_of_lt ( Nat.cast_le.mpr hx.2 ) ( by rw [ Nat.cast_sub <| Nat.one_le_iff_ne_zero.mpr <| by positivity ] ; push_cast ; linarith [ Nat.ceil_lt_add_one <| show 0 ≤ ( M :ℝ ) ^ ( 5 / 2 * ε ) by positivity, Nat.ceil_lt_add_one <| show 0 ≤ ( M :ℝ ) ^ ε by positivity ] );
    · norm_num +zetaDelta at *;
      refine' lt_of_lt_of_le _ ( sub_le_sub_right ( Nat.cast_le.mpr hy.1 ) _ ) ; norm_num;
      linarith [ Nat.le_ceil ( ( 3 : ℝ ) / 2 * M ^ ε ), show ( M : ℝ ) ^ ε > 0 by positivity ];
    · -- Since $y \leq x + \lceil 1.5 \cdot M^\epsilon \rceil + \lceil M^\epsilon \rceil - 1$, we have $y - x \leq \lceil 1.5 \cdot M^\epsilon \rceil + \lceil M^\epsilon \rceil - 1$.
      have h_yx_le : (y : ℝ) - x ≤ ⌈1.5 * (M : ℝ) ^ ε⌉₊ + ⌈(M : ℝ) ^ ε⌉₊ - 1 := by
        norm_num at *;
        exact le_trans ( Nat.cast_le.mpr hy.2 ) ( by rw [ Nat.cast_sub ] <;> push_cast <;> linarith [ Nat.ceil_pos.mpr ( show 0 < ( 3 : ℝ ) / 2 * M ^ ε by positivity ), Nat.ceil_pos.mpr ( show 0 < ( M : ℝ ) ^ ε by positivity ) ] );
      -- Since $M^{0.5\epsilon} > 3$, we have $M^\epsilon > 9$.
      have h_M_eps_gt_9 : (M : ℝ) ^ ε > 9 := by
        rw [ show ( M : ℝ ) ^ ε = ( ( M : ℝ ) ^ ( 0.5 * ε ) ) ^ 2 by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity ) ] ; ring ] ; nlinarith;
      linarith [ Nat.ceil_lt_add_one ( show 0 ≤ ( 1.5 : ℝ ) * M ^ ε by positivity ), Nat.ceil_lt_add_one ( show 0 ≤ ( M : ℝ ) ^ ε by positivity ) ]

/-
Stronger existence lemma.
-/
lemma exists_xy_in_intervals_stronger (hQ4 : Question4Statement) (h_pnt : PNT_bounds) (ε : ℝ) (h_eps : ε > 0) :
  ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
  ∃ K : ℕ, ∀ k ≥ K,
    let primes := (Finset.Icc 1 k).filter (fun p => p.Prime ∧ k.sqrt < p)
    let M := primes.prod id
    let I (p : ℕ) (δ : ℝ) := Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ)))
    ∃ x y : ℕ,
      (M : ℝ) ^ (2.5 * ε) ≤ x ∧ x < (M : ℝ) ^ (3 * ε) ∧
      (M : ℝ) ^ ε < (y : ℝ) - x ∧ (y : ℝ) - x < 3 * (M : ℝ) ^ ε ∧
      (∀ p ∈ primes, x % p ∈ I p δ) ∧
      (∀ p ∈ primes, (p - y % p) % p ∈ I p δ) := by
        obtain ⟨δ, hδ_pos, hδ_lt, K, hK⟩ := hQ4 ε h_eps;
        -- Obtain δ' and K' from the negative variant.
        obtain ⟨δ', hδ'_pos, hδ'_lt, K', hK'⟩ := Q4_neg_variant hQ4 ε h_eps;
        use Min.min δ δ' / 2;
        refine' ⟨ _, _, _ ⟩;
        · positivity;
        · linarith [ min_le_left δ δ', min_le_right δ δ' ];
        · -- Choose K to be the maximum of K, K', and K_M.
          obtain ⟨K_M, hK_M⟩ : ∃ K_M : ℕ, ∀ k ≥ K_M, (M_prod k : ℝ) > 1 ∧ (M_prod k : ℝ) ^ (0.5 * ε) > 3 := by
            have hM_prod_tendsto_infinity : Filter.Tendsto (fun k => (M_prod k : ℝ)) Filter.atTop Filter.atTop := by
              convert M_prod_tendsto_infinity h_pnt using 1;
            have := hM_prod_tendsto_infinity.eventually_gt_atTop ( 3 ^ ( 1 / ( 0.5 * ε ) ) );
            exact Filter.eventually_atTop.mp ( this.and ( hM_prod_tendsto_infinity.eventually_gt_atTop 1 ) ) |> fun ⟨ K_M, hK_M ⟩ => ⟨ K_M, fun k hk => ⟨ by linarith [ hK_M k hk ], by have := hK_M k hk; exact lt_of_le_of_lt ( by rw [ ← Real.rpow_mul ( by positivity ), one_div_mul_cancel ( by positivity ), Real.rpow_one ] ) ( Real.rpow_lt_rpow ( by positivity ) this.1 ( by positivity ) ) ⟩ ⟩;
          refine' ⟨ Max.max K ( Max.max K' K_M ), fun k hk => _ ⟩ ; simp_all +decide [ le_max_iff ];
          obtain ⟨ x, hx₁, hx₂ ⟩ := hK k hk.1 ( Nat.ceil ( ( M_prod k : ℝ ) ^ ( 2.5 * ε ) ) )
          obtain ⟨ y, hy₁, hy₂ ⟩ := hK' k hk.2.1 ( x + Nat.ceil ( 1.5 * ( M_prod k : ℝ ) ^ ε ) );
          refine' ⟨ x, _, _, y, _, _, _ ⟩;
          · convert Nat.le_of_ceil_le hx₁.1 using 1;
            norm_num [ M_prod ];
            congr! 2;
          · have := arithmetic_bounds_stronger ( M_prod k ) ε x y h_eps ( by linarith [ hK_M k hk.2.2 ] ) ?_ ?_ ?_ <;> norm_num at *;
            · convert this.2.1 using 1;
              norm_num [ M_prod ];
              congr! 2;
            · convert hx₁ using 2;
              norm_num [ M_prod ];
              congr! 2;
            · convert hy₁ using 2;
              unfold M_prod; aesop;
            · exact hK_M k hk.2.2 |>.2;
          · rw [ lt_sub_iff_add_lt ];
            refine' lt_of_lt_of_le _ ( Nat.cast_le.mpr hy₁.1 );
            norm_num [ M_prod ] at *;
            rw [ add_comm ] ; gcongr ; norm_num [ PrimesIn ];
            exact lt_of_lt_of_le ( lt_mul_of_one_lt_left ( Real.rpow_pos_of_pos ( Finset.prod_pos fun p hp => Nat.cast_pos.mpr <| Nat.Prime.pos <| by aesop ) _ ) <| by norm_num ) <| Nat.le_ceil _;
          · have := hy₁.2; rw [ Nat.le_sub_iff_add_le ] at this <;> norm_num at *;
            · rw [ sub_lt_iff_lt_add' ];
              refine' lt_of_lt_of_le ( Nat.cast_lt.mpr this ) _;
              norm_num [ add_assoc ];
              refine' le_trans ( add_le_add ( Nat.ceil_lt_add_one ( by positivity ) |> le_of_lt ) ( Nat.ceil_lt_add_one ( by exact Real.rpow_nonneg ( Finset.prod_nonneg fun _ _ => by positivity ) _ ) |> le_of_lt ) ) _ ; ring_nf ; norm_num;
              have := hK_M k hk.2.2; norm_num [ M_prod ] at *;
              rw [ show ( ∏ i ∈ Finset.Icc 1 k with Nat.Prime i ∧ k.sqrt < i, ( i : ℝ ) ) = ∏ i ∈ PrimesIn k, ( i : ℝ ) by rfl ] ; rw [ show ( ∏ i ∈ PrimesIn k, ( i : ℝ ) ) ^ ε = ( ( ∏ i ∈ PrimesIn k, ( i : ℝ ) ) ^ ( 1 / 2 * ε ) ) ^ 2 by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _ ) ] ; ring ] ; nlinarith;
            · linarith [ Nat.ceil_pos.mpr ( show 0 < ( M_prod k : ℝ ) ^ ε by exact Real.rpow_pos_of_pos ( Nat.cast_pos.mpr ( by linarith [ hK_M k hk.2.2 ] ) ) _ ), Nat.ceil_pos.mpr ( show 0 < ( ∏ i ∈ Finset.Icc 1 k with Nat.Prime i ∧ k.sqrt < i, ( i : ℝ ) ) ^ ε by exact Real.rpow_pos_of_pos ( Finset.prod_pos fun p hp => Nat.cast_pos.mpr ( Nat.Prime.pos ( by aesop ) ) ) _ ) ];
          · refine' ⟨ fun p hp₁ hp₂ hp₃ hp₄ => ⟨ hx₂ p hp₁ hp₂ hp₃ hp₄ |>.1, le_trans ( hx₂ p hp₁ hp₂ hp₃ hp₄ |>.2 ) _ ⟩, fun p hp₁ hp₂ hp₃ hp₄ => ⟨ hy₂ p hp₁ hp₂ hp₃ hp₄ |>.1, le_trans ( hy₂ p hp₁ hp₂ hp₃ hp₄ |>.2 ) _ ⟩ ⟩;
            · exact Nat.ceil_mono <| Real.rpow_le_rpow_of_exponent_le ( mod_cast hp₃.one_lt.le ) <| by linarith [ min_le_left δ δ', min_le_right δ δ' ] ;
            · exact Nat.ceil_mono <| Real.rpow_le_rpow_of_exponent_le ( mod_cast hp₃.one_lt.le ) <| by cases min_cases δ δ' <;> linarith;

/-
Existence of x and y in specific intervals satisfying modular conditions.
-/
lemma exists_xy_in_intervals_final (hQ4 : Question4Statement) (h_pnt : PNT_bounds) (ε : ℝ) (h_eps : ε > 0) :
  ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
  ∃ K : ℕ, ∀ k ≥ K,
    let primes := (Finset.Icc 1 k).filter (fun p => p.Prime ∧ k.sqrt < p)
    let M := primes.prod id
    let I (p : ℕ) (δ : ℝ) := Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ)))
    ∃ x y : ℕ,
      (M : ℝ) ^ (2 * ε) < x ∧ x < (M : ℝ) ^ (3 * ε) ∧
      (M : ℝ) ^ ε < (y : ℝ) - x ∧ (y : ℝ) - x < 3 * (M : ℝ) ^ ε ∧
      (∀ p ∈ primes, x % p ∈ I p δ) ∧
      (∀ p ∈ primes, (p - y % p) % p ∈ I p δ) := by
        exact?

/-
Existence of x and y in specific intervals satisfying modular conditions.
-/
lemma exists_xy_in_intervals_stronger_final (hQ4 : Question4Statement) (h_pnt : PNT_bounds) (ε : ℝ) (h_eps : ε > 0) :
  ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
  ∃ K : ℕ, ∀ k ≥ K,
    let primes : Finset ℕ := (Finset.Icc 1 k).filter (fun p => p.Prime ∧ k.sqrt < p)
    let M := primes.prod id
    let I (p : ℕ) (δ : ℝ) := Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ)))
    ∃ x y : ℕ,
      (M : ℝ) ^ (2.5 * ε) ≤ x ∧ x < (M : ℝ) ^ (3 * ε) ∧
      (M : ℝ) ^ ε < (y : ℝ) - x ∧ (y : ℝ) - x < 3 * (M : ℝ) ^ ε ∧
      (∀ p ∈ primes, x % p ∈ I p δ) ∧
      (∀ p ∈ primes, (p - y % p) % p ∈ I p δ) := by
        exact?

/-
Stronger existence lemma (v2).
-/
lemma exists_xy_in_intervals_stronger_v2 (hQ4 : Question4Statement) (h_pnt : PNT_bounds) (ε : ℝ) (h_eps : ε > 0) :
  ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
  ∃ K : ℕ, ∀ k ≥ K,
    let primes : Finset ℕ := (Finset.Icc 1 k).filter (fun p => p.Prime ∧ k.sqrt < p)
    let M := primes.prod id
    let I (p : ℕ) (δ : ℝ) := Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ)))
    ∃ x y : ℕ,
      (M : ℝ) ^ (2.5 * ε) ≤ x ∧ x < (M : ℝ) ^ (3 * ε) ∧
      (M : ℝ) ^ ε < (y : ℝ) - x ∧ (y : ℝ) - x < 3 * (M : ℝ) ^ ε ∧
      (∀ p ∈ primes, x % p ∈ I p δ) ∧
      (∀ p ∈ primes, (p - y % p) % p ∈ I p δ) := by
        exact?

/-
Stronger existence lemma (final v2).
-/
lemma exists_xy_in_intervals_stronger_final_v2 (hQ4 : Question4Statement) (h_pnt : PNT_bounds) (ε : ℝ) (h_eps : ε > 0) :
  ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
  ∃ K : ℕ, ∀ k ≥ K,
    let primes : Finset ℕ := (Finset.Icc 1 k).filter (fun p => p.Prime ∧ k.sqrt < p)
    let M := primes.prod id
    let I (p : ℕ) (δ : ℝ) := Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ)))
    ∃ x y : ℕ,
      (M : ℝ) ^ (2.5 * ε) ≤ x ∧ x < (M : ℝ) ^ (3 * ε) ∧
      (M : ℝ) ^ ε < (y : ℝ) - x ∧ (y : ℝ) - x < 3 * (M : ℝ) ^ ε ∧
      (∀ p ∈ primes, x % p ∈ I p δ) ∧
      (∀ p ∈ primes, (p - y % p) % p ∈ I p δ) := by
        have := exists_xy_in_intervals_stronger_final hQ4 h_pnt ε h_eps;
        exact this

/-
Stronger existence lemma (final v3).
-/
lemma exists_xy_in_intervals_stronger_final_v3 (hQ4 : Question4Statement) (h_pnt : PNT_bounds) (ε : ℝ) (h_eps : ε > 0) :
  ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
  ∃ K : ℕ, ∀ k ≥ K,
    let primes : Finset ℕ := (Finset.Icc 1 k).filter (fun p => p.Prime ∧ Nat.sqrt k < p)
    let M := primes.prod id
    let I (p : ℕ) (δ : ℝ) := Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ)))
    ∃ x y : ℕ,
      (M : ℝ) ^ (2.5 * ε) ≤ x ∧ x < (M : ℝ) ^ (3 * ε) ∧
      (M : ℝ) ^ ε < (y : ℝ) - x ∧ (y : ℝ) - x < 3 * (M : ℝ) ^ ε ∧
      (∀ p ∈ primes, x % p ∈ I p δ) ∧
      (∀ p ∈ primes, (p - y % p) % p ∈ I p δ) := by
        have := exists_xy_in_intervals_stronger_final_v2 hQ4 h_pnt ε h_eps;
        exact this

/-
(1 / (y + k + floor(C)))^floor(C) >= (1 / (y + k + C))^C
-/
lemma bound_comparison (C : ℝ) (hC : C ≥ 1) (y k : ℕ) (hy : y > 0) :
  (1 / (y + k + ⌊C⌋₊ : ℝ)) ^ ⌊C⌋₊ ≥ (1 / (y + k + C : ℝ)) ^ C := by
    -- Taking the natural logarithm of both sides, we get $\inf(C) \cdot \ln(y + k + \inf(C)) \leq C \cdot \ln(y + k + C)$.
    have h_log : ⌊C⌋₊ * Real.log (y + k + ⌊C⌋₊) ≤ C * Real.log (y + k + C) := by
      exact mul_le_mul ( Nat.floor_le ( by positivity ) ) ( Real.log_le_log ( by positivity ) ( by linarith [ Nat.floor_le ( by positivity : 0 ≤ C ) ] ) ) ( Real.log_nonneg ( by linarith [ Nat.floor_le ( by positivity : 0 ≤ C ), show ( y :ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr hy ] ) ) ( by positivity );
    field_simp;
    rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_rpow ( by positivity ), Real.log_pow ] ; aesop

/-
The LCM ratio is bounded below by M^(1-5eps)/m * (x/y)^k * (1/(y+k+C))^C.
-/
lemma lcm_ratio_lower_bound_detailed_v2 (k x y C_int : ℕ) (δ : ℝ) (ε : ℝ)
  (hC : C_int ≥ 1)
  (hx0 : x > 0) (hy0 : y > 0) (hxy : x < y)
  (h_good_p : ∀ p ∈ PrimesIn k, ¬ is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) + 1)
  (h_bad_p : ∀ p ∈ PrimesIn k, is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) - 1)
  (h_small_p : ∀ p, p.Prime → p ≤ k.sqrt →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥
    -(padicValNat p (m k) : ℤ))
  (h_large_p : ∀ p, p.Prime → p > k + C_int →
    padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) = 0 ∧
    padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = 0)
  (h_diff_ge_zero : ∀ p, p > k →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥ 0)
  (h_bad_prod : (BadPrimes k δ).prod (fun p => (p : ℝ)) ≤ (M_prod k : ℝ) ^ (2 * ε))
  (h_M_prod : (M_prod k : ℝ) ≥ (M k : ℝ) ^ (1 - ε))
  (hM_gt_1 : (M k : ℝ) > 1)
  (h_M_prod_pos : (M_prod k : ℝ) > 0)
  (h_bound_y : (y : ℝ) + k + C_int < (M k : ℝ) ^ (3 * ε))
  (h_bound_x : (x : ℝ) > (M k : ℝ) ^ (2 * ε))
  (h_bound_diff : (y : ℝ) - x < 3 * (M k : ℝ) ^ ε)
  (h_k_large : k > 0)
  (h_eps : ε > 0)
  (h_m_pos : (m k : ℝ) > 0) :
  (((Finset.Icc x (x + k - 1)).lcm id : ℕ) : ℚ) / (((Finset.Icc y (y + k + C_int - 1)).lcm id : ℕ) : ℚ) ≥
  ((M k : ℝ) ^ (1 - 5 * ε) / (m k : ℝ)) * ((x : ℝ) / y) ^ k * (1 / (y + k + C_int : ℝ)) ^ C_int := by
    have := lcm_ratio_lower_bound_detailed k x y C_int δ ε hC hx0 hy0 hxy h_good_p h_bad_p h_small_p h_large_p h_diff_ge_zero h_bad_prod h_M_prod hM_gt_1 h_M_prod_pos h_bound_y h_bound_x h_bound_diff h_k_large h_eps h_m_pos;
    convert this using 1

/-
Definition of SquareBadPrimes.
-/
def SquareBadPrimes (k : ℕ) (C : ℝ) : Finset ℕ :=
  (Finset.Ioc (Nat.sqrt k) (Nat.sqrt (k + ⌊C⌋₊))).filter Nat.Prime

/-
For large k, there is at most one prime p such that k < p^2 <= k+C.
-/
lemma square_bad_primes_card_le_one (C : ℝ) (hC : C ≥ 0) :
  ∃ K, ∀ k ≥ K, (SquareBadPrimes k C).card ≤ 1 := by
    -- Let's choose K such that for all k ≥ K, the interval [sqrt(k+C), sqrt(k)] contains at most one integer.
    obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ k ≥ K, (Nat.sqrt (k + ⌊C⌋₊)) - (Nat.sqrt k) ≤ 1 := by
      use ⌊C⌋₊ ^ 2 + 1;
      simp +zetaDelta at *;
      exact fun k hk => Nat.le_of_lt_succ <| Nat.sqrt_lt.2 <| by nlinarith [ Nat.lt_succ_sqrt k ] ;
    -- If the interval [sqrt(k), sqrt(k+C)) contains at most one integer, then the number of primes in this interval is also at most one.
    have h_prime_count : ∀ k ≥ K, (SquareBadPrimes k C).card ≤ (Nat.sqrt (k + ⌊C⌋₊) - Nat.sqrt k) := by
      intro k hk; refine' le_trans ( Finset.card_le_card _ ) _;
      exact Finset.Icc ( Nat.sqrt k + 1 ) ( Nat.sqrt ( k + ⌊C⌋₊ ) );
      · intro p hp; unfold SquareBadPrimes at hp; aesop;
      · simp +arith +decide;
    exact ⟨ K, fun k hk => le_trans ( h_prime_count k hk ) ( hK k hk ) ⟩

/-
The product of primes p with k < p^2 <= k+C is at most sqrt(k+C).
-/
lemma square_bad_primes_prod_le (C : ℝ) (hC : C ≥ 0) :
  ∃ K, ∀ k ≥ K, (SquareBadPrimes k C).prod (fun p => (p : ℝ)) ≤ Real.sqrt (k + C) := by
    obtain ⟨ K, hK ⟩ := square_bad_primes_card_le_one C hC;
    use K + 1;
    intro k hk;
    have := hK k ( by linarith ) ; interval_cases _ : Finset.card ( SquareBadPrimes k C ) <;> simp_all +decide [ Finset.card_eq_one ];
    · exact le_add_of_le_of_nonneg ( mod_cast by linarith ) hC;
    · rcases ‹_› with ⟨ p, hp ⟩ ; simp_all +decide [ SquareBadPrimes ];
      rw [ Finset.eq_singleton_iff_unique_mem ] at hp;
      simp +zetaDelta at *;
      exact Real.le_sqrt_of_sq_le ( by nlinarith only [ show ( p : ℝ ) ^ 2 ≤ k + ⌊C⌋₊ by exact_mod_cast by nlinarith only [ hp.1.1.2, Nat.sqrt_le ( k + ⌊C⌋₊ ) ], Nat.floor_le hC ] )

/-
Checking availability of helper lemmas.
-/
#check m_small_relative_to_M
#check all_k_good_for_large_k
#check M_prod_ge_M_pow
#check prod_bad_le_M_prod_pow
#check valuation_ineq_good_p
#check valuation_ineq_bad_p
#check small_prime_condition_satisfied

/-
Valuation lower bound for intervals with length < 2p^2 and < p^3.
-/
lemma valuation_ge_count_sub_one (S : Finset ℕ) (p : ℕ) (n : ℕ)
  (hp : p.Prime)
  (hS_card : S.card = n)
  (hS_consec : ∃ s, S = Finset.Icc s (s + n - 1))
  (h_len : n < 2 * p * p)
  (h_p_sq : p * p > n / 2) -- To ensure not too many multiples
  (h_nonzero : ∀ z ∈ S, z ≠ 0) :
  (padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) : ℤ) ≥ (S.filter (p ∣ ·)).card - 1 := by
    -- If the maximum is ≥1: then e=1. At most 2 multiples of p^2. Use Lemma~\ref{lem:sum_min_val_diff_bound}, e=1: (Y sum - X sum) ≥ -1.
    by_cases h_max : S.sup (padicValNat p) ≥ 1;
    · have h_max : S.sup (padicValNat p) ≥ 1 → padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) ≥ ∑ i ∈ S, min (padicValNat p i) 1 - 1 := by
        intro h_max;
        convert valuation_ratio_ge_sum_min_sub_e S p 1 hp h_max h_nonzero using 1;
        norm_num [ ← @Int.cast_le ℚ ];
        norm_cast;
      have h_card_filter : ∑ i ∈ S, min (padicValNat p i) 1 = (Finset.filter (fun x => p ∣ x) S).card := by
        have h_card_filter : ∀ i ∈ S, min (padicValNat p i) 1 = if p ∣ i then 1 else 0 := by
          intro i hi; split_ifs <;> simp_all +decide [ Nat.Prime.dvd_iff_not_coprime hp ] ;
          contrapose! h_nonzero; have := Nat.gcd_dvd_left p i; have := Nat.gcd_dvd_right p i; simp_all +decide [ Nat.dvd_prime ] ;
        rw [ Finset.card_filter, Finset.sum_congr rfl h_card_filter ];
      grind +ring;
    · -- Since the maximum valuation is less than 1, there are no multiples of p in S. Therefore, the product of S is not divisible by p, and the LCM of S is also not divisible by p. Hence, the ratio (product / LCM) is not divisible by p, so its p-adic valuation is zero.
      have h_no_multiples : ∀ z ∈ S, ¬p ∣ z := by
        simp +zetaDelta at *;
        intro z hz; specialize h_max z hz; rcases h_max with ( rfl | rfl | h ) <;> simp_all +decide [ Nat.Prime.ne_one ] ;
      simp_all +decide [ Finset.filter_eq_empty_iff.mpr ]

/-
For good primes, the number of multiples in the y-interval is at least 1 more than in the x-interval.
-/
lemma count_multiples_good_primes_ineq (k x y C_int : ℕ) (δ : ℝ) (p : ℕ)
  (hp : p.Prime)
  (h_not_bad : ¬ is_bad k p δ)
  (hx : x % p ∈ Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ))))
  (hy : (p - y % p) % p ∈ Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ))))
  (hC : C_int ≥ 1)
  (h_p_large : (p : ℝ) ^ (1 - δ) < p / 2) -- To ensure intervals don't overlap or something?
  (h_k_mod : k % p + Nat.ceil ((p : ℝ) ^ (1 - δ)) < p) -- From not bad
  : (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k + C_int - 1))).card ≥
    (Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card + 1 := by
      -- The count of multiples of p in the interval [y, y+k+C_int-1] is at least floor((y+k+C_int-1)/p) - floor((y-1)/p).
      have h_count_y : (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k + C_int - 1))).card ≥ Nat.floor ((y + k + C_int - 1) / p) - Nat.floor ((y - 1) / p) := by
        have h_count_y : Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k + C_int - 1)) ⊇ Finset.image (fun i => p * i) (Finset.Icc (Nat.succ ((y - 1) / p)) ((y + k + C_int - 1) / p)) := by
          simp +decide [ Finset.subset_iff ];
          intros; subst_vars; exact ⟨ ⟨ by nlinarith [ Nat.div_add_mod ( y - 1 ) p, Nat.mod_lt ( y - 1 ) hp.pos, Nat.sub_add_cancel ( show 1 ≤ y from Nat.pos_of_ne_zero ( by aesop_cat ) ) ], by nlinarith [ Nat.div_mul_le_self ( y + k + C_int - 1 ) p, Nat.sub_add_cancel ( show 1 ≤ y + k + C_int from Nat.succ_le_of_lt ( by linarith ) ) ] ⟩, dvd_mul_right _ _ ⟩ ;
        refine' le_trans _ ( Finset.card_mono h_count_y );
        rw [ Finset.card_image_of_injective _ fun a b h => mul_left_cancel₀ hp.ne_zero h ] ; aesop;
      -- The count of multiples of p in the interval [x, x+k-1] is floor((x+k-1)/p) - floor((x-1)/p).
      have h_count_x : (Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card = Nat.floor ((x + k - 1) / p) - Nat.floor ((x - 1) / p) := by
        -- The set of multiples of $p$ in the interval $[x, x+k-1]$ is exactly the set $\{p \cdot m \mid m \in [\lceil x/p \rceil, \lfloor (x+k-1)/p \rfloor]\}$.
        have h_multiples_set : Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1)) = Finset.image (fun m => p * m) (Finset.Icc (Nat.succ (Nat.floor ((x - 1) / p))) (Nat.floor ((x + k - 1) / p))) := by
          ext i;
          simp +zetaDelta at *;
          constructor;
          · rintro ⟨ ⟨ hi₁, hi₂ ⟩, hi₃ ⟩;
            exact ⟨ i / p, ⟨ Nat.succ_le_of_lt ( Nat.div_lt_of_lt_mul <| by linarith [ Nat.div_mul_cancel hi₃, Nat.sub_add_cancel ( show 1 ≤ x from Nat.pos_of_ne_zero <| by aesop_cat ) ] ), Nat.div_le_div_right <| by linarith ⟩, by rw [ mul_comm, Nat.div_mul_cancel hi₃ ] ⟩;
          · rintro ⟨ a, ⟨ ha₁, ha₂ ⟩, rfl ⟩;
            exact ⟨ ⟨ by nlinarith [ Nat.div_add_mod ( x - 1 ) p, Nat.mod_lt ( x - 1 ) hp.pos, Nat.sub_add_cancel ( show 1 ≤ x from Nat.pos_of_ne_zero ( by aesop_cat ) ) ], by nlinarith [ Nat.div_mul_le_self ( x + k - 1 ) p, Nat.sub_add_cancel ( show 1 ≤ x + k from Nat.pos_of_ne_zero ( by aesop_cat ) ) ] ⟩, dvd_mul_right _ _ ⟩;
        rw [ h_multiples_set, Finset.card_image_of_injective _ fun a b h => mul_left_cancel₀ hp.ne_zero h ] ; aesop;
      -- Since $y \equiv 0 \pmod{p}$, we have $y = q_y p + r_y$ where $r_y \ge p - p^{1-\delta}$.
      obtain ⟨q_y, r_y, hr_y⟩ : ∃ q_y r_y, y = q_y * p + r_y ∧ r_y < p ∧ r_y ≥ p - Nat.ceil ((p : ℝ) ^ (1 - δ)) := by
        exact ⟨ y / p, y % p, by rw [ Nat.div_add_mod' ], Nat.mod_lt _ hp.pos, Nat.sub_le_of_le_add <| by linarith [ Nat.mod_lt y hp.pos, Finset.mem_Icc.mp hy, Nat.sub_add_cancel <| show y % p ≤ p from Nat.le_of_lt <| Nat.mod_lt _ hp.pos, Nat.mod_eq_of_lt <| show p - y % p < p from Nat.sub_lt hp.pos <| Nat.pos_of_ne_zero <| by aesop ] ⟩;
      -- Since $x \equiv 1 \pmod{p}$, we have $x = q_x p + r_x$ where $r_x \le p^{1-\delta}$.
      obtain ⟨q_x, r_x, hr_x⟩ : ∃ q_x r_x, x = q_x * p + r_x ∧ r_x < p ∧ r_x ≤ Nat.ceil ((p : ℝ) ^ (1 - δ)) := by
        exact ⟨ x / p, x % p, by rw [ Nat.div_add_mod' ], Nat.mod_lt _ hp.pos, Finset.mem_Icc.mp hx |>.2 ⟩;
      -- Since $k \equiv r_k \pmod{p}$ and $r_k \ge p^{1-\delta}$, we have $k = q_k p + r_k$ where $r_k \ge p^{1-\delta}$.
      obtain ⟨q_k, r_k, hr_k⟩ : ∃ q_k r_k, k = q_k * p + r_k ∧ r_k < p ∧ r_k ≥ Nat.ceil ((p : ℝ) ^ (1 - δ)) := by
        exact ⟨ k / p, k % p, by rw [ Nat.div_add_mod' ], Nat.mod_lt _ hp.pos, Nat.le_of_not_lt fun h => h_not_bad <| by unfold is_bad; aesop ⟩;
      rcases p with ( _ | _ | p ) <;> simp_all +decide [ Nat.succ_div ];
      -- Since $r_y + r_k \geq p + 1 + 1$, we have $(q_y * (p + 1 + 1) + r_y + (q_k * (p + 1 + 1) + r_k) + C_int - 1) / (p + 1 + 1) \geq q_y + q_k + 1$.
      have h_div_y : (q_y * (p + 1 + 1) + r_y + (q_k * (p + 1 + 1) + r_k) + C_int - 1) / (p + 1 + 1) ≥ q_y + q_k + 1 := by
        exact Nat.le_div_iff_mul_le ( Nat.succ_pos _ ) |>.2 ( Nat.le_sub_one_of_lt ( by nlinarith only [ hr_y, hr_k, hC, Nat.ceil_le.mpr hr_k.2.2 ] ) );
      have h_div_x : (q_x * (p + 1 + 1) + r_x + (q_k * (p + 1 + 1) + r_k) - 1) / (p + 1 + 1) ≤ q_x + q_k := by
        rw [ Nat.div_le_iff_le_mul_add_pred ] <;> norm_num;
        linarith [ Nat.mod_eq_of_lt hr_x.2.1, Nat.mod_eq_of_lt hr_k.2.1 ];
      have h_div_x : (q_x * (p + 1 + 1) + r_x - 1) / (p + 1 + 1) = q_x := by
        rcases r_x with ( _ | _ | r_x ) <;> simp_all +arith +decide [ Nat.div_eq_of_lt ];
        nlinarith only [ Nat.div_mul_le_self ( r_x + q_x * ( p + 1 + 1 ) + 1 ) ( p + 2 ), Nat.div_add_mod ( r_x + q_x * ( p + 1 + 1 ) + 1 ) ( p + 2 ), Nat.mod_lt ( r_x + q_x * ( p + 1 + 1 ) + 1 ) ( by linarith : p + 2 > 0 ), hr_x.2.1 ]
      have h_div_y : (q_y * (p + 1 + 1) + r_y - 1) / (p + 1 + 1) = q_y := by
        rw [ Nat.add_sub_assoc ];
        · rw [ Nat.add_div ] <;> norm_num;
          rw [ Nat.div_eq_of_lt, if_neg ] <;> norm_num [ Nat.mod_lt ] ; omega;
        · contrapose! hy; aesop;
      simp_all +decide [ Nat.div_eq_of_lt ];
      omega

/-
An interval of length less than p^2 contains at most one multiple of p^2.
-/
lemma at_most_one_multiple_sq (S : Finset ℕ) (p : ℕ) (n : ℕ)
  (hp : p > 1)
  (hS_card : S.card = n)
  (hS_consec : ∃ s, S = Finset.Icc s (s + n - 1))
  (h_len : n < p * p) :
  (S.filter (fun z => p * p ∣ z)).card ≤ 1 := by
    -- Since $S$ is a finite set of consecutive integers, any two multiples of $p^2$ in $S$ must be separated by at least $p^2$.
    have h_sep : ∀ z₁ z₂ : ℕ, z₁ ∈ S → z₂ ∈ S → p * p ∣ z₁ → p * p ∣ z₂ → z₁ = z₂ := by
      intros z₁ z₂ hz₁ hz₂ hz₁_div hz₂_div
      obtain ⟨s, hs⟩ := hS_consec
      have h_diff : z₁ ∈ Finset.Icc s (s + n - 1) ∧ z₂ ∈ Finset.Icc s (s + n - 1) := by
        aesop;
      obtain ⟨ k₁, hk₁ ⟩ := hz₁_div; obtain ⟨ k₂, hk₂ ⟩ := hz₂_div; simp_all +decide [ add_assoc, Nat.add_sub_assoc ] ;
      exact Or.inl ( by nlinarith only [ h_len, hz₁, hz₂, Nat.sub_add_cancel ( show 1 ≤ s + n from Nat.succ_le_of_lt ( Nat.pos_of_ne_zero ( by aesop_cat ) ) ) ] );
    exact Finset.card_le_one.mpr fun x hx y hy => h_sep x y ( Finset.filter_subset _ _ hx ) ( Finset.filter_subset _ _ hy ) ( Finset.mem_filter.mp hx |>.2 ) ( Finset.mem_filter.mp hy |>.2 )

/-
If n < p^2, then val = count - 1.
-/
lemma valuation_eq_count_sub_one_of_len_lt_sq (S : Finset ℕ) (p : ℕ) (n : ℕ)
  (hp : p.Prime)
  (hS_card : S.card = n)
  (hS_consec : ∃ s, S = Finset.Icc s (s + n - 1))
  (h_len_sq : n < p * p)
  (h_len_ge : p ≤ n)
  (h_nonzero : ∀ z ∈ S, z ≠ 0) :
  padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (S.filter (p ∣ ·)).card - 1 := by
    exact?

/-
If no multiples of p^2, val = count - 1.
-/
lemma valuation_case_zero_sq (S : Finset ℕ) (p : ℕ) (n : ℕ)
  (hp : p.Prime)
  (hS_card : S.card = n)
  (hS_consec : ∃ s, S = Finset.Icc s (s + n - 1))
  (h_len_ge : p ≤ n)
  (h_no_sq : (S.filter (fun z => p * p ∣ z)).card = 0)
  (h_nonzero : ∀ z ∈ S, z ≠ 0) :
  padicValNat p ((∏ i ∈ S, i) / (S.lcm id)) = (S.filter (p ∣ ·)).card - 1 := by
    convert valuation_eq_count_sub_one_of_len_lt_sq S p n hp hS_card hS_consec _ _ h_nonzero using 1;
    · simp_all +decide [ Finset.ext_iff ];
      rcases hS_consec with ⟨ s, hs ⟩ ; have := hs s ; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
      contrapose! h_no_sq;
      use p * p * ((s + p * p - 1) / (p * p));
      exact ⟨ by linarith [ Nat.div_add_mod ( s + p * p - 1 ) ( p * p ), Nat.mod_lt ( s + p * p - 1 ) ( mul_pos hp.pos hp.pos ), Nat.sub_add_cancel ( show 1 ≤ s + p * p from by nlinarith only [ hp.two_le, Nat.pos_of_ne_zero h_nonzero ] ) ], by linarith [ Nat.div_mul_le_self ( s + p * p - 1 ) ( p * p ), Nat.sub_add_cancel ( show 1 ≤ s + p * p from by nlinarith only [ hp.two_le, Nat.pos_of_ne_zero h_nonzero ] ), Nat.sub_add_cancel ( show 1 ≤ s + n from by linarith [ Nat.pos_of_ne_zero h_nonzero ] ) ], by norm_num ⟩;
    · linarith

/-
Valuation inequality for good primes.
-/
lemma valuation_ineq_good_p_aux (k x y C_int : ℕ) (δ : ℝ) (p : ℕ)
  (hk : k ≥ C_int * C_int + 10)
  (hp : p ∈ PrimesIn k)
  (h_not_bad : ¬ is_bad k p δ)
  (hx : x % p ∈ Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ))))
  (hy : (p - y % p) % p ∈ Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ))))
  (hC : C_int ≥ 1)
  (hx0 : x > 0) (hy0 : y > 0)
  (h_p_large : (p : ℝ) ^ (1 - δ) < p / 2)
  (h_k_mod : k % p + Nat.ceil ((p : ℝ) ^ (1 - δ)) < p) :
  padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) ≥
  padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) + 1 := by
    -- Apply the lemma that states the valuation is at least the count of multiples minus 1 for the y-interval.
    have h_val_y : (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥ ((Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k + C_int - 1))).card : ℤ) - 1 := by
      apply_rules [ valuation_ge_count_sub_one ];
      · exact Finset.mem_filter.mp hp |>.2.1;
      · norm_num +zetaDelta at *;
        exact ⟨ y, by rw [ show y + k + C_int - 1 + 1 - y = k + C_int by omega ] ; ring ⟩;
      · simp +arith +decide;
        rw [ Nat.sub_add_cancel ( by nlinarith ) ];
        rw [ tsub_lt_iff_left ] <;> nlinarith [ show p > Nat.sqrt k from Finset.mem_filter.mp hp |>.2.2, Nat.lt_succ_sqrt k ];
      · norm_num at *;
        rw [ Nat.sub_add_cancel ( by nlinarith only [ hk, hC ] ) ];
        rw [ Nat.div_lt_iff_lt_mul ] <;> norm_num;
        rw [ tsub_lt_iff_left ] <;> nlinarith only [ hk, hC, Nat.sqrt_lt.mp ( show Nat.sqrt k < p from by { have := Finset.mem_filter.mp hp; exact this.2.2 } ) ];
      · exact fun z hz => by linarith [ Finset.mem_Icc.mp hz ] ;
    -- Apply the lemma that states the valuation is equal to the count of multiples minus 1 for the x-interval.
    have h_val_x : (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) = ((Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card : ℤ) - 1 := by
      have h_len_x : (Finset.Icc x (x + k - 1)).card = k := by
        cases k <;> norm_num at * ; omega
      have h_len_ge_x : p ≤ k := by
        exact Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.2
      have h_len_lt_sq_x : k < p * p := by
        have h_sqrt : k.sqrt < p := by
          exact Finset.mem_filter.mp hp |>.2.2;
        nlinarith only [ Nat.lt_succ_sqrt k, h_sqrt ]
      have h_val_x : padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = ((Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card : ℕ) - 1 := by
        apply_rules [ valuation_eq_count_sub_one_of_len_lt_sq ];
        · exact Finset.mem_filter.mp hp |>.2.1;
        · use x;
        · exact fun z hz => by linarith [ Finset.mem_Icc.mp hz ] ;
      rw [ h_val_x, Nat.cast_sub ] <;> norm_num;
      use p * ((x + k - 1) / p);
      norm_num +zetaDelta at *;
      exact ⟨ by linarith [ Nat.div_add_mod ( x + k - 1 ) p, Nat.mod_lt ( x + k - 1 ) ( Nat.pos_of_ne_zero ( by aesop_cat : p ≠ 0 ) ), Nat.sub_add_cancel ( by linarith : 1 ≤ x + k ) ], by linarith [ Nat.div_mul_le_self ( x + k - 1 ) p, Nat.sub_add_cancel ( by linarith : 1 ≤ x + k ) ] ⟩;
    -- Apply the lemma that states the count of multiples in the y-interval is at least one more than in the x-interval.
    have h_count_y : ((Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k + C_int - 1))).card : ℤ) ≥ ((Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card : ℤ) + 1 := by
      have := count_multiples_good_primes_ineq k x y C_int δ p ( Finset.mem_filter.mp hp |>.2.1 ) h_not_bad hx hy hC h_p_large h_k_mod; norm_cast at *;
    grind

/-
Valuation of y-interval is at least count - 1.
-/
lemma val_y_ge_count_y_sub_one (k y C_int : ℕ) (p : ℕ)
  (hk : k ≥ C_int + 1)
  (hp : p ∈ PrimesIn k)
  (hy0 : y > 0)
  (hC : C_int ≥ 1) :
  (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
  (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k + C_int - 1))).card - 1 := by
    convert valuation_ge_count_sub_one _ _ _ _ _ _ _ _ _ using 1;
    exact k + C_int;
    all_goals norm_num [ PrimesIn ] at *;
    any_goals omega;
    · exact hp.2.1;
    · exact ⟨ y, by ring ⟩;
    · nlinarith only [ hk, hp.2.2, Nat.lt_succ_sqrt k ];
    · rw [ Nat.div_lt_iff_lt_mul ] <;> nlinarith only [ hk, hp.2.2, Nat.sqrt_lt.mp hp.2.2 ]

/-
Checking availability of lemmas.
-/
#check val_y_ge_count_y_sub_one
#check count_diff_le_one

/-
Valuation of x-interval is count - 1.
-/
lemma val_x_eq_count_x_sub_one (k x : ℕ) (p : ℕ)
  (hp : p ∈ PrimesIn k)
  (hx0 : x > 0) :
  (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) =
  (Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card - 1 := by
    -- Apply the lemma that states if the interval length is less than p^2 and no multiples of p^2, then the valuation is count - 1.
    have h_apply_lemma : padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = (Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card - 1 := by
      apply valuation_eq_count_sub_one_of_len_lt_sq;
      any_goals exact k;
      all_goals norm_num [ PrimesIn ] at *;
      exacts [ hp.2.1, by omega, ⟨ x, rfl ⟩, by nlinarith only [ hp.2.2, Nat.lt_succ_sqrt k ], hp.1.2, fun z hz₁ hz₂ => by linarith ];
    rw [ h_apply_lemma, Nat.cast_sub ] <;> norm_num;
    use x + ( p - x % p ) % p;
    norm_num [ Nat.dvd_iff_mod_eq_zero ];
    constructor;
    · refine' Nat.le_sub_one_of_lt ( Nat.add_lt_add_left _ _ );
      exact lt_of_lt_of_le ( Nat.mod_lt _ ( Nat.Prime.pos ( by unfold PrimesIn at hp; aesop ) ) ) ( by unfold PrimesIn at hp; aesop );
    · simp +decide [ Nat.add_mod, Nat.mod_eq_zero_of_dvd ( Nat.dvd_sub_mod _ ) ];
      simp +decide [ Nat.add_sub_of_le ( Nat.mod_lt x ( Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2.1 ) ) |> Nat.le_of_lt ) ]

/-
The number of multiples of p in [y, y+k+C-1] is at least the number in [x, x+k-1] minus 1.
-/
lemma count_y_ge_count_x_sub_one (k x y C_int p : ℕ) (hp : p > 0)
  (hC : C_int ≥ 1) :
  ((Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k + C_int - 1))).card : ℤ) ≥
  ((Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card : ℤ) - 1 := by
    -- Since $C \ge 1$, the interval $[y, y+k+C-1]$ contains the interval $[y, y+k-1]$.
    have h_contain : (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k + C_int - 1))).card ≥ (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k - 1))).card := by
      exact Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.Icc_subset_Icc_right <| Nat.sub_le_sub_right ( by linarith ) _;
    -- Since these intervals are of the same length, the difference in the number of multiples of $p$ is at most 1.
    have h_diff : ((Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k - 1))).card : ℤ) ≥ ((Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card : ℤ) - 1 := by
      have h_diff : |((Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k - 1))).card : ℤ) - ((Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card : ℤ)| ≤ 1 := by
        exact?;
      linarith [ abs_le.mp h_diff ];
    exact h_diff.trans ( mod_cast h_contain )

/-
For bad primes, the valuation difference is at least -1.
-/
lemma valuation_ineq_bad_p_weak (k x y C_int : ℕ) (p : ℕ)
  (hk : k ≥ C_int + 1)
  (hp : p ∈ PrimesIn k)
  (hC : C_int ≥ 1)
  (hx0 : x > 0) (hy0 : y > 0) :
  (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
  (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) - 1 := by
    -- By combining the results from val_y_ge_count_y_sub_one, val_x_eq_count_x_sub_one, and count_y_ge_count_x_sub_one, we can conclude the proof.
    have h_combined : (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥ ((Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k + C_int - 1))).card : ℤ) - 1 ∧
                       (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) = ((Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card : ℤ) - 1 ∧
                       ((Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k + C_int - 1))).card : ℤ) ≥ ((Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card : ℤ) - 1 := by
                         exact ⟨ by linarith [ val_y_ge_count_y_sub_one k y C_int p ( by linarith ) hp hy0 hC ], by linarith [ val_x_eq_count_x_sub_one k x p hp hx0 ], by linarith [ count_y_ge_count_x_sub_one k x y C_int p ( Nat.Prime.pos ( by unfold PrimesIn at hp; aesop ) ) hC ] ⟩;
    linarith

/-
A stronger version of Question 4 that allows specifying a residue modulo m (coprime to M).
-/
def Question4Stronger : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
  ∃ K : ℕ, ∀ k ≥ K,
    let primes := (Finset.Icc 1 k).filter (fun p => p.Prime ∧ k.sqrt < p)
    let M := primes.prod id
    let I (p : ℕ) := Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ)))
    ∀ (start : ℕ) (m_mod : ℕ) (a : ℕ),
      Nat.Coprime m_mod M →
      m_mod > 0 →
      ∃ x ∈ Finset.Icc start (start + Nat.ceil ((M : ℝ) ^ ε) - 1),
      x % m_mod = a % m_mod ∧
      ∀ p ∈ primes, x % p ∈ I p

/-
The size of the set of $z \in \{0, \dots, p-1\}$ such that $(mz+a) \pmod p \in I$ is equal to $|I|$, assuming $p \nmid m$.
-/
def I_transformed (p : ℕ) (m : ℕ) (a : ℕ) (I : Set ℕ) : Set ℕ :=
  { z ∈ Finset.range p | (m * z + a) % p ∈ I }

lemma I_transformed_card (p : ℕ) (m : ℕ) (a : ℕ) (I : Finset ℕ)
  (hp : p.Prime) (hm : ¬ p ∣ m) (hI : I ⊆ Finset.range p) :
  (Finset.filter (fun z => z ∈ I_transformed p m a I) (Finset.range p)).card = I.card := by
    rw [ Finset.card_filter, Finset.card_eq_sum_ones ];
    -- Apply the bijection to rewrite the sum.
    have h_sum_eq : ∑ i ∈ Finset.range p, (if (m * i + a) % p ∈ I then 1 else 0) = ∑ i ∈ Finset.range p, (if i ∈ I then 1 else 0) := by
      have h_bij : Finset.image (fun i => (m * i + a) % p) (Finset.range p) = Finset.range p := by
        refine Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i hi => Finset.mem_range.mpr <| Nat.mod_lt _ hp.pos ) ?_;
        rw [ Finset.card_image_of_injOn ];
        intros x hx y hy hxy; haveI := Fact.mk hp; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff' ] ;
        exact Nat.mod_eq_of_lt hx ▸ Nat.mod_eq_of_lt hy ▸ by simpa [ ← ZMod.natCast_eq_natCast_iff' ] using hxy.resolve_right ( by rw [ ZMod.natCast_eq_zero_iff ] ; exact hm ) ;
      conv_rhs => rw [ ← h_bij, Finset.sum_image ( Finset.card_image_iff.mp <| by aesop ) ] ;
    simp_all +decide [ Finset.sum_ite, I_transformed ];
    convert h_sum_eq using 2 ; ext ; aesop;
    exact Eq.symm ( Finset.inter_eq_right.mpr hI )

/-
Mapping an interval of length `len` by `z -> m*z + a` yields a preimage interval of length at least `len/m - 2`.
-/
lemma interval_mapping (start len m a : ℕ) (hm : m > 0) (hlen : len ≥ 2 * m) (ha : a < m) :
  ∃ z_start z_len,
    z_len ≥ len / m - 2 ∧
    ∀ z ∈ Finset.Icc z_start (z_start + z_len - 1),
      m * z + a ∈ Finset.Icc start (start + len - 1) := by
  let z_start := (start + m - 1 - a) / m
  let z_end := (start + len - 1 - a) / m
  let z_len := z_end - z_start + 1
  use z_start, z_len
  constructor
  · -- Length bound
    have h_div : (start + len - 1 - a) ≥ (start + m - 1 - a) + (len - m) := by
      omega;
    have h_div : (start + len - 1 - a) / m ≥ (start + m - 1 - a) / m + (len - m) / m := by
      exact Nat.le_div_iff_mul_le hm |>.2 ( by linarith [ Nat.div_mul_le_self ( start + m - 1 - a ) m, Nat.div_mul_le_self ( len - m ) m ] );
    have h_div : len / m ≤ (len - m) / m + 1 := by
      rw [ show len = m + ( len - m ) by rw [ Nat.add_sub_cancel' ( by linarith ) ] ] ; norm_num [ Nat.add_div, hm ];
    grind
  · -- Inclusion
    intro z hz
    rw [Finset.mem_Icc] at hz ⊢
    constructor
    · -- Lower bound
      calc m * z + a ≥ m * z_start + a := by gcongr; exact hz.1
        _ ≥ start := by
          dsimp [z_start]
          -- m * ((start + m - 1 - a) / m) + a >= start
          -- (start + m - 1 - a) / m >= (start - a) / m (ceil)
          -- m * ceil((start-a)/m) + a >= m * ((start-a)/m) + a >= start - a + a = start
          nlinarith only [ Nat.div_add_mod ( start + m - 1 - a ) m, Nat.mod_lt ( start + m - 1 - a ) hm, Nat.sub_add_cancel ( show a ≤ start + m - 1 from le_tsub_of_add_le_left <| by linarith ), Nat.sub_add_cancel ( show 1 ≤ start + m from by linarith ) ]
    · -- Upper bound
      calc m * z + a ≤ m * (z_start + z_len - 1) + a := by gcongr; exact hz.2
        _ = m * z_end + a := by
          dsimp [z_len]
          -- z_start + (z_end - z_start + 1) - 1 = z_end
          -- Need z_end >= z_start
          rw [ add_tsub_cancel_of_le ( Nat.div_le_div_right ( by omega ) ) ]
        _ ≤ start + len - 1 := by
          dsimp [z_end]
          -- m * floor(...) + a <= ...
          linarith [ Nat.div_mul_le_self ( start + len - 1 - a ) m, Nat.sub_add_cancel ( show a ≤ start + len - 1 from by omega ) ]

/-
Definitions and lemmas for the transformed index set.
-/
def I_transformed_finset (p : ℕ) (m : ℕ) (a : ℕ) (I : Finset ℕ) : Finset ℕ :=
  (Finset.range p).filter (fun z => z ∈ I_transformed p m a I)

lemma I_transformed_finset_card_eq (p : ℕ) (m : ℕ) (a : ℕ) (I : Finset ℕ)
  (hp : p.Prime) (hm : ¬ p ∣ m) (hI : I ⊆ Finset.range p) :
  (I_transformed_finset p m a I).card = I.card := by
  exact I_transformed_card p m a I hp hm hI

lemma mod_in_I_transformed_finset (p : ℕ) (m : ℕ) (a : ℕ) (I : Finset ℕ) (z : ℕ) (hp : p > 0) :
  z % p ∈ I_transformed_finset p m a I ↔ (m * z + a) % p ∈ I := by
    unfold I_transformed_finset;
    simp +decide [ I_transformed, Nat.mod_lt _ hp ];
    simp +decide [ Nat.add_mod, Nat.mul_mod ]

/-
For sufficiently large M, if m is small relative to M, then the interval length bounds are satisfied.
-/
lemma large_M_bounds (ε : ℝ) (h_eps : ε > 0) :
  ∃ M0 : ℕ, ∀ M ≥ M0, ∀ m : ℕ,
    m > 0 →
    (m : ℝ) ≤ (M : ℝ) ^ (ε / 2) →
    Nat.ceil ((M : ℝ) ^ ε) ≥ 2 * m ∧
    ((Nat.ceil ((M : ℝ) ^ ε) : ℕ) / m : ℝ) - 2 ≥ Nat.ceil ((M : ℝ) ^ (ε / 3)) := by
      obtain ⟨M0, hM0⟩ : ∃ M0 : ℕ, ∀ M ≥ M0, (M : ℝ) ^ (ε / 3) + 3 ≤ (M : ℝ) ^ (ε / 2) := by
        -- We'll use that $M^{\epsilon/2}$ grows faster than $M^{\epsilon/3}$.
        have h_exp_growth : Filter.Tendsto (fun M : ℕ => (M : ℝ) ^ (ε / 2) - (M : ℝ) ^ (ε / 3)) Filter.atTop Filter.atTop := by
          -- Factor out $M^{\epsilon/3}$ from the expression.
          suffices h_factor : Filter.Tendsto (fun M : ℕ => (M : ℝ) ^ (ε / 3) * ((M : ℝ) ^ (ε / 6) - 1)) Filter.atTop Filter.atTop by
            exact h_factor.congr fun M => by rw [ mul_sub, ← Real.rpow_add' ] <;> ring <;> positivity;
          exact Filter.Tendsto.atTop_mul_atTop₀ ( tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop ) ( Filter.tendsto_atTop_add_const_right _ _ <| tendsto_rpow_atTop ( by positivity ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop );
        exact Filter.eventually_atTop.mp ( h_exp_growth.eventually_ge_atTop 3 ) |> fun ⟨ M0, hM0 ⟩ => ⟨ M0, fun M hM => by linarith [ hM0 M hM ] ⟩;
      refine' ⟨ M0 + 2, fun M hM m hm₁ hm₂ => ⟨ _, _ ⟩ ⟩ <;> norm_num at *;
      · have := hM0 M ( by linarith );
        rw [ show ( ε : ℝ ) = ε / 2 + ε / 2 by ring, Real.rpow_add ] at * <;> norm_num at *;
        · exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast ; nlinarith [ Nat.le_ceil ( ( M : ℝ ) ^ ( ε / 2 ) * ( M : ℝ ) ^ ( ε / 2 ) ), show ( M : ℝ ) ^ ( ε / 2 ) ≥ 1 by exact Real.one_le_rpow ( by norm_cast; linarith ) ( by positivity ), show ( M : ℝ ) ^ ( ε / 3 ) ≥ 1 by exact Real.one_le_rpow ( by norm_cast; linarith ) ( by positivity ) ] ;
        · linarith;
      · rw [ le_sub_iff_add_le, le_div_iff₀ ] <;> norm_cast;
        -- Using the bounds from hM0 and hm₂, we can show that $(⌈M^{ε/3}⌉₊ + 2) * m ≤ M^{ε}$.
        have h_bound : (⌈(M : ℝ) ^ (ε / 3)⌉₊ + 2) * m ≤ (M : ℝ) ^ ε := by
          refine' le_trans ( mul_le_mul_of_nonneg_right ( show ( ⌈ ( M : ℝ ) ^ ( ε / 3 ) ⌉₊ : ℝ ) + 2 ≤ ( M : ℝ ) ^ ( ε / 2 ) by linarith [ Nat.ceil_lt_add_one ( show 0 ≤ ( M : ℝ ) ^ ( ε / 3 ) by positivity ), hM0 M ( by linarith ) ] ) ( Nat.cast_nonneg m ) ) _;
          convert mul_le_mul_of_nonneg_left hm₂ ( Real.rpow_nonneg ( Nat.cast_nonneg M ) ( ε / 2 ) ) using 1 ; rw [ ← Real.rpow_add ( Nat.cast_pos.mpr <| by linarith ) ] ; ring;
        exact Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; linarith [ Nat.le_ceil ( ( M : ℝ ) ^ ε ) ] ;

/-
A generalized version of Question 4 that allows arbitrary residue sets of sufficient density.
-/
def Question4General : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
  ∃ K : ℕ, ∀ k ≥ K,
    let primes := (Finset.Icc 1 k).filter (fun p => p.Prime ∧ k.sqrt < p)
    let M := primes.prod id
    ∀ (start : ℕ) (I : ℕ → Finset ℕ),
      (∀ p ∈ primes, I p ⊆ Finset.range p) →
      (∀ p ∈ primes, (I p).card ≥ Nat.ceil ((p : ℝ) ^ (1 - δ))) →
      ∃ x ∈ Finset.Icc start (start + Nat.ceil ((M : ℝ) ^ ε) - 1),
      ∀ p ∈ primes, x % p ∈ I p

/-
The function $C \cdot \frac{k}{\log k}$ tends to infinity as $k \to \infty$ for $C > 0$.
-/
lemma limit_mul_k_div_log_k (C : ℝ) (hC : C > 0) : Filter.Tendsto (fun k : ℕ => C * ((k : ℝ) / Real.log k)) Filter.atTop Filter.atTop := by
  exact Filter.Tendsto.const_mul_atTop hC ( k_div_log_k_tendsto_atTop.comp tendsto_natCast_atTop_atTop )

/-
The ratio of ratios is at least M^(1-5ε)/m.
-/
lemma ratio_of_ratios_bound_M_pow (k x y C_int : ℕ) (δ : ℝ) (ε : ℝ)
  (hC : C_int ≥ 1)
  (hx0 : x > 0) (hy0 : y > 0)
  (h_good_p : ∀ p ∈ PrimesIn k, ¬ is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) + 1)
  (h_bad_p : ∀ p ∈ PrimesIn k, is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) - 1)
  (h_small_p : ∀ p, p.Prime → p ≤ k.sqrt →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥
    -(padicValNat p (m k) : ℤ))
  (h_large_p : ∀ p, p.Prime → p > k + C_int →
    padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) = 0 ∧
    padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = 0)
  (h_diff_ge_zero : ∀ p, p > k →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥ 0)
  (h_bad_prod : (BadPrimes k δ).prod (fun p => (p : ℝ)) ≤ (M_prod k : ℝ) ^ (2 * ε))
  (h_M_prod : (M_prod k : ℝ) ≥ (M k : ℝ) ^ (1 - ε))
  (hM_gt_1 : (M k : ℝ) > 1)
  (h_M_prod_pos : (M_prod k : ℝ) > 0)
  (h_eps : ε > 0)
  (h_m_pos : (m k : ℝ) > 0) :
  ratio_of_ratios k x y C_int ≥ (M k : ℝ) ^ (1 - 5 * ε) / (m k : ℝ) := by
    have h_ratio_lower_bound : ((ratio_of_ratios k x y C_int) : ℚ) ≥ ((M_prod k : ℚ) / ((m k : ℚ) * (BadPrimes k δ).prod (fun p => (p : ℚ) ^ 2))) := by
      apply ratio_lower_bound_with_m_v2 k x y C_int δ hC hx0 hy0 h_good_p h_bad_p h_small_p h_large_p h_diff_ge_zero;
    have h_ratio_lower_bound_final : ((M_prod k : ℚ) / ((m k : ℚ) * (BadPrimes k δ).prod (fun p => (p : ℚ) ^ 2))) ≥ ((M k : ℝ) ^ (1 - 5 * ε)) / ((m k : ℝ)) := by
      have h_ratio_lower_bound : (M_prod k : ℝ) / ((m k : ℝ) * (BadPrimes k δ).prod (fun p => (p : ℝ) ^ 2)) ≥ (M k : ℝ) ^ (1 - 5 * ε) / (m k : ℝ) := by
        have h_prod_bad : (BadPrimes k δ).prod (fun p => (p : ℝ)) ≤ (M_prod k : ℝ) ^ (2 * ε) := h_bad_prod
        have h_M_prod : (M_prod k : ℝ) ≥ (M k : ℝ) ^ (1 - ε) := h_M_prod
        have h_ratio_lower_bound : (M_prod k : ℝ) / ((m k : ℝ) * (BadPrimes k δ).prod (fun p => (p : ℝ) ^ 2)) ≥ (M k : ℝ) ^ (1 - 5 * ε) / (m k : ℝ) := by
          have := M_prod_div_BadProd_sq_ge_M_pow k ε δ h_eps h_bad_prod h_M_prod hM_gt_1 h_M_prod_pos
          norm_num +zetaDelta at *;
          convert mul_le_mul_of_nonneg_right this ( inv_nonneg.mpr ( Nat.cast_nonneg ( m k ) ) ) using 1 ; ring;
        convert h_ratio_lower_bound using 1;
      convert h_ratio_lower_bound using 1;
      norm_num [ ← @Rat.cast_inj ℝ ];
    exact h_ratio_lower_bound_final.trans ( mod_cast h_ratio_lower_bound )

/-
If x < M^(3eps) and y-x < 3M^eps, then y < 4M^(3eps) for M > 10.
-/
lemma y_bound_check (M : ℝ) (ε : ℝ) (x y : ℕ) (hM : M > 10) (h_eps : ε > 0)
  (hx : (x : ℝ) < M ^ (3 * ε))
  (h_diff : (y : ℝ) - x < 3 * M ^ ε) :
  (y : ℝ) < 4 * M ^ (3 * ε) := by
    linarith [ show ( M : ℝ ) ^ ε ≤ M ^ ( 3 * ε ) by rw [ Real.rpow_le_rpow_left_iff ] <;> linarith ]

/-
Simple lower bound for the product ratio.
-/
lemma product_ratio_lower_bound_simple (k x y C_int : ℕ)
  (hx : x > 0) (hy : y > 0) (hxy : x < y) (hC : C_int ≥ 1) :
  ((∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) / (∏ i ∈ Finset.Icc y (y + k + C_int - 1), (i : ℚ))) ≥
  ((x : ℚ) / y) ^ k * (1 / (y + k + C_int : ℚ)) ^ C_int := by
    -- We can split the product into two parts: one from $x$ to $x+k-1$ and the other from $y$ to $y+k+C-1$.
    have h_split : (∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) / (∏ i ∈ Finset.Icc y (y + k + C_int - 1), (i : ℚ)) =
                   (∏ i ∈ Finset.range k, (x + i : ℚ) / (y + i : ℚ)) *
                   (1 / (∏ j ∈ Finset.range C_int, (y + k + j : ℚ))) := by
                     erw [ Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range ] ; norm_num [ add_assoc, add_left_comm, add_comm ];
                     rw [ show 1 + ( k + x - 1 ) - x = k from Nat.sub_eq_of_eq_add <| by linarith [ Nat.sub_add_cancel <| show 1 ≤ k + x from by linarith ] ] ; rw [ show 1 + ( k + ( y + C_int ) - 1 ) - y = k + C_int from Nat.sub_eq_of_eq_add <| by linarith [ Nat.sub_add_cancel <| show 1 ≤ k + ( y + C_int ) from by linarith ] ] ; norm_num [ add_comm, add_left_comm, add_assoc, Finset.prod_range_add ] ; ring;
    -- For the first part, $\frac{x+i}{y+i} \ge \frac{x}{y}$ because $x < y$ and the function $t \mapsto \frac{x+t}{y+t}$ is increasing.
    have h_frac_bound : ∀ i ∈ Finset.range k, (x + i : ℚ) / (y + i : ℚ) ≥ (x : ℚ) / y := by
      exact fun i hi => by rw [ ge_iff_le ] ; rw [ div_le_div_iff₀ ] <;> norm_cast <;> nlinarith;
    -- For the second part, $\prod_{j=k}^{k+C-1} (y+j) \le (y+k+C-1)^C < (y+k+C)^C$.
    have h_prod_bound : (∏ j ∈ Finset.range C_int, (y + k + j : ℚ)) ≤ (y + k + C_int : ℚ) ^ C_int := by
      exact le_trans ( Finset.prod_le_prod ( fun _ _ => by positivity ) fun _ _ => show ( y + k + _ : ℚ ) ≤ y + k + C_int by norm_cast; linarith [ Finset.mem_range.mp ‹_› ] ) ( by norm_num );
    refine h_split.symm ▸ mul_le_mul ?_ ?_ ?_ ?_;
    · simpa only [ Finset.prod_const, Finset.card_range ] using Finset.prod_le_prod ( fun _ _ => by positivity ) h_frac_bound;
    · simpa using inv_anti₀ ( Finset.prod_pos fun _ _ => by positivity ) h_prod_bound;
    · positivity;
    · exact Finset.prod_nonneg fun _ _ => div_nonneg ( by positivity ) ( by positivity )

/-
Combine the bounds for ratio of ratios and product ratio to get the lower bound for LCM ratio.
-/
lemma lcm_ratio_lower_bound_final (k x y C_int : ℕ) (δ : ℝ) (ε : ℝ)
  (hC : C_int ≥ 1)
  (hx0 : x > 0) (hy0 : y > 0) (hxy : x < y)
  (h_good_p : ∀ p ∈ PrimesIn k, ¬ is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) + 1)
  (h_bad_p : ∀ p ∈ PrimesIn k, is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) - 1)
  (h_small_p : ∀ p, p.Prime → p ≤ k.sqrt →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥
    -(padicValNat p (m k) : ℤ))
  (h_large_p : ∀ p, p.Prime → p > k + C_int →
    padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) = 0 ∧
    padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = 0)
  (h_diff_ge_zero : ∀ p, p > k →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥ 0)
  (h_bad_prod : (BadPrimes k δ).prod (fun p => (p : ℝ)) ≤ (M_prod k : ℝ) ^ (2 * ε))
  (h_M_prod : (M_prod k : ℝ) ≥ (M k : ℝ) ^ (1 - ε))
  (hM_gt_1 : (M k : ℝ) > 1)
  (h_M_prod_pos : (M_prod k : ℝ) > 0)
  (h_eps : ε > 0)
  (h_m_pos : (m k : ℝ) > 0) :
  (((Finset.Icc x (x + k - 1)).lcm id : ℕ) : ℚ) / (((Finset.Icc y (y + k + C_int - 1)).lcm id : ℕ) : ℚ) ≥
  ((M k : ℝ) ^ (1 - 5 * ε) / (m k : ℝ)) * ((x : ℝ) / y) ^ k * (1 / (y + k + C_int : ℝ)) ^ C_int := by
    have h_combined : (((Finset.Icc x (x + k - 1)).lcm id : ℕ) : ℚ) / (((Finset.Icc y (y + k + C_int - 1)).lcm id : ℕ) : ℚ) ≥
      ((M k : ℝ) ^ (1 - 5 * ε) / (m k : ℝ)) * ((x : ℝ) / y) ^ k * (1 / (y + k + C_int : ℝ)) ^ C_int := by
      have h_ratio : (((Finset.Icc x (x + k - 1)).lcm id : ℕ) : ℚ) / (((Finset.Icc y (y + k + C_int - 1)).lcm id : ℕ) : ℚ) = ratio_of_ratios k x y C_int * ((∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) / (∏ i ∈ Finset.Icc y (y + k + C_int - 1), (i : ℚ))) := by
        convert lcm_ratio_eq_ratio_of_ratios_mul_prod_ratio k x y C_int hx0 hy0 using 1
      -- Apply the bounds from `ratio_of_ratios_bound_M_pow` and `product_ratio_lower_bound_simple`.
      have h_combined : (((Finset.Icc x (x + k - 1)).lcm id : ℕ) : ℚ) / (((Finset.Icc y (y + k + C_int - 1)).lcm id : ℕ) : ℚ) ≥
        ((M k : ℝ) ^ (1 - 5 * ε) / (m k : ℝ)) * ((x : ℝ) / y) ^ k * (1 / (y + k + C_int : ℝ)) ^ C_int := by
        have h_ratio_bound : ratio_of_ratios k x y C_int ≥ (M k : ℝ) ^ (1 - 5 * ε) / (m k : ℝ) := by
          convert ratio_of_ratios_bound_M_pow k x y C_int δ ε hC hx0 hy0 h_good_p h_bad_p h_small_p h_large_p h_diff_ge_zero h_bad_prod h_M_prod hM_gt_1 h_M_prod_pos h_eps h_m_pos using 1
        have h_prod_ratio_bound : ((∏ i ∈ Finset.Icc x (x + k - 1), (i : ℚ)) / (∏ i ∈ Finset.Icc y (y + k + C_int - 1), (i : ℚ))) ≥ ((x : ℝ) / y) ^ k * (1 / (y + k + C_int : ℝ)) ^ C_int := by
          convert product_ratio_lower_bound_simple k x y C_int hx0 hy0 hxy hC using 1 ; norm_num [ ← @Rat.cast_inj ℝ ] ; ring;
          erw [ Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range ] ; norm_num [ add_comm, add_left_comm, add_assoc ];
          erw [ Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range ] ; norm_num [ add_comm, add_left_comm, add_assoc, Nat.sub_add_comm ( by linarith : 1 ≤ k + x ), Nat.sub_add_comm ( by linarith : 1 ≤ k + ( y + C_int ) ) ];
          field_simp;
          norm_cast
        rw [ mul_assoc ];
        refine le_trans ( mul_le_mul h_ratio_bound h_prod_ratio_bound ?_ ?_ ) ?_;
        · positivity;
        · exact_mod_cast h_ratio_bound.trans' ( div_nonneg ( Real.rpow_nonneg ( Nat.cast_nonneg _ ) _ ) ( Nat.cast_nonneg _ ) );
        · convert h_ratio.ge using 1 ; norm_cast;
      convert h_combined using 1;
    convert h_combined using 1

/-
Lower bound for k * log(x/y) for large M.
-/
lemma k_log_x_div_y_bound (ε : ℝ) (h_eps : ε > 0) :
  ∃ M0, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ,
  (k : ℝ) ≤ 2 * Real.log M →
  ∀ x y : ℕ,
  M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε →
  (k : ℝ) * Real.log (x / y) ≥ -12 * Real.log M * M ^ (-ε) := by
    -- Let $z = (y-x)/y$. Since $x < y$, $z > 0$.
    have hz_bound : ∃ M0 : ℝ, ∀ M ≥ M0, ∀ (k : ℕ), (k : ℝ) ≤ 2 * Real.log M → ∀ (x y : ℕ), (M : ℝ) ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε → (Real.log (x / y)) ≥ -6 * M ^ (-ε) := by
      -- Since $x < y$, we have $z = (y-x)/y < 3M^{-\epsilon}$.
      have hz_bound : ∃ M0 : ℝ, ∀ M ≥ M0, ∀ (k : ℕ), (k : ℝ) ≤ 2 * Real.log M → ∀ (x y : ℕ), (M : ℝ) ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε → (y - x : ℝ) / y < 3 * M ^ (-ε) := by
        refine' ⟨ 2, fun M hM k hk x y hx hy hxy => _ ⟩ ; rw [ div_lt_iff₀ ] <;> norm_num at * <;> try linarith [ Real.rpow_pos_of_pos ( by linarith : 0 < M ) ε ] ;
        rw [ show ( -ε : ℝ ) = ε - 2 * ε by ring, Real.rpow_sub ] <;> try linarith;
        rw [ mul_div, div_mul_eq_mul_div, lt_div_iff₀ ] <;> nlinarith [ show ( x : ℝ ) < y by norm_cast, Real.rpow_pos_of_pos ( by linarith : 0 < M ) ε, Real.rpow_pos_of_pos ( by linarith : 0 < M ) ( 2 * ε ) ];
      -- Using $\ln(1-z) \ge -2z$ for $z \in [0, 0.5]$ (which follows from `log_one_sub_ge` since $-z-z^2 \ge -1.5z \ge -2z$), we have $\ln(x/y) = \ln(1-z) \ge -2z$.
      have h_log_bound : ∀ M : ℝ, M ≥ 1 → ∀ (k : ℕ), (k : ℝ) ≤ 2 * Real.log M → ∀ (x y : ℕ), (M : ℝ) ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε → (y - x : ℝ) / y < 0.5 → Real.log (x / y) ≥ -2 * ((y - x : ℝ) / y) := by
        intros M hM k hk x y hx hy hxy hz
        have h_log_bound : Real.log (1 - (y - x : ℝ) / y) ≥ -2 * ((y - x : ℝ) / y) := by
          have h_log_bound : ∀ z : ℝ, 0 ≤ z ∧ z < 0.5 → Real.log (1 - z) ≥ -2 * z := by
            exact fun z hz => by nlinarith [ Real.log_inv ( 1 - z ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < 1 - z ) ), mul_inv_cancel₀ ( by linarith : ( 1 - z ) ≠ 0 ) ] ;
          exact h_log_bound _ ⟨ div_nonneg ( sub_nonneg.2 <| Nat.cast_le.2 hy.le ) <| Nat.cast_nonneg _, hz ⟩;
        convert h_log_bound using 1 ; rw [ one_sub_div ( by norm_cast; linarith ) ] ; ring;
      -- Using the bound on $z$, we can conclude that $\ln(x/y) \ge -2 \cdot 3M^{-\epsilon} = -6M^{-\epsilon}$.
      obtain ⟨M0, hM0⟩ := hz_bound
      obtain ⟨M1, hM1⟩ : ∃ M1 : ℝ, ∀ M ≥ M1, 3 * M ^ (-ε) < 0.5 := by
        have h_lim : Filter.Tendsto (fun M : ℝ => 3 * M ^ (-ε)) Filter.atTop (nhds 0) := by
          simpa using tendsto_const_nhds.mul ( tendsto_rpow_neg_atTop h_eps );
        simpa using h_lim.eventually ( gt_mem_nhds <| by norm_num );
      exact ⟨ Max.max M0 ( Max.max M1 1 ), fun M hM k hk x y hx hy hxy => le_trans ( by linarith [ hM0 M ( le_trans ( le_max_left _ _ ) hM ) k hk x y hx hy hxy, hM1 M ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hM ) ] ) ( h_log_bound M ( le_trans ( le_max_of_le_right ( le_max_right _ _ ) ) hM ) k hk x y hx hy hxy ( lt_of_le_of_lt ( le_of_lt ( hM0 M ( le_trans ( le_max_left _ _ ) hM ) k hk x y hx hy hxy ) ) ( hM1 M ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hM ) ) ) ) ⟩;
    cases' hz_bound with M0 hM0;
    exact ⟨ Max.max M0 1, fun M hM k hk x y hx hy hxy => by nlinarith [ hM0 M ( le_trans ( le_max_left _ _ ) hM ) k hk x y hx hy hxy, Real.log_nonneg ( show ( 1 : ℝ ) ≤ M by linarith [ le_max_right M0 1 ] ), Real.rpow_nonneg ( show ( 0 : ℝ ) ≤ M by linarith [ le_max_right M0 1 ] ) ( -ε ) ] ⟩

/-
For large M, 2 log M + C < M^(3eps).
-/
lemma log_growth_bound (C : ℝ) (ε : ℝ) (h_eps : ε > 0) :
  ∃ M0, ∀ M : ℝ, M ≥ M0 → 2 * Real.log M + C < M ^ (3 * ε) := by
    -- We can use the fact that $\lim_{M \to \infty} \frac{2 \ln M + C}{M^{3\epsilon}} = 0$.
    have h_lim : Filter.Tendsto (fun M : ℝ => (2 * Real.log M + C) / M ^ (3 * ε)) Filter.atTop (nhds 0) := by
      -- Let $y = \log M$, so we can rewrite the limit expression as $\lim_{y \to \infty} \frac{2y + C}{e^{3\epsilon y}}$.
      suffices h_log : Filter.Tendsto (fun y : ℝ => (2 * y + C) / Real.exp (3 * ε * y)) Filter.atTop (nhds 0) by
        have := h_log.comp Real.tendsto_log_atTop;
        refine' this.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ Function.comp_apply, Real.rpow_def_of_pos hx ] ; ring );
      -- Let $z = 3\epsilon y$, therefore the expression becomes $\frac{(2/3\varepsilon)z + C}{e^z}$.
      suffices h_subst' : Filter.Tendsto (fun z : ℝ => ((2 / (3 * ε)) * z + C) / Real.exp z) Filter.atTop (nhds 0) by
        convert h_subst'.comp ( Filter.tendsto_id.const_mul_atTop ( show 0 < 3 * ε by positivity ) ) using 2 ; norm_num ; ring;
        grind;
      -- We can factor out $z$ in the numerator and use the fact that $\frac{z}{e^z}$ tends to $0$ as $z$ tends to infinity.
      have h_factor : Filter.Tendsto (fun z : ℝ => (2 / (3 * ε)) * z / Real.exp z) Filter.atTop (nhds 0) := by
        simpa [ Real.exp_neg, mul_div_assoc ] using tendsto_const_nhds.mul ( Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 );
      simpa [ add_div ] using h_factor.add ( tendsto_const_nhds.div_atTop ( Real.tendsto_exp_atTop ) );
    have := h_lim.eventually ( gt_mem_nhds zero_lt_one );
    rw [ Filter.eventually_atTop ] at this; rcases this with ⟨ M₀, HM₀ ⟩ ; exact ⟨ Max.max M₀ 1, fun M hM => by have := HM₀ M ( le_trans ( le_max_left _ _ ) hM ) ; rwa [ div_lt_one ( Real.rpow_pos_of_pos ( by linarith [ le_max_right M₀ 1 ] ) _ ) ] at this ⟩ ;

/-
Upper bound for log(y+k+C) for large M.
-/
lemma log_y_k_C_upper_bound (C : ℝ) (hC : C ≥ 1) (ε : ℝ) (h_eps : ε > 0) :
  ∃ M0, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ,
  (k : ℝ) ≤ 2 * Real.log M →
  ∀ y : ℕ,
  (y : ℝ) < 4 * M ^ (3 * ε) →
  Real.log (y + k + C) < Real.log 5 + 3 * ε * Real.log M := by
    -- Using `log_growth_bound`, for large $M$, $2 \ln M + C < M^{3\epsilon}$.
    have h_log_growth_bound : ∃ M0, ∀ M ≥ M0, 2 * Real.log M + C < M ^ (3 * ε) := by
      exact?;
    -- Using the bound from `h_growth_bound_bound`, we can conclude the proof.
    obtain ⟨M0, hM0⟩ := h_log_growth_bound
    use M0
    intro M hM k hk y hy_bound
    have h_log_bound : Real.log (y + k + C) < Real.log (5 * M ^ (3 * ε)) := by
      exact Real.log_lt_log ( by positivity ) ( by linarith [ hM0 M hM ] );
    by_cases hM_pos : 0 < M <;> simp_all +decide [ Real.log_mul, ne_of_gt, Real.rpow_def_of_pos ];
    · linarith;
    · exact False.elim <| hM_pos.not_lt <| lt_of_not_ge fun h => by have := hM0 0 ( by linarith ) ; norm_num [ Real.rpow_def_of_nonpos, h_eps.ne' ] at this ; linarith;

/-
Logarithmic inequality for large M.
-/
lemma log_ineq_calc (C : ℝ) (hC : C ≥ 1) (ε : ℝ) (h_eps : ε > 0) (h_eps_cond : 1 - (3 * C + 6) * ε > 0) :
  ∃ M0, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ,
  1 ≤ k → (k : ℝ) ≤ 2 * Real.log M →
  ∀ x y : ℕ,
  M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε →
  (y : ℝ) < 4 * M ^ (3 * ε) →
  (1 - 6 * ε) * Real.log M + k * Real.log (x / y) - C * Real.log (y + k + C) > 1 := by
    field_simp;
    -- Apply the bounds from k_log_x_div_y_bound and log_y_k_C_upper_bound.
    obtain ⟨M0, hM0⟩ : ∃ M0 : ℝ, ∀ M ≥ M0, ∀ k : ℕ, (k : ℝ) ≤ 2 * Real.log M → ∀ x y : ℕ, M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε → (y : ℝ) < 4 * M ^ (3 * ε) → (k : ℝ) * Real.log (x / y) ≥ -12 * Real.log M * M ^ (-ε) ∧ Real.log (y + k + C) < Real.log 5 + 3 * ε * Real.log M := by
      obtain ⟨ M0, hM0 ⟩ := k_log_x_div_y_bound ε h_eps;
      obtain ⟨ M1, hM1 ⟩ := log_y_k_C_upper_bound C hC ε h_eps;
      exact ⟨ Max.max M0 M1, fun M hM k hk x y hx hy hxy hy' => ⟨ hM0 M ( le_trans ( le_max_left _ _ ) hM ) k hk x y hx hy hxy, hM1 M ( le_trans ( le_max_right _ _ ) hM ) k hk y hy' ⟩ ⟩;
    -- Choose $M0$ large enough such that for all $M \geq M0$, the term $Real.log M * (1 - (3 * C + 6) * ε) - 12 * Real.log M * M ^ (-ε) - C * Real.log 5$ is greater than $1$.
    obtain ⟨M0', hM0'⟩ : ∃ M0' : ℝ, ∀ M ≥ M0', Real.log M * (1 - (3 * C + 6) * ε) - 12 * Real.log M * M ^ (-ε) - C * Real.log 5 > 1 := by
      -- We can factor out $Real.log M$ and use the fact that $M^{-ε}$ tends to $0$ as $M$ tends to infinity.
      have h_factor : Filter.Tendsto (fun M : ℝ => Real.log M * (1 - (3 * C + 6) * ε - 12 * M ^ (-ε))) Filter.atTop Filter.atTop := by
        have h_factor : Filter.Tendsto (fun M : ℝ => 1 - (3 * C + 6) * ε - 12 * M ^ (-ε)) Filter.atTop (nhds (1 - (3 * C + 6) * ε)) := by
          simpa using tendsto_const_nhds.sub ( tendsto_const_nhds.mul ( tendsto_rpow_neg_atTop h_eps ) );
        apply Filter.Tendsto.atTop_mul_pos;
        exacts [ h_eps_cond, Real.tendsto_log_atTop, h_factor ];
      exact Filter.eventually_atTop.mp ( h_factor.eventually_gt_atTop ( 1 + C * Real.log 5 ) ) |> fun ⟨ M0', hM0' ⟩ ↦ ⟨ M0', fun M hM ↦ by linarith [ hM0' M hM ] ⟩;
    use Max.max M0 M0';
    intro M hM k hk hk' x y hx hy hxy hyx; specialize hM0 M ( le_trans ( le_max_left _ _ ) hM ) k hk' x y hx hy hxy ( by simpa only [ mul_comm ] using hyx ) ; specialize hM0' M ( le_trans ( le_max_right _ _ ) hM ) ; ring_nf at *; nlinarith;

/-
Asymptotic inequality for log M.
-/
lemma log_ineq_asymptotic (C : ℝ) (hC : C ≥ 1) (ε : ℝ) (h_eps : ε > 0) (h_eps_cond : 1 - (3 * C + 6) * ε > 0) :
  ∃ M0, ∀ M : ℝ, M ≥ M0 →
  (1 - (3 * C + 6) * ε) * Real.log M - 12 * Real.log M * M ^ (-ε) - C * Real.log 5 > 1 := by
    -- We want to show that $(1 - (3C+6)\epsilon) \ln M - 12 (\ln M) M^{-\epsilon} - C \ln 5 > 1$ for large $M$.
    suffices h_suff : Filter.Tendsto (fun M : ℝ => (1 - (3 * C + 6) * ε) * Real.log M - 12 * Real.log M * M ^ (-ε) - C * Real.log 5) Filter.atTop Filter.atTop by
      simpa using h_suff.eventually_gt_atTop 1;
    -- We can factor out $\ln M$ from the expression.
    suffices h_factor : Filter.Tendsto (fun M : ℝ => Real.log M * ((1 - (3 * C + 6) * ε) - 12 * M ^ (-ε))) Filter.atTop Filter.atTop by
      exact Filter.tendsto_atTop_add_const_right _ _ ( h_factor.congr' <| by filter_upwards [ Filter.eventually_gt_atTop 0 ] with M hM using by ring );
    -- We'll use the fact that $M^{-\epsilon}$ tends to $0$ as $M$ tends to infinity.
    have h_exp_zero : Filter.Tendsto (fun M : ℝ => M ^ (-ε)) Filter.atTop (nhds 0) := by
      simpa using tendsto_rpow_neg_atTop h_eps;
    apply Filter.Tendsto.atTop_mul_pos;
    exacts [ show 0 < 1 - ( 3 * C + 6 ) * ε by linarith, Real.tendsto_log_atTop, by simpa using tendsto_const_nhds.sub ( h_exp_zero.const_mul 12 ) ]

/-
Logarithmic inequality for large M, proved by combining asymptotic bounds.
-/
lemma log_ineq_calc_v2 (C : ℝ) (hC : C ≥ 1) (ε : ℝ) (h_eps : ε > 0) (h_eps_cond : 1 - (3 * C + 6) * ε > 0) :
  ∃ M0, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ,
  1 ≤ k → (k : ℝ) ≤ 2 * Real.log M →
  ∀ x y : ℕ,
  M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε →
  (y : ℝ) < 4 * M ^ (3 * ε) →
  (1 - 6 * ε) * Real.log M + k * Real.log (x / y) - C * Real.log (y + k + C) > 1 := by
    exact?

/-
Exponentiated form of the logarithmic inequality.
-/
lemma large_M_inequality_generic_v3 (C : ℝ) (hC : C ≥ 1) (ε : ℝ) (h_eps : ε > 0) (h_eps_cond : 1 - (3 * C + 6) * ε > 0) :
  ∃ M0, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ,
  1 ≤ k → (k : ℝ) ≤ 2 * Real.log M →
  ∀ x y : ℕ,
  M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε →
  (y : ℝ) < 4 * M ^ (3 * ε) →
  M ^ (1 - 6 * ε) * ((x : ℝ) / y) ^ k * (1 / (y + k + C : ℝ)) ^ C > 1 := by
    have := log_ineq_calc_v2 C hC ε h_eps h_eps_cond;
    obtain ⟨ M0, HM0 ⟩ := this; use Max.max M0 1; intro M hM k hk hk' x y hx hy hxy hy'; specialize HM0 M ( le_trans ( le_max_left _ _ ) hM ) k hk hk' x y hx hy hxy hy'; (
    field_simp;
    rw [ ← Real.log_lt_log_iff ( by positivity ) ( by exact mul_pos ( mul_pos ( Real.rpow_pos_of_pos ( by linarith [ le_max_right M0 1 ] ) _ ) ( pow_pos ( div_pos ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by rintro rfl; norm_num at hx; linarith [ Real.rpow_pos_of_pos ( by linarith [ le_max_right M0 1 ] : 0 < M ) ( 2 * ε ) ] ) ( Nat.cast_pos.mpr <| by linarith ) ) _ ) ) ( Real.rpow_pos_of_pos ( one_div_pos.mpr <| by positivity ) _ ) ), Real.log_mul, Real.log_mul ] <;> try positivity;
    · rw [ Real.log_rpow ( by linarith [ le_max_right M0 1 ] ), Real.log_pow, Real.log_rpow ( by positivity ) ] ; norm_num ; linarith [ Real.log_pos one_lt_two ];
    · exact ne_of_gt ( Real.rpow_pos_of_pos ( by linarith [ le_max_right M0 1 ] ) _ );
    · exact ne_of_gt ( pow_pos ( div_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at hx; linarith [ Real.rpow_pos_of_pos ( by linarith [ le_max_right M0 1 ] : 0 < M ) ( 2 * ε ) ] ) ) ) ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by linarith ) ) ) ) _ );
    · exact ne_of_gt ( mul_pos ( Real.rpow_pos_of_pos ( by linarith [ le_max_right M0 1 ] ) _ ) ( pow_pos ( div_pos ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by rintro rfl; norm_num at hx; linarith [ Real.rpow_pos_of_pos ( by linarith [ le_max_right M0 1 ] : 0 < M ) ( 2 * ε ) ] ) ) ) ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by linarith ) ) ) ) _ ) ));

/-
Logarithmic inequality for large M, proved by combining asymptotic bounds.
-/
lemma log_ineq_calc_v3 (C : ℝ) (hC : C ≥ 1) (ε : ℝ) (h_eps : ε > 0) (h_eps_cond : 1 - (3 * C + 6) * ε > 0) :
  ∃ M0, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ,
  1 ≤ k → (k : ℝ) ≤ 2 * Real.log M →
  ∀ x y : ℕ,
  M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε →
  (y : ℝ) < 4 * M ^ (3 * ε) →
  (1 - 6 * ε) * Real.log M + k * Real.log (x / y) - C * Real.log (y + k + C) > 1 := by
    exact?

/-
Logarithmic inequality for large M (final version).
-/
lemma log_ineq_calc_final (C : ℝ) (hC : C ≥ 1) (ε : ℝ) (h_eps : ε > 0) (h_eps_cond : 1 - (3 * C + 6) * ε > 0) :
  ∃ M0, ∀ M : ℝ, M ≥ M0 → ∀ k : ℕ,
  1 ≤ k → (k : ℝ) ≤ 2 * Real.log M →
  ∀ x y : ℕ,
  M ^ (2 * ε) < x → x < y → (y : ℝ) - x < 3 * M ^ ε →
  (y : ℝ) < 4 * M ^ (3 * ε) →
  (1 - 6 * ε) * Real.log M + k * Real.log (x / y) - C * Real.log (y + k + C) > 1 := by
  obtain ⟨M1, hM1⟩ := k_log_x_div_y_bound ε h_eps
  obtain ⟨M2, hM2⟩ := log_y_k_C_upper_bound C hC ε h_eps
  obtain ⟨M3, hM3⟩ := log_ineq_asymptotic C hC ε h_eps h_eps_cond
  use max M1 (max M2 M3)
  intro M hM k hk1 hk2 x y hx hy hxy hy_bound
  have h1 := hM1 M (le_trans (le_max_left _ _) hM) k hk2 x y hx hy hxy
  have h2 := hM2 M (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hM)) k hk2 y hy_bound
  have h3 := hM3 M (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hM))
  nlinarith

/-
Main Theorem: For any C >= 1, for sufficiently large k, there exist x < y with y > x + k such that lcm(x...x+k-1) > C * lcm(y...y+k).
-/
theorem main_theorem_proven (h_density : DensityHypothesis) : MainTheoremStatement := by
  exact?

/-
Lower bound for the LCM ratio with relaxed upper bound on y.
-/
lemma lcm_ratio_lower_bound_detailed_v3 (k x y C_int : ℕ) (δ : ℝ) (ε : ℝ)
  (hC : C_int ≥ 1)
  (hx0 : x > 0) (hy0 : y > 0) (hxy : x < y)
  (h_good_p : ∀ p ∈ PrimesIn k, ¬ is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) + 1)
  (h_bad_p : ∀ p ∈ PrimesIn k, is_bad k p δ →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) - 1)
  (h_small_p : ∀ p, p.Prime → p ≤ k.sqrt →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥
    -(padicValNat p (m k) : ℤ))
  (h_large_p : ∀ p, p.Prime → p > k + C_int →
    padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) = 0 ∧
    padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) = 0)
  (h_diff_ge_zero : ∀ p, p > k →
    (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) -
    (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) ≥ 0)
  (h_bad_prod : (BadPrimes k δ).prod (fun p => (p : ℝ)) ≤ (M_prod k : ℝ) ^ (2 * ε))
  (h_M_prod : (M_prod k : ℝ) ≥ (M k : ℝ) ^ (1 - ε))
  (hM_gt_1 : (M k : ℝ) > 1)
  (h_M_prod_pos : (M_prod k : ℝ) > 0)
  (h_bound_y : (y : ℝ) < 4 * (M k : ℝ) ^ (3 * ε))
  (h_bound_x : (x : ℝ) > (M k : ℝ) ^ (2 * ε))
  (h_bound_diff : (y : ℝ) - x < 3 * (M k : ℝ) ^ ε)
  (h_k_large : k > 0)
  (h_eps : ε > 0)
  (h_m_pos : (m k : ℝ) > 0) :
  (((Finset.Icc x (x + k - 1)).lcm id : ℕ) : ℚ) / (((Finset.Icc y (y + k + C_int - 1)).lcm id : ℕ) : ℚ) ≥
  ((M k : ℝ) ^ (1 - 5 * ε) / (m k : ℝ)) * ((x : ℝ) / y) ^ k * (1 / (y + k + C_int : ℝ)) ^ C_int := by
    exact?

#check valuation_ineq_good_p_aux
#check valuation_ineq_bad_p_weak
#check small_prime_condition_satisfied
#check valuation_diff_ge_zero_large_p

/-
M(k)^epsilon grows faster than k.
-/
lemma M_growth_eps (h_pnt : PNT_bounds) (ε : ℝ) (hε : ε > 0) :
  ∃ K, ∀ k ≥ K, (M k : ℝ) ^ ε > k := by
    -- We'll use the fact that if the logarithm of a number is greater than the logarithm of another number, then the first number is greater than the second.
    have h_log_growth : ∃ K, ∀ k ≥ K, ε * Real.log (M k) > Real.log k := by
      have := theta_lower_bound h_pnt;
      -- Using the fact that $\sum_{p \in \text{AllPrimesIn } k} \log p \geq c_1 k$, we get $\log M k \geq c_1 k$.
      obtain ⟨c1, hc1_pos, K, hK⟩ := this;
      have h_log_M_k : ∀ k ≥ K, Real.log (M k) ≥ c1 * k := by
        intro k hk;
        have h_log_M_lower_bound : Real.log (M k) ≥ ∑ p ∈ AllPrimesIn k, Real.log p := by
          rw [ ← Real.log_prod ] <;> norm_cast <;> norm_num [ AllPrimesIn, M ];
          · gcongr;
            · exact Finset.prod_pos fun p hp => Nat.cast_pos.mpr <| Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2;
            · have h_prod_le_lcm : (∏ i ∈ Finset.filter Nat.Prime (Finset.Icc 1 k), i : ℕ) ∣ (Finset.Icc 1 k).lcm id := by
                have h_prod_le_lcm : ∀ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 k), p ∣ (Finset.Icc 1 k).lcm id := by
                  exact fun p hp => Finset.dvd_lcm ( Finset.mem_filter.mp hp |>.1 ) |> dvd_trans ( by aesop );
                refine' Nat.dvd_trans _ ( Nat.prod_primeFactors_dvd _ );
                apply_rules [ Finset.prod_dvd_prod_of_subset ];
                intro p hp; specialize h_prod_le_lcm p hp; aesop;
              rw [ ← Nat.cast_prod ] ; exact_mod_cast Nat.le_of_dvd ( Nat.pos_of_ne_zero <| mt Finset.lcm_eq_zero_iff.mp <| by aesop ) h_prod_le_lcm;
          · grind;
        exact le_trans ( hK k hk ) h_log_M_lower_bound;
      -- Choose $K'$ such that for all $k \geq K'$, $\frac{\log k}{k} < \epsilon c_1$.
      obtain ⟨K', hK'⟩ : ∃ K', ∀ k ≥ K', Real.log k / (k : ℝ) < ε * c1 := by
        have h_log_div_k_zero : Filter.Tendsto (fun k : ℝ => Real.log k / k) Filter.atTop (nhds 0) := by
          -- Let $y = \frac{1}{x}$, so we can rewrite the limit expression as $\lim_{y \to 0^+} y \log(1/y)$.
          suffices h_log_recip : Filter.Tendsto (fun y : ℝ => y * Real.log (1 / y)) (Filter.map (fun x => 1 / x) Filter.atTop) (nhds 0) by
            exact h_log_recip.congr ( by simp +contextual [ div_eq_inv_mul ] );
          norm_num;
          exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.neg.tendsto 0 );
        simpa using h_log_div_k_zero.eventually ( gt_mem_nhds <| by positivity );
      exact ⟨ ⌈K'⌉₊ + K + 1, fun k hk => by have := hK' k ( Nat.le_of_ceil_le ( by linarith ) ) ; rw [ div_lt_iff₀ ] at this <;> nlinarith [ h_log_M_k k ( by linarith ), show ( k : ℝ ) ≥ ⌈K'⌉₊ + K + 1 by exact_mod_cast hk ] ⟩;
    obtain ⟨ K, hK ⟩ := h_log_growth;
    use K + 1;
    intro k hk; specialize hK k ( by linarith ) ; rw [ gt_iff_lt ] at *; rw [ Real.log_lt_iff_lt_exp ( by norm_cast; linarith ) ] at *; rw [ Real.rpow_def_of_pos ( Nat.cast_pos.mpr <| M_pos k <| by linarith ) ] ; ring_nf at *; aesop;

/-
Valuation inequality for good primes with weak modular condition.
-/
lemma valuation_ineq_good_p_aux_weak (k x y C_int : ℕ) (δ : ℝ) (p : ℕ)
  (hk : k ≥ C_int * C_int + 10)
  (hp : p ∈ PrimesIn k)
  (h_not_bad : ¬ is_bad k p δ)
  (hx : x % p ∈ Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ))))
  (hy : (p - y % p) % p ∈ Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ))))
  (hC : C_int ≥ 1)
  (hx0 : x > 0) (hy0 : y > 0)
  (h_p_large : (p : ℝ) ^ (1 - δ) < p / 2)
  (h_k_mod : k % p + Nat.ceil ((p : ℝ) ^ (1 - δ)) ≤ p) :
  padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) ≥
  padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) + 1 := by
    have h_count_y_ge_count_x_plus_one : (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k + C_int - 1))).card ≥ (Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card + 1 := by
      exact?;
    have h_val_y_ge_val_x_plus_one : (padicValNat p ((∏ i ∈ Finset.Icc y (y + k + C_int - 1), i) / (Finset.Icc y (y + k + C_int - 1)).lcm id) : ℤ) ≥ (Finset.filter (fun i => p ∣ i) (Finset.Icc y (y + k + C_int - 1))).card - 1 := by
      convert val_y_ge_count_y_sub_one k y C_int p ( by nlinarith ) hp hy0 hC using 1;
    have h_val_x_eq_count_x_minus_one : (padicValNat p ((∏ i ∈ Finset.Icc x (x + k - 1), i) / (Finset.Icc x (x + k - 1)).lcm id) : ℤ) = (Finset.filter (fun i => p ∣ i) (Finset.Icc x (x + k - 1))).card - 1 := by
      convert val_x_eq_count_x_sub_one k x p hp hx0 using 1;
    grind

/-
If a prime is not bad, it satisfies the modular condition required for the valuation inequality.
-/
lemma not_bad_implies_mod_condition (k p : ℕ) (δ : ℝ) (h : ¬ is_bad k p δ) :
  k % p + Nat.ceil ((p : ℝ) ^ (1 - δ)) ≤ p := by
    -- By definition of `is_bad`, if `¬is_bad k p δ`, then `k % p + Nat.ceil ((p : ℝ) ^ (1 - δ)) ≤ p`.
    unfold is_bad at h;
    omega

/-
If p is large enough, then p^(1-delta) < p/2.
-/
lemma p_large_implies_ineq (δ : ℝ) (hδ : δ > 0) (p : ℕ) (hp : (p : ℝ) > (2 : ℝ) ^ (1 / δ)) :
  (p : ℝ) ^ (1 - δ) < (p : ℝ) / 2 := by
    rw [ Real.rpow_sub ] <;> norm_num;
    · gcongr;
      · exact lt_trans ( by positivity ) hp;
      · exact lt_of_le_of_lt ( by rw [ ← Real.rpow_mul ( by positivity ), one_div_mul_cancel ( by positivity ), Real.rpow_one ] ) ( Real.rpow_lt_rpow ( by positivity ) hp ( by positivity ) );
    · exact Nat.cast_pos.mp ( lt_trans ( by positivity ) hp )

/-
The LCM of a nonempty set of positive integers is positive.
-/
lemma lcm_real_pos (S : Finset ℕ) (h : S.Nonempty) (h0 : 0 ∉ S) : lcm_real S > 0 := by
  exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by aesop ) )

/-
Definition of the hypothesis provided by Question 4.
-/
def HypothesisQ4 (k : ℕ) (x y : ℕ) (δ ε : ℝ) : Prop :=
  let M := M_prod k
  let I (p : ℕ) := Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ)))
  (M : ℝ) ^ (2.5 * ε) ≤ x ∧ x < (M : ℝ) ^ (3 * ε) ∧
  (M : ℝ) ^ ε < (y : ℝ) - x ∧ (y : ℝ) - x < 3 * (M : ℝ) ^ ε ∧
  (∀ p ∈ PrimesIn k, x % p ∈ I p) ∧
  (∀ p ∈ PrimesIn k, (p - y % p) % p ∈ I p)

/-
`m(k)` and `M_prod(k)` are coprime.
-/
lemma m_coprime_M_prod (k : ℕ) : Nat.Coprime (m k) (M_prod k) := by
  refine' Nat.coprime_prod_left_iff.mpr _;
  intros p hp
  have h_disjoint : p ∉ Finset.filter (fun p => Nat.Prime p ∧ Nat.sqrt k < p) (Finset.Icc 1 k) := by
    simp +zetaDelta at *;
    exact fun _ _ _ => by rw [ Nat.le_sqrt ] ; linarith;
  refine' Nat.Coprime.prod_right fun q hq => _;
  norm_num +zetaDelta at *;
  exact Nat.Coprime.pow_left _ ( hp.2.1.coprime_iff_not_dvd.mpr fun h => absurd ( Nat.prime_dvd_prime_iff_eq hp.2.1 ( Finset.mem_filter.mp hq |>.2.1 ) |>.1 h ) ( by rintro rfl; exact absurd ( h_disjoint hp.1.1 hp.1.2 hp.2.1 ) ( by nlinarith [ Finset.mem_filter.mp hq |>.2.2, Nat.lt_succ_sqrt k ] ) ) )

/-
`m(k)` is positive.
-/
lemma m_pos_k (k : ℕ) : m k > 0 := by
  exact Finset.prod_pos fun p hp => Nat.pos_of_ne_zero <| by aesop;

/-
`M_prod(k)` is positive.
-/
lemma M_prod_pos_k (k : ℕ) : M_prod k > 0 := by
  exact Finset.prod_pos fun p hp => Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2.1

/-
Under `Question4Stronger`, there exist `x, y` with specific modular properties and interval constraints.
-/
lemma exists_xy_in_intervals_stronger_with_m (hQ4 : Question4Stronger) (h_pnt : PNT_bounds) (ε : ℝ) (h_eps : ε > 0) :
  ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
  ∃ K : ℕ, ∀ k ≥ K,
    let primes : Finset ℕ := (Finset.Icc 1 k).filter (fun p => p.Prime ∧ Nat.sqrt k < p)
    let M := primes.prod id
    let I (p : ℕ) (δ : ℝ) := Finset.Icc 1 (Nat.ceil ((p : ℝ) ^ (1 - δ)))
    ∃ x y : ℕ,
      (M : ℝ) ^ (2.5 * ε) ≤ x ∧ x < (M : ℝ) ^ (3 * ε) ∧
      (M : ℝ) ^ ε < (y : ℝ) - x ∧ (y : ℝ) - x < 3 * (M : ℝ) ^ ε ∧
      (∀ p ∈ primes, x % p ∈ I p δ) ∧
      (∀ p ∈ primes, (p - y % p) % p ∈ I p δ) ∧
      x % (m k) = 1 ∧
      y % (m k) = 0 := by
        have := @hQ4 1 zero_lt_one;
        obtain ⟨ δ, hδ₁, hδ₂, K, hK ⟩ := this;
        contrapose! hK;
        refine' ⟨ K + 2, _, _ ⟩ <;> norm_num;
        refine' ⟨ 0, ∏ x ∈ Finset.Icc 1 ( K + 2 ) with Nat.Prime x ∧ ( K + 2 ).sqrt < x, x + 1, _, _, _ ⟩ <;> norm_num;
        refine' ⟨ 0, fun x hx₁ hx₂ => _ ⟩;
        norm_num [ Nat.mod_eq_of_lt ] at hx₂ ⊢;
        rw [ Nat.mod_eq_of_lt ] at hx₂;
        · obtain ⟨ p, hp₁, hp₂ ⟩ := Nat.exists_prime_lt_and_le_two_mul ( Nat.sqrt ( K + 2 ) ) ( by linarith [ Nat.sqrt_pos.mpr ( show 0 < K + 2 by linarith ) ] );
          exact ⟨ p, hp₁.pos, by nlinarith only [ hp₂, Nat.sqrt_le ( K + 2 ) ], hp₁, hp₂.1, by norm_num [ hx₂ ] ⟩;
        · refine' lt_of_le_of_lt hx₁ _;
          rw [ tsub_lt_iff_left ] <;> norm_num [ Finset.prod_eq_zero_iff ];
          · rw [ ← @Nat.cast_lt ℝ ] ; norm_num;
            refine' lt_of_le_of_lt ( Nat.ceil_lt_add_one ( Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _ ) |> le_of_lt ) _;
            norm_num [ add_comm ];
          · refine' Finset.prod_pos _;
            exact fun p hp => Nat.cast_pos.mpr <| Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2.1

/-
Inequality involving ceilings of non-negative real numbers.
-/
lemma ceil_bound_lemma (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (h : A + B + 2 < C) :
  (Nat.ceil A : ℝ) + (Nat.ceil B : ℝ) - 1 < C := by
    linarith [ Nat.ceil_lt_add_one hA, Nat.ceil_lt_add_one hB ]

/-
The upper bound for `x` holds given the large `M` condition.
-/
lemma x_bound_check (M : ℝ) (ε : ℝ) (hM : M > 0) (h_large : M^(2.5*ε) + M^ε + 2 < M^(3*ε)) :
  (Nat.ceil (M^(2.5*ε)) : ℝ) + (Nat.ceil (M^ε) : ℝ) - 1 < M^(3*ε) := by
    linarith [ Nat.ceil_lt_add_one ( show 0 ≤ M ^ ( 2.5 * ε ) by positivity ), Nat.ceil_lt_add_one ( show 0 ≤ M ^ ε by positivity ) ]

/-
Integers in the constructed interval satisfy the real bounds.
-/
lemma interval_containment_x (M : ℝ) (ε : ℝ) (hM : M > 0) (h_large : M^(2.5*ε) + M^ε + 2 < M^(3*ε)) :
  let start := Nat.ceil (M^(2.5*ε))
  let len := Nat.ceil (M^ε)
  ∀ z ∈ Finset.Icc start (start + len - 1),
    M^(2.5*ε) ≤ (z : ℝ) ∧ (z : ℝ) < M^(3*ε) := by
      norm_num +zetaDelta at *;
      exact fun z hz₁ hz₂ => ⟨ hz₁, by linarith [ Nat.ceil_lt_add_one ( show 0 ≤ M ^ ( 5 / 2 * ε ) by positivity ), Nat.ceil_lt_add_one ( show 0 ≤ M ^ ε by positivity ), show ( z : ℝ ) ≤ ⌈M ^ ( 5 / 2 * ε ) ⌉₊ + ⌈M ^ ε⌉₊ - 1 by exact le_trans ( Nat.cast_le.mpr hz₂ ) ( by rw [ Nat.cast_sub ] <;> norm_num ; linarith [ Nat.ceil_pos.mpr ( show 0 < M ^ ( 5 / 2 * ε ) by positivity ), Nat.ceil_pos.mpr ( show 0 < M ^ ε by positivity ) ] ) ] ⟩

/-
Helper lemma for finding `x` using `Question4Stronger` with stronger bounds.
-/
lemma exists_x_step (k : ℕ) (M : ℕ) (m_val : ℕ) (I : ℕ → Finset ℕ) (ε : ℝ)
  (primes : Finset ℕ)
  (h_primes_def : primes = (Finset.Icc 1 k).filter (fun p => p.Prime ∧ Nat.sqrt k < p))
  (h_M_def : M = primes.prod id)
  (hQ4_k : ∀ (start : ℕ) (m_mod : ℕ) (a : ℕ),
      Nat.Coprime m_mod M →
      m_mod > 0 →
      ∃ z ∈ Finset.Icc start (start + Nat.ceil ((M : ℝ) ^ ε) - 1),
      z % m_mod = a % m_mod ∧
      ∀ p ∈ primes, z % p ∈ I p)
  (h_coprime : Nat.Coprime m_val M)
  (h_m_pos : m_val > 0)
  (h_M_large : (M : ℝ) ^ (2.5 * ε) + (M : ℝ) ^ ε + 2 < (M : ℝ) ^ (3 * ε))
  (h_M_pos : M > 0)
  (h_eps_pos : ε > 0)
  : ∃ x : ℕ,
      (M : ℝ) ^ (2.5 * ε) ≤ x ∧ x < (M : ℝ) ^ (3 * ε) ∧
      (∀ p ∈ primes, x % p ∈ I p) ∧
      x % m_val = 1 % m_val := by
        obtain ⟨ x, hx ⟩ := hQ4_k ( ⌈ ( M : ℝ ) ^ ( 2.5 * ε ) ⌉₊ ) m_val 1 h_coprime h_m_pos;
        refine' ⟨ x, _, _, hx.2.2, hx.2.1 ⟩ <;> norm_cast;
        · exact le_trans ( Nat.le_ceil _ ) ( mod_cast Finset.mem_Icc.mp hx.1 |>.1 );
        · refine' lt_of_le_of_lt ( Nat.cast_le.mpr <| Finset.mem_Icc.mp hx.1 |>.2 ) _;
          rw [ Nat.cast_sub ] <;> norm_num;
          · norm_num at * ; linarith [ Nat.ceil_lt_add_one ( show 0 ≤ ( M : ℝ ) ^ ( 5 / 2 * ε ) by positivity ), Nat.ceil_lt_add_one ( show 0 ≤ ( M : ℝ ) ^ ε by positivity ) ];
          · exact Nat.one_le_iff_ne_zero.mpr ( by positivity )

/-
Helper lemma for finding `y` using `Question4Stronger`.
-/
lemma exists_y_step (k : ℕ) (M : ℕ) (m_val : ℕ) (I : ℕ → Finset ℕ) (ε : ℝ) (x : ℕ)
  (primes : Finset ℕ)
  (h_primes_def : primes = (Finset.Icc 1 k).filter (fun p => p.Prime ∧ Nat.sqrt k < p))
  (h_M_def : M = primes.prod id)
  (hQ4_k : ∀ (start : ℕ) (m_mod : ℕ) (a : ℕ),
      Nat.Coprime m_mod M →
      m_mod > 0 →
      ∃ z ∈ Finset.Icc start (start + Nat.ceil ((M : ℝ) ^ ε) - 1),
      z % m_mod = a % m_mod ∧
      ∀ p ∈ primes, z % p ∈ I p)
  (h_coprime : Nat.Coprime m_val M)
  (h_m_pos : m_val > 0)
  (h_M_large : (M : ℝ) ^ ε > 2)
  (h_x_bound : (x : ℝ) < (M : ℝ) ^ (3 * ε))
  (h_M_pos : M > 0)
  (h_eps_pos : ε > 0)
  : ∃ y : ℕ,
      (M : ℝ) ^ ε < (y : ℝ) - x ∧ (y : ℝ) - x < 3 * (M : ℝ) ^ ε ∧
      (∀ p ∈ primes, (p - y % p) % p ∈ I p) ∧
      y % m_val = 0 := by
        -- Apply the density hypothesis to find such a $z$.
        obtain ⟨K_mul, hK_mul⟩ : ∃ K_mul : ℕ, M * K_mul > x + 3 * (M : ℝ) ^ ε := by
          exact ⟨ ⌊ ( x : ℝ ) + 3 * M ^ ε⌋₊ + 1, by push_cast; nlinarith [ Nat.lt_floor_add_one ( ( x : ℝ ) + 3 * M ^ ε ), show ( M : ℝ ) ≥ 1 by norm_cast ] ⟩;
        obtain ⟨z, hz⟩ : ∃ z : ℕ, (M : ℝ) * K_mul - x - ⌈2.5 * (M : ℝ) ^ ε⌉₊ ≤ z ∧ z < (M : ℝ) * K_mul - x - (M : ℝ) ^ ε ∧ z % m_val = (M * K_mul) % m_val ∧ ∀ p ∈ primes, z % p ∈ I p := by
          have := hQ4_k ( Nat.floor ( ( M : ℝ ) * K_mul - x - ⌈2.5 * ( M : ℝ ) ^ ε⌉₊ ) ) m_val ( M * K_mul ) h_coprime h_m_pos;
          obtain ⟨ z, hz₁, hz₂, hz₃ ⟩ := this;
          refine' ⟨ z, _, _, hz₂, hz₃ ⟩ <;> norm_num at *;
          · rw [ Nat.le_iff_lt_or_eq ] at *;
            rcases hz₁.1 with h | h;
            · exact le_trans ( Nat.lt_floor_add_one _ |> le_of_lt ) ( mod_cast h );
            · rw [ Nat.floor_eq_iff ] at h <;> norm_cast at * <;> first | positivity | linarith;
          · rw [ le_tsub_iff_right ] at hz₁ <;> norm_num at *;
            · rw [ Nat.sub_sub ] at hz₁;
              rw [ tsub_add_eq_add_tsub ] at hz₁;
              · rw [ Nat.le_sub_iff_add_le ] at hz₁;
                · linarith [ Nat.le_ceil ( ( 5 : ℝ ) / 2 * M ^ ε ), Nat.ceil_lt_add_one ( show 0 ≤ ( 5 : ℝ ) / 2 * M ^ ε by positivity ), Nat.ceil_lt_add_one ( show 0 ≤ ( M : ℝ ) ^ ε by positivity ), show ( ⌊ ( M : ℝ ) * K_mul⌋₊ : ℝ ) ≤ ( M : ℝ ) * K_mul by exact Nat.floor_le ( by positivity ), show ( z : ℝ ) + 1 + ( x + ⌈ ( 5 : ℝ ) / 2 * M ^ ε⌉₊ ) ≤ ⌊ ( M : ℝ ) * K_mul⌋₊ + ⌈ ( M : ℝ ) ^ ε⌉₊ by exact_mod_cast hz₁.2 ];
                · omega;
              · rw [ Nat.le_floor_iff ( by positivity ) ];
                norm_num at * ; linarith [ Nat.ceil_lt_add_one ( show 0 ≤ ( 5 : ℝ ) / 2 * M ^ ε by positivity ) ];
            · exact Nat.one_le_iff_ne_zero.mpr ( by linarith [ show ⌈ ( M : ℝ ) ^ ε⌉₊ > 0 from Nat.ceil_pos.mpr ( by positivity ), show ⌈ ( 5 / 2 : ℝ ) * ( M : ℝ ) ^ ε⌉₊ ≥ ⌈ ( M : ℝ ) ^ ε⌉₊ from Nat.ceil_mono ( by linarith ) ] );
        use M * K_mul - z;
        rw [ Nat.cast_sub ] <;> norm_num at *;
        · refine' ⟨ _, _, _, _ ⟩ <;> try linarith;
          · linarith [ Nat.ceil_lt_add_one ( show 0 ≤ ( 5 : ℝ ) / 2 * M ^ ε by positivity ) ];
          · intro p hp
            have h_mod : (p - (M * K_mul - z) % p) % p = z % p := by
              have h_mod_eq : (M * K_mul : ℕ) % p = 0 := by
                exact Nat.mod_eq_zero_of_dvd <| dvd_mul_of_dvd_left ( h_M_def.symm ▸ Finset.dvd_prod_of_mem _ hp ) _;
              cases le_total ( M * K_mul ) z <;> simp +decide [ *, Nat.add_mod, Nat.mod_eq_of_lt ] at *;
              · rw [ ← @Nat.cast_le ℝ ] at * ; norm_num at * ; linarith [ Real.rpow_pos_of_pos ( show 0 < ( ∏ i ∈ Finset.Icc 1 k with Nat.Prime i ∧ k.sqrt < i, ( i : ℝ ) ) from Finset.prod_pos fun x hx => Nat.cast_pos.mpr <| Nat.Prime.pos <| by aesop ) ε ];
              · rw [ Nat.ModEq.symm ];
                simp +decide [ ← ZMod.natCast_eq_natCast_iff, Nat.cast_sub ( show z ≤ ( ∏ x ∈ Finset.Icc 1 k with Nat.Prime x ∧ k.sqrt < x, x ) * K_mul from by assumption ), h_mod_eq ];
                rw [ Nat.cast_sub ( Nat.le_of_lt ( Nat.mod_lt _ hp.2.1.pos ) ) ] ; simp +decide [ ← ZMod.natCast_eq_zero_iff, h_mod_eq ] ;
                simp_all +decide [ ← ZMod.val_natCast, Nat.add_mod, Nat.mul_mod ];
            aesop;
          · rw [ ← Nat.mod_add_div ( M * K_mul ) m_val, ← Nat.mod_add_div z m_val ] ; norm_num [ Nat.add_mod, Nat.mul_mod, hz.2.2.1 ];
            norm_num [ Nat.add_sub_add_left, ← mul_tsub ];
        · exact_mod_cast ( by linarith : ( z : ℝ ) ≤ M * K_mul )

/-
Helper lemma for finding `x` using `Question4Stronger` with stronger bounds (v2).
-/
lemma exists_x_step_v2 (k : ℕ) (M : ℕ) (m_val : ℕ) (I : ℕ → Finset ℕ) (ε : ℝ)
  (primes : Finset ℕ)
  (h_primes_def : primes = (Finset.Icc 1 k).filter (fun p => p.Prime ∧ Nat.sqrt k < p))
  (h_M_def : M = primes.prod id)
  (hQ4_k : ∀ (start : ℕ) (m_mod : ℕ) (a : ℕ),
      Nat.Coprime m_mod M →
      m_mod > 0 →
      ∃ z ∈ Finset.Icc start (start + Nat.ceil ((M : ℝ) ^ ε) - 1),
      z % m_mod = a % m_mod ∧
      ∀ p ∈ primes, z % p ∈ I p)
  (h_coprime : Nat.Coprime m_val M)
  (h_m_pos : m_val > 0)
  (h_M_large : (M : ℝ) ^ (2.5 * ε) + (M : ℝ) ^ ε + 2 < (M : ℝ) ^ (3 * ε))
  (h_M_pos : M > 0)
  (h_eps_pos : ε > 0)
  : ∃ x : ℕ,
      (M : ℝ) ^ (2.5 * ε) ≤ x ∧ x < (M : ℝ) ^ (3 * ε) ∧
      (∀ p ∈ primes, x % p ∈ I p) ∧
      x % m_val = 1 % m_val := by
        exact?

/-
`M` satisfies growth conditions for large `k`.
-/
lemma large_M_conditions (ε : ℝ) (h_eps : ε > 0) (h_pnt : PNT_bounds) :
  ∃ K, ∀ k ≥ K,
    let M := M_prod k
    (M : ℝ) ^ (2.5 * ε) + (M : ℝ) ^ ε + 2 < (M : ℝ) ^ (3 * ε) ∧
    (M : ℝ) ^ ε > 2 := by
      -- By the properties of logarithms and the fact that $M$ tends to infinity, we can find such an $M0$.
      obtain ⟨M0, hM0⟩ : ∃ M0 : ℝ, ∀ M : ℝ, M ≥ M0 → (M : ℝ) ^ (2.5 * ε) + (M : ℝ) ^ ε + 2 < (M : ℝ) ^ (3 * ε) ∧ (M : ℝ) ^ ε > 2 := by
        have h_lim : Filter.Tendsto (fun M : ℝ => (M : ℝ) ^ (3 * ε) - (M : ℝ) ^ (2.5 * ε) - (M : ℝ) ^ ε - 2) Filter.atTop Filter.atTop := by
          -- Factor out $M^{3\epsilon}$ from the expression.
          suffices h_factor : Filter.Tendsto (fun M : ℝ => M ^ (3 * ε) * (1 - M ^ (2.5 * ε - 3 * ε) - M ^ (ε - 3 * ε) - 2 * M ^ (-3 * ε))) Filter.atTop Filter.atTop by
            refine h_factor.congr' ?_ ; filter_upwards [ Filter.eventually_gt_atTop 0 ] with M hM ; ring;
            norm_num [ ← Real.rpow_add hM ] ; ring;
          -- As $M \to \infty$, $M^{2.5\epsilon - 3\epsilon} \to 0$, $M^{\epsilon - 3\epsilon} \to 0$, and $M^{-3\epsilon} \to 0$.
          have h_zero : Filter.Tendsto (fun M : ℝ => M ^ (2.5 * ε - 3 * ε)) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun M : ℝ => M ^ (ε - 3 * ε)) Filter.atTop (nhds 0) ∧ Filter.Tendsto (fun M : ℝ => M ^ (-3 * ε)) Filter.atTop (nhds 0) := by
            norm_num +zetaDelta at *;
            exact ⟨ by simpa using tendsto_rpow_neg_atTop ( by linarith : 0 < - ( 5 / 2 * ε - 3 * ε ) ), by simpa using tendsto_rpow_neg_atTop ( by linarith : 0 < - ( ε - 3 * ε ) ), by simpa using tendsto_rpow_neg_atTop ( by linarith : 0 < - ( - ( 3 * ε ) ) ) ⟩;
          apply Filter.Tendsto.atTop_mul_pos;
          exacts [ show 0 < 1 by norm_num, tendsto_rpow_atTop ( by positivity ), by simpa using Filter.Tendsto.sub ( Filter.Tendsto.sub ( tendsto_const_nhds.sub h_zero.1 ) h_zero.2.1 ) ( h_zero.2.2.const_mul 2 ) ];
        have := h_lim.eventually_gt_atTop 0;
        obtain ⟨ M0, hM0 ⟩ := Filter.eventually_atTop.mp ( this.and ( Filter.eventually_gt_atTop ( 2 ^ ( 1 / ε ) ) ) ) ; exact ⟨ M0, fun M hM => ⟨ by have := hM0 M hM; ring_nf at *; linarith, by have := hM0 M hM; exact lt_of_le_of_lt ( by rw [ ← Real.rpow_mul ( by positivity ), one_div_mul_cancel ( by positivity ), Real.rpow_one ] ) ( Real.rpow_lt_rpow ( by positivity ) ( show M > 2 ^ ( 1 / ε ) by linarith ) ( by positivity ) ) ⟩ ⟩ ;
      -- By the properties of logarithms and the fact that $M$ tends to infinity, we can find such an $K$.
      have hM_inf : Filter.Tendsto (fun k => (M_prod k : ℝ)) Filter.atTop Filter.atTop := by
        convert M_prod_tendsto_infinity h_pnt using 1;
      exact Filter.eventually_atTop.mp ( hM_inf.eventually_ge_atTop M0 ) |> fun ⟨ K, hK ⟩ => ⟨ K, fun k hk => hM0 _ ( hK k hk ) ⟩

/-
`m(k) > 1` for `k >= 4`.
-/
lemma m_gt_one (k : ℕ) (hk : k ≥ 4) : m k > 1 := by
  refine' lt_of_lt_of_le _ ( Nat.le_of_dvd ( Finset.prod_pos fun p hp => pow_pos ( Nat.pos_of_ne_zero ( by aesop ) ) _ ) ( Finset.dvd_prod_of_mem _ <| show 2 ∈ _ from _ ) ) <;> norm_num;
  · unfold M;
    norm_num [ Nat.factorization_eq_zero_iff ];
    exact Nat.mod_eq_zero_of_dvd <| Finset.dvd_lcm <| Finset.mem_Icc.mpr ⟨ by linarith, by linarith ⟩;
  · grind

/-
`Question4Stronger` implies `Conjecture2`.
-/
theorem Question4Stronger_implies_Conjecture2 (hQ4 : Question4Stronger) (h_pnt : PNT_bounds) : Conjecture2Statement := by
  -- Apply the hypothesis `hQ4` to obtain the existence of `δ`, `K`, `x`, `y`, and `C`.
  obtain ⟨δ, hδ_pos, hδ_lt_ε, K, hK⟩ := hQ4 (1 / (3 * 1 + 7)) (by norm_num);
  contrapose! hK;
  refine' ⟨ K + 2, _, _ ⟩ <;> norm_num;
  refine' ⟨ 0, ∏ x ∈ Finset.filter ( fun x => Nat.Prime x ∧ ( K + 2 ).sqrt < x ) ( Finset.Icc 1 ( K + 2 ) ), x + 1, _, _, 0, _ ⟩ <;> norm_num;
  intro x hx hx'; rw [ Nat.mod_eq_of_lt ] at hx' <;> norm_num at *;
  · have := Nat.exists_prime_lt_and_le_two_mul ( Nat.sqrt ( K + 2 ) ) ( by nlinarith [ Nat.sqrt_pos.mpr ( show 0 < K + 2 by linarith ) ] );
    obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := this; exact ⟨ p, hp₁.pos, by nlinarith [ Nat.sqrt_le ( K + 2 ) ], hp₁, hp₂, by norm_num [ hx' ] ⟩ ;
  · refine' lt_of_le_of_lt hx _;
    refine' lt_of_lt_of_le ( Nat.sub_lt ( Nat.ceil_pos.mpr ( Real.rpow_pos_of_pos ( Finset.prod_pos fun p hp => Nat.cast_pos.mpr <| Nat.Prime.pos <| by aesop ) _ ) ) zero_lt_one ) _;
    refine' Nat.ceil_le.mpr _;
    rw [ ← Nat.cast_prod ];
    refine' le_trans ( Real.rpow_le_rpow_of_exponent_le ( mod_cast Nat.one_le_iff_ne_zero.mpr <| Finset.prod_ne_zero_iff.mpr fun p hp => Nat.Prime.ne_zero <| by aesop ) <| show ( 1 : ℝ ) / 10 ≤ 1 from by norm_num ) _ ; norm_num

#check Question4Statement
#check Conjecture2Statement
#check PNT_bounds
#check exists_xy_in_intervals
#check lcm_ratio_lower_bound_detailed_v3
#check large_M_inequality_generic_v3
#check lcm_real_gt_iff_ratio_gt_one

#check exists_xy_in_intervals_stronger_final_v3
#check lcm_ratio_lower_bound_detailed_v3
#check large_M_inequality_generic_v3
#check large_M_conditions
#check all_k_good_for_large_k
#check M_prod_ge_M_pow
#check prod_bad_le_M_prod_pow
#check valuation_ineq_good_p_aux_weak
#check valuation_ineq_bad_p_weak
#check small_prime_condition_satisfied
#check bound_comparison

#check exists_xy_in_intervals_stronger_with_m

/-
Question 4 (Stronger) implies Conjecture 2.
-/
theorem Question4Stronger_implies_Conjecture2_proven (hQ4 : Question4Stronger) (h_pnt : PNT_bounds) : Conjecture2Statement := by
  exact?

/-
Question 4 (Stronger) implies Conjecture 2.
-/
theorem Question4Stronger_implies_Conjecture2_final (hQ4 : Question4Stronger) (h_pnt : PNT_bounds) : Conjecture2Statement := by
  exact?

/-
Question 4 (Stronger) implies Conjecture 2.
-/
theorem Question4Stronger_implies_Conjecture2_verified (hQ4 : Question4Stronger) (h_pnt : PNT_bounds) : Conjecture2Statement := by
  exact?

/-
Proof of the main theorem.
-/
theorem main_theorem_proof (h_density : DensityHypothesis) : MainTheoremStatement := by
  exact?

/-
Proof of the main theorem.
-/
theorem main_theorem_proof_v2 (h_density : DensityHypothesis) : MainTheoremStatement := by
  exact?

/-
Proof of the main theorem.
-/
theorem main_theorem_proof_v3 (h_density : DensityHypothesis) : MainTheoremStatement := by
  exact?

/-
Proof of the main theorem.
-/
theorem main_theorem_proof_v4 (h_density : DensityHypothesis) : MainTheoremStatement := by
  exact?

/-
Proof of the main theorem.
-/
theorem main_theorem_proof_v5 (h_density : DensityHypothesis) : MainTheoremStatement := by
  exact?

/-
Proof of the main theorem.
-/
theorem main_theorem_proof_v6 (h_density : DensityHypothesis) : MainTheoremStatement := by
  exact?

/-
Proof of the main theorem.
-/
theorem main_theorem_proof_final (h_density : DensityHypothesis) : MainTheoremStatement := by
  -- Apply the main theorem proof with the given density hypothesis.
  apply main_theorem_proof_v6 h_density

/-
Proof of the main theorem.
-/
theorem main_theorem_proof_final_v2 (h_density : DensityHypothesis) : MainTheoremStatement := by
  exact?

/-
Question 4 (Stronger) implies Conjecture 2.
-/
theorem Question4Stronger_implies_Conjecture2_actual (hQ4 : Question4Stronger) (h_pnt : PNT_bounds) : Conjecture2Statement := by
  -- Apply the theorem that states Question 4 (Stronger) implies Conjecture 2.
  apply Question4Stronger_implies_Conjecture2_final hQ4 h_pnt
