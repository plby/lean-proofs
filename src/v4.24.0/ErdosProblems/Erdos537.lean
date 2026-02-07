/-

This is a Lean formalization of a solution to Erdős Problem 537.
https://www.erdosproblems.com/forum/thread/537

The original proof was found by: Ruzsa


A proof was auto-formalized by Aristotle (from Harmonic).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


import Mathlib

open scoped Classical

/-
The set of all squarefree numbers of the shape $p_1\cdots p_r$ where $p_{i+1}>2p_i$ for $1\leq i<r$.
-/
def SpecialSet : Set ℕ := { n | Squarefree n ∧ n.primeFactorsList.IsChain (fun p q => 2 * p < q) }

/-
If a list of naturals is sorted and satisfies the chain condition $2p < q$ for adjacent elements, then any two elements $p < q$ in the list satisfy $2p < q$.
-/
lemma List.IsChain_spread {l : List ℕ} (h_sorted : l.Sorted (· ≤ ·)) (h_chain : l.IsChain (fun p q => 2 * p < q))
  {p q : ℕ} (hp : p ∈ l) (hq : q ∈ l) (hlt : p < q) : 2 * p < q := by
    obtain ⟨i, hi⟩ : ∃ i : Fin l.length, l.get i = p := by
      exact mem_iff_get.mp hp
    obtain ⟨j, hj⟩ : ∃ j : Fin l.length, l.get j = q := by
      exact mem_iff_get.mp hq
    have h_chain' : ∀ i j : Fin l.length, i < j → 2 * l.get i < l.get j := by
      intro i j hij;
      induction' j with j hj generalizing i;
      induction' j with j ih generalizing i;
      · tauto;
      · rcases eq_or_lt_of_le ( show i ≤ ⟨ j, by linarith ⟩ from Nat.le_of_lt_succ hij ) with rfl | hi <;> simp_all +decide
        · have := List.isChain_iff_get.mp h_chain;
          exact this _ ‹_›;
        · have := List.isChain_iff_get.mp h_chain;
          grind
    have h_lt : i < j := by
      contrapose! hlt;
      rw [ ← hj, ← hi ] ; exact h_sorted.rel_get_of_le hlt;
    have h_final : 2 * p < q := by
      simpa only [ hi, hj ] using h_chain' i j h_lt
    exact h_final

/-
If $n$ is in the special set, and $p, q$ are prime factors of $n$ with $p < q$, then $2p < q$.
-/
lemma SpecialSet.spread {n p q : ℕ} (hn : n ∈ SpecialSet) (hp : p.Prime) (hq : q.Prime) (hpn : p ∣ n) (hqn : q ∣ n) (hlt : p < q) : 2 * p < q := by
  -- Since $n \in \text{SpecialSet}$, $n$ is squarefree and its prime factors are spread out.
  obtain ⟨h_sqfree, h_chain⟩ := hn
  have h_prime_factors : p ∈ n.primeFactorsList ∧ q ∈ n.primeFactorsList := by
    aesop;
  have h_sorted : n.primeFactorsList.Sorted (· ≤ ·) := by
    convert Nat.primeFactorsList_sorted n using 1
  have h_chain_sorted : n.primeFactorsList.IsChain (fun p q => 2 * p < q) := by
    exact h_chain
  have h_chain_all : ∀ p q : ℕ, p ∈ n.primeFactorsList → q ∈ n.primeFactorsList → p < q → 2 * p < q := by
    exact fun p q a a_1 a_2 => List.IsChain_spread h_sorted h_chain a a_1 a_2
  exact h_chain_all p q h_prime_factors.left h_prime_factors.right hlt

/-
The subset of SpecialSet in the interval (N/2, N].
-/
noncomputable def SpecialFinset (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter (fun n => n ∈ SpecialSet ∧ N / 2 < n)

/-
If $a_1, a_2, a_3$ are in the special set (squarefree with spread factors) and in $(N/2, N]$, then they cannot satisfy $a_1 p_1 = a_2 p_2 = a_3 p_3$ for distinct primes $p_i$.
-/
lemma special_set_contradiction {N : ℕ} {a₁ a₂ a₃ p₁ p₂ p₃ : ℕ}
  (ha₁ : a₁ ∈ SpecialFinset N) (ha₂ : a₂ ∈ SpecialFinset N) (ha₃ : a₃ ∈ SpecialFinset N)
  (hp₁ : p₁.Prime) (hp₂ : p₂.Prime) (hp₃ : p₃.Prime)
  (hp₁₂ : p₁ ≠ p₂) (hp₁₃ : p₁ ≠ p₃) (hp₂₃ : p₂ ≠ p₃)
  (h_eq : a₁ * p₁ = a₂ * p₂ ∧ a₂ * p₂ = a₃ * p₃) : False := by
    -- WLOG assume $a_2 > a_3$. This implies $p_2 < p_3$ because $a_2 p_2 = a_3 p_3$.
    suffices h_wlog : ∀ (a₁ a₂ a₃ : ℕ) (p₁ p₂ p₃ : ℕ), a₁ ∈ SpecialFinset N → a₂ ∈ SpecialFinset N → a₃ ∈ SpecialFinset N → Nat.Prime p₁ → Nat.Prime p₂ → Nat.Prime p₃ → p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ → a₁ * p₁ = a₂ * p₂ → a₂ * p₂ = a₃ * p₃ → a₂ > a₃ → False by
      by_cases h_cases : a₂ > a₃ ∨ a₃ > a₂;
      · cases' h_cases with h h;
        · exact h_wlog a₁ a₂ a₃ p₁ p₂ p₃ ha₁ ha₂ ha₃ hp₁ hp₂ hp₃ hp₁₂ hp₁₃ hp₂₃ h_eq.1 h_eq.2 h;
        · specialize h_wlog a₁ a₃ a₂ p₁ p₃ p₂ ; aesop;
      · unfold SpecialFinset at ha₂; aesop;
    intros a₁ a₂ a₃ p₁ p₂ p₃ ha₁ ha₂ ha₃ hp₁ hp₂ hp₃ hp₁₂ hp₁₃ hp₂₃ h_eq₁ h_eq₂ h_gt
    have h_p2_div_a1 : p₂ ∣ a₁ := by
      exact Or.resolve_right ( hp₂.dvd_mul.mp ( h_eq₁.symm ▸ dvd_mul_left _ _ ) ) ( by rintro H; have := Nat.prime_dvd_prime_iff_eq hp₂ hp₁; tauto )
    have h_p3_div_a1 : p₃ ∣ a₁ := by
      have h_p3_div_a1 : p₃ ∣ a₁ * p₁ := by
        aesop;
      exact Or.resolve_right ( hp₃.dvd_mul.mp h_p3_div_a1 ) ( by rw [ Nat.dvd_prime hp₁ ] ; aesop );
    -- Since $a_1$ is in the special set, by `SpecialSet.spread`, and since $p_2 < p_3$, we must have $2 p_2 < p_3$.
    have h_spread : 2 * p₂ < p₃ := by
      apply_rules [ SpecialSet.spread ];
      · exact Finset.mem_filter.mp ha₁ |>.2.1;
      · nlinarith [ Nat.Prime.one_lt hp₁, Nat.Prime.one_lt hp₂, Nat.Prime.one_lt hp₃ ];
    have h_ratio : a₂ ≤ N ∧ a₃ > N / 2 := by
      exact ⟨ Nat.le_of_lt_succ <| Finset.mem_range.mp <| Finset.mem_filter.mp ha₂ |>.1, by simpa using Finset.mem_filter.mp ha₃ |>.2.2 ⟩;
    nlinarith [ Nat.div_add_mod N 2, Nat.mod_lt N two_pos ]

/-
A pair of primes (p, q) is bad if p < q <= 2p.
-/
def BadPair (p q : ℕ) : Prop := p.Prime ∧ q.Prime ∧ p < q ∧ q ≤ 2 * p

/-
A number $n$ is in the special set if and only if it is squarefree and not divisible by any "bad pair" of primes.
-/
lemma SpecialSet_iff (n : ℕ) : n ∈ SpecialSet ↔ Squarefree n ∧ ∀ p q, BadPair p q → ¬ (p * q ∣ n) := by
  constructor;
  · intro hn
    obtain ⟨hn_sqf, hn_chain⟩ := hn
    constructor
    exact hn_sqf
    intro p q hq hdiv
    have hsp : 2 * p < q := by
      have hsp : p ∈ n.primeFactorsList ∧ q ∈ n.primeFactorsList := by
        rw [ Nat.mem_primeFactorsList ];
        · exact ⟨ ⟨ hq.1, dvd_of_mul_right_dvd hdiv ⟩, Nat.mem_primeFactorsList ( by aesop ) |>.2 ⟨ hq.2.1, Nat.dvd_trans ( by aesop ) hdiv ⟩ ⟩;
        · aesop;
      have hsp_sorted : List.Sorted (· ≤ ·) n.primeFactorsList := by
        exact Nat.primeFactorsList_sorted n;
      apply List.IsChain_spread hsp_sorted hn_chain hsp.left hsp.right hq.right.right.left
    exact absurd hsp (by
    linarith [ hq.2.2.2 ]);
  · rintro ⟨ hn, h ⟩;
    refine' ⟨ hn, _ ⟩;
    refine' List.isChain_iff_get.mpr _;
    intro i hi;
    contrapose! h;
    refine' ⟨ n.primeFactorsList.get ⟨ i, by linarith ⟩, n.primeFactorsList.get ⟨ i + 1, hi ⟩, _, _ ⟩;
    · refine' ⟨ _, _, _, h ⟩;
      · exact Nat.prime_of_mem_primeFactorsList ( List.getElem_mem _ );
      · exact Nat.prime_of_mem_primeFactorsList ( List.getElem_mem _ );
      · have h_sorted : List.Sorted (· ≤ ·) n.primeFactorsList := by
          exact Nat.primeFactorsList_sorted _;
        refine' lt_of_le_of_ne _ _;
        · exact h_sorted.rel_get_of_lt ( Nat.lt_succ_self _ );
        · intro H; have := List.nodup_iff_injective_get.mp ( show List.Nodup n.primeFactorsList from ?_ ) ; have := @this ⟨ i, by linarith ⟩ ⟨ i + 1, hi ⟩ ; aesop;
          exact Squarefree.nodup_primeFactorsList hn;
    · have h_div : n.primeFactorsList.get ⟨i, by linarith⟩ ∣ n ∧ n.primeFactorsList.get ⟨i + 1, hi⟩ ∣ n := by
        exact ⟨ Nat.dvd_of_mem_primeFactorsList <| by simp, Nat.dvd_of_mem_primeFactorsList <| by simp ⟩;
      convert Nat.Coprime.mul_dvd_of_dvd_of_dvd _ h_div.1 h_div.2 using 1;
      have h_distinct : n.primeFactorsList.get ⟨i, by linarith⟩ ≠ n.primeFactorsList.get ⟨i + 1, hi⟩ := by
        intro H;
        have := List.nodup_iff_injective_get.mp ( show List.Nodup ( Nat.primeFactorsList n ) from ?_ );
        · exact absurd ( this H ) ( by simp +decide );
        · exact Squarefree.nodup_primeFactorsList hn;
      have := Nat.coprime_primes ( Nat.prime_of_mem_primeFactorsList ( show n.primeFactorsList.get ⟨ i, by linarith ⟩ ∈ n.primeFactorsList from by simp ) ) ( Nat.prime_of_mem_primeFactorsList ( show n.primeFactorsList.get ⟨ i + 1, hi ⟩ ∈ n.primeFactorsList from by simp ) ) ; aesop;

/-
The property that for any epsilon > 0, any subset of {1, ..., N} with density at least epsilon contains a solution to a_1 p_1 = a_2 p_2 = a_3 p_3 with distinct primes.
-/
def RothLikeProperty : Prop :=
  ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, ∀ A, A ⊆ Finset.range (N + 1) → (A.card : ℝ) ≥ ε * N →
  ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ a₃ ∈ A, ∃ p₁ p₂ p₃, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
  p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧ a₁ * p₁ = a₂ * p₂ ∧ a₂ * p₂ = a₃ * p₃

/-
If the Special Set has positive density, then the Roth-like property (that dense sets contain solutions to a1 p1 = a2 p2 = a3 p3) is false.
-/
theorem answer (h_density : ∃ c > 0, ∃ N₀, ∀ N ≥ N₀, ((SpecialFinset N).card : ℝ) ≥ c * N) : ¬ RothLikeProperty := by
  -- Assume RothLikeProperty holds.
  by_contra h_roth
  obtain ⟨c, hc_pos, N₀, hN₀⟩ := h_density
  set ε := c with hε
  obtain ⟨N₀', hN₀'⟩ := h_roth ε hc_pos
  obtain ⟨N, hN₁, hN₂⟩ : ∃ N, N ≥ max N₀ N₀' ∧ 2 * (SpecialFinset N).card > ε * N := by
    -- Since $c > 0$, we can choose $N$ large enough such that $2cN > cN$, which simplifies to $N > 0$.
    obtain ⟨N, hN₁, hN₂⟩ : ∃ N, N ≥ max N₀ N₀' ∧ N > 0 := by
      exact ⟨ Max.max N₀ N₀' + 1, by linarith [ le_max_left N₀ N₀', le_max_right N₀ N₀' ], by linarith [ le_max_left N₀ N₀', le_max_right N₀ N₀' ] ⟩
    generalize_proofs at *; (
    exact ⟨ N, hN₁, by nlinarith [ show ( N : ℝ ) ≥ 1 by exact_mod_cast hN₂, hN₀ N ( le_trans ( le_max_left _ _ ) hN₁ ) ] ⟩)
  generalize_proofs at *;
  specialize hN₀' N ( le_trans ( le_max_right _ _ ) hN₁ ) ( SpecialFinset N ) ?_ ?_ <;> simp_all +decide [ Finset.subset_iff ];
  · exact fun x hx => Finset.mem_range.mp ( Finset.mem_filter.mp hx |>.1 );
  · obtain ⟨ a₁, ha₁, a₂, ha₂, a₃, ha₃, p₁, hp₁, p₂, hp₂, p₃, hp₃, h₁, h₂, h₃, h₄, h₅ ⟩ := hN₀' ; exact special_set_contradiction ha₁ ha₂ ha₃ hp₁ hp₂ hp₃ h₁ h₂ h₃ ⟨ h₄, h₅ ⟩ ;

/-
I have formalized the definition of `RothLikeProperty` and the counterexample construction `SpecialSet` (based on squarefree numbers with spreading prime factors). I proved `special_set_contradiction`, showing that any solution in `SpecialSet` leads to a contradiction. I then proved `answer`, which establishes that `RothLikeProperty` is false, conditional on the fact that `SpecialSet` has positive density. The positive density of `SpecialSet` is a known number-theoretic result (Galambos 1976) which relies on the convergence of the sum of reciprocals of 'bad' prime pairs; I formalized the density of the 'small constraints' part of the set, but the full density result is taken as a hypothesis in the final theorem.
-/


/-
Definition of Chebyshev's theta function.
-/
noncomputable def vartheta (x : ℝ) : ℝ := ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p

/-
Definition of the prime counting function $\pi(x)$.
-/
noncomputable def pi_real (x : ℝ) : ℕ := ((Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime).card

/-
Definition of the Chebyshev upper bound assumption.
-/
def ChebyshevUpperBound : Prop := ∀ x : ℝ, 2 ≤ x → vartheta x ≤ Real.log 4 * x

/-
Lemma 1: For every real $y\ge 2$, $\pi(2y)-\pi(y)\le \frac{2(\log 4)}{\log y}\,y$.
-/
lemma lem_dyadicprimecount (hChebyshev : ChebyshevUpperBound) (y : ℝ) (hy : 2 ≤ y) :
  (pi_real (2 * y) : ℝ) - pi_real y ≤ (2 * Real.log 4 / Real.log y) * y := by
    -- By definition of $vartheta$, we have $\vartheta(2y) - \vartheta(y) = \sum_{y < p \leq 2y} \log p$.
    have h_vartheta_diff : (vartheta (2 * y)) - (vartheta y) = ∑ p ∈ (Finset.filter Nat.Prime (Finset.Icc (⌊y⌋₊ + 1) (⌊2 * y⌋₊))), Real.log p := by
      unfold vartheta;
      erw [ Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.sum_Ico_eq_sub _ _ ];
      exact Nat.succ_le_succ ( Nat.floor_mono <| by linarith );
    -- Since $\log p \geq \log y$ for $p \in (y, 2y]$, we have $\sum_{y < p \leq 2y} \log p \geq (\pi(2y) - \pi(y)) \log y$.
    have h_log_bound : ∑ p ∈ (Finset.filter Nat.Prime (Finset.Icc (⌊y⌋₊ + 1) (⌊2 * y⌋₊))), Real.log p ≥ (pi_real (2 * y) - pi_real y) * Real.log y := by
      have h_log_bound : ∀ p ∈ Finset.filter Nat.Prime (Finset.Icc (⌊y⌋₊ + 1) (⌊2 * y⌋₊)), Real.log p ≥ Real.log y := by
        exact fun p hp => Real.log_le_log ( by positivity ) ( by linarith [ Nat.lt_floor_add_one y, show ( p : ℝ ) ≥ ⌊y⌋₊ + 1 by exact_mod_cast Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 ] );
      refine' le_trans _ ( Finset.sum_le_sum h_log_bound );
      simp +decide [ pi_real ];
      rw [ show ( Finset.filter Nat.Prime ( Finset.range ( ⌊2 * y⌋₊ + 1 ) ) ) = Finset.filter Nat.Prime ( Finset.range ( ⌊y⌋₊ + 1 ) ) ∪ Finset.filter Nat.Prime ( Finset.Icc ( ⌊y⌋₊ + 1 ) ⌊2 * y⌋₊ ) from ?_, Finset.card_union_of_disjoint ];
      · norm_num;
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;
      · ext; simp [Finset.mem_union, Finset.mem_Icc];
        exact ⟨ fun h => if h' : _ < ⌊y⌋₊ + 1 then Or.inl ⟨ h', h.2 ⟩ else Or.inr ⟨ ⟨ not_lt.mp h', Nat.le_of_lt_succ h.1 ⟩, h.2 ⟩, fun h => h.elim ( fun h => ⟨ Nat.lt_succ_of_le ( Nat.le_trans ( Nat.le_of_lt_succ h.1 ) ( Nat.floor_mono ( by linarith ) ) ), h.2 ⟩ ) fun h => ⟨ Nat.lt_succ_of_le h.1.2, h.2 ⟩ ⟩;
    -- By definition of $vartheta$, we have $\vartheta(2y) \leq (\log 4) \cdot 2y$.
    have h_vartheta_2y : vartheta (2 * y) ≤ (Real.log 4) * (2 * y) := by
      exact hChebyshev _ ( by linarith );
    rw [ div_mul_eq_mul_div, le_div_iff₀ ] <;> nlinarith [ Real.log_pos <| show 1 < y by linarith, Real.log_pos <| show 1 < 4 by norm_num, show ( 0 :ℝ ) ≤ vartheta y by exact Finset.sum_nonneg fun _ _ => Real.log_nonneg <| Nat.one_le_cast.2 <| Nat.Prime.pos <| by aesop ]

set_option maxHeartbeats 0 in
/-
Lemma 2: The series $\sum_{p}\frac{1}{p\log p}$ converges.
-/
lemma lem_prime_series (hChebyshev : ChebyshevUpperBound) : Summable (fun p : ℕ => if p.Prime then 1 / (p * Real.log p) else 0) := by
  -- Let's consider the series $\sum_{p}\frac{1}{p\log p}$.
  -- We'll show that this series converges by comparing it to a convergent series.
  have h_comparison : ∀ k : ℕ, k ≥ 2 → (∑ p ∈ Finset.filter Nat.Prime (Finset.Icc (2^(k-1) + 1) (2^k)), (1 : ℝ) / (p * Real.log p)) ≤ (2 * Real.log 4) / ((k - 1) ^ 2 * (Real.log 2) ^ 2) := by
    -- For primes $p \in I_k$, we have $p \geq 2^{k-1}$ and $\log p \geq \log(2^{k-1}) = (k-1)\log 2$, hence $\frac{1}{p\log p} \leq \frac{1}{2^{k-1}(k-1)\log 2}$.
    intros k hk
    have h_bound : ∀ p ∈ Finset.filter Nat.Prime (Finset.Icc (2^(k-1) + 1) (2^k)), (1 : ℝ) / (p * Real.log p) ≤ 1 / (2^(k-1) * (k-1) * Real.log 2) := by
      intro p hp
      have h_p_ge : (p : ℝ) ≥ 2^(k-1) := by
        exact_mod_cast Finset.mem_Icc.mp ( Finset.mem_filter.mp hp |>.1 ) |>.1 |> Nat.le_of_succ_le
      have h_log_p_ge : Real.log p ≥ (k-1) * Real.log 2 := by
        rw [ ← Real.log_rpow zero_lt_two ] ; gcongr ; cases k <;> norm_num at * ; norm_cast at *
      have h_bound : (1 : ℝ) / (p * Real.log p) ≤ 1 / (2^(k-1) * (k-1) * Real.log 2) := by
        exact one_div_le_one_div_of_le ( mul_pos ( mul_pos ( pow_pos ( by norm_num ) _ ) ( sub_pos.mpr ( Nat.one_lt_cast.mpr hk ) ) ) ( Real.log_pos one_lt_two ) ) ( by nlinarith [ show ( 0 :ℝ ) < 2 ^ ( k - 1 ) by positivity, show ( 0 :ℝ ) < Real.log p by exact Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.Prime.one_lt <| Finset.mem_filter.mp hp |>.2 ] )
      exact h_bound;
    -- By Lemma 1, we have $\pi(2^k) - \pi(2^{k-1}) \leq \frac{2(\log 4)}{\log(2^{k-1})}2^{k-1} = \frac{2(\log 4)}{(k-1)\log 2}2^{k-1}$.
    have h_prime_count : ((Finset.filter Nat.Prime (Finset.Icc (2^(k-1) + 1) (2^k))).card : ℝ) ≤ (2 * Real.log 4 / ((k - 1) * Real.log 2)) * 2^(k-1) := by
      have h_prime_count : (pi_real (2^k) : ℝ) - (pi_real (2^(k-1)) : ℝ) ≤ (2 * Real.log 4 / ((k - 1) * Real.log 2)) * 2^(k-1) := by
        convert lem_dyadicprimecount hChebyshev ( 2 ^ ( k - 1 ) ) ( by exact le_trans ( by norm_num ) ( pow_le_pow_right₀ ( by norm_num ) ( Nat.le_sub_one_of_lt hk ) ) ) using 1 ; norm_num [ Real.log_pow ] ; ring_nf;
        · cases k <;> trivial;
        · norm_num [ div_mul_eq_mul_div ];
          rw [ Nat.cast_pred ( by linarith ) ];
      convert h_prime_count using 1;
      unfold pi_real;
      rw [ show ( Finset.filter Nat.Prime ( Finset.range ( ⌊ ( 2 : ℝ ) ^ k⌋₊ + 1 ) ) ) = Finset.filter Nat.Prime ( Finset.range ( ⌊ ( 2 : ℝ ) ^ ( k - 1 ) ⌋₊ + 1 ) ) ∪ Finset.filter Nat.Prime ( Finset.Icc ( ⌊ ( 2 : ℝ ) ^ ( k - 1 ) ⌋₊ + 1 ) ( ⌊ ( 2 : ℝ ) ^ k⌋₊ ) ) from ?_, Finset.card_union_of_disjoint ];
      · norm_num [ show ⌊ ( 2 : ℝ ) ^ k⌋₊ = 2 ^ k by exact_mod_cast Nat.floor_natCast _, show ⌊ ( 2 : ℝ ) ^ ( k - 1 ) ⌋₊ = 2 ^ ( k - 1 ) by exact_mod_cast Nat.floor_natCast _ ];
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;
      · ext; simp [Finset.mem_union, Finset.mem_Icc];
        exact ⟨ fun h => if h' : _ < ⌊ ( 2 : ℝ ) ^ ( k - 1 ) ⌋₊ + 1 then Or.inl ⟨ h', h.2 ⟩ else Or.inr ⟨ ⟨ by linarith, by linarith ⟩, h.2 ⟩, fun h => h.elim ( fun h => ⟨ by linarith [ show ⌊ ( 2 : ℝ ) ^ k⌋₊ ≥ ⌊ ( 2 : ℝ ) ^ ( k - 1 ) ⌋₊ from Nat.floor_mono <| pow_le_pow_right₀ ( by norm_num ) <| Nat.pred_le _ ], h.2 ⟩ ) fun h => ⟨ by linarith, h.2 ⟩ ⟩;
    field_simp;
    refine le_trans ( mul_le_mul_of_nonneg_right ( Finset.sum_le_sum h_bound ) ( sq_nonneg _ ) ) ?_ ; norm_num at *;
    convert mul_le_mul_of_nonneg_right h_prime_count ( show 0 ≤ ( Real.log 2 ) ⁻¹ * ( ( k - 1 : ℝ ) ⁻¹ * ( 2 ^ ( k - 1 ) ) ⁻¹ ) * Real.log 2 ^ 2 by exact mul_nonneg ( mul_nonneg ( inv_nonneg.2 ( Real.log_nonneg ( by norm_num ) ) ) ( mul_nonneg ( inv_nonneg.2 ( sub_nonneg.2 ( Nat.one_le_cast.2 ( by linarith ) ) ) ) ( inv_nonneg.2 ( pow_nonneg ( by norm_num ) _ ) ) ) ) ( sq_nonneg _ ) ) using 1 ; ring;
    field_simp;
  -- By comparison, it suffices to show that $\sum_{k=2}^{\infty} \frac{2 \log 4}{(k-1)^2 (\log 2)^2}$ converges.
  have h_summable_comparison : Summable (fun k : ℕ => (2 * Real.log 4) / ((k - 1) ^ 2 * (Real.log 2) ^ 2)) := by
    -- We'll use the fact that $\sum_{k=2}^{\infty} \frac{1}{(k-1)^2}$ converges.
    have h_summable_one_over_k_squared : Summable (fun k : ℕ => (1 : ℝ) / ((k - 1) ^ 2)) := by
      exact summable_nat_add_iff 1 |>.1 <| by simp;
    convert h_summable_one_over_k_squared.mul_left ( 2 * Real.log 4 / Real.log 2 ^ 2 ) using 2 ; ring_nf;
    field_simp;
    ring;
  have h_summable_comparison : Summable (fun k : ℕ => ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc (2^(k-1) + 1) (2^k)), (1 : ℝ) / (p * Real.log p)) := by
    rw [ ← summable_nat_add_iff 2 ] at *;
    exact Summable.of_nonneg_of_le ( fun n => Finset.sum_nonneg fun _ _ => by positivity ) ( fun n => h_comparison _ le_add_self ) h_summable_comparison;
  have h_summable_comparison : Summable (fun p : ℕ => if Nat.Prime p then (1 : ℝ) / (p * Real.log p) else 0) := by
    have h_partial_sums : ∀ N : ℕ, ∑ p ∈ Finset.Icc 1 (2^N), (if Nat.Prime p then (1 : ℝ) / (p * Real.log p) else 0) ≤ ∑ k ∈ Finset.range (N + 1), ∑ p ∈ Finset.filter Nat.Prime (Finset.Icc (2^(k-1) + 1) (2^k)), (1 : ℝ) / (p * Real.log p) := by
      intro N
      induction' N with N ih;
      · norm_num [ Finset.sum_filter ];
      · have h_split : Finset.Icc 1 (2^(N+1)) = Finset.Icc 1 (2^N) ∪ Finset.Icc (2^N + 1) (2^(N+1)) := by
          exact Eq.symm ( Finset.Ico_union_Ico_eq_Ico ( by norm_num ) ( by ring_nf; norm_num ) );
        rw [ h_split, Finset.sum_union ];
        · simp_all +decide [ Finset.sum_range_succ ];
          exact add_le_add_right ih _ |> le_trans <| by simp +decide [ Finset.sum_ite ] ;
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Icc.mp hx₁, Finset.mem_Icc.mp hx₂ ] ;
    have h_partial_sums_bounded : BddAbove (Set.range (fun N : ℕ => ∑ p ∈ Finset.Icc 1 (2^N), (if Nat.Prime p then (1 : ℝ) / (p * Real.log p) else 0))) := by
      exact ⟨ _, Set.forall_mem_range.mpr fun N => le_trans ( h_partial_sums N ) ( Summable.sum_le_tsum ( Finset.range ( N + 1 ) ) ( fun _ _ => Finset.sum_nonneg fun _ _ => by positivity ) h_summable_comparison ) ⟩;
    have h_partial_sums_bounded : BddAbove (Set.range (fun N : ℕ => ∑ p ∈ Finset.range (2^N + 1), (if Nat.Prime p then (1 : ℝ) / (p * Real.log p) else 0))) := by
      obtain ⟨ M, hM ⟩ := h_partial_sums_bounded; use M + 1; rintro x ⟨ N, rfl ⟩ ; simp_all +decide [ Finset.sum_range_succ' ] ;
      have := hM ⟨ N, rfl ⟩ ; simp_all +decide
      erw [ Finset.sum_Ico_eq_sum_range ] at this ; norm_num [ add_comm, Finset.sum_range_succ' ] at * ; linarith;
    refine' summable_iff_not_tendsto_nat_atTop_of_nonneg ( fun p => by positivity ) |>.2 _;
    rw [ Filter.tendsto_atTop_atTop ];
    push_neg;
    obtain ⟨ b, hb ⟩ := h_partial_sums_bounded;
    exact ⟨ b + 1, fun N => ⟨ 2 ^ N + 1, by linarith [ Nat.le_ceil ( Real.logb 2 N ), Nat.le_ceil ( Real.logb 2 ( 2 ^ N + 1 ) ), show 2 ^ N ≥ N from Nat.recOn N ( by norm_num ) fun n ihn => by rw [ pow_succ' ] ; linarith [ ihn, Nat.one_le_pow n 2 zero_lt_two ], Nat.le_ceil ( Real.logb 2 ( 2 ^ N ) ) ], by linarith [ hb <| Set.mem_range_self N ] ⟩ ⟩;
  convert h_summable_comparison using 1

/-
Lemma 3: The double series $\sum_{p<q\le 2p}\frac{1}{pq}$ converges.
-/
lemma lem_close_pairs_series (hChebyshev : ChebyshevUpperBound) :
  Summable (fun x : ℕ × ℕ => if x.1.Prime ∧ x.2.Prime ∧ x.1 < x.2 ∧ x.2 ≤ 2 * x.1 then 1 / (x.1 * x.2 : ℝ) else 0) := by
    -- By Fubini's theorem, we can interchange the order of summation.
    have h_fubini : Summable (fun p : ℕ => if p.Prime then (1 / (p : ℝ)) * (∑ q ∈ ((Finset.range (2 * p + 1)).filter Nat.Prime).filter (fun q => p < q), (1 / (q : ℝ))) else 0) := by
      -- By Lemma 2, we know that $\sum_{p<q\le 2p}\frac{1}{q} \le \frac{2(\log 4)}{\log p}$.
      have h_bound : ∀ p : ℕ, Nat.Prime p → p ≥ 2 → (∑ q ∈ ((Finset.range (2 * p + 1)).filter Nat.Prime).filter (fun q => p < q), (1 / (q : ℝ))) ≤ (2 * Real.log 4 / Real.log p) := by
        -- By Lemma 1, we know that $\pi(2p) - \pi(p) \le \frac{2(\log 4)}{\log p}\,p$.
        have h_pi_bound : ∀ p : ℕ, Nat.Prime p → p ≥ 2 → (pi_real (2 * p) : ℝ) - pi_real p ≤ (2 * Real.log 4 / Real.log p) * p := by
          intro p hp hp'; have := lem_dyadicprimecount hChebyshev p ( Nat.cast_le.mpr hp' ) ; aesop;
        -- By definition of $pi_real$, we know that $\sum_{q \in \text{Finset.filter Nat.Prime (Finset.range (2 * p + 1)) with p < q}} \frac{1}{q} \leq \frac{\pi(2p) - \pi(p)}{p}$.
        intros p hp hp_ge_2
        have h_sum_bound : (∑ q ∈ ((Finset.range (2 * p + 1)).filter Nat.Prime).filter (fun q => p < q), (1 / (q : ℝ))) ≤ ((pi_real (2 * p) : ℝ) - pi_real p) / p := by
          have h_sum_bound : (∑ q ∈ ((Finset.range (2 * p + 1)).filter Nat.Prime).filter (fun q => p < q), (1 / (q : ℝ))) ≤ (∑ q ∈ ((Finset.range (2 * p + 1)).filter Nat.Prime).filter (fun q => p < q), (1 / (p : ℝ))) := by
            exact Finset.sum_le_sum fun x hx => one_div_le_one_div_of_le ( Nat.cast_pos.mpr hp.pos ) ( Nat.cast_le.mpr <| Finset.mem_filter.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 |> fun h => by linarith [ Finset.mem_filter.mp hx |>.2 ] );
          convert h_sum_bound using 1 ; norm_num [ div_eq_mul_inv ];
          rw [ show ( Finset.filter ( fun q => p < q ) ( Finset.filter Nat.Prime ( Finset.range ( 2 * p + 1 ) ) ) ) = Finset.filter Nat.Prime ( Finset.range ( 2 * p + 1 ) ) \ Finset.filter Nat.Prime ( Finset.range ( p + 1 ) ) from ?_, Finset.card_sdiff ];
          · rw [ Nat.cast_sub ];
            · rw [ Finset.inter_eq_left.mpr ] <;> norm_num [ Finset.subset_iff ];
              · unfold pi_real; norm_num;
                norm_num [ show ⌊ ( 2 : ℝ ) * p⌋₊ = 2 * p by exact_mod_cast Nat.floor_natCast _ ];
              · exact fun x hx₁ hx₂ => ⟨ by linarith, hx₂ ⟩;
            · exact Finset.card_mono <| Finset.inter_subset_right;
          · ext; aesop ;
        exact h_sum_bound.trans ( div_le_iff₀ ( by positivity ) |>.2 ( by linarith [ h_pi_bound p hp hp_ge_2 ] ) );
      -- By Lemma 2, we know that $\sum_{p}\frac{1}{p\log p}$ converges.
      have h_summable : Summable (fun p : ℕ => if p.Prime then (1 / (p : ℝ)) * (1 / Real.log p) else 0) := by
        convert lem_prime_series hChebyshev using 1;
        exact funext fun p => by split_ifs <;> ring;
      refine' .of_nonneg_of_le ( fun p => _ ) ( fun p => _ ) ( h_summable.mul_left ( 2 * Real.log 4 ) );
      · split_ifs <;> positivity;
      · split_ifs <;> simp_all +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
        exact mul_le_mul_of_nonneg_left ( h_bound p ‹_› ( Nat.Prime.two_le ‹_› ) ) ( by positivity );
    rw [ summable_prod_of_nonneg ];
    · constructor;
      · intro x;
        refine' summable_of_ne_finset_zero _;
        exacts [ Finset.range ( 2 * x + 1 ), fun b hb => if_neg fun h => hb <| Finset.mem_range.mpr <| by linarith ];
      · refine' .of_nonneg_of_le ( fun p => _ ) ( fun p => _ ) h_fubini;
        · exact tsum_nonneg fun _ => by positivity;
        · split_ifs <;> simp_all +decide
          rw [ tsum_eq_sum ];
          any_goals exact Finset.filter Nat.Prime ( Finset.range ( 2 * p + 1 ) ) |> Finset.filter ( fun x => p < x );
          · rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun x hx => by rw [ if_pos ⟨ Finset.mem_filter.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2, Finset.mem_filter.mp hx |>.2, by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp ( Finset.mem_filter.mp hx |>.1 ) |>.1 ) ] ⟩ ] ; ring_nf; norm_num;
          · grind;
    · exact fun _ => by positivity;

/-
Definition of the set of forbidden divisors $\mathcal{D}$.
-/
def ForbiddenDivisors : Set ℕ := { n | (∃ p, Nat.Prime p ∧ n = p ^ 2) ∨ (∃ p q, BadPair p q ∧ n = p * q) }

/-
Proposition 1: The series $\sum_{d\in\D}\frac{1}{d}$ converges.
-/
theorem prop_Dsum (hChebyshev : ChebyshevUpperBound) : Summable (fun d : ℕ => if d ∈ ForbiddenDivisors then 1 / (d : ℝ) else 0) := by
  -- By definition of $D$, we can split the sum into two parts: one over prime squares and one over bad pairs.
  have h_split_sum : Summable (fun d : ℕ => if d ∈ {d | ∃ p, Nat.Prime p ∧ d = p^2} then 1 / (d : ℝ) else 0) ∧ Summable (fun d : ℕ => if d ∈ {d | ∃ p q, BadPair p q ∧ d = p * q} then 1 / (d : ℝ) else 0) := by
    constructor;
    · refine' summable_of_sum_le _ _;
      exact ∑' p : ℕ, ( if p.Prime then 1 / ( p ^ 2 : ℝ ) else 0 );
      · exact fun _ => by positivity;
      · intro u;
        -- Since these are the only terms in the sum, we can bound it by the sum over all primes.
        have h_sum_le : ∑ x ∈ u, (if ∃ p, Nat.Prime p ∧ x = p^2 then (1 : ℝ) / x else 0) ≤ ∑ p ∈ Finset.image (fun x => Nat.sqrt x) (u.filter (fun x => ∃ p, Nat.Prime p ∧ x = p^2)), (if Nat.Prime p then (1 : ℝ) / p^2 else 0) := by
          rw [ Finset.sum_image ];
          · rw [ Finset.sum_filter ] ; gcongr ; aesop;
          · intro x hx y hy; aesop;
        refine' le_trans h_sum_le ( Summable.sum_le_tsum _ _ _ );
        · exact fun _ _ => by positivity;
        · exact Summable.of_nonneg_of_le ( fun p => by positivity ) ( fun p => by aesop ) ( Real.summable_one_div_nat_pow.2 one_lt_two );
    · have h_summable_bad_pairs : Summable (fun x : ℕ × ℕ => if x.1.Prime ∧ x.2.Prime ∧ x.1 < x.2 ∧ x.2 ≤ 2 * x.1 then 1 / (x.1 * x.2 : ℝ) else 0) := by
        convert lem_close_pairs_series hChebyshev using 1;
      have h_summable_bad_pairs : Summable (fun d : ℕ => ∑ x ∈ Finset.filter (fun x => x.1 * x.2 = d) (Finset.product (Finset.range (d + 1)) (Finset.range (d + 1))), if x.1.Prime ∧ x.2.Prime ∧ x.1 < x.2 ∧ x.2 ≤ 2 * x.1 then 1 / (x.1 * x.2 : ℝ) else 0) := by
        refine' summable_of_sum_le _ _;
        exact ∑' x : ℕ × ℕ, if Nat.Prime x.1 ∧ Nat.Prime x.2 ∧ x.1 < x.2 ∧ x.2 ≤ 2 * x.1 then 1 / ( x.1 * x.2 : ℝ ) else 0;
        · exact fun _ => Finset.sum_nonneg fun _ _ => by positivity;
        · intro u;
          refine' le_trans _ ( Summable.sum_le_tsum _ _ h_summable_bad_pairs );
          rotate_left;
          exact Finset.biUnion u fun x => Finset.filter ( fun y => y.1 * y.2 = x ) ( Finset.product ( Finset.range ( x + 1 ) ) ( Finset.range ( x + 1 ) ) );
          · exact fun _ _ => by positivity;
          · rw [ Finset.sum_biUnion ];
            intro x hx y hy hxy; simp_all +decide [ Finset.disjoint_left ] ;
      refine' h_summable_bad_pairs.of_nonneg_of_le ( fun d => _ ) ( fun d => _ );
      · positivity;
      · split_ifs <;> norm_num;
        · rename_i hd;
          obtain ⟨ p, q, hpq, rfl ⟩ := hd;
          refine' le_trans _ ( Finset.single_le_sum ( fun x _ => by positivity ) ( show ( p, q ) ∈ Finset.filter ( fun x => x.1 * x.2 = p * q ) ( Finset.product ( Finset.range ( p * q + 1 ) ) ( Finset.range ( p * q + 1 ) ) ) from _ ) ) <;> norm_num;
          · rw [ if_pos ⟨ hpq.1, hpq.2.1, hpq.2.2.1, hpq.2.2.2 ⟩, mul_comm ];
          · constructor <;> nlinarith [ hpq.1.two_le, hpq.2.1.two_le ];
        · exact Finset.sum_nonneg fun _ _ => by positivity;
  refine' Summable.of_nonneg_of_le ( fun d => _ ) ( fun d => _ ) ( h_split_sum.1.add h_split_sum.2 );
  · positivity;
  · split_ifs <;> norm_num;
    cases ‹d ∈ ForbiddenDivisors› <;> tauto

/-
Definitions of upper, lower, and natural density.
-/
noncomputable def upperDensity (E : Set ℕ) : ℝ :=
  Filter.limsup (fun X : ℕ => ((Finset.filter (· ∈ E) (Finset.Icc 1 X)).card : ℝ) / X) Filter.atTop

noncomputable def lowerDensity (E : Set ℕ) : ℝ :=
  Filter.liminf (fun X : ℕ => ((Finset.filter (· ∈ E) (Finset.Icc 1 X)).card : ℝ) / X) Filter.atTop

def HasNaturalDensity (E : Set ℕ) : Prop := upperDensity E = lowerDensity E

noncomputable def naturalDensity (E : Set ℕ) : ℝ := upperDensity E

set_option maxHeartbeats 0 in
/-
Lemma 4: The set $\{n\in\N:\ n\equiv a\pmod m\}$ has density $1/m$.
-/
lemma lem_APdensity (m : ℕ) (a : ℕ) (hm : m > 0) (ha : a < m) :
  HasNaturalDensity {n | n % m = a} ∧ naturalDensity {n | n % m = a} = 1 / m := by
    -- The set {n | n ≡ a (mod m)} is periodic with period m, so its density is 1/m.
    have h_periodic : ∀ X : ℕ, X ≥ 1 → ((Finset.filter (fun n => n % m = a) (Finset.Icc 1 X)).card : ℝ) / X ≤ 1 / m + 1 / X := by
      -- The cardinality of the set {n ∈ Finset.Icc 1 X | n % m = a} is at most (X / m) + 1.
      have h_card : ∀ X : ℕ, X ≥ 1 → ((Finset.filter (fun n => n % m = a) (Finset.Icc 1 X)).card : ℝ) ≤ (X / m : ℝ) + 1 := by
        intro X hX
        have h_card : ((Finset.filter (fun n => n % m = a) (Finset.Icc 1 X)).card : ℝ) ≤ (Finset.image (fun n => n / m) (Finset.filter (fun n => n % m = a) (Finset.Icc 1 X))).card := by
          rw [ Finset.card_image_of_injOn ];
          intro x hx y hy; have := Nat.mod_add_div x m; have := Nat.mod_add_div y m; aesop;
        refine le_trans h_card ?_;
        refine' le_trans ( Nat.cast_le.mpr <| Finset.card_le_card <| Finset.image_subset_iff.mpr _ ) _;
        exact Finset.Icc 0 ( X / m );
        · exact fun x hx => Finset.mem_Icc.mpr ⟨ Nat.zero_le _, Nat.div_le_div_right <| Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2 ⟩;
        · norm_num [ Nat.cast_div, hm ];
          rw [ le_div_iff₀ ] <;> norm_cast ; linarith [ Nat.div_mul_le_self X m ];
      intro X hX; rw [ div_le_iff₀ ( by positivity ) ] ; convert h_card X hX using 1 ; ring_nf;
      rw [ mul_inv_cancel₀ ( by positivity ), add_comm ];
    -- The set {n | n ≡ a (mod m)} is periodic with period m, so its density is 1/m. We can use the fact that the density of a periodic set is the reciprocal of its period.
    have h_periodic_density : Filter.Tendsto (fun X : ℕ => ((Finset.filter (fun n => n % m = a) (Finset.Icc 1 X)).card : ℝ) / X) Filter.atTop (nhds (1 / m)) := by
      have h_periodic_density : ∀ X : ℕ, X ≥ 1 → ((Finset.filter (fun n => n % m = a) (Finset.Icc 1 X)).card : ℝ) / X ≥ 1 / m - 1 / X := by
        -- Let's choose any $X \geq 1$.
        intro X hX_pos
        have h_floor : ((Finset.filter (fun n => n % m = a) (Finset.Icc 1 X)).card : ℝ) ≥ (X / m : ℝ) - 1 := by
          -- The set $\{n \in \mathbb{N} : n \equiv a \pmod{m}\}$ is periodic with period $m$, so its cardinality in any interval of length $m$ is exactly $1$.
          have h_periodic_card : ∀ k : ℕ, ((Finset.filter (fun n => n % m = a) (Finset.Icc (k * m + 1) ((k + 1) * m))).card : ℝ) ≥ 1 := by
            intro k
            have h_exists : ∃ n ∈ Finset.Icc (k * m + 1) ((k + 1) * m), n % m = a := by
              by_cases ha0 : a = 0;
              · exact ⟨ ( k + 1 ) * m, Finset.mem_Icc.mpr ⟨ by nlinarith, by nlinarith ⟩, by simp +decide [ ha0 ] ⟩;
              · exact ⟨ k * m + a, Finset.mem_Icc.mpr ⟨ by nlinarith [ Nat.pos_of_ne_zero ha0 ], by nlinarith ⟩, by simp +decide [ Nat.add_mod, Nat.mod_eq_of_lt ha ] ⟩;
            exact_mod_cast Finset.card_pos.mpr ⟨ h_exists.choose, Finset.mem_filter.mpr ⟨ h_exists.choose_spec.1, h_exists.choose_spec.2 ⟩ ⟩;
          -- By summing the cardinalities of the intervals, we get the total cardinality.
          have h_sum_card : ((Finset.filter (fun n => n % m = a) (Finset.Icc 1 X)).card : ℝ) ≥ ∑ k ∈ Finset.range (X / m), ((Finset.filter (fun n => n % m = a) (Finset.Icc (k * m + 1) ((k + 1) * m))).card : ℝ) := by
            have h_sum_card : ((Finset.filter (fun n => n % m = a) (Finset.Icc 1 (X / m * m))).card : ℝ) ≥ ∑ k ∈ Finset.range (X / m), ((Finset.filter (fun n => n % m = a) (Finset.Icc (k * m + 1) ((k + 1) * m))).card : ℝ) := by
              have h_sum_card : Finset.filter (fun n => n % m = a) (Finset.Icc 1 (X / m * m)) = Finset.biUnion (Finset.range (X / m)) (fun k => Finset.filter (fun n => n % m = a) (Finset.Icc (k * m + 1) ((k + 1) * m))) := by
                ext n; simp [Finset.mem_biUnion, Finset.mem_filter];
                constructor;
                · intro hn
                  use (n - 1) / m;
                  exact ⟨ Nat.div_lt_of_lt_mul <| by linarith [ Nat.sub_add_cancel hn.1.1 ], ⟨ by linarith [ Nat.div_mul_le_self ( n - 1 ) m, Nat.sub_add_cancel hn.1.1 ], by linarith [ Nat.div_add_mod ( n - 1 ) m, Nat.mod_lt ( n - 1 ) hm, Nat.sub_add_cancel hn.1.1 ] ⟩, hn.2 ⟩;
                · rintro ⟨ k, hk₁, ⟨ hk₂, hk₃ ⟩, hk₄ ⟩ ; exact ⟨ ⟨ by nlinarith, by nlinarith [ Nat.div_mul_le_self X m ] ⟩, hk₄ ⟩;
              rw [ h_sum_card, Finset.card_biUnion ];
              · norm_cast;
              · intros k hk l hl hkl; simp_all +decide [ Finset.disjoint_left ];
                intro n hn₁ hn₂ hn₃ hn₄; contrapose! hkl; nlinarith;
            exact h_sum_card.trans ( mod_cast Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.Icc_subset_Icc_right <| Nat.div_mul_le_self _ _ );
          refine le_trans ?_ h_sum_card;
          refine' le_trans _ ( Finset.sum_le_sum fun _ _ => h_periodic_card _ ) ; norm_num;
          rw [ div_le_iff₀ ] <;> norm_cast ; linarith [ Nat.div_add_mod X m, Nat.mod_lt X hm ];
        field_simp;
        nlinarith [ show ( m : ℝ ) ≥ 1 by norm_cast, div_mul_cancel₀ ( X : ℝ ) ( show ( m : ℝ ) ≠ 0 by positivity ) ];
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' ( by simpa using tendsto_const_nhds.sub ( tendsto_inverse_atTop_nhds_zero_nat ) ) ( by simpa using tendsto_const_nhds.add ( tendsto_inverse_atTop_nhds_zero_nat ) ) ( Filter.eventually_atTop.mpr ⟨ 1, fun X hX => h_periodic_density X hX ⟩ ) ( Filter.eventually_atTop.mpr ⟨ 1, fun X hX => h_periodic X hX ⟩ );
    unfold HasNaturalDensity naturalDensity;
    rw [ show upperDensity { n | n % m = a } = 1 / m from ?_, show lowerDensity { n | n % m = a } = 1 / m from ?_ ];
    · norm_num [ hm.ne' ];
    · convert h_periodic_density.liminf_eq using 1;
      unfold lowerDensity; norm_num [ Filter.limsup_eq, Filter.liminf_eq ] ;
      convert rfl;
    · convert h_periodic_density.limsup_eq using 1;
      unfold upperDensity;
      norm_num [ Finset.filter_congr ];
      convert rfl

/-
The intersection of the arithmetic progressions $n \equiv a \pmod L$ and $n \equiv b \pmod d$ (where $\gcd(L,d)=1$) is the arithmetic progression $n \equiv x \pmod{Ld}$ for some $x < Ld$.
-/
lemma crt_ap_intersection (L d : ℕ) (a b : ℕ) (hL : L > 0) (hd : d > 0) (hgcd : L.gcd d = 1) :
  ∃ x < L * d, {n | n % L = a % L ∧ n % d = b % d} = {n | n % (L * d) = x} := by
    -- By the Chinese Remainder Theorem, there exists a unique $x$ modulo $Ld$ such that $x \equiv a \pmod{L}$ and $x \equiv b \pmod{d}$.
    obtain ⟨x, hx⟩ : ∃ x, x < L * d ∧ x % L = a % L ∧ x % d = b % d := by
      have := Nat.chineseRemainder hgcd a b;
      exact ⟨ this.1 % ( L * d ), Nat.mod_lt _ ( Nat.mul_pos hL hd ), by simpa [ Nat.ModEq, Nat.mod_mod ] using this.2.1, by simpa [ Nat.ModEq, Nat.mod_mod ] using this.2.2 ⟩;
    refine' ⟨ x, hx.1, Set.ext fun n => ⟨ fun hn => _, fun hn => _ ⟩ ⟩ <;> simp_all +decide
    · -- By the Chinese Remainder Theorem, since $n \equiv x \pmod{L}$ and $n \equiv x \pmod{d}$, we have $n \equiv x \pmod{Ld}$.
      have h_crt : n ≡ x [MOD L] ∧ n ≡ x [MOD d] → n ≡ x [MOD (L * d)] := by
        rw [ Nat.modEq_and_modEq_iff_modEq_mul ] ; aesop;
        assumption;
      exact h_crt ⟨ hn.1.trans hx.2.1.symm, hn.2.trans hx.2.2.symm ⟩ ▸ Nat.mod_eq_of_lt hx.1;
    · exact ⟨ by rw [ ← Nat.mod_mod_of_dvd n ( dvd_mul_right L d ), hn, hx.2.1 ], by rw [ ← Nat.mod_mod_of_dvd n ( dvd_mul_left d L ), hn, hx.2.2 ] ⟩

/-
The set of integers $n$ such that $n \equiv 1 \pmod L$ and $d \mid n$ has natural density $1/(Ld)$, assuming $\gcd(L,d)=1$.
-/
lemma lem_CRTdensity (L d : ℕ) (hL : L > 0) (hd : d > 0) (hgcd : L.gcd d = 1) :
  HasNaturalDensity {n | n ≡ 1 [MOD L] ∧ d ∣ n} ∧ naturalDensity {n | n ≡ 1 [MOD L] ∧ d ∣ n} = 1 / (L * d) := by
    -- By `crt_ap_intersection`, there exists an `x < L * d` such that `{n | n ≡ 1 [MOD L] ∧ d ∣ n} = {n | n % (L * d) = x}`.
    obtain ⟨x, hx⟩ : ∃ x < L * d, {n | n ≡ 1 [MOD L] ∧ d ∣ n} = {n | n % (L * d) = x} := by
      convert crt_ap_intersection L d 1 0 hL hd hgcd using 3 ; simp +decide [ Nat.ModEq ];
      simp +decide [ Nat.dvd_iff_mod_eq_zero ];
    have := @lem_APdensity ( L * d ) x ?_ ?_ <;> aesop

/-
The upper density of a finite union of sets is at most the sum of their upper densities.
-/
lemma upper_density_finite_union_le {ι : Type*} (s : Finset ι) (E : ι → Set ℕ) :
  upperDensity (⋃ i ∈ s, E i) ≤ ∑ i ∈ s, upperDensity (E i) := by
    by_contra h_contra;
    -- By definition of upper density, we know that
    have h_upper_density : ∀ (E : Set ℕ), upperDensity E = sInf {a : ℝ | ∀ᶠ n in Filter.atTop, ((Finset.filter (fun x => x ∈ E) (Finset.Icc 1 n)).card : ℝ) / n ≤ a} := by
      exact fun E => rfl;
    simp_all +decide
    refine' h_contra.not_ge _;
    refine' le_of_forall_pos_le_add fun ε εpos => _;
    -- For each $i \in s$, there exists $a_i$ such that $\forallᶠ n in Filter.atTop, ((Finset.filter (fun x => x ∈ E i) (Finset.Icc 1 n)).card : ℝ) / n ≤ a_i$.
    obtain ⟨a, ha⟩ : ∃ a : ι → ℝ, (∀ i ∈ s, ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → ((Finset.filter (fun x => x ∈ E i) (Finset.Icc 1 b)).card : ℝ) / b ≤ a i) ∧ ∑ i ∈ s, a i ≤ ∑ i ∈ s, sInf {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → ((Finset.filter (fun x => x ∈ E i) (Finset.Icc 1 b)).card : ℝ) / b ≤ a} + ε := by
      have h_exists_a : ∀ i ∈ s, ∃ a_i, a_i ∈ {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → ((Finset.filter (fun x => x ∈ E i) (Finset.Icc 1 b)).card : ℝ) / b ≤ a} ∧ a_i ≤ sInf {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → ((Finset.filter (fun x => x ∈ E i) (Finset.Icc 1 b)).card : ℝ) / b ≤ a} + ε / (s.card + 1) := by
        intro i hi;
        have := exists_lt_of_csInf_lt ( show { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → ( Finset.card ( Finset.filter ( fun x => x ∈ E i ) ( Finset.Icc 1 b ) ) : ℝ ) / b ≤ a }.Nonempty from ?_ ) ( lt_add_of_pos_right _ ( div_pos εpos ( Nat.cast_add_one_pos s.card ) ) );
        · exact ⟨ this.choose, this.choose_spec.1, this.choose_spec.2.le ⟩;
        · exact ⟨ 1, ⟨ 1, fun n hn => div_le_one_of_le₀ ( mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by simp ) ) ( Nat.cast_nonneg _ ) ⟩ ⟩;
      choose! a ha₁ ha₂ using h_exists_a;
      exact ⟨ a, ha₁, le_trans ( Finset.sum_le_sum ha₂ ) ( by simp +decide [ Finset.sum_add_distrib ] ; nlinarith [ mul_div_cancel₀ ε ( by positivity : ( s.card : ℝ ) + 1 ≠ 0 ) ] ) ⟩;
    refine' le_trans ( csInf_le _ _ ) ha.2;
    · exact ⟨ 0, by rintro x ⟨ a_1, ha_1 ⟩ ; exact le_trans ( by positivity ) ( ha_1 _ le_rfl ) ⟩;
    · -- Since the cardinality of the union is at most the sum of the cardinalities of each E_i, we have:
      have h_card_union : ∀ b : ℕ, ((Finset.filter (fun x => ∃ i ∈ s, x ∈ E i) (Finset.Icc 1 b)).card : ℝ) ≤ ∑ i ∈ s, ((Finset.filter (fun x => x ∈ E i) (Finset.Icc 1 b)).card : ℝ) := by
        intro b
        have h_card_union : ((Finset.filter (fun x => ∃ i ∈ s, x ∈ E i) (Finset.Icc 1 b)).card : ℝ) ≤ ∑ i ∈ s, ((Finset.filter (fun x => x ∈ E i) (Finset.Icc 1 b)).card : ℝ) := by
          have h_card_union : Finset.filter (fun x => ∃ i ∈ s, x ∈ E i) (Finset.Icc 1 b) ⊆ Finset.biUnion s (fun i => Finset.filter (fun x => x ∈ E i) (Finset.Icc 1 b)) := by
            simp +contextual [ Finset.subset_iff ]
          exact_mod_cast le_trans ( Finset.card_le_card h_card_union ) ( Finset.card_biUnion_le );
        convert h_card_union using 1;
      choose! N hN using ha.1;
      refine' ⟨ Finset.sup s N + 1, fun b hb => _ ⟩;
      refine' le_trans ( div_le_div_of_nonneg_right ( h_card_union b ) ( Nat.cast_nonneg _ ) ) _;
      rw [ Finset.sum_div _ _ _ ] ; exact Finset.sum_le_sum fun i hi => hN i hi b ( le_trans ( Finset.le_sup hi ) ( Nat.le_of_succ_le hb ) )

/-
The set of integers not divisible by any element of F.
-/
def S_avoid (F : Set ℕ) : Set ℕ := {n | ∀ f ∈ F, ¬ f ∣ n}

/-
A periodic set has a natural density equal to the fraction of elements in one period.
-/
lemma periodic_has_density_value (S : Set ℕ) (M : ℕ) (hM : M > 0) (h_per : ∀ n, n ∈ S ↔ (n + M) ∈ S) :
  HasNaturalDensity S ∧ naturalDensity S = ((Finset.filter (· ∈ S) (Finset.range M)).card : ℝ) / M := by
    field_simp;
    -- By definition of periodicity, the number of elements in $S$ up to $X$ is approximately $(X/M) \cdot |S \cap \{0, 1, \ldots, M-1\}|$.
    have h_card_approx : Filter.Tendsto (fun X => ((Finset.filter (fun n => n ∈ S) (Finset.range X)).card : ℝ) / X) Filter.atTop (nhds ((Finset.card (Finset.filter (fun x => x ∈ S) (Finset.range M)) : ℝ) / M)) := by
      -- Let $c$ be the number of elements in $S \cap \{0, 1, \ldots, M-1\}$.
      set c := Finset.card (Finset.filter (fun x => x ∈ S) (Finset.range M)) with hc_def;
      -- By definition of $c$, we know that for any $X$, the number of elements in $S$ up to $X$ is approximately $c \cdot \frac{X}{M}$.
      have h_card_approx : ∀ X, ((Finset.filter (fun n => n ∈ S) (Finset.range X)).card : ℝ) ≤ c * (X / M + 1) ∧ ((Finset.filter (fun n => n ∈ S) (Finset.range X)).card : ℝ) ≥ c * (X / M - 1) := by
        intro X
        have h_card_approx : ((Finset.filter (fun n => n ∈ S) (Finset.range X)).card : ℝ) ≤ c * (X / M + 1) := by
          -- By definition of $c$, we know that for any $X$, the number of elements in $S$ up to $X$ is at most $c \cdot \frac{X}{M}$.
          have h_card_approx : ((Finset.filter (fun n => n ∈ S) (Finset.range X)).card : ℝ) ≤ c * (X / M + 1) := by
            have h_card_approx_step : ∀ k : ℕ, ((Finset.filter (fun n => n ∈ S) (Finset.range (k * M))).card : ℝ) ≤ c * k := by
              intro k
              induction' k with k ih;
              · norm_num +zetaDelta at *;
              · rw [ Nat.succ_mul, Finset.card_filter ];
                rw [ Finset.sum_range_add _ _ M ];
                norm_num [ Finset.sum_ite ] at *;
                rw [ show ( Finset.filter ( fun x => k * M + x ∈ S ) ( Finset.range M ) ) = Finset.image ( fun x => x ) ( Finset.filter ( fun x => x ∈ S ) ( Finset.range M ) ) from ?_ ];
                · norm_num [ mul_add ] at * ; linarith;
                · ext x; simp
                  exact fun hx => Nat.recOn k ( by norm_num ) fun n ihn => by rw [ Nat.succ_mul, ← add_right_comm, ← h_per ] ; exact ihn;
            have := h_card_approx_step ( X / M + 1 ) ; norm_num at *;
            refine' le_trans _ ( this.trans _ );
            · exact_mod_cast Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.range_mono <| by nlinarith [ Nat.div_add_mod X M, Nat.mod_lt X hM ] ;
            · exact mul_le_mul_of_nonneg_left ( add_le_add_right ( by rw [ le_div_iff₀ ( by positivity ) ] ; norm_cast; linarith [ Nat.div_mul_le_self X M ] ) _ ) ( Nat.cast_nonneg _ );
          convert h_card_approx using 1
        have h_card_approx_lower : ((Finset.filter (fun n => n ∈ S) (Finset.range X)).card : ℝ) ≥ c * (X / M - 1) := by
          -- By definition of $c$, we know that for any $X$, the number of elements in $S$ up to $X$ is at least $c \cdot \frac{X}{M}$.
          have h_card_approx_lower : ((Finset.filter (fun n => n ∈ S) (Finset.range X)).card : ℝ) ≥ c * (X / M - 1) := by
            have h_card_approx_lower_step : ∀ k : ℕ, ((Finset.filter (fun n => n ∈ S) (Finset.range (k * M))).card : ℝ) ≥ c * k := by
              intro k
              have h_card_approx_lower_step : ((Finset.filter (fun n => n ∈ S) (Finset.range (k * M))).card : ℝ) = ∑ i ∈ Finset.range k, ((Finset.filter (fun n => n ∈ S) (Finset.Ico (i * M) ((i + 1) * M))).card : ℝ) := by
                induction' k with k ih;
                · norm_num;
                · rw [ Finset.sum_range_succ, ← ih ];
                  rw_mod_cast [ ← Finset.card_union_of_disjoint ];
                  · congr with n ; simp +decide
                    exact ⟨ fun h => if h' : n < k * M then Or.inl ⟨ h', h.2 ⟩ else Or.inr ⟨ ⟨ by linarith, h.1 ⟩, h.2 ⟩, fun h => h.elim ( fun h => ⟨ by linarith, h.2 ⟩ ) fun h => ⟨ by linarith, h.2 ⟩ ⟩;
                  · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_range.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Ico.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;
              -- Since $S$ is periodic with period $M$, each interval $[iM, (i+1)M)$ contains exactly $c$ elements of $S$.
              have h_card_interval : ∀ i : ℕ, ((Finset.filter (fun n => n ∈ S) (Finset.Ico (i * M) ((i + 1) * M))).card : ℝ) = c := by
                intro i
                have h_card_interval : ((Finset.filter (fun n => n ∈ S) (Finset.Ico (i * M) ((i + 1) * M))).card : ℝ) = ((Finset.filter (fun n => n ∈ S) (Finset.range M)).card : ℝ) := by
                  rw [ Finset.card_filter, Finset.card_filter ];
                  rw [ Finset.sum_Ico_eq_sum_range ] ; norm_num [ add_mul, Finset.sum_range_succ' ] ; ring_nf;
                  exact congr_arg Finset.card ( Finset.filter_congr fun x hx => by exact Nat.recOn i ( by norm_num ) fun n ihn => by rw [ Nat.succ_mul, ← add_right_comm, ← h_per ] ; exact ihn );
                exact h_card_interval.trans ( by rfl );
              simp_all +singlePass [ mul_comm ]
            have := h_card_approx_lower_step ( X / M );
            refine le_trans ?_ ( this.trans ?_ );
            · exact mul_le_mul_of_nonneg_left ( sub_le_iff_le_add.mpr <| by rw [ div_le_iff₀ <| by positivity ] ; norm_cast ; linarith [ Nat.div_add_mod X M, Nat.mod_lt X hM ] ) <| Nat.cast_nonneg _;
            · exact_mod_cast Finset.card_mono <| Finset.filter_subset_filter _ <| Finset.range_mono <| Nat.div_mul_le_self _ _;
          exact h_card_approx_lower
        exact ⟨h_card_approx, h_card_approx_lower⟩;
      -- Using the bounds from h_card_approx, we can show that the ratio of the number of elements in S up to X to X converges to c / M.
      have h_ratio_bounds : ∀ X : ℕ, X > 0 → ((Finset.filter (fun n => n ∈ S) (Finset.range X)).card : ℝ) / X ≤ c / M + c / X ∧ ((Finset.filter (fun n => n ∈ S) (Finset.range X)).card : ℝ) / X ≥ c / M - c / X := by
        intro X hX_pos
        specialize h_card_approx X
        field_simp [hX_pos] at h_card_approx ⊢
        exact ⟨by
        exact h_card_approx.left, by
          exact h_card_approx.2.trans ( by norm_num )⟩
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' ( by simpa using tendsto_const_nhds.sub ( tendsto_const_nhds.mul tendsto_inverse_atTop_nhds_zero_nat ) ) ( by simpa using tendsto_const_nhds.add ( tendsto_const_nhds.mul tendsto_inverse_atTop_nhds_zero_nat ) ) ( Filter.eventually_atTop.mpr ⟨ 1, fun X hX => h_ratio_bounds X hX |>.2 ⟩ ) ( Filter.eventually_atTop.mpr ⟨ 1, fun X hX => h_ratio_bounds X hX |>.1 ⟩ );
    unfold HasNaturalDensity naturalDensity;
    unfold upperDensity lowerDensity;
    -- Since these two limits are equal, we can conclude that the natural density exists and is equal to the fraction of elements in one period.
    have h_nat_density : Filter.Tendsto (fun X => ((Finset.filter (fun n => n ∈ S) (Finset.Icc 1 X)).card : ℝ) / X) Filter.atTop (nhds ((Finset.card (Finset.filter (fun x => x ∈ S) (Finset.range M)) : ℝ) / M)) := by
      have h_nat_density : Filter.Tendsto (fun X => ((Finset.filter (fun n => n ∈ S) (Finset.range (X + 1))).card : ℝ) / X) Filter.atTop (nhds ((Finset.card (Finset.filter (fun x => x ∈ S) (Finset.range M)) : ℝ) / M)) := by
        have h_nat_density : Filter.Tendsto (fun X => ((Finset.filter (fun n => n ∈ S) (Finset.range (X + 1))).card : ℝ) / (X + 1)) Filter.atTop (nhds ((Finset.card (Finset.filter (fun x => x ∈ S) (Finset.range M)) : ℝ) / M)) := by
          exact_mod_cast h_card_approx.comp ( Filter.tendsto_add_atTop_nat 1 );
        have h_nat_density : Filter.Tendsto (fun X => ((Finset.filter (fun n => n ∈ S) (Finset.range (X + 1))).card : ℝ) / (X + 1) * (X + 1) / X) Filter.atTop (nhds ((Finset.card (Finset.filter (fun x => x ∈ S) (Finset.range M)) : ℝ) / M)) := by
          have h_nat_density : Filter.Tendsto (fun X => ((Finset.filter (fun n => n ∈ S) (Finset.range (X + 1))).card : ℝ) / (X + 1) * (1 + 1 / X)) Filter.atTop (nhds ((Finset.card (Finset.filter (fun x => x ∈ S) (Finset.range M)) : ℝ) / M)) := by
            convert h_nat_density.mul ( tendsto_const_nhds.add ( tendsto_one_div_atTop_nhds_zero_nat ) ) using 2 ; ring;
          refine h_nat_density.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with X hX using by rw [ one_add_div ( by positivity ) ] ; ring );
        exact h_nat_density.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with X hX using by rw [ div_mul_cancel₀ _ ( by positivity ) ] );
      have h_nat_density : ∀ X : ℕ, ((Finset.filter (fun n => n ∈ S) (Finset.Icc 1 X)).card : ℝ) = ((Finset.filter (fun n => n ∈ S) (Finset.range (X + 1))).card : ℝ) - (if 0 ∈ S then 1 else 0) := by
        intro X; rw [ Finset.range_eq_Ico ] ; rw [ Finset.Ico_eq_cons_Ioo, Finset.filter_cons ] <;> norm_num;
        split_ifs <;> norm_num [ Finset.filter_insert, Finset.filter_singleton ];
        · exact rfl;
        · exact rfl;
      convert ‹Filter.Tendsto ( fun X : ℕ => ( Finset.card ( Finset.filter ( fun n => n ∈ S ) ( Finset.range ( X + 1 ) ) ) : ℝ ) / X ) Filter.atTop ( nhds ( Finset.card ( Finset.filter ( fun x => x ∈ S ) ( Finset.range M ) ) / M ) ) ›.sub ( show Filter.Tendsto ( fun X : ℕ => ( if 0 ∈ S then 1 else 0 : ℝ ) / X ) Filter.atTop ( nhds 0 ) from tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop ) using 2 <;> norm_num [ h_nat_density ];
      ring;
    rw [ h_nat_density.limsup_eq, h_nat_density.liminf_eq ];
    exact ⟨ rfl, div_mul_cancel₀ _ <| Nat.cast_ne_zero.mpr hM.ne' ⟩

/-
The set of integers avoiding a finite set of positive divisors has a natural density.
-/
lemma S_avoid_finite_has_density (F : Set ℕ) (hF : F.Finite) (hF_pos : ∀ f ∈ F, f > 0) : HasNaturalDensity (S_avoid F) := by
  -- Let $M$ be the least common multiple of the elements in $F$.
  set M := hF.toFinset.prod id with hM_def
  have hM_gt_zero : M > 0 := by
    exact Finset.prod_pos fun x hx => hF_pos x <| hF.mem_toFinset.mp hx
  have h_periodic : ∀ n, n ∈ S_avoid F ↔ (n + M) ∈ S_avoid F := by
    intro n
    simp [S_avoid, hM_def];
    constructor <;> intro h f hf <;> specialize h f hf <;> simp_all +decide [ Finset.prod_eq_prod_diff_singleton_mul ( hF.mem_toFinset.mpr hf ) ];
    · rwa [ Nat.dvd_add_left ( dvd_mul_left _ _ ) ];
    · exact fun hn => h ( dvd_add hn ( dvd_mul_left _ _ ) );
  convert periodic_has_density_value _ _ hM_gt_zero _ |> And.left using 1;
  exact h_periodic

/-
The difference between the set avoiding the truncated set and the set avoiding the full set is contained in the union of multiples of elements in the tail.
-/
lemma S_avoid_diff_subset_tail (F : Set ℕ) (T : ℕ) :
  S_avoid {f ∈ F | f ≤ T} \ S_avoid F ⊆ ⋃ f ∈ {x ∈ F | x > T}, {n | f ∣ n} := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := hn
    simp [S_avoid] at hn1 hn2;
    exact Set.mem_iUnion₂.mpr ( by obtain ⟨ f, hf1, hf2 ⟩ := hn2; exact ⟨ f, ⟨ hf1, not_le.mp fun hf3 => hn1 f hf1 hf3 hf2 ⟩, hf2 ⟩ )

set_option maxHeartbeats 0 in
/-
The upper density of a countable union of sets is bounded by the sum of their upper densities, provided the sum converges.
-/
lemma upper_density_multiples_tail_bound (F : Set ℕ) (T : ℕ) (hF_subset : F ⊆ {n | 1 ≤ n})
  (h_summable : Summable (fun f => if f ∈ F then 1 / (f : ℝ) else 0)) :
  upperDensity (⋃ f ∈ {x ∈ F | x > T}, {n | f ∣ n}) ≤ ∑' f, if f ∈ F ∧ f > T then 1 / (f : ℝ) else 0 := by
    have h_upper_density_multiples_tail_bound : ∀ s : Finset ℕ, upperDensity (⋃ f ∈ s.filter (fun f => f > T ∧ f ∈ F), {n | f ∣ n}) ≤ ∑ f ∈ s.filter (fun f => f > T ∧ f ∈ F), (1 / (f : ℝ)) := by
      intros s
      have h_upper_density_multiples_tail_bound : upperDensity (⋃ f ∈ s.filter (fun f => f > T ∧ f ∈ F), {n | f ∣ n}) ≤ ∑ f ∈ s.filter (fun f => f > T ∧ f ∈ F), upperDensity {n | f ∣ n} := by
        convert upper_density_finite_union_le ( s.filter ( fun f => f > T ∧ f ∈ F ) ) _;
      refine le_trans h_upper_density_multiples_tail_bound <| Finset.sum_le_sum fun f hf => ?_;
      -- The set of multiples of $f$ has density $1/f$.
      have h_density_multiples : HasNaturalDensity {n | f ∣ n} ∧ naturalDensity {n | f ∣ n} = 1 / (f : ℝ) := by
        convert lem_APdensity f 0 ( Nat.pos_of_ne_zero ( by linarith [ Finset.mem_filter.mp hf, hF_subset ( Finset.mem_filter.mp hf |>.2.2 ) ] ) ) ( Nat.pos_of_ne_zero ( by linarith [ Finset.mem_filter.mp hf, hF_subset ( Finset.mem_filter.mp hf |>.2.2 ) ] ) ) using 1;
        · simp +decide only [Nat.dvd_iff_mod_eq_zero];
        · simp +decide [ Nat.dvd_iff_mod_eq_zero ];
      exact h_density_multiples.2 ▸ le_rfl;
    refine' le_of_forall_pos_le_add fun ε ε_pos => _;
    -- Choose a finite subset $s$ of $F$ such that the sum of the reciprocals of the elements in $s$ is greater than the total sum minus $\epsilon$.
    obtain ⟨s, hs⟩ : ∃ s : Finset ℕ, (∑ f ∈ s.filter (fun f => f > T ∧ f ∈ F), (1 / (f : ℝ))) ≥ (∑' f, if f ∈ F ∧ f > T then (1 / (f : ℝ)) else 0) - ε / 2 := by
      have h_summable_tail : Summable (fun f : ℕ => if f ∈ F ∧ f > T then (1 / (f : ℝ)) else 0) := by
        exact Summable.of_nonneg_of_le ( fun f => by positivity ) ( fun f => by aesop ) h_summable;
      have := h_summable_tail.hasSum.tendsto_sum_nat;
      rcases Metric.tendsto_atTop.mp this ( ε / 2 ) ( half_pos ε_pos ) with ⟨ N, hN ⟩ ; use Finset.range N ; simp_all +decide [ Finset.sum_filter ];
      have := hN N le_rfl; rw [ dist_eq_norm ] at this; rw [ Real.norm_eq_abs ] at this; rw [ abs_lt ] at this; simp_all +decide [ and_comm ] ; linarith;
    have h_upper_density_multiples_tail_bound : upperDensity (⋃ f ∈ {x | x ∈ F ∧ x > T}, {n | f ∣ n}) ≤ upperDensity (⋃ f ∈ s.filter (fun f => f > T ∧ f ∈ F), {n | f ∣ n}) + upperDensity (⋃ f ∈ {x ∈ F | x > T} \ s.filter (fun f => f > T ∧ f ∈ F), {n | f ∣ n}) := by
      convert upper_density_finite_union_le { 0, 1 } ( fun i => if i = 0 then ⋃ f ∈ { f ∈ s | f > T ∧ f ∈ F }, { n | f ∣ n } else ⋃ f ∈ { x | x ∈ F ∧ x > T } \ ↑ ( { f ∈ s | f > T ∧ f ∈ F } ), { n | f ∣ n } ) |> le_trans <| _ using 1;
      · congr! 1;
        ext; simp [Set.mem_iUnion];
        grind;
      · grind;
    -- The upper density of the union of the sets {n | f ∣ n} for f in the tail (those not in s) is bounded by the sum of their densities.
    have h_upper_density_tail : upperDensity (⋃ f ∈ {x ∈ F | x > T} \ s.filter (fun f => f > T ∧ f ∈ F), {n | f ∣ n}) ≤ ∑' f : ℕ, if f ∈ F ∧ f > T ∧ f ∉ s.filter (fun f => f > T ∧ f ∈ F) then (1 / (f : ℝ)) else 0 := by
      have h_upper_density_tail : ∀ (s : Set ℕ), (∀ f ∈ s, f > 0) → Summable (fun f : ℕ => if f ∈ s then (1 / (f : ℝ)) else 0) → upperDensity (⋃ f ∈ s, {n | f ∣ n}) ≤ ∑' f : ℕ, if f ∈ s then (1 / (f : ℝ)) else 0 := by
        intros s hs_pos hs_summable
        have h_upper_density_tail : ∀ X : ℕ, ((Finset.filter (fun n => ∃ f ∈ s, f ∣ n) (Finset.Icc 1 X)).card : ℝ) ≤ X * (∑ f ∈ Finset.filter (fun f => f ∈ s) (Finset.range (X + 1)), (1 / (f : ℝ))) := by
          intros X
          have h_card : ((Finset.filter (fun n => ∃ f ∈ s, f ∣ n) (Finset.Icc 1 X)).card : ℝ) ≤ ∑ f ∈ Finset.filter (fun f => f ∈ s) (Finset.range (X + 1)), (Finset.card (Finset.filter (fun n => f ∣ n) (Finset.Icc 1 X)) : ℝ) := by
            have h_card : Finset.filter (fun n => ∃ f ∈ s, f ∣ n) (Finset.Icc 1 X) ⊆ Finset.biUnion (Finset.filter (fun f => f ∈ s) (Finset.range (X + 1))) (fun f => Finset.filter (fun n => f ∣ n) (Finset.Icc 1 X)) := by
              simp +contextual [ Finset.subset_iff ];
              exact fun x hx₁ hx₂ f hf₁ hf₂ => ⟨ f, ⟨ Nat.lt_succ_of_le ( Nat.le_trans ( Nat.le_of_dvd hx₁ hf₂ ) hx₂ ), hf₁ ⟩, hf₂ ⟩;
            exact_mod_cast le_trans ( Finset.card_le_card h_card ) ( Finset.card_biUnion_le );
          have h_card : ∀ f ∈ Finset.filter (fun f => f ∈ s) (Finset.range (X + 1)), (Finset.card (Finset.filter (fun n => f ∣ n) (Finset.Icc 1 X)) : ℝ) ≤ X / f := by
            intros f hf
            have h_card : (Finset.card (Finset.filter (fun n => f ∣ n) (Finset.Icc 1 X)) : ℝ) ≤ X / f := by
              have h_div : Finset.filter (fun n => f ∣ n) (Finset.Icc 1 X) ⊆ Finset.image (fun n => f * n) (Finset.Icc 1 (X / f)) := by
                simp +decide [ Finset.subset_iff ];
                exact fun x hx₁ hx₂ hx₃ => ⟨ x / f, ⟨ Nat.div_pos ( Nat.le_of_dvd hx₁ hx₃ ) ( hs_pos f ( Finset.mem_filter.mp hf |>.2 ) ), Nat.div_le_div_right hx₂ ⟩, Nat.mul_div_cancel' hx₃ ⟩
              exact le_trans ( Nat.cast_le.mpr ( Finset.card_le_card h_div ) ) ( by rw [ Finset.card_image_of_injective _ fun x y hxy => mul_left_cancel₀ ( ne_of_gt ( hs_pos f ( Finset.mem_filter.mp hf |>.2 ) ) ) hxy ] ; simpa using Nat.cast_div_le .. |> le_trans <| by norm_num )
            exact h_card
          simpa only [ Finset.mul_sum _ _ _, mul_one_div ] using le_trans ‹_› ( Finset.sum_le_sum h_card );
        have h_upper_density_tail : ∀ X : ℕ, ((Finset.filter (fun n => ∃ f ∈ s, f ∣ n) (Finset.Icc 1 X)).card : ℝ) / X ≤ ∑ f ∈ Finset.filter (fun f => f ∈ s) (Finset.range (X + 1)), (1 / (f : ℝ)) := by
          intro X; specialize h_upper_density_tail X; rcases eq_or_ne X 0 with rfl | hX <;> simp_all +decide
          · exact Finset.sum_nonneg fun _ _ => inv_nonneg.2 <| Nat.cast_nonneg _;
          · rwa [ div_le_iff₀' ( by positivity ) ];
        have h_upper_density_tail : Filter.limsup (fun X : ℕ => ((Finset.filter (fun n => ∃ f ∈ s, f ∣ n) (Finset.Icc 1 X)).card : ℝ) / X) Filter.atTop ≤ ∑' f : ℕ, if f ∈ s then (1 / (f : ℝ)) else 0 := by
          refine' le_trans ( Filter.limsup_le_of_le _ _ ) _;
          exact ∑' f : ℕ, if f ∈ s then 1 / ( f : ℝ ) else 0;
          · use 0; simp
            exact fun a x hx => le_trans ( by positivity ) ( hx x le_rfl );
          · filter_upwards [ Filter.eventually_gt_atTop 0 ] with X hX using le_trans ( h_upper_density_tail X ) ( by simpa [ Finset.sum_filter ] using Summable.sum_le_tsum ( Finset.range ( X + 1 ) ) ( fun _ _ => by positivity ) hs_summable );
          · norm_num +zetaDelta at *;
        unfold upperDensity; aesop;
      convert h_upper_density_tail ( { x ∈ F | x > T } \ s.filter ( fun f => f > T ∧ f ∈ F ) ) _ _ using 1;
      · simp +contextual [ and_assoc, and_comm, and_left_comm ];
      · exact fun f hf => hF_subset hf.1.1;
      · refine' Summable.of_nonneg_of_le ( fun f => by positivity ) ( fun f => _ ) h_summable;
        split_ifs <;> norm_num ; aesop;
    have h_upper_density_tail_sum : ∑' f : ℕ, (if f ∈ F ∧ f > T ∧ f ∉ s.filter (fun f => f > T ∧ f ∈ F) then (1 / (f : ℝ)) else 0) ≤ (∑' f : ℕ, if f ∈ F ∧ f > T then (1 / (f : ℝ)) else 0) - (∑ f ∈ s.filter (fun f => f > T ∧ f ∈ F), (1 / (f : ℝ))) := by
      have h_upper_density_tail_sum : ∑' f : ℕ, (if f ∈ F ∧ f > T ∧ f ∉ s.filter (fun f => f > T ∧ f ∈ F) then (1 / (f : ℝ)) else 0) = ∑' f : ℕ, (if f ∈ F ∧ f > T then (1 / (f : ℝ)) else 0) - ∑' f : ℕ, (if f ∈ F ∧ f > T ∧ f ∈ s.filter (fun f => f > T ∧ f ∈ F) then (1 / (f : ℝ)) else 0) := by
        rw [ ← Summable.tsum_sub ] ; congr ; ext f ; by_cases hf : f ∈ F <;> by_cases hf' : f > T <;> by_cases hf'' : f ∈ { f ∈ s | f > T ∧ f ∈ F } <;> simp +decide [ hf, hf', hf'' ] ;
        · exact Summable.of_nonneg_of_le ( fun f => by positivity ) ( fun f => by aesop ) h_summable;
        · refine' Summable.of_nonneg_of_le ( fun f => _ ) ( fun f => _ ) h_summable <;> aesop;
      convert h_upper_density_tail_sum.le using 2;
      rw [ tsum_eq_sum ];
      any_goals exact s.filter ( fun f => f > T ∧ f ∈ F );
      · exact Finset.sum_congr rfl fun x hx => by aesop;
      · aesop;
    linarith [ ‹∀ s : Finset ℕ, upperDensity ( ⋃ f ∈ { f ∈ s | f > T ∧ f ∈ F }, { n | f ∣ n } ) ≤ ∑ f ∈ s with f > T ∧ f ∈ F, 1 / ( f : ℝ ) › s ]

/-
The lower density of a set is always less than or equal to its upper density.
-/
lemma lower_le_upper_density (E : Set ℕ) : lowerDensity E ≤ upperDensity E := by
  -- The lower density is the liminf and the upper density is the limsup of the same sequence. Since the sequence is bounded (between 0 and 1), the liminf is less than or equal to the limsup.
  have h_bounds : ∀ n, ((Finset.filter (· ∈ E) (Finset.Icc 1 n)).card : ℝ) / n ≤ 1 ∧ 0 ≤ ((Finset.filter (· ∈ E) (Finset.Icc 1 n)).card : ℝ) / n := by
    exact fun n => ⟨ div_le_one_of_le₀ ( mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by norm_num ) ) ( Nat.cast_nonneg _ ), by positivity ⟩;
  apply_rules [ Filter.liminf_le_limsup ];
  · exact ⟨ 1, Filter.eventually_atTop.mpr ⟨ 1, fun n hn => h_bounds n |>.1 ⟩ ⟩;
  · exact ⟨ 0, Filter.eventually_atTop.mpr ⟨ 1, fun n hn => h_bounds n |>.2 ⟩ ⟩

/-
If a set has a natural density, the sequence of its densities converges to the natural density.
-/
lemma tendsto_density_of_has_natural_density (E : Set ℕ) (h : HasNaturalDensity E) :
  Filter.Tendsto (fun n => ((Finset.filter (· ∈ E) (Finset.Icc 1 n)).card : ℝ) / n) Filter.atTop (nhds (naturalDensity E)) := by
    -- Since the upper and lower densities are equal, the limit superior and limit inferior of the sequence of densities are equal.
    have h_lim_sup_inf : Filter.limsup (fun n : ℕ => ((Finset.filter (· ∈ E) (Finset.Icc 1 n)).card : ℝ) / n) Filter.atTop = Filter.liminf (fun n : ℕ => ((Finset.filter (· ∈ E) (Finset.Icc 1 n)).card : ℝ) / n) Filter.atTop := by
      exact h;
    convert tendsto_order.2 ⟨ _, _ ⟩;
    exact Real.instPreorder;
    · infer_instance;
    · intro a ha;
      contrapose! ha;
      refine' h_lim_sup_inf.le.trans _;
      refine' csSup_le _ _ <;> norm_num;
      · exact ⟨ 0, ⟨ 1, fun n hn => by positivity ⟩ ⟩;
      · exact fun b x hx => le_of_not_gt fun hx' => ha <| Filter.eventually_atTop.mpr ⟨ x, fun n hn => hx' |> lt_of_lt_of_le <| hx n hn ⟩;
    · intro a ha;
      have := h_lim_sup_inf ▸ Filter.limsup_eq;
      contrapose! ha;
      refine' le_trans _ ( this.ge.trans _ );
      · exact le_csInf ⟨ 1, Filter.eventually_atTop.mpr ⟨ 1, fun n hn => by rw [ div_le_iff₀ ] <;> norm_cast ; linarith [ show Finset.card ( Finset.filter ( fun x => x ∈ E ) ( Finset.Icc 1 n ) ) ≤ n from le_trans ( Finset.card_filter_le _ _ ) ( by simp ) ] ⟩ ⟩ fun x hx => le_of_not_gt fun hx' => ha <| hx.mono fun n hn => lt_of_le_of_lt hn hx';
      · exact le_of_eq this

/-
The upper density of a subset is less than or equal to the upper density of the superset.
-/
lemma upperDensity_mono {A B : Set ℕ} (h : A ⊆ B) : upperDensity A ≤ upperDensity B := by
  apply_rules [ Filter.limsup_le_limsup ];
  · filter_upwards [ Filter.eventually_gt_atTop 0 ] with X hX using by gcongr ; exact fun x hx => by aesop;
  · refine' ⟨ 0, _ ⟩;
    intro a ha; obtain ⟨ X, hX ⟩ := Filter.eventually_atTop.mp ha; exact le_trans ( by positivity ) ( hX _ le_rfl ) ;
  · refine' ⟨ 1, Filter.eventually_atTop.2 ⟨ 1, fun X hX => _ ⟩ ⟩;
    exact Set.mem_setOf_eq.mpr ( div_le_one_of_le₀ ( mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by simp ) ) ( by positivity ) )

/-
If $A \subseteq B$ and $B$ has a natural density, then $\underline{d}(A) \ge d(B) - \overline{d}(B \setminus A)$.
-/
lemma lower_density_diff_bound {A B : Set ℕ} (h_density : HasNaturalDensity B) :
  lowerDensity A ≥ naturalDensity B - upperDensity (B \ A) := by
    -- By definition of density, we have:
    have h_lower_bound : ∀ n : ℕ, ((Finset.filter (· ∈ B) (Finset.Icc 1 n)).card : ℝ) ≤ ((Finset.filter (· ∈ A) (Finset.Icc 1 n)).card : ℝ) + ((Finset.filter (· ∈ B \ A) (Finset.Icc 1 n)).card : ℝ) := by
      intro n; norm_cast; rw [ ← Finset.card_union_add_card_inter ] ;
      exact le_add_right ( Finset.card_mono fun x hx => by by_cases hx' : x ∈ A <;> aesop );
    -- By dividing both sides of the inequality by $n$ and taking limits, we get:
    have h_divide_bound : Filter.Tendsto (fun n : ℕ => ((Finset.filter (· ∈ B) (Finset.Icc 1 n)).card : ℝ) / n) Filter.atTop (nhds (naturalDensity B)) := by
      exact tendsto_density_of_has_natural_density B h_density;
    -- By definition of upper density, we have:
    have h_upper_density : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ((Finset.filter (· ∈ B \ A) (Finset.Icc 1 n)).card : ℝ) / n ≤ upperDensity (B \ A) + ε := by
      intro ε ε_pos
      have h_upper_density : Filter.limsup (fun n : ℕ => ((Finset.filter (· ∈ B \ A) (Finset.Icc 1 n)).card : ℝ) / n) Filter.atTop ≤ upperDensity (B \ A) := by
        unfold upperDensity; aesop;
      contrapose! h_upper_density;
      refine' lt_of_lt_of_le ( lt_add_of_pos_right _ ε_pos ) ( le_csInf _ _ ) <;> norm_num;
      · exact ⟨ 1, ⟨ 1, fun n hn => div_le_one_of_le₀ ( mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by norm_num ) ) ( Nat.cast_nonneg _ ) ⟩ ⟩;
      · intro b x hx; obtain ⟨ n, hn₁, hn₂ ⟩ := h_upper_density x; exact le_trans ( le_of_lt hn₂ ) ( hx n hn₁ ) ;
    -- By combining the results from h_divide_bound and h_upper_density, we get:
    have h_combined : ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ((Finset.filter (· ∈ A) (Finset.Icc 1 n)).card : ℝ) / n ≥ (naturalDensity B) - (upperDensity (B \ A) + ε) := by
      intro ε hε_pos
      obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n ≥ N₁, ((Finset.filter (· ∈ B) (Finset.Icc 1 n)).card : ℝ) / n ≥ naturalDensity B - ε / 2 := by
        exact Filter.eventually_atTop.mp ( h_divide_bound.eventually ( le_mem_nhds ( by linarith ) ) );
      obtain ⟨ N₂, hN₂ ⟩ := h_upper_density ( ε / 2 ) ( half_pos hε_pos ) ; use Max.max N₁ N₂; intros n hn; specialize hN₁ n ( le_trans ( le_max_left _ _ ) hn ) ; specialize hN₂ n ( le_trans ( le_max_right _ _ ) hn ) ; simp_all +decide [ div_eq_mul_inv ] ;
      nlinarith [ h_lower_bound n, inv_nonneg.2 ( show ( n : ℝ ) ≥ 0 by positivity ) ];
    refine' le_of_forall_pos_le_add fun ε ε_pos => _;
    refine' le_trans _ ( add_le_add_right ( le_csSup _ <| show naturalDensity B - ( upperDensity ( B \ A ) + ε / 2 ) ∈ _ from _ ) _ );
    · linarith;
    · exact ⟨ 1, fun x hx => by rcases Filter.eventually_atTop.mp hx with ⟨ n, hn ⟩ ; exact le_trans ( hn _ le_rfl ) ( div_le_one_of_le₀ ( mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by norm_num ) ) ( Nat.cast_nonneg _ ) ) ⟩;
    · aesop

/-
The upper density of the difference between the truncated avoidance set and the full avoidance set is bounded by the tail sum of reciprocals.
-/
lemma upper_density_diff_le_tail (F : Set ℕ) (T : ℕ) (hF_subset : F ⊆ {n | 1 ≤ n})
  (h_summable : Summable (fun f => if f ∈ F then 1 / (f : ℝ) else 0)) :
  upperDensity (S_avoid {f ∈ F | f ≤ T} \ S_avoid F) ≤ ∑' f, if f ∈ F ∧ f > T then 1 / (f : ℝ) else 0 := by
    refine' le_trans ( upperDensity_mono <| _ ) ( upper_density_multiples_tail_bound F T hF_subset _ );
    · exact S_avoid_diff_subset_tail F T;
    · convert h_summable using 1

/-
Let $\mathcal{F}\subseteq\{2,3,4,\dots\}$ be a set of integers with $\sum_{f\in\mathcal{F}}1/f<\infty$. Define
\[
S(\mathcal{F}):=\{n\in\N:\ f\nmid n\ \text{for every } f\in\mathcal{F}\}.
\]
Then $S(\mathcal{F})$ has a natural density.
-/
theorem prop_avoid_density (F : Set ℕ) (hF_subset : F ⊆ {n | 2 ≤ n})
  (h_summable : Summable (fun f => if f ∈ F then 1 / (f : ℝ) else 0)) :
  HasNaturalDensity (S_avoid F) := by
    -- Apply the lemma that states the lower density of A is at least the natural density of B minus the upper density of B \ A.
    have h_lower_density : ∀ T : ℕ, lowerDensity (S_avoid F) ≥ naturalDensity (S_avoid {f ∈ F | f ≤ T}) - upperDensity (S_avoid {f ∈ F | f ≤ T} \ S_avoid F) := by
      intro T
      apply lower_density_diff_bound;
      · convert S_avoid_finite_has_density { f ∈ F | f ≤ T } _ _ using 1;
        · exact Set.finite_iff_bddAbove.mpr ⟨ T, fun x hx => hx.2 ⟩;
        · exact fun f hf => lt_of_lt_of_le ( by norm_num ) ( hF_subset hf.1 );
    -- Since $\delta_T$ is nonincreasing in $T$ and bounded below by $0$, $\delta_T$ has a limit $\delta:=\lim_{T\to\infty}\delta_T$.
    obtain ⟨δ, hδ⟩ : ∃ δ, Filter.Tendsto (fun T => naturalDensity (S_avoid {f ∈ F | f ≤ T})) Filter.atTop (nhds δ) := by
      have h_noninc : Antitone (fun T => naturalDensity (S_avoid {f ∈ F | f ≤ T})) := by
        refine' antitone_nat_of_succ_le _;
        intro T; exact (by
        apply_rules [ upperDensity_mono ];
        exact fun x hx => fun f hf => hx f ⟨ hf.1, by linarith [ hf.2 ] ⟩);
      exact ⟨ _, tendsto_atTop_ciInf h_noninc ⟨ 0, Set.forall_mem_range.mpr fun T => by exact le_trans ( by norm_num ) ( show 0 ≤ naturalDensity ( S_avoid { f | f ∈ F ∧ f ≤ T } ) from by exact le_trans ( by norm_num ) ( show 0 ≤ Filter.limsup ( fun X => ( Finset.card ( Finset.filter ( · ∈ S_avoid { f | f ∈ F ∧ f ≤ T } ) ( Finset.Icc 1 X ) ) : ℝ ) / X ) Filter.atTop from by exact Real.sInf_nonneg fun x hx => by rcases Filter.eventually_atTop.mp hx with ⟨ N, hN ⟩ ; exact le_trans ( by positivity ) ( hN _ le_rfl ) ) ) ⟩ ⟩;
    -- Since $\sum_{f\in\mathcal{F}}1/f<\infty$, the tail $\sum_{f\in\mathcal{F},\,f>T}1/f\to 0$ as $T\to\infty$.
    have h_tail_zero : Filter.Tendsto (fun T => ∑' f, if f ∈ F ∧ f > T then 1 / (f : ℝ) else 0) Filter.atTop (nhds 0) := by
      have h_tail_zero : Filter.Tendsto (fun T => ∑' f, (if f ∈ F then (1 / (f : ℝ)) else 0) * (if f > T then 1 else 0)) Filter.atTop (nhds (∑' f, (if f ∈ F then (1 / (f : ℝ)) else 0) * 0)) := by
        refine' ( tendsto_tsum_of_dominated_convergence _ _ _ );
        use fun k => if k ∈ F then 1 / ( k : ℝ ) else 0;
        · convert h_summable using 1;
        · intro k; exact tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop k ] with x hx; split_ifs <;> linarith ) ;
        · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using fun k => by split_ifs <;> norm_num;
      convert h_tail_zero using 2 <;> norm_num [ mul_assoc, mul_comm, mul_left_comm ];
      exact tsum_congr fun _ => by split_ifs <;> tauto;
    -- By combining the results from h_lower_density, h_upper_density, and h_tail_zero, we get:
    have h_squeeze : δ ≤ lowerDensity (S_avoid F) ∧ lowerDensity (S_avoid F) ≤ upperDensity (S_avoid F) ∧ upperDensity (S_avoid F) ≤ δ := by
      have h_squeeze : ∀ T : ℕ, lowerDensity (S_avoid F) ≥ naturalDensity (S_avoid {f ∈ F | f ≤ T}) - ∑' f, if f ∈ F ∧ f > T then 1 / (f : ℝ) else 0 := by
        intros T
        specialize h_lower_density T
        have h_upper_density : upperDensity (S_avoid {f ∈ F | f ≤ T} \ S_avoid F) ≤ ∑' f, if f ∈ F ∧ f > T then 1 / (f : ℝ) else 0 := by
          convert upper_density_diff_le_tail F T _ _ using 1;
          · exact fun x hx => Nat.one_le_of_lt ( hF_subset hx );
          · convert h_summable using 1
        linarith;
      have h_squeeze : ∀ T : ℕ, upperDensity (S_avoid F) ≤ naturalDensity (S_avoid {f ∈ F | f ≤ T}) := by
        intro T
        have h_subset : S_avoid F ⊆ S_avoid {f ∈ F | f ≤ T} := by
          exact fun x hx => fun f hf => hx f hf.1 |> fun h => by aesop;
        apply_rules [ upperDensity_mono ];
      have h_squeeze : Filter.Tendsto (fun T => naturalDensity (S_avoid {f ∈ F | f ≤ T}) - ∑' f, if f ∈ F ∧ f > T then 1 / (f : ℝ) else 0) Filter.atTop (nhds δ) := by
        simpa using hδ.sub h_tail_zero;
      exact ⟨ le_of_tendsto_of_tendsto' h_squeeze tendsto_const_nhds ‹_›, lower_le_upper_density _, le_of_tendsto_of_tendsto' tendsto_const_nhds hδ ‹_› ⟩;
    exact le_antisymm ( le_of_not_gt fun h => by linarith ) ( le_of_not_gt fun h => by linarith )

/-
The sum of reciprocals of forbidden divisors with all prime factors greater than K tends to 0 as K goes to infinity.
-/
def ForbiddenDivisorsWithMinPrime (K : ℕ) : Set ℕ :=
  {d ∈ ForbiddenDivisors | ∀ p, p.Prime → p ∣ d → p > K}

lemma forbidden_divisors_tail_sum_tendsto_zero (hChebyshev : ChebyshevUpperBound) :
  Filter.Tendsto (fun K => ∑' d, if d ∈ ForbiddenDivisorsWithMinPrime K then 1 / (d : ℝ) else 0) Filter.atTop (nhds 0) := by
    have h_tail_sum : Summable (fun d : ℕ => if d ∈ ForbiddenDivisors then (1 : ℝ) / d else 0) := by
      convert prop_Dsum hChebyshev using 1;
    -- Since the set `ForbiddenDivisorsWithMinPrime K` decreases to the empty set as $K \to \infty$, the sum over this set tends to zero.
    have h_empty : ∀ d ∈ ForbiddenDivisors, ∃ K₀, ∀ K ≥ K₀, d ∉ ForbiddenDivisorsWithMinPrime K := by
      intro d hd
      obtain ⟨p, hp_prime, hp_min⟩ : ∃ p, Nat.Prime p ∧ p ∣ d ∧ ∀ q, Nat.Prime q → q ∣ d → p ≤ q := by
        rcases hd with ( ⟨ p, hp_prime, rfl ⟩ | ⟨ p, q, hpq, rfl ⟩ ) <;> simp_all +decide
        · exact ⟨ p, hp_prime, dvd_pow_self _ two_ne_zero, fun q hq hq' => Nat.Prime.two_le hq |> fun hq'' => Nat.le_of_not_lt fun hq''' => by have := Nat.Prime.dvd_of_dvd_pow hq hq'; simp_all +decide [ Nat.prime_dvd_prime_iff_eq ] ⟩;
        · exact ⟨ Nat.minFac ( p * q ), Nat.minFac_prime ( Nat.ne_of_gt ( one_lt_mul'' hpq.1.one_lt hpq.2.1.one_lt ) ), Nat.minFac_dvd _, fun q hq hq' => Nat.minFac_le_of_dvd hq.two_le hq' ⟩;
      unfold ForbiddenDivisorsWithMinPrime; aesop;
    have h_tail_sum_zero : Filter.Tendsto (fun K => ∑' (d : ℕ), if d ∈ ForbiddenDivisors ∧ d ∈ ForbiddenDivisorsWithMinPrime K then (1 : ℝ) / d else 0) Filter.atTop (nhds 0) := by
      have h_tail_sum_zero : Filter.Tendsto (fun K => ∑' (d : ℕ), if d ∈ ForbiddenDivisors ∧ d ∈ ForbiddenDivisorsWithMinPrime K then (1 : ℝ) / d else 0) Filter.atTop (nhds (∑' (d : ℕ), if d ∈ ForbiddenDivisors ∧ False then (1 : ℝ) / d else 0)) := by
        refine' ( tendsto_tsum_of_dominated_convergence _ _ _ );
        use fun d => if d ∈ ForbiddenDivisors then ( 1 : ℝ ) / d else 0;
        · convert h_tail_sum using 1;
        · intro k; by_cases hk : k ∈ ForbiddenDivisors <;> simp +decide [ hk ] ;
          exact tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ge_atTop ( Classical.choose ( h_empty k hk ) ) ] with x hx; rw [ if_neg ( Classical.choose_spec ( h_empty k hk ) x hx ) ] );
        · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn k ; split_ifs <;> norm_num;
          tauto;
      convert h_tail_sum_zero using 2 ; norm_num [ tsum_eq_single 0 ];
    refine' squeeze_zero ( fun K => tsum_nonneg fun _ => by positivity ) ( fun K => Summable.tsum_le_tsum _ _ _ ) h_tail_sum_zero;
    · intro d; split_ifs <;> simp_all +decide [ ForbiddenDivisorsWithMinPrime ] ;
    · refine' Summable.of_nonneg_of_le ( fun d => by positivity ) ( fun d => _ ) h_tail_sum;
      unfold ForbiddenDivisorsWithMinPrime at * ; aesop;
    · exact Summable.of_nonneg_of_le ( fun _ => by positivity ) ( fun _ => by aesop ) h_tail_sum

/-
Definitions of TailForbiddenDivisors, L_val, and BadMultiples.
-/
def TailForbiddenDivisors (Y : ℕ) : Set ℕ := ForbiddenDivisorsWithMinPrime (2 * Y)

noncomputable def L_val (Y : ℕ) : ℕ := ∏ p ∈ Finset.filter Nat.Prime (Finset.range (2 * Y + 1)), p

def BadMultiples (Y : ℕ) : Set ℕ := ⋃ d ∈ TailForbiddenDivisors Y, {n | n ≡ 1 [MOD L_val Y] ∧ d ∣ n}

/-
L_val Y is positive.
-/
lemma L_val_pos (Y : ℕ) : L_val Y > 0 := by
  exact Finset.prod_pos fun p hp => Nat.Prime.pos <| Finset.mem_filter.mp hp |>.2

/-
The gcd of L_val Y and any d in TailForbiddenDivisors Y is 1.
-/
lemma gcd_L_d_eq_one (Y : ℕ) (d : ℕ) (hd : d ∈ TailForbiddenDivisors Y) : (L_val Y).gcd d = 1 := by
  -- Since $d$ only has prime factors greater than $2Y$, none of the primes in the product defining $L_val Y$ can divide $d$.
  have h_no_common_factors : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (2 * Y + 1)), ¬(p ∣ d) := by
    intro p hp hpd; have := hd.2 p; simp_all +decide [ Nat.dvd_iff_mod_eq_zero ] ;
    linarith [ hp.1 ];
  exact Nat.Coprime.prod_left fun p hp => Nat.Prime.coprime_iff_not_dvd ( Finset.mem_filter.mp hp |>.2 ) |>.2 ( h_no_common_factors p hp )

/-
The upper density of the union of CRT sets is bounded by (1/L) times the sum of reciprocals.
-/
lemma upper_density_union_CRT_le (L : ℕ) (S : Set ℕ) (hL : L > 0) (hS_subset : S ⊆ {n | 1 ≤ n})
  (h_coprime : ∀ d ∈ S, L.gcd d = 1)
  (h_summable : Summable (fun d => if d ∈ S then 1 / (d : ℝ) else 0)) :
  upperDensity (⋃ d ∈ S, {n | n ≡ 1 [MOD L] ∧ d ∣ n}) ≤ (1 / (L : ℝ)) * ∑' d, if d ∈ S then 1 / (d : ℝ) else 0 := by
    have h_upper_density : ∀ K, upperDensity (⋃ d ∈ S, {n | n ≡ 1 [MOD L] ∧ d ∣ n}) ≤ upperDensity (⋃ d ∈ S ∩ {n | n ≤ K}, {n | n ≡ 1 [MOD L] ∧ d ∣ n}) + ∑' d, if d ∈ S ∧ d > K then 1 / (d : ℝ) else 0 := by
      intro K
      have h_upper_density : upperDensity (⋃ d ∈ S, {n | n ≡ 1 [MOD L] ∧ d ∣ n}) ≤ upperDensity (⋃ d ∈ S ∩ {n | n ≤ K}, {n | n ≡ 1 [MOD L] ∧ d ∣ n}) + upperDensity (⋃ d ∈ S ∩ {n | n > K}, {n | d ∣ n}) := by
        refine' le_trans ( upperDensity_mono _ ) _;
        exact ( ⋃ d ∈ S ∩ { n | n ≤ K }, { n | n ≡ 1 [MOD L] ∧ d ∣ n } ) ∪ ( ⋃ d ∈ S ∩ { n | n > K }, { n | d ∣ n } );
        · simp +contextual [ Set.subset_def ];
          exact fun x hx y hy hyx => if h : y ≤ K then Or.inl ⟨ y, ⟨ hy, h ⟩, hyx ⟩ else Or.inr ⟨ y, ⟨ hy, not_le.mp h ⟩, hyx ⟩;
        · convert upper_density_finite_union_le { 0, 1 } ( fun i => if i = 0 then ⋃ d ∈ S ∩ { n | n ≤ K }, { n | n ≡ 1 [MOD L] ∧ d ∣ n } else ⋃ d ∈ S ∩ { n | n > K }, { n | d ∣ n } ) using 1;
          · congr with x ; simp +decide
          · rw [ Finset.sum_pair ] <;> norm_num;
      refine le_trans h_upper_density <| add_le_add_left ?_ _;
      convert upper_density_multiples_tail_bound S K _ _ using 1;
      · assumption;
      · convert h_summable using 1;
    -- The upper density of the union of CRT sets for $d \le K$ is bounded by $(1/L) \sum_{d \in S_{\le K}} \frac{1}{d}$.
    have h_upper_density_crt : ∀ K, upperDensity (⋃ d ∈ S ∩ {n | n ≤ K}, {n | n ≡ 1 [MOD L] ∧ d ∣ n}) ≤ (1 / L : ℝ) * ∑ d ∈ Finset.filter (fun d => d ∈ S ∧ d ≤ K) (Finset.range (K + 1)), (1 / (d : ℝ)) := by
      intros K
      have h_upper_density : upperDensity (⋃ d ∈ S ∩ {n | n ≤ K}, {n | n ≡ 1 [MOD L] ∧ d ∣ n}) ≤ ∑ d ∈ Finset.filter (fun d => d ∈ S ∧ d ≤ K) (Finset.range (K + 1)), upperDensity {n | n ≡ 1 [MOD L] ∧ d ∣ n} := by
        have h_upper_density : ∀ (s : Finset ℕ), upperDensity (⋃ d ∈ s, {n | n ≡ 1 [MOD L] ∧ d ∣ n}) ≤ ∑ d ∈ s, upperDensity {n | n ≡ 1 [MOD L] ∧ d ∣ n} := by
          exact fun s => upper_density_finite_union_le s fun i => {n | n ≡ 1 [MOD L] ∧ i ∣ n};
        convert h_upper_density ( Finset.filter ( fun d => d ∈ S ∧ d ≤ K ) ( Finset.range ( K + 1 ) ) ) using 1;
        congr! 2;
        ext; simp +decide [ Nat.lt_succ_iff ] ;
      -- The upper density of each CRT set is bounded by $1/(Ld)$.
      have h_upper_density_crt_each : ∀ d ∈ S ∩ {n | n ≤ K}, upperDensity {n | n ≡ 1 [MOD L] ∧ d ∣ n} ≤ (1 / (L * d : ℝ)) := by
        intros d hd
        have h_upper_density_crt_each : HasNaturalDensity {n | n ≡ 1 [MOD L] ∧ d ∣ n} ∧ naturalDensity {n | n ≡ 1 [MOD L] ∧ d ∣ n} = 1 / (L * d : ℝ) := by
          convert lem_CRTdensity L d hL ( hS_subset hd.1 ) ( h_coprime d hd.1 ) using 1;
        convert h_upper_density_crt_each.2.le using 1;
      refine le_trans h_upper_density ?_;
      rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_le_sum fun x hx => by simpa [ mul_comm ] using h_upper_density_crt_each x <| by aesop;
    -- The sum of reciprocals of elements in $S_{>K}$ tends to 0 as $K \to \infty$.
    have h_tail_sum_zero : Filter.Tendsto (fun K => ∑' d, if d ∈ S ∧ d > K then 1 / (d : ℝ) else 0) Filter.atTop (nhds 0) := by
      have h_tail_sum_zero : Filter.Tendsto (fun K => ∑' d, (if d ∈ S then (1 / (d : ℝ)) else 0) * (if d > K then 1 else 0)) Filter.atTop (nhds (∑' d, (if d ∈ S then (1 / (d : ℝ)) else 0) * 0)) := by
        refine' ( tendsto_tsum_of_dominated_convergence _ _ _ );
        use fun k => if k ∈ S then 1 / ( k : ℝ ) else 0;
        · convert h_summable using 1;
        · intro k; exact tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop k ] with x hx; split_ifs <;> linarith ) ;
        · filter_upwards [ Filter.eventually_gt_atTop 0 ] with n hn using fun k => by split_ifs <;> norm_num;
      convert h_tail_sum_zero using 2 <;> norm_num [ tsum_mul_right ] ; ring_nf;
      exact tsum_congr fun _ => by split_ifs <;> tauto;
    -- The sum of reciprocals of elements in $S_{\le K}$ tends to $\sum_{d \in S} \frac{1}{d}$ as $K \to \infty$.
    have h_sum_le_K : Filter.Tendsto (fun K => ∑ d ∈ Finset.filter (fun d => d ∈ S ∧ d ≤ K) (Finset.range (K + 1)), (1 / (d : ℝ))) Filter.atTop (nhds (∑' d, if d ∈ S then 1 / (d : ℝ) else 0)) := by
      convert h_summable.hasSum.tendsto_sum_nat.comp ( Filter.tendsto_add_atTop_nat 1 ) using 1;
      ext; simp +decide [ Finset.sum_ite ] ;
      congr! 1;
      exact Finset.filter_congr fun x hx => ⟨ fun hx' => hx'.1, fun hx' => ⟨ hx', Finset.mem_range_succ_iff.mp hx ⟩ ⟩;
    have h_lim_sup : Filter.Tendsto (fun K => (1 / L : ℝ) * ∑ d ∈ Finset.filter (fun d => d ∈ S ∧ d ≤ K) (Finset.range (K + 1)), (1 / (d : ℝ)) + ∑' d, if d ∈ S ∧ d > K then 1 / (d : ℝ) else 0) Filter.atTop (nhds ((1 / L : ℝ) * ∑' d, if d ∈ S then 1 / (d : ℝ) else 0)) := by
      simpa using Filter.Tendsto.add ( h_sum_le_K.const_mul _ ) h_tail_sum_zero;
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds h_lim_sup fun K => le_trans ( h_upper_density K ) ( add_le_add ( h_upper_density_crt K ) le_rfl )

/-
The upper density of BadMultiples Y is bounded by (1/L) * sum(1/d).
-/
lemma bad_multiples_upper_density_le (Y : ℕ) (hChebyshev : ChebyshevUpperBound) :
  upperDensity (BadMultiples Y) ≤ (1 / (L_val Y : ℝ)) * ∑' d, if d ∈ TailForbiddenDivisors Y then 1 / (d : ℝ) else 0 := by
    convert upper_density_union_CRT_le ( L_val Y ) ( TailForbiddenDivisors Y ) ( L_val_pos Y ) _ _ _ using 1;
    · intro n hn
      obtain ⟨hn_forbidden, hn_min⟩ := hn;
      rcases hn_forbidden with ( ⟨ p, hp, rfl ⟩ | ⟨ p, q, h, rfl ⟩ ) <;> norm_num at *;
      · nlinarith [ hp.two_le ];
      · exact Nat.mul_pos h.1.pos h.2.1.pos;
    · exact fun d a => gcd_L_d_eq_one Y d a;
    · have h_summable : Summable (fun d : ℕ => if d ∈ ForbiddenDivisors then 1 / (d : ℝ) else 0) := by
        convert prop_Dsum hChebyshev using 1;
      refine' .of_nonneg_of_le ( fun d => _ ) ( fun d => _ ) h_summable;
      · positivity;
      · unfold TailForbiddenDivisors ForbiddenDivisorsWithMinPrime; aesop;

/-
The set of numbers congruent to 1 mod L(Y) but not in BadMultiples(Y) is a subset of S_avoid ForbiddenDivisors.
-/
lemma safe_set_subset_avoid (Y : ℕ) :
  ({n | n ≡ 1 [MOD L_val Y]} \ BadMultiples Y) ⊆ S_avoid ForbiddenDivisors := by
    intro n hn d hd hdn;
    by_cases h : ∃ p : ℕ, Nat.Prime p ∧ p ∣ d ∧ p ≤ 2 * Y <;> simp_all +decide [ BadMultiples ];
    · obtain ⟨ p, hp₁, hp₂, hp₃ ⟩ := h;
      -- Since $p \leq 2Y$, we have $p \mid L_val Y$.
      have hp_div_L : p ∣ L_val Y := by
        exact Finset.dvd_prod_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith [ hp₁.two_le ] ), hp₁ ⟩ );
      have := hn.1.of_dvd hp_div_L; simp_all +decide [ Nat.ModEq, Nat.dvd_iff_mod_eq_zero ] ;
      have := Nat.mod_mod_of_dvd n ( Nat.dvd_of_mod_eq_zero hp₂ ) ; simp_all +decide [ Nat.mod_eq_of_lt hp₁.two_le ] ;
    · exact hn.2 hn.1 d ⟨ hd, h ⟩ hdn

/-
L_val Y is at least 2 for Y >= 1.
-/
lemma L_val_ge_two (Y : ℕ) (hY : Y ≥ 1) : L_val Y ≥ 2 := by
  -- Since $Y \geq 1$, the set $\{2, 3, \ldots, 2Y+1\}$ contains the prime number 2.
  have h_prime_two : 2 ∈ Finset.filter Nat.Prime (Finset.range (2 * Y + 1)) := by
    exact Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith ), Nat.prime_two ⟩;
  exact Nat.le_of_dvd ( Finset.prod_pos fun p hp => Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) ( Finset.dvd_prod_of_mem _ h_prime_two ) |> le_trans ( by norm_num )

/-
Lower density is monotonic with respect to set inclusion.
-/
lemma lowerDensity_mono {A B : Set ℕ} (h : A ⊆ B) : lowerDensity A ≤ lowerDensity B := by
  refine' csSup_le _ _ <;> norm_num;
  · exact ⟨ 0, ⟨ 0, fun n hn => by positivity ⟩ ⟩;
  · intro b x hx; refine' le_csSup _ _ <;> norm_num;
    · exact ⟨ 1, by rintro a ⟨ y, hy ⟩ ; exact le_trans ( hy ( y + 1 ) ( by linarith ) ) ( div_le_one_of_le₀ ( mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by norm_num ) ) ( by positivity ) ) ⟩;
    · exact ⟨ x, fun n hn => le_trans ( hx n hn ) ( by gcongr ; aesop ) ⟩

/-
The lower density of the safe set (congruent to 1 mod L and not in BadMultiples) is positive.
-/
lemma lower_density_safe_set_pos (Y : ℕ) (hChebyshev : ChebyshevUpperBound)
  (hY_ge_1 : Y ≥ 1)
  (hY_sum : (∑' d, if d ∈ TailForbiddenDivisors Y then 1 / (d : ℝ) else 0) < 1/2) :
  lowerDensity ({n | n ≡ 1 [MOD L_val Y]} \ BadMultiples Y) > 0 := by
    -- By `lower_density_diff_bound`, $\underline{d}(B) \ge d(P) - \overline{d}(P \cap Bad)$.
    have h_lower_density_B : lowerDensity ({n | n ≡ 1 [MOD L_val Y]} \ BadMultiples Y) ≥ naturalDensity {n | n ≡ 1 [MOD L_val Y]} - upperDensity (BadMultiples Y) := by
      convert lower_density_diff_bound _ using 1;
      congr! 1;
      · congr! 1;
        ext; simp [BadMultiples];
      · convert lem_APdensity ( L_val Y ) 1 ( L_val_pos Y ) ( Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by linarith [ L_val_pos Y ], by
          exact ne_of_gt ( lt_of_lt_of_le ( by decide ) ( L_val_ge_two Y hY_ge_1 ) ) ⟩ ) using 1
        generalize_proofs at *;
        constructor <;> intro h <;> simp_all +decide [ Nat.ModEq ];
        · convert lem_APdensity ( L_val Y ) 1 ( L_val_pos Y ) ( Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨ by linarith [ L_val_pos Y ], by
            exact ne_of_gt ( L_val_ge_two Y hY_ge_1 ) ⟩ ) using 1
          generalize_proofs at *;
          norm_num [ Nat.mod_eq_of_lt ( show 1 < L_val Y from lt_of_lt_of_le ( by decide ) ( L_val_ge_two Y hY_ge_1 ) ) ];
        · convert h.1 using 1;
          norm_num [ Nat.mod_eq_of_lt ( show 1 < L_val Y from lt_of_lt_of_le ( by decide ) ( L_val_ge_two Y hY_ge_1 ) ) ];
    -- By `lem_APdensity`, $d(P) = 1/L$.
    have h_density_P : naturalDensity {n | n ≡ 1 [MOD L_val Y]} = 1 / (L_val Y : ℝ) := by
      convert lem_APdensity ( L_val Y ) 1 _ _ using 1 <;> norm_num [ Nat.mod_eq_of_lt, L_val_pos ];
      · constructor <;> intro h;
        · convert lem_APdensity ( L_val Y ) 1 _ _ using 1 <;> norm_num [ Nat.mod_eq_of_lt, L_val_pos ];
          exact lt_of_lt_of_le ( by decide ) ( Nat.le_of_dvd ( L_val_pos Y ) ( Finset.dvd_prod_of_mem _ ( Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith ), Nat.prime_two ⟩ ) ) );
        · convert h.2 using 1;
          norm_num [ Nat.ModEq, Nat.mod_eq_of_lt ( show 1 < L_val Y from lt_of_lt_of_le ( by decide ) ( L_val_ge_two Y hY_ge_1 ) ) ];
      · exact lt_of_lt_of_le ( by decide ) ( L_val_ge_two Y hY_ge_1 );
    -- By `bad_multiples_upper_density_le`, $\overline{d}(Bad) \le (1/L) * \text{tail\_sum}$.
    have h_upper_density_Bad : upperDensity (BadMultiples Y) ≤ (1 / (L_val Y : ℝ)) * ∑' d, (if d ∈ TailForbiddenDivisors Y then (1 : ℝ) / d else 0) := by
      convert bad_multiples_upper_density_le Y hChebyshev using 1;
    nlinarith [ show ( 0 : ℝ ) < 1 / L_val Y from one_div_pos.mpr ( Nat.cast_pos.mpr ( L_val_pos Y ) ) ]

/-
The set S(D) has a positive natural density.
-/
theorem prop_avoid_positive (hChebyshev : ChebyshevUpperBound) :
  HasNaturalDensity (S_avoid ForbiddenDivisors) ∧ naturalDensity (S_avoid ForbiddenDivisors) > 0 := by
    -- By Lemma `lowerDensity_mono`, since the lower density of the safe set is positive, the lower density of S_avoid (ForbiddenDivisors) must also be positive.
    have h_lower_density_pos : lowerDensity (S_avoid (ForbiddenDivisors)) > 0 := by
      -- By Lemma `lowerDensity_mono`, since the lower density of the safe set is positive, the lower density of S_avoid (ForbiddenDivisors) must also be positive. Hence, we conclude:
      have h_lower_density_pos : ∃ Y ≥ 1, lowerDensity ({n | n ≡ 1 [MOD L_val Y]} \ BadMultiples Y) > 0 := by
        -- By Lemma `forbidden_divisors_tail_sum_tendsto_zero`, there exists a Y such that the sum of the reciprocals of the forbidden divisors with all prime factors greater than 2Y is less than 1/2.
        obtain ⟨Y, hY_ge_1, hY_sum⟩ : ∃ Y ≥ 1, (∑' d, if d ∈ TailForbiddenDivisors Y then (1 : ℝ) / d else 0) < 1 / 2 := by
          have := forbidden_divisors_tail_sum_tendsto_zero hChebyshev; norm_num at *; exact Filter.eventually_atTop.mp ( this.eventually ( gt_mem_nhds <| by norm_num ) ) |> fun ⟨ Y, hY ⟩ ↦ ⟨ Y + 1, by linarith, hY _ <| by linarith ⟩ ;
        exact ⟨ Y, hY_ge_1, lower_density_safe_set_pos Y hChebyshev hY_ge_1 <| by simpa using hY_sum ⟩;
      obtain ⟨ Y, hY₁, hY₂ ⟩ := h_lower_density_pos;
      exact lt_of_lt_of_le hY₂ ( lowerDensity_mono <| safe_set_subset_avoid Y );
    have := @prop_avoid_density ( ForbiddenDivisors ) ?_ ?_ <;> norm_num at *;
    · exact ⟨ this, by linarith [ show lowerDensity ( S_avoid ForbiddenDivisors ) ≤ naturalDensity ( S_avoid ForbiddenDivisors ) from lower_le_upper_density _ ] ⟩;
    · intro n hn; obtain ⟨ p, hp, rfl ⟩ | ⟨ p, q, hpq, rfl ⟩ := hn <;> norm_num [ Nat.Prime.two_le ] ;
      · nlinarith [ hp.two_le ];
      · nlinarith [ hpq.1.two_le, hpq.2.1.two_le ];
    · convert prop_Dsum hChebyshev using 1;
      grind

/-
SpecialSet is equal to S_avoid ForbiddenDivisors.
-/
lemma SpecialSet_eq_S_avoid : SpecialSet = S_avoid ForbiddenDivisors := by
  -- By definition of $SpecialSet$, we know that $n \in SpecialSet$ if and only if $n$ is squarefree and not divisible by any element in $ForbiddenDivisors$.
  ext n
  simp [SpecialSet_iff, S_avoid];
  constructor <;> intro h <;> simp_all +decide [ BadPair, ForbiddenDivisors ];
  · rintro f ( ⟨ p, hp, rfl ⟩ | ⟨ p, q, ⟨ hp, hq, hpq, hq' ⟩, rfl ⟩ ) <;> simp_all +decide [ sq ];
    exact fun h' => hp.not_isUnit <| by have := h.1 p; simp_all +decide
  · refine' ⟨ _, _ ⟩;
    · refine' Nat.squarefree_iff_prime_squarefree.mpr _;
      exact fun p pp d => h _ ( Or.inl ⟨ p, pp, by ring ⟩ ) d;
    · exact fun p q hp hq hpq hq' => h _ ( Or.inr ⟨ p, q, ⟨ hp, hq, hpq, hq' ⟩, rfl ⟩ )

/-
The set $\A$ from Definition~\ref{def:A} has a natural density, and this density is positive.
-/
theorem main_theorem (hChebyshev : ChebyshevUpperBound) :
  HasNaturalDensity SpecialSet ∧ naturalDensity SpecialSet > 0 := by
    convert prop_avoid_positive hChebyshev using 1;
    · rw [ SpecialSet_eq_S_avoid ];
    · rw [ SpecialSet_eq_S_avoid ]

/-
I have formalized the definitions and theorems from the provided LaTeX document.
The main results are:
- `prop_avoid_density`: The set of integers avoiding a set of forbidden divisors has a natural density, provided the sum of reciprocals of the divisors converges.
- `prop_avoid_positive`: The set of integers avoiding the specific set of "forbidden divisors" $\mathcal{D}$ has a positive natural density.
- `main_theorem`: The set $\mathcal{A}$ of squarefree integers with exponentially spaced prime factors has a positive natural density.

I used the provided `ChebyshevUpperBound` assumption and the pre-loaded lemmas.
I proved the intermediate results `SpecialSet_eq_S_avoid`, `lower_density_safe_set_pos`, `safe_set_subset_avoid`, `lowerDensity_mono`, `bad_multiples_upper_density_le`, `upper_density_union_CRT_le`, and `forbidden_divisors_tail_sum_tendsto_zero` to support the main proofs.
-/

lemma chebyshev_upper_bound_holds : ChebyshevUpperBound := by
  intro x hx
  have h_log_prod : Real.log (primorial ⌊x⌋₊) ≤ Real.log (4 ^ ⌊x⌋₊) := by
    exact Real.log_le_log ( mod_cast Nat.pos_of_ne_zero ( by exact ne_of_gt ( Finset.prod_pos fun p hp => Nat.Prime.pos ( Finset.mem_filter.mp hp |>.2 ) ) ) ) ( mod_cast primorial_le_4_pow _ );
  unfold vartheta;
  convert le_trans h_log_prod _ using 1;
  · unfold primorial; rw [ ← Real.log_prod ] ; aesop;
    exact fun p hp => Nat.cast_ne_zero.mpr <| Nat.Prime.ne_zero <| Finset.mem_filter.mp hp |>.2;
  · rw [ mul_comm, Real.log_pow ] ; gcongr ; linarith [ Nat.floor_le ( by positivity : 0 ≤ x ) ]

lemma density_implies_interval_bound {S : Set ℕ} (d : ℝ) (hd : d > 0) (h : HasNaturalDensity S ∧ naturalDensity S = d) : ∃ c > 0, ∃ N₀, ∀ N ≥ N₀, ((Finset.filter (· ∈ S) (Finset.Ioc (N / 2) N)).card : ℝ) ≥ c * N := by
  -- Let $a_N = |S \cap [1, N]|$. We are given $a_N/N \to d$.
  set a : ℕ → ℝ := fun N => ((Finset.filter (· ∈ S) (Finset.Icc 1 N)).card : ℝ) / N
  have ha_tendsto : Filter.Tendsto a Filter.atTop (nhds d) := by
    convert tendsto_density_of_has_natural_density S h.1 using 1 ; aesop;
  -- We want to bound $|S \cap (N/2, N]| = a_N - a_{N/2}$.
  -- Consider the sequence $u_N = (a_N - a_{N/2})/N = a_N/N - (a_{N/2}/(N/2)) \cdot ((N/2)/N)$.
  -- We know $a_N/N \to d$.
  -- Since $N/2 \to \infty$, $a_{N/2}/(N/2) \to d$.
  -- Also $(N/2)/N \to 1/2$.
  -- So $u_N \to d - d(1/2) = d/2$.
  have hu_tendsto : Filter.Tendsto (fun N => ((a N - a (N / 2) * (N / 2 : ℝ) / N))) Filter.atTop (nhds (d / 2)) := by
    convert ha_tendsto.sub ( Filter.Tendsto.div_const ( ha_tendsto.comp ( Filter.tendsto_atTop_atTop.mpr _ ) |> Filter.Tendsto.mul_const ( 1 / 2 : ℝ ) ) 1 ) using 2 <;> norm_num ; ring_nf;
    · by_cases h : ‹_› = 0 <;> aesop;
    · ring;
    · exact fun b => ⟨ 2 * b, fun n hn => by linarith [ Nat.div_add_mod n 2, Nat.mod_lt n two_pos ] ⟩;
  -- Since $d > 0$, $d/2 > 0$. So eventually $u_N \ge d/4$.
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ N ≥ N₀, ((a N - a (N / 2) * (N / 2 : ℝ) / N)) ≥ d / 4 := by
    exact Filter.eventually_atTop.mp ( hu_tendsto.eventually ( le_mem_nhds <| by linarith ) ) |> fun ⟨ N₀, hN₀ ⟩ => ⟨ N₀, fun N hN => hN₀ N hN ⟩;
  refine' ⟨ d / 4, by positivity, N₀ + 2, fun N hN => _ ⟩ ; specialize hN₀ N ( by linarith ) ; rcases N with ( _ | _ | N ) <;> norm_num [ Nat.succ_div ] at *;
  · linarith;
  · rw [ show ( Finset.filter ( fun x => x ∈ S ) ( Finset.Ioc ( ( N / 2 + if 2 ∣ N + 1 then 1 else 0 ) + if 2 ∣ N then 1 else 0 ) ( N + 1 + 1 ) ) ) = Finset.filter ( fun x => x ∈ S ) ( Finset.Icc 1 ( N + 1 + 1 ) ) \ Finset.filter ( fun x => x ∈ S ) ( Finset.Icc 1 ( ( N / 2 + if 2 ∣ N + 1 then 1 else 0 ) + if 2 ∣ N then 1 else 0 ) ) from ?_ ];
    · rw [ Finset.card_sdiff ];
      rw [ Nat.cast_sub ];
      · rw [ Finset.inter_eq_left.mpr ];
        · rw [ div_sub_div, div_mul_eq_mul_div, div_le_div_iff₀ ] at * <;> try positivity;
          split_ifs at * <;> norm_num at *;
          · grind;
          · field_simp at hN₀;
            nlinarith [ show ( N : ℝ ) ≥ 2 * ( N / 2 : ℕ ) by norm_cast; linarith [ Nat.div_mul_le_self N 2 ], show ( N : ℝ ) ≥ 2 * ( N / 2 : ℕ ) by norm_cast; linarith [ Nat.div_mul_le_self N 2 ], show ( N : ℝ ) ≥ 2 * ( N / 2 : ℕ ) by norm_cast; linarith [ Nat.div_mul_le_self N 2 ], show ( N : ℝ ) ≥ 2 * ( N / 2 : ℕ ) by norm_cast; linarith [ Nat.div_mul_le_self N 2 ] ];
          · field_simp at hN₀;
            nlinarith [ show ( N : ℝ ) ≥ 2 * ( N / 2 : ℕ ) by norm_cast; linarith [ Nat.div_mul_cancel ‹2 ∣ N› ] ];
          · omega;
        · exact Finset.filter_subset_filter _ <| Finset.Icc_subset_Icc_right <| by split_ifs <;> omega;
      · exact Finset.card_mono fun x hx => by aesop;
    · ext; simp [Finset.mem_sdiff, Finset.mem_Icc, Finset.mem_Ioc];
      grind +ring

/-
Put together the results above.
-/
theorem erdos_537 : ¬(∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, ∀ A, A ⊆ Finset.range (N + 1) → (A.card : ℝ) ≥ ε * N →
  ∃ a₁ ∈ A, ∃ a₂ ∈ A, ∃ a₃ ∈ A, ∃ p₁ p₂ p₃, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧
  p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧ a₁ * p₁ = a₂ * p₂ ∧ a₂ * p₂ = a₃ * p₃) := by
  by_contra h_contra;
  -- Apply the theorem `answer` to obtain the contradiction.
  apply answer;
  · -- Apply the theorem `main_theorem` to obtain the positive density of `SpecialSet`.
    have h_density : HasNaturalDensity SpecialSet ∧ naturalDensity SpecialSet > 0 := by
      convert main_theorem chebyshev_upper_bound_holds using 1;
    -- Apply the theorem `density_implies_interval_bound` to obtain the positive density of `SpecialSet` in the interval $(N/2, N]$.
    obtain ⟨c, hc_pos, N₀, hN₀⟩ : ∃ c > 0, ∃ N₀, ∀ N ≥ N₀, ((Finset.filter (· ∈ SpecialSet) (Finset.Ioc (N / 2) N)).card : ℝ) ≥ c * N := by
      have := density_implies_interval_bound ( naturalDensity SpecialSet ) h_density.2 ⟨ h_density.1, rfl ⟩;
      exact this;
    use c, hc_pos, N₀ + 1;
    intro N hN; specialize hN₀ N ( by linarith ) ; rw [ show SpecialFinset N = Finset.filter ( fun x => x ∈ SpecialSet ) ( Finset.Ioc ( N / 2 ) N ) from ?_ ] ; aesop;
    ext; simp [SpecialFinset];
    exact ⟨ fun h => ⟨ ⟨ h.2.2, by linarith ⟩, h.2.1 ⟩, fun h => ⟨ by linarith, h.2, h.1.1 ⟩ ⟩;
  · exact h_contra

#print axioms erdos_537
-- 'erdos_537' depends on axioms: [propext, Classical.choice, Quot.sound]
