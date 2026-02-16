/-

This is a Lean formalization of a solution to Erdős Problem 487
https://www.erdosproblems.com/forum/thread/487

The original proof was found by: Kleitman

[Kl71] Kleitman, Daniel, Collections of subsets containing no two sets
and their union. Proceedings of the LA Meeting AMS (1971), 153-155.


Kleitman's proof was auto-formalized by Aristotle (from Harmonic).


The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/


/-
We have formally proved the main theorem of the paper: any subset of the natural numbers with positive lower asymptotic density contains a distinct triple $\{a, b, c\}$ such that $\text{lcm}(a, b) = c$.

The proof follows the strategy outlined in the paper:
1.  **Reduction to odd integers**: We use the fact that if $A$ has positive lower density, then for some $t$, the set $B_t = \{a/2^t : a \in A, v_2(a) = t\}$ has positive upper logarithmic density (and consists of odd integers). This relies on the provided lemmas `exists_t_upper_log_density_At_pos` and `upper_log_density_Bt`.
2.  **Upper bound for lcm-triple free sets**: We use the provided result `I_N_upper_bound_asymptotic` (which relies on Kleitman's bound) to show that if a set is lcm-triple free, the quantity $I(N)$ grows slower than $N \log N$.
3.  **Lower bound for sets with positive density**: We show that if a set has positive upper logarithmic density, then $I(N)$ must grow at least as fast as $N \log N$ along a subsequence. This is formalized in `lcm_triple_of_upper_log_density_pos`.
4.  **Contradiction**: Combining the upper and lower bounds yields a contradiction, proving that the set must contain an lcm-triple.

Key intermediate lemmas proved include:
*   `lcm_triple_of_upper_log_density_pos`: The core argument for odd integers.
*   `upper_log_density_Bt`: Relates the density of $B_t$ to $A_t$.
*   `limsup_log_density_stretch`: A technical lemma for handling the density scaling.
*   `lcm_triple_exists`: The final theorem.
-/

import Mathlib
import ErdosProblems.Erdos447

namespace Erdos487

open scoped Nat
open scoped Classical
open Asymptotics Filter
open Erdos447

/-
Definition of lower asymptotic density of a set A of natural numbers.
-/
noncomputable def lowerDensity (A : Set ℕ) : ℝ :=
  Filter.liminf (fun N => ((Finset.Icc 1 N).filter (· ∈ A)).card / (N : ℝ)) Filter.atTop

/-
Definitions of arithmetic functions: Omega(n) (total number of prime factors), tau(n) (number of divisors), and v2(n) (exponent of 2).
-/
def Om (n : ℕ) : ℕ := (Nat.factorization n).sum (fun _ k => k)

def tauu (n : ℕ) : ℕ := (Nat.divisors n).card

def v2 (n : ℕ) : ℕ := padicValNat 2 n

/-
Helper definitions for the reduction to odd integers: A_t is the subset of A with v_2(a) = t, and B_t is A_t scaled down by 2^t.
-/
def At (A : Set ℕ) (t : ℕ) : Set ℕ := {a ∈ A | v2 a = t}

def Bt (A : Set ℕ) (t : ℕ) : Set ℕ := (At A t).image (fun n => n / 2^t)

/-
If B_t(A) contains an lcm-triple, then A contains an lcm-triple.
-/
lemma lcm_triple_preservation (A : Set ℕ) (t : ℕ)
  (b1 b2 b3 : ℕ) (h1 : b1 ∈ Bt A t) (h2 : b2 ∈ Bt A t) (h3 : b3 ∈ Bt A t)
  (h_distinct : b1 ≠ b2 ∧ b2 ≠ b3 ∧ b1 ≠ b3)
  (h_lcm : Nat.lcm b1 b2 = b3) :
  ∃ a1 ∈ A, ∃ a2 ∈ A, ∃ a3 ∈ A, a1 ≠ a2 ∧ a2 ≠ a3 ∧ a1 ≠ a3 ∧ Nat.lcm a1 a2 = a3 := by
    obtain ⟨ x, hx, rfl ⟩ := h1;
    obtain ⟨ y, hy, rfl ⟩ := h2
    obtain ⟨ z, hz, rfl ⟩ := h3;
    refine' ⟨ x, hx.1, y, hy.1, z, hz.1, _, _, _, _ ⟩ <;> simp_all +decide
    · grind;
    · grind;
    · unfold At at * ; aesop;
    · have h_lcm_eq : x = 2^t * (x / 2^t) ∧ y = 2^t * (y / 2^t) ∧ z = 2^t * (z / 2^t) := by
        have h_lcm_eq : 2^t ∣ x ∧ 2^t ∣ y ∧ 2^t ∣ z := by
          exact ⟨ Nat.dvd_trans ( pow_dvd_pow _ <| show t ≤ padicValNat 2 x from hx.2.ge ) <| Nat.ordProj_dvd _ _, Nat.dvd_trans ( pow_dvd_pow _ <| show t ≤ padicValNat 2 y from hy.2.ge ) <| Nat.ordProj_dvd _ _, Nat.dvd_trans ( pow_dvd_pow _ <| show t ≤ padicValNat 2 z from hz.2.ge ) <| Nat.ordProj_dvd _ _ ⟩;
        exact ⟨ Eq.symm ( Nat.mul_div_cancel' h_lcm_eq.1 ), Eq.symm ( Nat.mul_div_cancel' h_lcm_eq.2.1 ), Eq.symm ( Nat.mul_div_cancel' h_lcm_eq.2.2 ) ⟩;
      rw [ h_lcm_eq.1, h_lcm_eq.2.1, h_lcm_eq.2.2, Nat.lcm_mul_left ] ; norm_num [ h_lcm ]

/-
Every element in B_t is odd (assuming A contains no zeros).
-/
lemma Bt_odd (A : Set ℕ) (t : ℕ) (hA : ∀ a ∈ A, a ≠ 0) : ∀ b ∈ Bt A t, Odd b := by
  intro b hb; obtain ⟨ a, ha, rfl ⟩ := hb; simp +decide
  -- By definition of $At$, we know that $v2 a = t$, which means $a$ is divisible by $2^t$ but not by $2^{t+1}$.
  have h_div : 2 ^ t ∣ a ∧ ¬2 ^ (t + 1) ∣ a := by
    have h_div : padicValNat 2 a = t := by
      exact ha.2;
    exact ⟨ h_div ▸ Nat.ordProj_dvd _ _, h_div ▸ Nat.pow_succ_factorization_not_dvd ( hA a ha.1 ) ( by decide ) ⟩;
  exact Nat.odd_iff.mpr ( Nat.mod_two_ne_zero.mp fun h => h_div.2 <| by convert Nat.mul_dvd_mul_left ( 2 ^ t ) ( Nat.dvd_of_mod_eq_zero h ) using 1; rw [ Nat.mul_div_cancel' h_div.1 ] )

/-
The sum of reciprocals of elements in A intersected with (2^(k-1), 2^k] is at least the cardinality divided by 2^k.
-/
lemma sum_recip_dyadic_bound (A : Set ℕ) (k : ℕ) :
  ∑ a ∈ (Finset.Ioc (2^(k-1)) (2^k)).filter (· ∈ A), (1 : ℝ) / a ≥ ((Finset.Ioc (2^(k-1)) (2^k)).filter (· ∈ A)).card / (2^k : ℝ) := by
    have h_le : ∀ a ∈ Finset.filter (fun x => x ∈ A) (Finset.Ioc (2 ^ (k - 1)) (2 ^ k)), (1 / a : ℝ) ≥ (1 / 2 ^ k : ℝ) := by
      field_simp;
      exact fun x hx => by rw [ one_le_div ( Nat.cast_pos.mpr <| Nat.pos_of_ne_zero fun h => by aesop ) ] ; exact_mod_cast Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx |>.1 ) |>.2;
    simpa [ div_eq_mul_inv ] using Finset.sum_le_sum h_le |> le_trans ( by norm_num )

/-
Definition of b_k as the number of elements of A in {1, ..., 2^k}.
-/
noncomputable def bk (A : Set ℕ) (k : ℕ) : ℕ := ((Finset.Icc 1 (2^k)).filter (· ∈ A)).card

/-
Algebraic lemma: lower bound for the sum involving b_k.
-/
lemma sum_density_lower_bound (b : ℕ → ℕ) (δ' : ℝ) (k1 K : ℕ) (hk1 : k1 + 1 < K)
  (h_density : ∀ k, k1 ≤ k → k < K → (b k : ℝ) ≥ δ' * 2^k) :
  ∑ k ∈ Finset.Icc (k1 + 1) K, ((b k : ℝ) - b (k - 1)) / 2^k ≥ (δ' / 2) * (K - k1 - 2) - (b k1 : ℝ) / 2^(k1+1) := by
    -- Applying the summation by parts formula.
    have h_sum_parts : ∀ N : ℕ, k1 + 1 ≤ N → N < K → ∑ k ∈ Finset.Icc (k1 + 1) N, (b k - b (k - 1) : ℝ) / 2 ^ k = b N / 2 ^ N - b k1 / 2 ^ (k1 + 1) + ∑ k ∈ Finset.Icc (k1 + 1) (N - 1), (b k : ℝ) / 2 ^ (k + 1) := by
      field_simp;
      intro N hN₁ hN₂; induction hN₁ <;> norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc), pow_succ' ] at * ; ring;
      field_simp;
      rename_i m hm ih; rw [ Finset.sum_Ioc_succ_top ( by linarith ) ] ; simp_all +decide [ pow_succ' ] ; ring_nf;
      convert congr_arg ( · + ( b ( 1 + m ) : ℝ ) * 2 ^ k1 - ( b m : ℝ ) * 2 ^ k1 ) ( ih ( by linarith ) ) using 1 <;> ring_nf;
      · norm_num [ mul_assoc, ← mul_pow ];
      · rw [ show ( Finset.Ioc k1 m : Finset ℕ ) = Finset.Ioc k1 ( m - 1 ) ∪ { m } from ?_, Finset.sum_union ] <;> norm_num ; ring_nf;
        · simp +zetaDelta at *;
        · exact fun _ => by linarith;
        · exact Eq.symm (Finset.insert_Ioc_sub_one_right_eq_Ioc hm);
    -- Applying the summation by parts formula to the sum up to K-1.
    have h_sum_parts_K_minus_1 : ∑ k ∈ Finset.Icc (k1 + 1) (K - 1), (b k - b (k - 1) : ℝ) / 2 ^ k = (b (K - 1) : ℝ) / 2 ^ (K - 1) - (b k1 : ℝ) / 2 ^ (k1 + 1) + ∑ k ∈ Finset.Icc (k1 + 1) (K - 2), (b k : ℝ) / 2 ^ (k + 1) := by
      exact h_sum_parts _ ( Nat.le_sub_one_of_lt hk1 ) ( Nat.sub_lt ( by linarith ) ( by linarith ) );
    -- Applying the density condition to the sum up to K-1.
    have h_density_sum : ∑ k ∈ Finset.Icc (k1 + 1) (K - 2), (b k : ℝ) / 2 ^ (k + 1) ≥ (δ' / 2) * (K - k1 - 2) := by
      have h_density_sum : ∀ k ∈ Finset.Icc (k1 + 1) (K - 2), (b k : ℝ) / 2 ^ (k + 1) ≥ δ' / 2 := by
        intro k hk; rw [ ge_iff_le ] ; rw [ div_le_div_iff₀ ] <;> first | positivity | have := h_density k ( by linarith [ Finset.mem_Icc.mp hk ] ) ( by linarith [ Finset.mem_Icc.mp hk, Nat.sub_add_cancel ( by linarith : 2 ≤ K ) ] ) ; ring_nf at * ; nlinarith [ pow_pos ( zero_lt_two' ℝ ) k ] ;
      refine' le_trans _ ( Finset.sum_le_sum h_density_sum ) ; norm_num [ mul_comm ];
      rw [ Nat.cast_sub <| by omega, Nat.cast_add, Nat.cast_sub <| by omega ] ; push_cast ; ring_nf ; norm_num;
    rcases K with ( _ | _ | K ) <;> simp_all +decide [ (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
    rw [ Finset.sum_Ioc_succ_top ] <;> norm_num;
    · refine le_trans h_density_sum ?_;
      rw [ h_sum_parts_K_minus_1 ] ; ring_nf ; norm_num;
      exact le_add_of_nonneg_of_le ( by positivity ) ( Finset.sum_le_sum fun _ _ => by ring_nf; norm_num );
    · linarith

/-
If A has positive lower density, then b_k(A) is bounded below by delta' * 2^k for large k.
-/
lemma bk_lower_bound (A : Set ℕ) (hA : lowerDensity A > 0) :
  ∃ k1 δ', δ' > 0 ∧ ∀ k ≥ k1, (bk A k : ℝ) ≥ δ' * 2^k := by
    -- By definition of liminf, there exists $N_1$ such that for all $N \ge N_1$, $|A \cap \{1, \dots, N\}|/N \ge \delta'$.
    obtain ⟨N1, hN1⟩ : ∃ N1, ∀ N ≥ N1, ((Finset.Icc 1 N).filter (· ∈ A)).card / (N : ℝ) ≥ lowerDensity A / 2 := by
      have h_liminf : Filter.liminf (fun N => ((Finset.Icc 1 N).filter (· ∈ A)).card / (N : ℝ)) Filter.atTop ≥ lowerDensity A := by
        unfold lowerDensity; aesop;
      rw [ Filter.liminf_eq ] at h_liminf;
      contrapose! h_liminf;
      refine' lt_of_le_of_lt ( csSup_le _ _ ) _;
      exact lowerDensity A / 2;
      · exact ⟨ 0, Filter.Eventually.of_forall fun n => by positivity ⟩;
      · exact fun x hx => by rcases Filter.eventually_atTop.mp hx with ⟨ N, hN ⟩ ; obtain ⟨ M, hM₁, hM₂ ⟩ := h_liminf N; linarith [ hN M hM₁ ] ;
      · linarith;
    refine' ⟨ Nat.log 2 N1 + 1, lowerDensity A / 2, half_pos hA, fun k hk => _ ⟩;
    have := hN1 ( 2 ^ k ) ( by linarith [ Nat.lt_pow_of_log_lt one_lt_two ( by linarith : Nat.log 2 N1 < k ) ] ) ; rw [ ge_iff_le, le_div_iff₀ ] at this <;> norm_cast at * ; aesop;

theorem helper {b : ℕ} (hb : 1 < b) {x y : ℕ} (hy : y ≠ 0) : y < b ^ x ↔ Nat.log b y < x := by
  simp_all only [ne_eq]
  apply Iff.intro
  · intro a
    rw [Nat.log_lt_iff_lt_pow]
    simp_all only
    exact hb
    exact hy
  · intro a
    rw [Nat.log_lt_iff_lt_pow] at a
    simp_all only
    exact hb
    exact hy

/-
Lemma 2: A harmonic lower bound from lower density. If A has positive lower density, then the sum of reciprocals of A up to N is at least c log N.
-/
lemma harmonic_lower_bound (A : Set ℕ) (hA : lowerDensity A > 0) :
  ∃ N0 c, c > 0 ∧ ∀ N ≥ N0, ∑ a ∈ (Finset.Icc 1 N).filter (· ∈ A), (1 : ℝ) / a ≥ c * Real.log N := by
    -- Use `bk_lower_bound` to get $k1, \delta'$.
    obtain ⟨k1, δ', hδ'_pos, hk1⟩ : ∃ k1 δ', δ' > 0 ∧ ∀ k ≥ k1, (bk A k : ℝ) ≥ δ' * 2^k := by
      exact bk_lower_bound A hA;
    -- Let $N$ be large. Let $K = \lfloor \log_2 N \rfloor$.
    obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, ∀ N ≥ N0, ∑ k ∈ Finset.Icc (k1 + 1) (Nat.log 2 N), ((bk A k : ℝ) - bk A (k - 1)) / 2^k ≥ (δ' / 2) * (Nat.log 2 N - k1 - 2) - (bk A k1 : ℝ) / 2^(k1+1) := by
      use 2 ^ ( k1 + 2 );
      intro N hN
      have h_log : Nat.log 2 N ≥ k1 + 2 := by
        exact Nat.le_log_of_pow_le ( by norm_num ) hN;
      exact sum_density_lower_bound (bk A) δ' k1 (Nat.log 2 N) h_log fun k a a_1 => hk1 k a;
    -- The sum becomes $\sum_{k=k_1+1}^K \frac{b_k - b_{k-1}}{2^k}$.
    have h_sum_bound : ∀ N ≥ 2^(k1 + 1), ∑ a ∈ (Finset.Icc 1 N).filter (· ∈ A), (1 : ℝ) / a ≥ ∑ k ∈ Finset.Icc (k1 + 1) (Nat.log 2 N), ((bk A k : ℝ) - bk A (k - 1)) / 2^k := by
      intros N hN
      have h_sum_bound : ∑ a ∈ (Finset.Icc 1 N).filter (· ∈ A), (1 : ℝ) / a ≥ ∑ k ∈ Finset.Icc (k1 + 1) (Nat.log 2 N), ∑ a ∈ (Finset.Ioc (2^(k-1)) (2^k)).filter (· ∈ A), (1 : ℝ) / a := by
        rw [ ← Finset.sum_biUnion ];
        · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity;
          simp +contextual [ Finset.subset_iff ];
          exact fun x k hk₁ hk₂ hk₃ hk₄ hx => ⟨ Nat.pos_of_ne_zero ( by aesop ), hk₄.trans ( Nat.pow_le_of_le_log ( by aesop ) ( by linarith ) ) ⟩;
        · intros k hk l hl hkl; simp_all +decide [ Finset.disjoint_left ] ;
          intro a ha₁ ha₂ ha₃ ha₄; contrapose! hkl;
          exact le_antisymm ( Nat.le_of_not_lt fun h => by linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( Nat.le_sub_one_of_lt h ) ] ) ( Nat.le_of_not_lt fun h => by linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( Nat.le_sub_one_of_lt h ) ] );
      refine le_trans ?_ h_sum_bound;
      refine Finset.sum_le_sum fun k hk => ?_;
      refine' le_trans _ ( sum_recip_dyadic_bound A k );
      · gcongr;
        rw [ sub_le_iff_le_add' ];
        norm_cast;
        rw [ show bk A k = ( Finset.filter ( fun x => x ∈ A ) ( Finset.Icc 1 ( 2 ^ k ) ) ).card from rfl, show bk A ( k - 1 ) = ( Finset.filter ( fun x => x ∈ A ) ( Finset.Icc 1 ( 2 ^ ( k - 1 ) ) ) ).card from rfl ];
        rw [ ← Finset.card_union_of_disjoint ];
        · refine' Finset.card_mono _;
          intro x hx; by_cases hx' : x ≤ 2 ^ ( k - 1 ) <;> aesop;
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx₁ |>.1 ), Finset.mem_Ioc.mp ( Finset.mem_filter.mp hx₂ |>.1 ) ] ;
    -- Since $K \approx \log N$, the result follows.
    obtain ⟨N1, hN1⟩ : ∃ N1 : ℕ, ∀ N ≥ N1, (δ' / 2) * (Nat.log 2 N - k1 - 2) - (bk A k1 : ℝ) / 2^(k1 + 1) ≥ (δ' / 8) * Real.log N := by
      -- We'll use that $Nat.log 2 N \geq \frac{\log N}{\log 2}$ for large $N$.
      have h_log_bound : ∃ N1 : ℕ, ∀ N ≥ N1, (Nat.log 2 N : ℝ) ≥ (Real.log N) / (Real.log 2) - 1 := by
        use 2
        intro N hN
        rw [ ge_iff_le ]
        rw [ div_sub_one, div_le_iff₀ ] <;> norm_num [ Real.log_pos ]
        ring_nf
        rw [ ← Real.log_rpow, ← Real.log_mul, Real.log_le_log_iff ] <;> norm_cast <;> try positivity
        rw [ ← pow_succ, Nat.le_iff_lt_or_eq, helper ] <;> norm_num
        linarith
      obtain ⟨ N1, hN1 ⟩ := h_log_bound;
      -- We'll use that $Real.log N$ grows faster than any linear function in $N$.
      have h_log_growth : Filter.Tendsto (fun N : ℕ => (δ' / 2) * ((Real.log N) / (Real.log 2) - 1 - k1 - 2) - (bk A k1 : ℝ) / 2^(k1 + 1) - (δ' / 8) * Real.log N) Filter.atTop Filter.atTop := by
        ring_nf;
        -- We can factor out the common term $\delta'$ and use the fact that $\log N$ grows faster than any linear function in $N$.
        have h_log_growth : Filter.Tendsto (fun N : ℕ => Real.log N * (δ' * (Real.log 2)⁻¹ * (1 / 2) - δ' * (1 / 8))) Filter.atTop Filter.atTop := by
          exact Filter.Tendsto.atTop_mul_const ( by nlinarith [ show ( Real.log 2 ) ⁻¹ > 1 by exact one_lt_inv₀ ( Real.log_pos one_lt_two ) |>.2 ( Real.log_two_lt_d9.trans_le ( by norm_num ) ) ] ) ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
        rw [ Filter.tendsto_atTop_atTop ] at *;
        exact fun b => by obtain ⟨ i, hi ⟩ := h_log_growth ( b + 3 * δ' / 2 + δ' * k1 / 2 + ( bk A k1 : ℝ ) * 2⁻¹ ^ k1 * ( 1 / 2 ) ) ; exact ⟨ i, fun a ha => by linarith [ hi a ha ] ⟩ ;
      exact Filter.eventually_atTop.mp ( h_log_growth.eventually_ge_atTop 0 ) |> fun ⟨ N2, hN2 ⟩ => ⟨ Max.max N1 N2, fun N hN => by nlinarith [ hN1 N ( le_trans ( le_max_left _ _ ) hN ), hN2 N ( le_trans ( le_max_right _ _ ) hN ) ] ⟩;
    exact ⟨ Max.max N0 ( Max.max N1 ( 2 ^ ( k1 + 1 ) ) ), δ' / 8, by positivity, fun N hN => le_trans ( hN1 N ( le_trans ( le_max_of_le_right ( le_max_left _ _ ) ) hN ) ) ( le_trans ( hN0 N ( le_trans ( le_max_left _ _ ) hN ) ) ( h_sum_bound N ( le_trans ( le_max_of_le_right ( le_max_right _ _ ) ) hN ) ) ) ⟩

/-
Definitions of U_n and Phi_n. U_n is the set of pairs (p, k) where p is a prime factor of n and 1 <= k <= v_p(n). Phi_n(d) is the subset of U_n corresponding to the divisor d.
-/
def Un (n : ℕ) : Finset ((_ : ℕ) × ℕ) :=
  (Nat.factorization n).support.sigma (fun p => Finset.Icc 1 (Nat.factorization n p))

def Phi_n (n d : ℕ) : Finset ((_ : ℕ) × ℕ) :=
  (Nat.factorization n).support.sigma (fun p => Finset.Icc 1 (Nat.factorization d p))

/-
Lemma 3: Divisors as subsets; lcm as union. Phi_n maps divisors to subsets of U_n, is injective, and preserves lcm as union.
-/
lemma divisors_to_subsets (n : ℕ) (hn : n ≠ 0) :
  (∀ d, d ∣ n → Phi_n n d ⊆ Un n) ∧
  ({d | d ∣ n}.InjOn (Phi_n n)) ∧
  (∀ d1 d2, d1 ∣ n → d2 ∣ n → Phi_n n (Nat.lcm d1 d2) = Phi_n n d1 ∪ Phi_n n d2) := by
    refine' ⟨ _, _, _ ⟩;
    · intro d hd x hx
      simp_all +decide [ Phi_n, Un ]
      exact le_trans hx.2.2 ( Nat.factorization_le_iff_dvd ( by aesop ) ( by aesop ) |>.2 hd _ )
    · intro d1 hd1 d2 hd2 h_eq;
      -- Since the factorizations are equal, we can conclude that d1 = d2.
      have h_factorization_eq : d1.factorization = d2.factorization := by
        ext p; by_cases hp : p ∈ n.primeFactors <;> simp_all +decide [ Finset.ext_iff, Phi_n ] ;
        · -- Apply the hypothesis `h_eq` with `a = (p, d1.factorization p + 1)` and `a = (p, d2.factorization p + 1)`.
          have h1 := h_eq ⟨p, d1.factorization p + 1⟩ hp.left hp.right (by linarith)
          have h2 := h_eq ⟨p, d2.factorization p + 1⟩ hp.left hp.right (by linarith);
          grind +ring;
        · by_cases hp : Nat.Prime p <;> simp_all +decide
          rw [ Nat.factorization_eq_zero_of_not_dvd ( fun h => ‹¬p ∣ n› <| dvd_trans h hd1 ), Nat.factorization_eq_zero_of_not_dvd ( fun h => ‹¬p ∣ n› <| dvd_trans h hd2 ) ];
      rw [ ← Nat.factorization_prod_pow_eq_self ( Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos hd1 ( Nat.pos_of_ne_zero hn ) ) ), ← Nat.factorization_prod_pow_eq_self ( Nat.ne_of_gt ( Nat.pos_of_dvd_of_pos hd2 ( Nat.pos_of_ne_zero hn ) ) ), h_factorization_eq ];
    · intro d1 d2 hd1 hd2;
      ext ⟨ p, k ⟩ ; simp +decide [ Phi_n ] ;
      rw [ Nat.factorization_lcm ] <;> aesop

/-
Lemma 4: From lcm-triple-free to union-free. If A is lcm-triple-free, then the family of subsets corresponding to divisors of n in A is union-free.
-/
lemma lcmfree_to_unionfree (A : Set ℕ)
  (h_lcm_free : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → b ≠ c → a ≠ c → Nat.lcm a b ≠ c)
  (n : ℕ) (hn : n ≠ 0) :
  UnionFree (((Nat.divisors n).filter (· ∈ A)).image (Phi_n n)) := by
    intro x hx y hy z hz hxy hyz hxz h_union
    obtain ⟨d_x, hd_x⟩ := Finset.mem_image.mp hx
    obtain ⟨d_y, hd_y⟩ := Finset.mem_image.mp hy
    obtain ⟨d_z, hd_z⟩ := Finset.mem_image.mp hz
    have h_lcm : Nat.lcm d_x d_y = d_z := by
      have h_lcm : Phi_n n (Nat.lcm d_x d_y) = Phi_n n d_x ∪ Phi_n n d_y := by
        apply (divisors_to_subsets n hn).2.2 d_x d_y (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd_x.1 |>.1)) (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd_y.1 |>.1));
      have h_lcm : ∀ d1 d2, d1 ∣ n → d2 ∣ n → Phi_n n d1 = Phi_n n d2 → d1 = d2 := by
        have := divisors_to_subsets n hn; aesop;
      apply h_lcm;
      · exact Nat.lcm_dvd ( Nat.dvd_of_mem_divisors ( Finset.mem_filter.mp hd_x.1 |>.1 ) ) ( Nat.dvd_of_mem_divisors ( Finset.mem_filter.mp hd_y.1 |>.1 ) );
      · exact Nat.dvd_of_mem_divisors ( Finset.mem_filter.mp hd_z.1 |>.1 );
      · grind +ring;
    grind

/-
Lemma 5: A binomial upper bound. There exists a constant C0 such that the central binomial coefficient of k is at most C0 * 2^k / sqrt(k).
-/
lemma central_binom_bound :
  ∃ C0, ∀ k ≥ 1, (Nat.choose k (k / 2) : ℝ) ≤ C0 * (2^k / Real.sqrt k) := by
    -- We'll use the fact that $\binom{2m}{m} \leq \frac{4^m}{\sqrt{3m+1}}$ for all $m \geq 0$.
    have h_binom_bound : ∀ m : ℕ, (Nat.choose (2 * m) m : ℝ) ≤ (4 ^ m) / Real.sqrt (3 * m + 1) := by
      intro m
      have h_stirling : (Nat.choose (2 * m) m : ℝ) ≤ (4 ^ m) / Real.sqrt (3 * m + 1) := by
        have h_binom : (Nat.choose (2 * m) m : ℝ) ^ 2 ≤ (4 ^ (2 * m)) / (3 * m + 1) := by
          field_simp;
          induction' m with m ih <;> norm_num [ Nat.cast_succ, Nat.mul_succ, pow_succ', pow_mul' ] at *;
          have h_binom_succ : (Nat.choose (2 * m + 2) (m + 1) : ℝ) = (Nat.choose (2 * m) m : ℝ) * (2 * m + 1) * 2 / (m + 1) := by
            rw [ Nat.cast_choose, Nat.cast_choose ] <;> try linarith;
            norm_num [ two_mul, add_assoc, Nat.factorial ] ; ring_nf;
            rw [ show 2 + m * 2 - ( 1 + m ) = m + 1 by rw [ Nat.sub_eq_of_eq_add ] ; ring ] ; norm_num [ Nat.factorial_succ ] ; ring_nf;
            -- Combine and simplify the fractions
            field_simp
            ring;
          rw [ h_binom_succ, div_mul_div_comm, div_mul_eq_mul_div, div_le_iff₀ ] <;> ring_nf at * <;> try positivity;
          nlinarith [ pow_nonneg ( Nat.cast_nonneg m : ( 0 : ℝ ) ≤ m ) 3 ]
        convert Real.le_sqrt_of_sq_le h_binom using 1 ; norm_num [ pow_mul' ];
      convert h_stirling using 1;
    -- Let's choose $C0 = 2$.
    use 2;
    intro k hk; rcases Nat.even_or_odd' k with ⟨ c, rfl | rfl ⟩ <;> norm_num at *;
    · refine le_trans ( h_binom_bound c ) ?_ ; ring_nf ; norm_num [ pow_mul' ];
      field_simp;
      rw [ le_div_iff₀ ( Real.sqrt_pos.mpr ( Nat.cast_pos.mpr ( by linarith ) ) ) ] ; nlinarith [ Real.sqrt_nonneg 2, Real.sqrt_nonneg ( 1 + c * 3 ), Real.mul_self_sqrt ( show 0 ≤ 2 by norm_num ), Real.mul_self_sqrt ( show 0 ≤ 1 + ( c : ℝ ) * 3 by positivity ), Real.sqrt_nonneg c, Real.mul_self_sqrt ( show 0 ≤ ( c : ℝ ) by positivity ) ];
    · have := h_binom_bound ( c + 1 ) ; norm_num [ Nat.add_div, Nat.mul_succ, pow_succ', pow_mul ] at *;
      rw [ show ( 2 * c + 2 : ℕ ) = 2 * c + 1 + 1 by ring, Nat.choose_succ_succ ] at this ; ring_nf at * ; norm_num at *;
      refine le_trans ?_ ( this.trans ?_ );
      · exact le_add_of_nonneg_right ( Nat.cast_nonneg _ );
      · gcongr <;> norm_num

/-
Definitions of arithmetic functions g, d_odd, and f.
-/
noncomputable def g_val (p k : ℕ) : ℝ :=
  if p = 2 then 0
  else if k = 1 then 0
  else (2 : ℝ) ^ (k - 2)

noncomputable def g_func : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (Nat.factorization n).prod (fun p k => g_val p k), by simp⟩

noncomputable def d_odd_func : ArithmeticFunction ℝ :=
  ⟨fun n => if Odd n then (tauu n : ℝ) else 0, by simp⟩

noncomputable def f_func : ArithmeticFunction ℝ :=
  ⟨fun n => if Odd n then (2 : ℝ) ^ Om n else 0, by simp⟩

/-
The arithmetic function g is multiplicative.
-/
lemma g_func_multiplicative : ArithmeticFunction.IsMultiplicative g_func := by
  constructor;
  · unfold g_func; norm_num;
  · intro m n hmn
    unfold g_func
    by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp [hm, hn];
    rw [ Finsupp.prod_add_index_of_disjoint ];
    exact hmn.disjoint_primeFactors

/-
The arithmetic function d_odd is multiplicative.
-/
lemma d_odd_func_multiplicative : ArithmeticFunction.IsMultiplicative d_odd_func := by
  unfold d_odd_func;
  constructor;
  · aesop;
  · intro m n hmn; simp +decide [ * ] ;
    split_ifs <;> simp_all +decide [ Nat.odd_iff, Nat.mul_mod ];
    unfold tauu; norm_cast;
    exact Nat.Coprime.card_divisors_mul hmn

/-
The arithmetic function f is multiplicative.
-/
lemma f_func_multiplicative : ArithmeticFunction.IsMultiplicative f_func := by
  constructor;
  · unfold f_func; norm_num;
    unfold Om; norm_num;
  · intro m n hmn
    by_cases hm : Even m <;> by_cases hn : Even n <;> simp +decide [ f_func ];
    · exact absurd ( Nat.dvd_gcd ( even_iff_two_dvd.mp hm ) ( even_iff_two_dvd.mp hn ) ) ( by aesop );
    · grind;
    · simp_all +decide [ Nat.even_iff, Nat.odd_iff, Nat.mul_mod ];
    · simp_all +decide [ Nat.even_iff, Nat.odd_iff, Om ];
      rw [ ← pow_add, Nat.factorization_mul ( by aesop ) ( by aesop ), Finsupp.sum_add_index' ] <;> aesop

set_option maxHeartbeats 1000000 in
/-
Identity for the convolution sum at odd prime powers.
-/
lemma sum_g_odd_prime (p k : ℕ) (hp : Nat.Prime p) (hp_odd : p ≠ 2) :
  ∑ j ∈ Finset.range (k + 1), (j + 1 : ℝ) * g_func (p ^ (k - j)) = (2 : ℝ) ^ k := by
    -- Let's simplify the expression using the definition of `g_func`.
    suffices h_simp : ∑ j ∈ Finset.range (k + 1), (j + 1) * (if k - j = 0 then 1 else if k - j = 1 then 0 else (2 : ℝ) ^ (k - j - 2)) = 2 ^ k by
      unfold g_func;
      convert h_simp using 2 ; norm_num [ g_val ] ; ring_nf;
      split_ifs <;> simp_all +decide [ hp.ne_zero ];
      · ring;
      · erw [ Finsupp.prod_of_support_subset ] <;> norm_num [ hp.ne_zero, hp_odd ];
        any_goals exact { p };
        · rw [ Finset.prod_singleton ] ; aesop;
        · intro q hq; contrapose! hq; simp_all +decide
        · aesop;
    induction' k using Nat.strong_induction_on with k ih;
    rcases k with ( _ | _ | k ) <;> simp_all +decide [ Finset.sum_range_succ', pow_succ' ];
    · norm_num +zetaDelta at *;
    · have H₁ := ih k ( by linarith ) ; have H₂ := ih ( k + 1 ) ( by linarith ) ; simp_all +decide [ Finset.sum_range_succ', pow_succ' ] ;
      rcases k with ( _ | _ | k ) <;> norm_num [ Finset.sum_add_distrib, add_mul, mul_assoc, pow_succ' ] at *;
      norm_num [ Finset.sum_add_distrib, add_assoc, add_left_comm, add_comm, Finset.sum_ite ] at *;
      linarith

/-
The functions f and d_odd * g agree on prime powers.
-/
lemma f_eq_d_odd_mul_g_prime_pow (p k : ℕ) (hp : Nat.Prime p) :
  f_func (p ^ k) = (d_odd_func * g_func) (p ^ k) := by
    -- Apply the lemma sum_g_odd_prime to conclude the proof for prime powers.
    have h_prime_pow : ∀ p k : ℕ, Nat.Prime p → ∑ j ∈ Finset.range (k + 1), (d_odd_func (p ^ j) : ℝ) * (g_func (p ^ (k - j)) : ℝ) = (f_func (p ^ k) : ℝ) := by
      intro p k hp;
      by_cases hp2 : p = 2 <;> simp_all +decide [ d_odd_func, f_func ];
      · simp +decide [ Nat.odd_iff, g_func ];
        unfold tauu Om g_val; aesop;
      · -- Apply the lemma sum_g_odd_prime to conclude the proof for odd primes.
        have := sum_g_odd_prime p k hp hp2; simp_all +decide [ tauu, Om ];
        convert this using 2;
        · rw [ if_pos ( by exact Odd.pow ( by simpa using hp.eq_two_or_odd'.resolve_left hp2 ) ), Nat.divisors_prime_pow hp ] ; aesop;
        · simp +decide [ hp.even_iff, hp2, parity_simps ];
    rw [ ← h_prime_pow p k hp, ArithmeticFunction.mul_apply ];
    rw [ Nat.sum_divisorsAntidiagonal fun i j => d_odd_func i * g_func j ];
    norm_num [ Nat.divisors_prime_pow hp ];
    exact Finset.sum_congr rfl fun x hx => by rw [ Nat.div_eq_of_eq_mul_left ( pow_pos hp.pos _ ) ] ; rw [ ← pow_add, Nat.sub_add_cancel ( Finset.mem_range_succ_iff.mp hx ) ] ;

/-
The function f is equal to the Dirichlet convolution of d_odd and g.
-/
lemma f_eq_d_odd_mul_g : f_func = d_odd_func * g_func := by
  apply ArithmeticFunction.ext;
  -- By definition of multiplicative functions, if two multiplicative functions agree on prime powers, they are equal everywhere.
  have h_mul_eq : ∀ (f g : ArithmeticFunction ℝ), ArithmeticFunction.IsMultiplicative f → ArithmeticFunction.IsMultiplicative g → (∀ p k, Nat.Prime p → f (p ^ k) = g (p ^ k)) → f = g := by
    intros f g hf hg hfg;
    exact (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers f hf g hg).mpr hfg;
  exact fun n => congr_arg ( fun f => f n ) ( h_mul_eq _ _ ( f_func_multiplicative ) ( d_odd_func_multiplicative.mul g_func_multiplicative ) fun p k hp => f_eq_d_odd_mul_g_prime_pow p k hp ) ▸ rfl

/-
The sum of the divisor function is O(N log N).
-/
lemma sum_tau_bound : (fun N => ∑ n ∈ Finset.range (N + 1), (tauu n : ℝ)) =O[Filter.atTop] (fun N => (N : ℝ) * Real.log N) := by
  -- The sum of the divisor function $\tau(n)$ over $n \leq N$ is $O(N \log N)$.
  have h_sum_divisors : ∀ N : ℕ, (∑ n ∈ Finset.range (N + 1), (tauu n : ℝ)) ≤ (N + 1) * (Real.log (N + 1) + 1) := by
    intro N;
    -- We'll use the fact that $\sum_{n \leq N} � \�tau(n) \leq \sum_{d \leq N �}� \left\lfloor \frac{N}{d} \right\rfloor$.
    have h_sum_divisors_le_floor : ∑ n ∈ Finset.range (N + 1), (tauu n : ℝ) ≤ ∑ d ∈ Finset.Ico 1 (N + 1), (N / d : ℝ) := by
      -- We'll use the fact that $\sum_{n \leq N} \tau(n)$ is equal to $\sum_{d \leq N} \left\lfloor \frac{N}{d} \right\rfloor$.
      have h_sum_divisors_eq : ∑ n ∈ Finset.range (N + 1), (tauu n : ℝ) = ∑ d ∈ Finset.Ico 1 (N + 1), (Nat.floor (N / d) : ℝ) := by
        induction N <;> simp_all +decide [ Finset.sum_range_succ, Nat.succ_div ];
        simp +decide [ Finset.sum_add_distrib, Finset.sum_Ico_succ_top, Nat.div_eq_of_lt ];
        unfold tauu; aesop;
      exact h_sum_divisors_eq.le.trans ( Finset.sum_le_sum fun x hx => by rw [ le_div_iff₀ ] <;> norm_cast <;> nlinarith [ Finset.mem_Ico.mp hx, Nat.div_mul_le_self N x, Nat.floor_le ( show 0 ≤ N / x from Nat.zero_le _ ) ] );
    -- We'll use the fact � that� $\sum_{d=1}^{N} \frac{1}{d} \leq \log N + 1$.
    have h_harmonic : ∑ d ∈ Finset.Ico 1 (N + 1), (1 / (d : ℝ)) ≤ Real.log N + 1 := by
      have h_sum_divisors_le_harmonic : ∀ N : ℕ, N ≥ 1 → ∑ x ∈ Finset.Ico 1 (N + 1), (1 / (x : ℝ)) ≤ Real.log N + 1 := by
        intros N hN; induction' hN with N hN ih <;> norm_num [ Finset.sum_Ico_succ_top ] at *;
        field_simp;
        have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( N : ℝ ) / ( N + 1 ) ) ; rw [ Real.log_div ( by positivity ) ( by positivity ) ] at this ; norm_num at * ; nlinarith [ mul_div_cancel₀ ( N : ℝ ) ( by positivity : ( N + 1 : ℝ ) ≠ 0 ) ] ;
      exact if hN : 1 ≤ N then h_sum_divisors_le_harmonic N hN else by aesop;
    rcases N.eq_zero_or_pos with hN | hN <;> simp_all +decide [ div_eq_mul_inv ];
    exact h_sum_divisors_le_floor.trans ( by rw [ ← Finset.mul_sum _ _ _ ] ; nlinarith [ Real.log_nonneg ( show ( N:ℝ ) ≥ 1 by norm_cast ), Real.log_le_log ( by positivity ) ( show ( N:ℝ ) + 1 ≥ N by linarith ) ] );
  refine' Asymptotics.IsBigO.of_bound 8 _;
  filter_upwards [ Filter.eventually_gt_atTop 1 ] with N hN ; rw [ Real.norm_of_nonneg <| Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ] ; rw [ Real.norm_of_nonneg <| by positivity ] ; specialize h_sum_divisors N ; rcases N with ( _ | _ | N ) <;> norm_num at *;
  have := Real.log_le_sub_one_of_pos ( by positivity : 0 < ( N + 1 + 1 + 1 : ℝ ) / ( N + 1 + 1 ) ) ; rw [ Real.log_div ( by positivity ) ( by positivity ) ] at this ; ring_nf at * ; norm_num at *;
  nlinarith [ Real.log_inv ( 2 + N : ℝ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by linarith : 0 < ( 2 + N : ℝ ) ) ), mul_inv_cancel₀ ( by linarith : ( 2 + N : ℝ ) ≠ 0 ), Real.log_pos ( by linarith : ( 2 + N : ℝ ) > 1 ), Real.log_le_log ( by linarith ) ( by linarith : ( 3 + N : ℝ ) ≥ ( 2 + N : ℝ ) ) ]

/-
The arithmetic function g is non-negative.
-/
lemma g_func_nonneg (n : ℕ) : 0 ≤ g_func n := by
  unfold g_func;
  unfold g_val;
  norm_num +zetaDelta at *;
  split_ifs <;> norm_num [ Finsupp.prod ];
  exact Finset.prod_nonneg fun _ _ => by split_ifs <;> positivity;

/-
Identity for the sum of a Dirichlet convolution.
-/
lemma sum_convolution_eq {f g : ArithmeticFunction ℝ} (N : ℕ) :
  ∑ n ∈ Finset.range (N + 1), (f * g) n = ∑ q ∈ Finset.range (N + 1), g q * ∑ m ∈ Finset.range (N / q + 1), f m := by
    simp +decide only [ArithmeticFunction.mul_apply];
    simp +decide only [Nat.divisorsAntidiagonal, Finset.sum_sigma'];
    rw [ show ( Finset.range ( N + 1 ) ).sigma ( fun a => Finset.filterMap ( fun x => if x * ( a / x ) = a then some ( x, a / x ) else none ) ( Finset.Icc 1 a ) _ ) = Finset.biUnion ( Finset.range ( N + 1 ) ) ( fun x => Finset.image ( fun m => ⟨ x * m, ( m, x ) ⟩ ) ( Finset.Icc 1 ( N / x ) ) ) from ?_, Finset.sum_biUnion ];
    · simp +decide [ mul_comm, Finset.mul_sum _ _ _ ];
      exact Finset.sum_congr rfl fun i hi => by erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num;
    · intros x hx y hy hxy; simp [Finset.disjoint_left, Finset.mem_image];
      grind;
    · -- To prove equality of finite � sets�, we show each set is a subset of the other.
      apply Finset.ext
      intro p
      simp [Finset.mem_sigma, Finset.mem_biUnion, Finset.mem_image];
      constructor;
      · rintro ⟨ h₁, a, ⟨ ha₁, ha₂ ⟩, ha₃, ha₄ ⟩;
        use p.fst / a, by
          nlinarith [ Nat.div_mul_le_self p.fst a ], a, by
          exact ⟨ ha₁, by rw [ Nat.le_div_iff_mul_le ( Nat.div_pos ( by linarith ) ( by linarith ) ) ] ; nlinarith ⟩
        generalize_proofs at *;
        grind;
      · rintro ⟨ a, ha, b, hb, rfl ⟩;
        rcases a with ( _ | a ) <;> rcases b with ( _ | b ) <;> norm_num at *;
        exact ⟨ by nlinarith [ Nat.div_mul_le_self N ( a + 1 ) ], b + 1, ⟨ by linarith, by nlinarith ⟩, by rw [ Nat.mul_div_cancel' ] ; exact dvd_mul_left _ _, rfl, by rw [ Nat.mul_div_cancel _ ( by linarith ) ] ⟩

/-
The sum of g(p^k)/p^k is bounded by 1 + 3/p^2 for odd primes p.
-/
lemma prime_sum_bound (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) :
    Summable (fun k => g_func (p ^ k) / (p ^ k : ℝ)) ∧
    ∑' k, g_func (p ^ k) / (p ^ k : ℝ) ≤ 1 + 3 / (p ^ 2 : ℝ) := by
      constructor;
      · refine' summable_nat_add_iff 2 |>.1 _;
        -- We'll use the fact that $g(p^k) = 2^{k-2}$ for $k \geq 2$.
        have h_g_p_k : ∀ k ≥ 2, g_func (p ^ k) = (2 : ℝ) ^ (k - 2) := by
          unfold g_func;
          unfold g_val; aesop;
        norm_num [ h_g_p_k ];
        ring_nf;
        simpa only [ mul_assoc, ← mul_pow ] using Summable.mul_left _ ( summable_geometric_of_lt_one ( by positivity ) ( by rw [ inv_mul_lt_iff₀ ( by norm_cast; linarith [ hp.pos ] ) ] ; norm_cast; linarith [ hp.two_le, show p > 2 from lt_of_le_of_ne hp.two_le ( Ne.symm hp_odd ) ] ) );
      · -- For an odd prime $p$, $g(p^0)=1$, $g(p^1)=0$, and $g(p^k)=2^{k-2}$ for $k \ge 2$.
        have h_g_prime_power (k : ℕ) : g_func (p ^ k) = if k = 0 then 1 else if k = 1 then 0 else (2 : ℝ) ^ (k - 2) := by
          unfold g_func;
          unfold g_val; aesop;
        -- The sum of the geometric series $\sum_{k=2}^\infty \frac{2^{k-2}} �{�p^k}$ is $\frac{1}{p^2} \sum_{j=0}^\in �fty� \left(\frac{2}{p}\right)^j = \frac{1}{p^2} \cdot \frac{1}{1 - \frac{2}{p}} = \frac{1}{p(p-2)}$.
        have h_geo_series : ∑' k : ℕ, (if k = 0 then 1 else if k = 1 then 0 else (2 : ℝ) ^ (k - 2)) / (p ^ k : ℝ) = 1 + (1 / (p ^ 2 : ℝ)) * (1 / (1 - 2 / p)) := by
          rw [ ← Summable.sum_add_tsum_nat_add 2 ];
          · norm_num [ Finset.sum_range_succ' ];
            rw [ ← tsum_geometric_of_lt_one ( by positivity ) ( show ( 2 : ℝ ) / p < 1 by rw [ div_lt_iff₀ ( Nat.cast_pos.mpr hp.pos ) ] ; norm_cast; linarith [ show p > 2 from lt_of_le_of_ne hp.two_le ( Ne.symm hp_odd ) ] ) ] ; rw [ ← tsum_mul_left ] ; congr ; ext i ; ring_nf;
            grind;
          · rw [ ← summable_nat_add_iff 2 ];
            norm_num [ pow_add, ← div_div ];
            norm_num [ Nat.succ_inj ];
            simpa only [ ← div_pow ] using Summable.mul_right _ ( summable_geometric_of_lt_one ( by positivity ) ( by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ hp.two_le, show p > 2 from lt_of_le_of_ne hp.two_le ( Ne.symm hp_odd ) ] ) );
        simp_all +decide [ division_def ];
        rw [ ← mul_inv, mul_comm ];
        rw [ inv_le_comm₀ ] <;> norm_num <;> nlinarith only [ show ( p : ℝ ) ≥ 3 by norm_cast; contrapose! hp_odd; interval_cases p <;> trivial, inv_mul_cancel₀ ( show ( p : ℝ ) ≠ 0 by norm_cast; exact hp.ne_zero ), inv_mul_cancel₀ ( show ( p ^ 2 : ℝ ) ≠ 0 by norm_cast; exact pow_ne_zero 2 hp.ne_zero ) ]

/-
The product of (1 + 3/p^2) is bounded.
-/
lemma prod_one_plus_inv_sq_bound : ∃ C, ∀ (S : Finset ℕ), (∀ p ∈ S, p ≥ 1) → ∏ p ∈ S, (1 + 3 / (p ^ 2 : ℝ)) ≤ C := by
  use Real.exp ( ∑' p : ℕ, ( 3 / ( p : ℝ ) ^ 2 ) );
  intros S hS_pos
  have h_prod_le_exp : (∏ p ∈ S, (1 + 3 / (p : ℝ) ^ 2)) ≤ Real.exp (∑ p ∈ S, (3 / (p : ℝ) ^ 2)) := by
    rw [ Real.exp_sum ] ; exact Finset.prod_le_prod ( fun _ _ => by positivity ) fun _ _ => by rw [ add_comm ] ; exact Real.add_one_le_exp _;
  exact h_prod_le_exp.trans ( Real.exp_le_exp.mpr <| Summable.sum_le_tsum _ ( fun _ _ => by positivity ) <| by simpa using Summable.mul_left _ <| Real.summable_one_div_nat_pow.2 one_lt_two )

/-
The sum of a non-negative multiplicative function is bounded by the product of its prime power sums.
-/
lemma sum_le_prod_of_multiplicative_bounded (f : ℕ → ℝ) (hf_pos : ∀ n, 0 ≤ f n)
    (hf_mul : ∀ m n, m.Coprime n → f (m * n) = f m * f n) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n ≤
    ∏ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (∑ k ∈ Finset.range (Nat.log p N + 1), f (p ^ k)) := by
      by_contra h_contra;
      -- Let $S = \{p \in \mathbb{P} \mid p \le N\}$.
      set S : Finset ℕ := Finset.filter Nat.Prime (Finset.range (N + 1)) with hS_def;
      -- By definition of $S$, we know that every $n \in \{1, \ldots, N\}$ can be written as $n = \prod_{p \in S} p^{e_p}$ where $0 \leq e_p \le �q� \lfloor \log_p N \rfloor$.
      have h_factorization : ∀ n ∈ Finset.Icc 1 N, ∃ e : ℕ → ℕ, (∀ p, p ∉ S → e p = 0) ∧ (∀ p ∈ S, e p ≤ Nat.log p N) ∧ n = ∏ p ∈ S, p ^ e p := by
        intro n hn
        use fun p => Nat.factorization n p
        simp [hS_def];
        refine' ⟨ _, _, _ ⟩;
        · intro p hp; by_cases hp_prime : Nat.Prime p <;> simp_all +decide [ Nat.factorization_eq_zero_iff ] ;
          exact Or.inl ( Nat.not_dvd_of_pos_of_lt hn.1 ( by linarith ) );
        · exact fun p hp₁ hp₂ => Nat.le_log_of_pow_le hp₂.one_lt <| Nat.le_trans ( Nat.le_of_dvd ( Finset.mem_Icc.mp hn |>.1 ) <| Nat.ordProj_dvd _ _ ) <| Finset.mem_Icc.mp hn |>.2;
        · conv_lhs => rw [ ← Nat.factorization_prod_pow_eq_self ( by linarith [ Finset.mem_Icc.mp hn ] : n ≠ 0 ) ] ;
          rw [ Finsupp.prod_of_support_subset ] <;> norm_num;
          exact fun p hp => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( Nat.lt_succ_of_le ( Nat.le_trans ( Nat.le_of_mem_primeFactors hp ) ( Finset.mem_Icc.mp hn |>.2 ) ) ), Nat.prime_of_mem_primeFactors hp ⟩;
      -- By definition of $f$, we know that $f(n) = \prod_{p \in S} f(p^{e_p})$ for any $n = \prod_{p \in S} p^{e_p}$.
      have h_f_factorization : ∀ n ∈ Finset.Icc 1 N, ∀ e : ℕ → ℕ, (∀ p, p ∉ S → e p = 0) ∧ (∀ p ∈ S, e p ≤ Nat.log p N) ∧ n = ∏ p ∈ S, p ^ e p → f n = ∏ p ∈ S, f (p ^ e p) := by
        intros n hn e he
        have h_f_factorization_step : ∀ (ps : Finset ℕ), (∀ p ∈ ps, Nat.Prime p) → (∀ p ∈ ps, e p ≤ Nat.log p N) → f (∏ p ∈ ps, p ^ e p) = ∏ p ∈ ps, f (p ^ e p) := by
          intros ps hps_prime hps_log; induction' ps using Finset.induction with p ps hps ih; simp_all +decide
          · by_cases h : f 1 = 0;
            · have h_f_zero : ∀ n, 1 ≤ n → n ≤ N → f n = 0 := by
                exact fun n hn hn' => by simpa [ h ] using hf_mul n 1 ( by norm_num ) ;
              exact False.elim <| h_contra.not_ge <| by rw [ Finset.sum_eq_zero fun x hx => h_f_zero x ( Finset.mem_Icc.mp hx |>.1 ) ( Finset.mem_Icc.mp hx |>.2 ) ] ; exact Finset.prod_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hf_pos _;
            · simpa [ h ] using hf_mul 1 1 ( by norm_num );
          · rw [ Finset.prod_insert hps, hf_mul ];
            · rw [ Finset.prod_insert hps, ih ( fun q hq => hps_prime q ( Finset.mem_insert_of_mem hq ) ) ( fun q hq => hps_log q ( Finset.mem_insert_of_mem hq ) ) ];
            · exact Nat.Coprime.prod_right fun q hq => Nat.Coprime.pow _ _ <| by have := Nat.coprime_primes ( hps_prime p <| Finset.mem_insert_self _ _ ) ( hps_prime q <| Finset.mem_insert_of_mem hq ) ; aesop;
        rw [ he.2.2, h_f_factorization_step S ( fun p hp => Finset.mem_filter.mp hp |>.2 ) ( fun p hp => he.2.1 p hp ) ];
      refine' h_contra _;
      choose! e he using h_factorization;
      rw [ Finset.prod_sum ];
      refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
      case refine'_2 => exact Finset.image ( fun n => fun p hp => e n p ) ( Finset.Icc 1 N );
      · rw [ Finset.sum_image ];
        · refine' Finset.sum_le_sum fun n hn => _;
          convert h_f_factorization n hn ( fun p => e n p ) ( he n hn ) |> le_of_eq using 1;
          conv_rhs => rw [ ← Finset.prod_attach ] ;
        · intros n hn m hm hnm;
          rw [ he n hn |>.2.2, he m hm |>.2.2 ];
          exact Finset.prod_congr rfl fun p hp => congr_arg _ ( congr_fun ( congr_fun hnm p ) hp );
      · exact Finset.image_subset_iff.mpr fun n hn => Finset.mem_pi.mpr fun p hp => Finset.mem_range.mpr ( Nat.lt_succ_of_le ( he n hn |>.2.1 p hp ) );
      · exact fun _ _ _ => Finset.prod_nonneg fun _ _ => hf_pos _

/-
The sum of g(q)/q is bounded.
-/
lemma sum_g_div_q_bound : ∃ C, ∀ N, ∑ q ∈ Finset.range (N + 1), g_func q / q ≤ C := by
  -- By definition of $g_func$, we know that $g_func(q) = 0$ for $q = 0$.
  use ∑' q : ℕ, g_func q / (q : ℝ);
  have h_sum_le_prod : Summable (fun q : ℕ => g_func q / (q : ℝ)) := by
    have h_sum_g_bounded : Summable (fun q : ℕ => (g_func q : ℝ) / (q : ℝ)) := by
      have h_sum_g_bounded : Summable (fun q : ℕ => (g_func (q : ℕ) : ℝ) / (q : ℝ)) := by
        have := @prod_one_plus_inv_sq_bound
        have h_sum_le_prod : ∀ N : ℕ, ∑ q ∈ Finset.range (N + 1), (g_func q : ℝ) / q ≤ ∏ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (1 + 3 / (p ^ 2 : ℝ)) := by
          intro N
          have h_sum_le_prod : ∑ q ∈ Finset.Icc 1 N, (g_func q : ℝ) / q ≤ ∏ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), (∑ k ∈ Finset.range (Nat.log p N + 1), (g_func (p ^ k) : ℝ) / p ^ k) := by
            convert sum_le_prod_of_multiplicative_bounded _ _ _ _ using 1;
            · norm_num [ div_eq_mul_inv ];
            · exact fun n => div_nonneg ( g_func_nonneg n ) ( Nat.cast_nonneg n );
            · intro m n hmn
              have h_mul : g_func (m * n) = g_func m * g_func n := by
                have := g_func_multiplicative; aesop;
              by_cases hm : m = 0 <;> by_cases hn : n = 0 <;> simp_all +decide [ mul_div_mul_comm ];
          have h_sum_le_prod : ∀ p ∈ Finset.filter Nat.Prime (Finset.range (N + 1)), ∑ k ∈ Finset.range (Nat.log p N + 1), (g_func (p ^ k) : ℝ) / p ^ k ≤ 1 + 3 / (p ^ 2 : ℝ) := by
            intros p hp
            by_cases hp2 : p = 2;
            · unfold g_func; norm_num [ hp2 ] ; ring_nf; norm_num;
              norm_num [ Finsupp.prod ];
              rw [ add_comm, Finset.sum_eq_single 0 ] <;> norm_num [ Finsupp.support_single_ne_zero ];
              intro b hb hb'; rw [ Finsupp.support_single_ne_zero ] <;> aesop;
            · have := prime_sum_bound p ( Finset.mem_filter.mp hp |>.2 ) hp2;
              exact le_trans ( Summable.sum_le_tsum ( Finset.range ( Nat.log p N + 1 ) ) ( fun _ _ => div_nonneg ( g_func_nonneg _ ) ( pow_nonneg ( Nat.cast_nonneg _ ) _ ) ) this.1 ) this.2;
          refine le_trans ?_ ( le_trans ‹_› <| Finset.prod_le_prod ?_ h_sum_le_prod );
          · erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ];
          · exact fun p hp => Finset.sum_nonneg fun _ _ => div_nonneg ( g_func_nonneg _ ) ( pow_nonneg ( Nat.cast_nonneg _ ) _ );
        rw [ summable_iff_not_tendsto_nat_atTop_of_nonneg ];
        · rw [ ← Filter.tendsto_add_atTop_iff_nat 1 ] ; exact fun h => absurd ( h.eventually_gt_atTop ( this.choose : ℝ ) ) fun h' => by obtain ⟨ N, hN ⟩ := h'.exists; exact not_le_of_gt hN <| le_trans ( h_sum_le_prod N ) <| this.choose_spec _ fun p hp => Nat.Prime.pos <| by aesop;
        · exact fun n => div_nonneg ( g_func_nonneg n ) ( Nat.cast_nonneg n )
      exact h_sum_g_bounded;
    convert h_sum_g_bounded using 1;
  exact fun N => Summable.sum_le_tsum ( Finset.range ( N + 1 ) ) ( fun _ _ => div_nonneg ( g_func_nonneg _ ) ( Nat.cast_nonneg _ ) ) h_sum_le_prod

/-
The sum of f is bounded by the convolution of g and tau.
-/
lemma sum_f_le_sum_g_mul_sum_tau (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), f_func n ≤
    ∑ q ∈ Finset.range (N + 1), g_func q * ∑ m ∈ Finset.range (N / q + 1), (tauu m : ℝ) := by
      rw [ f_eq_d_odd_mul_g ];
      rw [ sum_convolution_eq ];
      gcongr;
      · (expose_names; exact g_func_nonneg i);
      · unfold d_odd_func; aesop

/-
There exists a constant C such that the sum of tau(n) is bounded by C * N * (log N + 1) for all N >= 1.
-/
lemma sum_tau_explicit_bound : ∃ C, ∀ N ≥ 1, ∑ n ∈ Finset.range (N + 1), (tauu n : ℝ) ≤ C * N * (Real.log N + 1) := by
  have := sum_tau_bound;
  rw [ Asymptotics.isBigO_iff' ] at this;
  obtain ⟨ C, hC₀, hC ⟩ := this; erw [ Filter.eventually_atTop ] at hC; obtain ⟨ N₀, hN₀ ⟩ := hC; use Max.max C ( ∑ n ∈ Finset.range ( N₀ + 1 ), ( tauu n : ℝ ) ) ; intro N hN; rcases le_or_gt N N₀ with hN' | hN' <;> simp_all +decide [ mul_assoc ] ;
  · refine' le_trans _ ( mul_le_mul_of_nonneg_right ( le_max_right _ _ ) ( by positivity ) );
    exact le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.range_mono ( by linarith ) ) fun _ _ _ => Nat.cast_nonneg _ ) ( le_mul_of_one_le_right ( Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ) ( by nlinarith [ Real.log_nonneg ( show ( N : ℝ ) ≥ 1 by norm_cast ), show ( N : ℝ ) ≥ 1 by norm_cast ] ) );
  · refine' le_trans ( le_of_abs_le ( hN₀ N hN'.le ) ) _;
    rw [ abs_of_nonneg ( Real.log_nonneg ( Nat.one_le_cast.mpr hN ) ) ] ; exact mul_le_mul ( le_max_left _ _ ) ( by nlinarith [ Real.log_nonneg ( Nat.one_le_cast.mpr hN ) ] ) ( by positivity ) ( by positivity ) ;

/-
The sum of f(n) is bounded by C * N * (log N + 1).
-/
lemma sum_f_explicit_bound : ∃ C, ∀ N ≥ 1, ∑ n ∈ Finset.range (N + 1), f_func n ≤ C * N * (Real.log N + 1) := by
  -- By combining the results from sum_f_le_sum_g_mul_sum_tau and sum_tau_explicit_bound, we can conclude the proof.
  obtain ⟨C1, hC1⟩ := sum_tau_explicit_bound
  obtain ⟨C2, hC2⟩ := sum_g_div_q_bound
  use C1 * C2;
  intros N hN
  have h_sum_g_mul_sum_tau : ∑ n ∈ Finset.range (N + 1), f_func n ≤ ∑ q ∈ Finset.range (N + 1), g_func q * (C1 * (N / q) * (Real.log N + 1)) := by
    refine le_trans ( sum_f_le_sum_g_mul_sum_tau N ) ?_;
    refine Finset.sum_le_sum fun q hq => mul_le_mul_of_nonneg_left ?_ <| ?_;
    · by_cases hq0 : q = 0;
      · aesop;
      · refine le_trans ( hC1 ( N / q ) ( Nat.div_pos ( by linarith [ Finset.mem_range.mp hq ] ) ( Nat.pos_of_ne_zero hq0 ) ) ) ?_;
        gcongr <;> norm_cast;
        · exact mul_nonneg ( by have := hC1 1 le_rfl; norm_num [ Finset.sum_range_succ, tauu ] at this; nlinarith [ Real.log_nonneg one_le_two ] ) ( by positivity );
        · specialize hC1 1 ; norm_num at hC1 ; linarith [ show ( ∑ n ∈ Finset.range 2, ( tauu n : ℝ ) ) ≥ 0 by exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _ ];
        · rw [ le_div_iff₀ ( Nat.cast_pos.mpr ( Nat.pos_of_ne_zero hq0 ) ) ] ; norm_cast ; linarith [ Nat.div_mul_le_self N q ];
        · exact Nat.div_pos ( by linarith [ Finset.mem_range.mp hq ] ) ( Nat.pos_of_ne_zero hq0 );
        · exact Nat.div_le_self _ _;
    · exact g_func_nonneg q;
  refine le_trans h_sum_g_mul_sum_tau ?_;
  convert mul_le_mul_of_nonneg_left ( hC2 N ) ( show 0 ≤ C1 * ↑N * ( Real.log ↑N + 1 ) by exact mul_nonneg ( mul_nonneg ( show 0 ≤ C1 by have := hC1 1 le_rfl; norm_num [ Finset.sum_range_succ, tauu ] at this; nlinarith ) ( Nat.cast_nonneg _ ) ) ( add_nonneg ( Real.log_natCast_nonneg _ ) zero_le_one ) ) using 1 ; ring_nf;
  · rw [ Finset.mul_sum _ _ _, Finset.mul_sum _ _ _ ] ; rw [ ← Finset.sum_add_distrib ] ; exact Finset.sum_congr rfl fun _ _ => by ring;
  · ring

/-
A summatory bound for $2^{\Om(n)}$ over odd integers.
Define $f(n)=2^{\Om(n)}$ if $n$ is odd and $f(n)=0$ if $n$ is even.
Then
\[
\sum_{n\le N} f(n)\ \ll\ N\log N.
\]
-/
lemma sum_2Omega_odd : (fun N => ∑ n ∈ Finset.range (N + 1), f_func n) =O[Filter.atTop] (fun N => (N : ℝ) * Real.log N) := by
  choose! C hC using sum_f_explicit_bound;
  refine' Asymptotics.IsBigO.of_bound ( |C| + |C| ) _;
  filter_upwards [ Filter.eventually_ge_atTop 3 ] with N hN;
  rw [ Real.norm_of_nonneg ( Finset.sum_nonneg fun _ _ => ?_ ), Real.norm_of_nonneg ( by positivity ) ];
  · refine le_trans ( hC N ( by linarith ) ) ?_;
    cases abs_cases C <;> nlinarith [ show ( N : ℝ ) * Real.log N ≥ N by nlinarith [ show ( N : ℝ ) ≥ 3 by norm_cast, Real.le_log_iff_exp_le ( by positivity : 0 < ( N : ℝ ) ) |>.2 <| by exact Real.exp_one_lt_d9.le.trans <| by norm_num; linarith [ show ( N : ℝ ) ≥ 3 by norm_cast ] ], show ( N : ℝ ) ≥ 3 by norm_cast ];
  · unfold f_func; aesop;

/-
h(n) is bounded by C * 2^Omega(n) / sqrt(Omega(n)) for odd n >= 3.
-/
noncomputable def h_func (n : ℕ) : ℝ :=
  if Odd n then ((Om n).choose ((Om n) / 2) : ℝ) else 0

lemma h_func_bound_exists : ∃ C, ∀ n, Odd n → n ≥ 3 → h_func n ≤ C * (2 ^ (Om n) / Real.sqrt (Om n)) := by
  -- Apply Lemma~\ref{lem:central_binom_bound} with a pre-factored $2^k$.
  obtain ⟨C0, hC0⟩ := central_binom_bound;
  -- Let $k = \Omega(n)$. Then $h(n) = \binom{k}{k/2} \le C_0 2^k / \sqrt{k}$.
  use C0;
  intros n hn hn_ge_3
  have h_om : Om n ≥ 1 := by
    exact Finset.sum_pos ( fun p hp => Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp hp ) ) ⟨ Nat.minFac _, Nat.mem_primeFactors.mpr ⟨ Nat.minFac_prime ( by linarith ), Nat.minFac_dvd _, by linarith ⟩ ⟩
  generalize_proofs at *; (
  unfold h_func; aesop;)

/-
$h(n) \le 2^{\Omega(n)}$ for all $n$.
-/
lemma h_func_le_two_pow_Om (n : ℕ) : h_func n ≤ (2 : ℝ) ^ Om n := by
  by_cases hn : Odd n <;> simp_all +decide [ h_func ];
  · rw_mod_cast [ ← Nat.sum_range_choose ] ; exact Finset.single_le_sum ( fun x _ => Nat.zero_le _ ) ( Finset.mem_range.mpr <| Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.div_add_mod ( Om n ) 2, Nat.mod_lt ( Om n ) two_pos ] ) ;
  · exact if_neg ( by simpa using hn ) |> fun h => h.symm ▸ by norm_num;

/-
The sum of $h(n)$ for $\Omega(n) < L$ is bounded by $(N+1) 2^L$.
-/
lemma sum_h_lt_L_bound (N L : ℕ) :
    ∑ n ∈ (Finset.range (N + 1)).filter (λ n => Odd n ∧ Om n < L), h_func n ≤ (N + 1 : ℝ) * (2 : ℝ) ^ L := by
      refine' le_trans ( Finset.sum_le_sum fun i hi => show h_func i ≤ 2 ^ L from _ ) _;
      · refine' le_trans ( h_func_le_two_pow_Om i ) _;
        exact pow_le_pow_right₀ ( by norm_num ) ( by linarith [ Finset.mem_filter.mp hi ] );
      · norm_num [ Finset.sum_const ];
        exact_mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by norm_num )

/-
Let $C_h$ be the constant such that $h(n) \le C_h 2^{\Omega(n)} / \sqrt{\Omega(n)}$ for odd $n \ge 3$.
-/
noncomputable def C_h : ℝ := h_func_bound_exists.choose

lemma h_func_le_C_h (n : ℕ) (hn_odd : Odd n) (hn_ge_3 : n ≥ 3) :
    h_func n ≤ C_h * (2 ^ (Om n) / Real.sqrt (Om n)) :=
  h_func_bound_exists.choose_spec n hn_odd hn_ge_3

/-
The sum of $h(n)$ for $\Omega(n) \ge L$ is bounded by $\frac{C_h}{\sqrt{L}} \sum f(n)$.
-/
lemma sum_h_ge_L_bound (N L : ℕ) (hL : L ≥ 1) :
    ∑ n ∈ (Finset.range (N + 1)).filter (λ n => Odd n ∧ Om n ≥ L), h_func n ≤
    (C_h / Real.sqrt L) * ∑ n ∈ Finset.range (N + 1), f_func n := by
      -- By `h_func_le_C_h`, $h(n) \le C_h \frac{2^{\Omega(n)}}{\sqrt{\Omega(n)}} \le C_h \frac{2^{\Omega(n)}}{\sqrt{L}}$.
      have h_bound : ∀ n, Odd n → L ≤ Om n → (h_func n) ≤ (C_h / Real.sqrt L) * (f_func n) := by
        intros n hn_odd hn_L
        have h_le_C_h : h_func n ≤ C_h * (2 ^ (Om n) / Real.sqrt (Om n)) := by
          by_cases hn_ge_3 : n ≥ 3;
          · convert h_func_le_C_h n hn_odd hn_ge_3 using 1;
          · interval_cases n <;> simp_all +decide [ Om ];
        have h_bound : (2 ^ (Om n) / Real.sqrt (Om n)) ≤ (2 ^ (Om n) / Real.sqrt L) := by
          gcongr;
        have h_f_eq : f_func n = (2 : ℝ) ^ (Om n) := by
          unfold f_func; aesop;
        convert h_le_C_h.trans ( mul_le_mul_of_nonneg_left h_bound <| show 0 ≤ C_h by exact le_of_not_gt fun h => by have := h_func_le_C_h 3 ( by decide ) ( by decide ) ; norm_num [ h_func, Om ] at this ; nlinarith [ Real.sqrt_nonneg 1, Real.sq_sqrt zero_le_one ] ) using 1 ; rw [ h_f_eq ] ; ring;
      field_simp;
      rw [ Finset.sum_mul _ _ _ ];
      refine' le_trans ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right ( h_bound i ( Finset.mem_filter.mp hi |>.2.1 ) ( Finset.mem_filter.mp hi |>.2.2 ) ) ( Real.sqrt_nonneg _ ) ) _;
      norm_num [ div_mul_eq_mul_div, Finset.mul_sum _ _ _ ];
      field_simp;
      exact Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => mul_nonneg ( show 0 ≤ C_h by exact le_of_not_gt fun h => by have := h_func_le_C_h 3 ( by decide ) ( by decide ) ; norm_num [ h_func, Om ] at this ; linarith ) ( show 0 ≤ f_func _ by exact by unfold f_func; aesop )

/-
Define $L(N) = \lfloor \frac{1}{2} \log \log N \rfloor$.
-/
noncomputable def L_nat (N : ℕ) : ℕ := Nat.floor (Real.log (Real.log N) / 2)

/-
$L(N) \to \infty$ as $N \to \infty$.
-/
lemma L_nat_tendsto : Filter.Tendsto L_nat Filter.atTop Filter.atTop := by
  -- Since $\log(\log N)$ tends to infinity as $N$ tends to infinity, dividing by 2 and taking the floor will also tend to infinity.
  have h_log_log_inf : Filter.Tendsto (fun N => Real.log (Real.log N)) Filter.atTop Filter.atTop := by
    exact Real.tendsto_log_atTop.comp Real.tendsto_log_atTop;
  rw [ Filter.tendsto_atTop_atTop ] at *;
  exact fun b => by obtain ⟨ i, hi ⟩ := h_log_log_inf ( 2 * ( b + 1 ) ) ; exact ⟨ ⌈i⌉₊ + 1, fun a ha => Nat.le_floor <| by linarith [ hi a <| Nat.le_of_ceil_le <| by linarith ] ⟩ ;

/-
Eventually $L(N) \ge 1$.
-/
lemma L_nat_ge_one : ∀ᶠ N in Filter.atTop, 1 ≤ L_nat N := by
  -- Since $L_nat N$ tends to infinity as $N$ tends to infinity, there exists some $N₀$ such that for all $N \geq N₀$, $L_nat N \geq 1$.
  have hL_nat_inf : Filter.Tendsto L_nat Filter.atTop Filter.atTop := by
    convert L_nat_tendsto;
  exact hL_nat_inf.eventually_ge_atTop 1

/-
$(N+1) 2^{L(N)} = o(N \log N)$.
-/
lemma part1_bound_asymptotics : (fun (N : ℕ) => (N + 1 : ℝ) * (2 : ℝ) ^ (L_nat N)) =o[Filter.atTop] (fun (N : ℕ) => (N : ℝ) * Real.log N) := by
  -- Using the fact that $(N+1) * 2^{L(N)} \leq (N+1) * (\log N)^{\frac{\log 2}{2}}$ and $\frac{\log 2}{2} < 1$, we can show that $(N+1) * (\log N)^{\frac{\log 2}{2}} = o(N \log N)$.
  have h_exp : (fun N : ℕ => (N + 1 : ℝ) * (Real.log N) ^ (Real.log 2 / 2)) =o[Filter.atTop] (fun N : ℕ => (N : ℝ) * Real.log N) := by
    -- We can factor out $N$ and use the fact that $(\log N)^{\frac{\log 2}{2}} / \log N$ tends to $0$ as $N$ tends to infinity.
    have h_factor : Filter.Tendsto (fun N : ℕ => (1 + 1 / (N : ℝ)) * (Real.log N) ^ (Real.log 2 / 2 - 1)) Filter.atTop (nhds 0) := by
      simpa using Filter.Tendsto.mul ( tendsto_const_nhds.add ( tendsto_inverse_atTop_nhds_zero_nat ) ) ( tendsto_rpow_neg_atTop ( show 0 < - ( Real.log 2 / 2 - 1 ) by linarith [ Real.log_lt_sub_one_of_pos zero_lt_two ( by norm_num ) ] ) |> Filter.Tendsto.comp <| Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop );
    rw [ Asymptotics.isLittleO_iff_tendsto' ];
    · refine h_factor.congr' ?_;
      filter_upwards [ Filter.eventually_gt_atTop 1 ] with N hN;
      rw [ Real.rpow_sub_one ( ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hN ) ] ; ring_nf;
      simpa [ show N ≠ 0 by linarith ] using by ring;
    · filter_upwards [ Filter.eventually_gt_atTop 1 ] with N hN using by intro h; exact absurd h <| ne_of_gt <| mul_pos ( Nat.cast_pos.mpr <| pos_of_gt hN ) <| Real.log_pos <| Nat.one_lt_cast.mpr hN;
  -- Using the fact that $2^{L(N)} \leq (\log N)^{\frac{\log 2}{2}}$, we can bound the expression.
  have h_bound : ∀ N : ℕ, N ≥ 3 → (2 : ℝ) ^ L_nat N ≤ (Real.log N) ^ (Real.log 2 / 2) := by
    intro N hN
    have h_log : L_nat N ≤ Real.log (Real.log N) / 2 := by
      exact Nat.floor_le ( div_nonneg ( Real.log_nonneg ( Real.le_log_iff_exp_le ( by positivity ) |>.2 ( by exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( N : ℝ ) ≥ 3 by norm_cast ] ) ) ) ) zero_le_two );
    rw [ Real.le_rpow_iff_log_le ] <;> norm_num;
    · nlinarith [ Real.log_pos one_lt_two ];
    · exact Real.log_pos <| by norm_cast; linarith;
  rw [ Asymptotics.isLittleO_iff_tendsto' ] at * <;> norm_num at *;
  · refine' squeeze_zero_norm' _ h_exp;
    filter_upwards [ Filter.eventually_ge_atTop 3 ] with N hN using by rw [ Real.norm_of_nonneg ( by positivity ) ] ; exact div_le_div_of_nonneg_right ( mul_le_mul_of_nonneg_left ( h_bound N hN ) ( by positivity ) ) ( by positivity ) ;
  · exact ⟨ 3, by intros; norm_cast at *; aesop ⟩;
  · exact ⟨ 3, by rintro N hN ( rfl | rfl | h ) <;> norm_cast at * ⟩

/-
$\frac{C_h}{\sqrt{L(N)}} \sum f(n) = o(N \log N)$.
-/
lemma part2_bound_asymptotics :
    (fun N => (C_h / Real.sqrt (L_nat N)) * ∑ n ∈ Finset.range (N + 1), f_func n) =o[Filter.atTop] (fun N => (N : ℝ) * Real.log N) := by
      -- We know that $L(N) \to \infty$ as $N \to \infty$.
      have h_L_nat_tendsto : Filter.Tendsto L_nat Filter.atTop Filter.atTop := by
        exact L_nat_tendsto;
      -- We know that $\sum_{n \leq N} f(n) = O(N \log N)$ by `sum_2Omega_odd`.
      have h_sum_f_O : (fun N => ∑ n ∈ Finset.range (N + 1), f_func n) =O[Filter.atTop] (fun N => (N : ℝ) * Real.log N) := by
        convert sum_2Omega_odd using 1;
      -- We know that $C_h / \sqrt{L(N)} \to 0$ as $N \to \infty$.
      have h_C_h_div_sqrt_L_nat_zero : Filter.Tendsto (fun N => C_h / Real.sqrt (L_nat N)) Filter.atTop (nhds 0) := by
        exact tendsto_const_nhds.div_atTop ( by simpa only [ Real.sqrt_eq_rpow ] using tendsto_rpow_atTop ( by norm_num ) |> Filter.Tendsto.comp <| tendsto_natCast_atTop_atTop.comp h_L_nat_tendsto );
      rw [ Asymptotics.isLittleO_iff_tendsto' ];
      · rw [ Asymptotics.isBigO_iff' ] at h_sum_f_O;
        obtain ⟨ c, hc₀, hc ⟩ := h_sum_f_O;
        refine' squeeze_zero_norm' _ _;
        use fun N => |C_h / Real.sqrt ( L_nat N )| * c;
        · filter_upwards [ hc, Filter.eventually_gt_atTop 1 ] with N hN hN' ; simp_all +decide [ abs_div ];
          rw [ div_le_iff₀ ( mul_pos ( by positivity ) ( abs_pos.mpr ( ne_of_gt ( Real.log_pos ( Nat.one_lt_cast.mpr hN' ) ) ) ) ) ] ; nlinarith [ show 0 ≤ |C_h| / |Real.sqrt ( L_nat N )| by positivity ];
        · simpa using Filter.Tendsto.mul ( h_C_h_div_sqrt_L_nat_zero.abs ) tendsto_const_nhds;
      · filter_upwards [ Filter.eventually_gt_atTop 1 ] with N hN h using by rw [ show N = 0 by exact_mod_cast absurd h ( by exact ne_of_gt ( mul_pos ( Nat.cast_pos.mpr <| pos_of_gt hN ) <| Real.log_pos <| Nat.one_lt_cast.mpr hN ) ) ] ; norm_num;;

/-
The sum of $h(n)$ is $o(N \log N)$.
-/
lemma sum_central_binom_odd : (fun (N : ℕ) => ∑ n ∈ Finset.range (N + 1), h_func n) =o[Filter.atTop] (fun (N : ℕ) => (N : ℝ) * Real.log N) := by
  have h_split_sum : ∀ N : ℕ, (∑ n ∈ Finset.range (N + 1), h_func n) ≤ (∑ n ∈ (Finset.range (N + 1)).filter (λ n => Odd n ∧ Om n < L_nat N), h_func n) + (∑ n ∈ (Finset.range (N + 1)).filter (λ n => Odd n ∧ Om n ≥ L_nat N), h_func n) := by
    intro N
    have h_sum_split : ∑ n ∈ Finset.range (N + 1), h_func n ≤ ∑ n ∈ Finset.filter (fun n => Odd n) (Finset.range (N + 1)), h_func n := by
      rw [ Finset.sum_filter ];
      exact Finset.sum_le_sum fun x hx => by unfold h_func; aesop;
    have h_sum_split' : ∑ n ∈ Finset.filter (fun n => Odd n) (Finset.range (N + 1)), h_func n = ∑ n ∈ Finset.filter (fun n => Odd n ∧ Om n < L_nat N) (Finset.range (N + 1)), h_func n + ∑ n ∈ Finset.filter (fun n => Odd n ∧ Om n ≥ L_nat N) (Finset.range (N + 1)), h_func n := by
      rw [ ← Finset.sum_union ];
      · rcongr n ; by_cases hn : L_nat N ≤ Om n <;> aesop;
      · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
    linarith [h_sum_split, h_sum_split'];
  have h_sum_lt : (fun N : ℕ => (N + 1 : ℝ) * (2 : ℝ) ^ (L_nat N)) =o[Filter.atTop] (fun N : ℕ => (N : ℝ) * Real.log N) := by
    exact part1_bound_asymptotics

  have h_sum_ge : (fun N : ℕ => (C_h / Real.sqrt (L_nat N)) * ∑ n ∈ Finset.range (N + 1), f_func n) =o[Filter.atTop] (fun N : ℕ => (N : ℝ) * Real.log N) := by
    convert part2_bound_asymptotics using 1;
  have h_sum_bound : ∀ᶠ N in Filter.atTop, (∑ n ∈ Finset.range (N + 1), h_func n) ≤ (N + 1 : ℝ) * (2 : ℝ) ^ (L_nat N) + (C_h / Real.sqrt (L_nat N)) * ∑ n ∈ Finset.range (N + 1), f_func n := by
    filter_upwards [ Filter.eventually_ge_atTop 3, L_nat_ge_one ] with N hN₁ hN₂ using le_trans ( h_split_sum N ) ( add_le_add ( sum_h_lt_L_bound N ( L_nat N ) ) ( sum_h_ge_L_bound N ( L_nat N ) hN₂ ) ) |> le_trans <| by norm_num [ mul_assoc, mul_comm, mul_left_comm ] ;
  rw [ Asymptotics.isLittleO_iff_tendsto' ] at * <;> norm_num at *;
  · refine' squeeze_zero_norm' _ ( by simpa using h_sum_lt.add h_sum_ge );
    field_simp;
    filter_upwards [ Filter.eventually_ge_atTop h_sum_bound.choose, Filter.eventually_gt_atTop 1 ] with n hn hn' using by rw [ Real.norm_of_nonneg ( div_nonneg ( Finset.sum_nonneg fun _ _ => by unfold h_func; positivity ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( Real.log_nonneg ( Nat.one_le_cast.mpr hn'.le ) ) ) ) ] ; exact div_le_div_of_nonneg_right ( by simpa only [ div_mul_eq_mul_div ] using h_sum_bound.choose_spec n hn ) ( mul_nonneg ( Nat.cast_nonneg _ ) ( Real.log_nonneg ( Nat.one_le_cast.mpr hn'.le ) ) ) ;
  · exact ⟨ 2, by intros; norm_cast at *; aesop ⟩;
  · exact ⟨ 2, by intros; norm_cast at *; aesop ⟩;
  · exact ⟨ 2, by rintro N hN ( rfl | rfl | h ) <;> norm_cast at * ⟩

/-
There exists a constant $C_K$ such that for all $n$, the size of any union-free family is at most $C_K \binom{n}{\lfloor n/2 \rfloor}$.
-/
lemma kleitman_uniform : ∃ C_K : ℝ, C_K > 0 ∧ ∀ n, (MaxUnionFree n : ℝ) ≤ C_K * (n.choose (n / 2) : ℝ) := by
  -- By `erdos_447`, `MaxUnionFree n ~ binom n (n/2)`.
  have h_ratio : Filter.Tendsto (fun n : ℕ => (MaxUnionFree n : ℝ) / (n.choose (n / 2) : ℝ)) Filter.atTop (nhds 1) := by
    have := @erdos_447;
    rw [ Asymptotics.IsEquivalent ] at this;
    rw [ Asymptotics.isLittleO_iff_tendsto' ] at this <;> norm_num at *;
    · simpa using this.add_const 1 |> Filter.Tendsto.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with x hx using by rw [ sub_div, div_self <| Nat.cast_ne_zero.mpr <| Nat.ne_of_gt <| Nat.choose_pos <| Nat.div_le_self _ _ ] ; ring );
    · exact ⟨ 1, fun n hn hn' => absurd hn' <| ne_of_gt <| Nat.choose_pos <| Nat.div_le_self _ _ ⟩;
  -- A convergent sequence is bounded away from zero.
  obtain ⟨C_K, hC_K⟩ : ∃ C_K > 0, ∀ᶠ n in Filter.atTop, (MaxUnionFree n : ℝ) / (n.choose (n / 2)) ≤ C_K := by
    exact ⟨ 2, by norm_num, h_ratio.eventually ( ge_mem_nhds <| by norm_num ) ⟩;
  -- By combining the results for large and small n, we can conclude the existence of such a C_K.
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, (MaxUnionFree n : ℝ) / (n.choose (n / 2)) ≤ C_K := by
    exact Filter.eventually_atTop.mp hC_K.2;
  -- Let $C_K'$ be the maximum of $C_K$ and the maximum of $(MaxUnionFree n : ℝ) / (n.choose (n / 2))$ for $n < N$.
  obtain ⟨C_K', hC_K'⟩ : ∃ C_K' > 0, ∀ n < N, (MaxUnionFree n : ℝ) / (n.choose (n / 2)) ≤ C_K' := by
    have h_finite : Set.Finite (Set.image (fun n => (MaxUnionFree n : ℝ) / (n.choose (n / 2))) (Set.Iio N)) := by
      exact Set.Finite.image _ <| Set.finite_Iio N;
    exact ⟨ Max.max ( h_finite.bddAbove.choose + 1 ) 1, by positivity, fun n hn => le_trans ( h_finite.bddAbove.choose_spec <| Set.mem_image_of_mem _ hn ) <| le_max_of_le_left <| by linarith ⟩;
  use Max.max C_K C_K';
  exact ⟨ lt_max_of_lt_left hC_K.1, fun n => if hn : n < N then by have := hC_K'.2 n hn; rw [ div_le_iff₀ ( Nat.cast_pos.mpr <| Nat.choose_pos <| Nat.div_le_self _ _ ) ] at this; nlinarith [ le_max_right C_K C_K' ] else by have := hN n ( le_of_not_gt hn ) ; rw [ div_le_iff₀ ( Nat.cast_pos.mpr <| Nat.choose_pos <| Nat.div_le_self _ _ ) ] at this; nlinarith [ le_max_left C_K C_K' ] ⟩

/-
$I(N) = \sum_{a \in A, a \le N} |\{m \le N/a : m \text{ odd}\}|$.
-/
noncomputable def I_N (A : Set ℕ) (N : ℕ) : ℕ :=
  ∑ n ∈ (Finset.range (N + 1)).filter Odd, ((Nat.divisors n).filter (· ∈ A)).card

lemma I_N_equality (A : Set ℕ) (hA_odd : ∀ a ∈ A, Odd a) (N : ℕ) :
  I_N A N = ∑ a ∈ (Finset.range (N + 1)).filter (· ∈ A), ((Finset.range (N / a + 1)).filter Odd).card := by
    unfold I_N;
    simp +decide only [Finset.card_filter, Finset.sum_filter];
    -- By interchanging the order of summation, we can rewrite the left-hand side.
    have h_interchange : ∑ a ∈ Finset.range (N + 1), (if Odd a then ∑ i ∈ Nat.divisors a, if i ∈ A then 1 else 0 else 0) = ∑ i ∈ Finset.filter (fun i => i ∈ A) (Finset.range (N + 1)), ∑ a ∈ Finset.filter (fun a => Odd a) (Finset.range (N + 1)), (if i ∣ a then 1 else 0) := by
      simp +decide only [Finset.sum_filter, ← Finset.sum_product'];
      rw [ Finset.sum_product, Finset.sum_comm ];
      refine' Finset.sum_congr rfl fun y hy => _;
      split_ifs <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
      congr 1 with x ; simp +decide [ Nat.dvd_iff_mod_eq_zero ];
      exact ⟨ fun h => ⟨ ⟨ Nat.lt_succ_of_le ( Nat.le_trans ( Nat.le_of_dvd ( Nat.pos_of_ne_zero ( by aesop ) ) ( Nat.dvd_of_mod_eq_zero h.1.1 ) ) ( Nat.le_of_lt_succ hy ) ), h.2 ⟩, h.1.1 ⟩, fun h => ⟨ ⟨ h.2, by aesop ⟩, h.1.2 ⟩ ⟩;
    rw [ h_interchange, Finset.sum_filter ];
    refine' Finset.sum_congr rfl fun x hx => _;
    split_ifs <;> simp_all +decide
    refine' Finset.card_bij ( fun y hy => y / x ) _ _ _ <;> simp_all +decide
    · intro a ha₁ ha₂ ha₃; rw [ Nat.div_lt_iff_lt_mul <| Nat.pos_of_dvd_of_pos ha₃ <| Nat.pos_of_ne_zero <| by aesop ] ;
      exact ⟨ by nlinarith [ Nat.div_add_mod N x, Nat.mod_lt N ( Nat.pos_of_dvd_of_pos ha₃ ( Nat.pos_of_ne_zero ( by aesop ) ) ) ], by exact ha₂.of_dvd_nat ( Nat.div_dvd_of_dvd ha₃ ) ⟩;
    · exact fun b hb hb_odd => ⟨ x * b, ⟨ ⟨ by nlinarith [ Nat.div_mul_le_self N x ], by simp [ *, parity_simps ] ⟩, by simp +decide ⟩, by rw [ Nat.mul_div_cancel_left _ ( Nat.pos_of_ne_zero ( by specialize hA_odd x ‹_›; aesop ) ) ] ⟩

/-
$I(N) \ge \sum_{a \in A, a \le N} (\frac{N}{2a} - 1)$.
-/
lemma I_N_lower_bound (A : Set ℕ) (hA_odd : ∀ a ∈ A, Odd a) (N : ℕ) :
  (I_N A N : ℝ) ≥ ∑ a ∈ (Finset.range (N + 1)).filter (· ∈ A), ((N / a : ℝ) / 2 - 1) := by
    -- By definition of $I_N$, we have $I_N(A, N) = \sum_{a \in A, a \le N} |\{m \le N/a : m \text{ odd}\}|$.
    have h_I_N_def : (I_N A N : ℝ) = ∑ a ∈ (Finset.range (N + 1)).filter (· ∈ A), ((Finset.range (N / a + 1)).filter Odd).card := by
      convert congr_arg _ ( I_N_equality A hA_odd N ) using 1;
    rw [h_I_N_def];
    push_cast [ Finset.sum_div _ _ _ ];
    gcongr;
    field_simp;
    rename_i a ha;
    refine' le_trans _ ( mul_le_mul_of_nonneg_left ( Nat.cast_le.mpr <| show Finset.card ( Finset.filter Odd ( Finset.range ( N / a + 1 ) ) ) ≥ N / a / 2 from _ ) zero_le_two );
    · rw [ div_sub', div_le_iff₀ ] <;> norm_cast <;> norm_num at *;
      · norm_cast; nlinarith [ Nat.div_add_mod N a, Nat.mod_lt N ( Nat.pos_of_ne_zero ( by specialize hA_odd a ha.2; aesop : a ≠ 0 ) ), Nat.div_add_mod ( N / a ) 2, Nat.mod_lt ( N / a ) two_pos ] ;
      · exact Nat.pos_of_ne_zero fun h => by simpa [ h ] using hA_odd a ha.2;
      · exact Nat.ne_of_gt ( Nat.pos_of_ne_zero fun h => by simpa [ h ] using hA_odd a ha.2 );
    · refine' le_trans _ ( Finset.card_mono <| show Finset.image ( fun x => 2 * x + 1 ) ( Finset.range ( N / a / 2 ) ) ⊆ Finset.filter Odd ( Finset.range ( N / a + 1 ) ) from _ );
      · rw [ Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
      · grind

/-
Let $C_K$ be the constant from Kleitman's uniform bound.
-/
noncomputable def C_K_val : ℝ := kleitman_uniform.choose

lemma C_K_pos : C_K_val > 0 := kleitman_uniform.choose_spec.1

lemma MaxUnionFree_le_C_K (n : ℕ) : (MaxUnionFree n : ℝ) ≤ C_K_val * (n.choose (n / 2) : ℝ) := kleitman_uniform.choose_spec.2 n

set_option maxHeartbeats 1000000 in
/-
If $A$ is lcm-triple free, then $|A \cap \Div(n)| \le \text{MaxUnionFree}(\Omega(n))$.
-/
lemma card_A_cap_Div_le_MaxUnionFree (A : Set ℕ)
  (h_lcm_free : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → b ≠ c → a ≠ c → Nat.lcm a b ≠ c)
  (n : ℕ) (hn : n ≠ 0) :
  ((Nat.divisors n).filter (· ∈ A)).card ≤ MaxUnionFree (Om n) := by
    -- Since $A \cap \Div(n)$ is lcm-triple-free, the family of subsets $\{\Phi_n(d) \mid d \in A \cap \Div(n)\}$ is union-free.
    have h_union_free : UnionFree (Finset.image (fun d => Phi_n n d) (Nat.divisors n ∩ Finset.filter (· ∈ A) (Finset.range (n + 1)))) := by
      convert lcmfree_to_unionfree A h_lcm_free n hn using 1;
      ext; simp [Finset.mem_image];
      exact ⟨ fun ⟨ a, ha, ha' ⟩ => ⟨ a, ⟨ ⟨ ha.1.1, ha.1.2 ⟩, ha.2.2 ⟩, ha' ⟩, fun ⟨ a, ha, ha' ⟩ => ⟨ a, ⟨ ⟨ ha.1.1, ha.1.2 ⟩, Nat.lt_succ_of_le ( Nat.le_of_dvd ( Nat.pos_of_ne_zero hn ) ha.1.1 ), ha.2 ⟩, ha' ⟩ ⟩;
    -- Since $\Phi_n$ is injective, the cardinality of the image of $A \cap \Div(n)$ under $\Phi_n$ is equal to the cardinality of $A \cap \Div(n)$.
    have h_card_eq : (Finset.image (fun d => Phi_n n d) (Nat.divisors n ∩ Finset.filter (· ∈ A) (Finset.range (n + 1)))).card = ((Nat.divisors n).filter (· ∈ A)).card := by
      have h_inj : ∀ d1 d2, d1 ∈ Nat.divisors n → d2 ∈ Nat.divisors n → Phi_n n d1 = Phi_n n d2 → d1 = d2 := by
        intros d1 d2 hd1 hd2 h_eq
        have := divisors_to_subsets n hn
        aesop;
      rw [ Finset.card_image_of_injOn fun x hx y hy hxy => h_inj x y ( by aesop ) ( by aesop ) hxy ];
      congr 1 with x ; simp +decide [ Nat.lt_succ_iff ];
      exact fun hx _ hx' => Nat.le_of_dvd ( Nat.pos_of_ne_zero hn ) hx;
    refine' h_card_eq ▸ _;
    -- Since the image of the divisors under Phi_n is a union-free family, its cardinality is bounded by the maximum size of a union-free family on a set of size Om n.
    have h_card_le_max : ∀ (F : Finset (Finset ((p : ℕ) × ℕ))), F ⊆ Finset.powerset (Un n) → UnionFree F → F.card ≤ MaxUnionFree (Om n) := by
      intros F hF_sub hF_union_free
      have h_card_le_max : F.card ≤ MaxUnionFree (Om n) := by
        have h_card_le_max : ∃ (f : Fin (Om n) → ((p : ℕ) × ℕ)), Finset.image f Finset.univ = Un n := by
          have h_card_le_max : Finset.card (Un n) = Om n := by
            unfold Un Om; aesop;
          have h_card_le_max : Nonempty (Fin (Om n) ≃ Un n) := by
            exact ⟨ Fintype.equivOfCardEq <| by simp +decide [ h_card_le_max ] ⟩;
          obtain ⟨ f ⟩ := h_card_le_max;
          use fun i => f i |>.1;
          ext x; simp [Finset.mem_image];
          exact ⟨ fun ⟨ a, ha ⟩ => ha ▸ Subtype.mem _, fun hx => ⟨ f.symm ⟨ x, hx ⟩, by simp +decide ⟩ ⟩
        obtain ⟨f, hf⟩ := h_card_le_max;
        have h_card_le_max : ∃ (F' : Finset (Finset (Fin (Om n)))), F'.card = F.card ∧ UnionFree F' := by
          use Finset.image (fun s => Finset.filter (fun i => f i ∈ s) Finset.univ) F;
          rw [ Finset.card_image_of_injOn ];
          · simp_all +decide [ Finset.subset_iff, UnionFree ];
            intro A hA B hB C hC hAB hBC hAC h_union; specialize hF_union_free A hA B hB C hC; simp_all +decide [ Finset.ext_iff ] ;
            grind;
          · intro s hs t ht h_eq; simp_all +decide [ Finset.ext_iff ] ;
            grind;
        obtain ⟨F', hF'_card, hF'_union_free⟩ := h_card_le_max;
        exact (by
        exact hF'_card ▸ Finset.le_sup ( f := Finset.card ) ( Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hF'_union_free ⟩ ) |> le_trans <| by unfold MaxUnionFree; aesop;);
      exact h_card_le_max;
    apply h_card_le_max _ ?_ h_union_free;
    exact Finset.image_subset_iff.mpr fun x hx => Finset.mem_powerset.mpr <| divisors_to_subsets n hn |>.1 x <| Nat.dvd_of_mem_divisors <| Finset.mem_filter.mp hx |>.1 |> fun h => by aesop;

/-
If $A$ is lcm-triple free, then $I(N) \le C_K \sum_{n \le N} h(n)$.
-/
lemma I_N_upper_bound_explicit (A : Set ℕ)
  (h_lcm_free : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → b ≠ c → a ≠ c → Nat.lcm a b ≠ c)
  (N : ℕ) :
  (I_N A N : ℝ) ≤ C_K_val * ∑ n ∈ Finset.range (N + 1), h_func n := by
    -- By definition of $I_N$, we have $I_N(A, N) = \sum_{n \le N, n \text{ odd}} |\{m \le N/n : m \text{ odd}\}|$.
    have h_I_N_def : I_N A N = ∑ n ∈ (Finset.range (N + 1)).filter Odd, ((Nat.divisors n).filter (· ∈ A)).card := by
      rfl;
    -- By definition of $h_func$, we have $|A \cap \Div(n)| \le C_K h(n)$ for all odd $n$.
    have h_card_le_C_K_h : ∀ n ∈ (Finset.range (N + 1)).filter Odd, ((Nat.divisors n).filter (· ∈ A)).card ≤ C_K_val * h_func n := by
      intros n hn_odd
      have h_card_le_C_K_h : ((Nat.divisors n).filter (· ∈ A)).card ≤ C_K_val * (Nat.choose (Om n) ((Om n) / 2) : ℝ) := by
        have h_card_le_C_K_h : ((Nat.divisors n).filter (· ∈ A)).card ≤ MaxUnionFree (Om n) := by
          by_cases hn : n = 0 <;> simp_all +decide [ card_A_cap_Div_le_MaxUnionFree ];
        exact le_trans ( Nat.cast_le.mpr h_card_le_C_K_h ) ( MaxUnionFree_le_C_K _ );
      unfold h_func; aesop;
    rw [ h_I_N_def, Finset.mul_sum _ _ _ ] ; exact le_trans ( mod_cast Finset.sum_le_sum fun n hn => h_card_le_C_K_h n <| by aesop ) ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => mul_nonneg ( le_of_lt <| C_K_pos ) <| by unfold h_func; positivity ) ;

/-
If $A$ is lcm-triple free, then $I(N) = o(N \log N)$.
-/
lemma I_N_upper_bound_asymptotic (A : Set ℕ)
  (h_lcm_free : ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → b ≠ c → a ≠ c → Nat.lcm a b ≠ c) :
  (fun N => (I_N A N : ℝ)) =o[Filter.atTop] (fun N => (N : ℝ) * Real.log N) := by
    -- By `I_N_upper_bound_explicit`, $I(N) \le C_K \sum_{n \le N} h(n)$.
    have h_upper_bound : ∀ N : ℕ, (I_N A N : ℝ) ≤ C_K_val * ∑ n ∈ Finset.range (N + 1), h_func n := by
      exact fun N => I_N_upper_bound_explicit A h_lcm_free N;
    have h_sum_h_asymptotic : (fun N => C_K_val * ∑ n ∈ Finset.range (N + 1), h_func n) =o[Filter.atTop] (fun N => (N : ℝ) * Real.log N) := by
      have h_sum_h_asymptotic : (fun N => ∑ n ∈ Finset.range (N + 1), h_func n) =o[Filter.atTop] (fun N => (N : ℝ) * Real.log N) := by
        convert sum_central_binom_odd using 1;
      exact h_sum_h_asymptotic.const_mul_left _;
    rw [ Asymptotics.isLittleO_iff ] at *;
    intro c hc; filter_upwards [ h_sum_h_asymptotic hc ] with N hN; rw [ Real.norm_of_nonneg ( Nat.cast_nonneg _ ) ] ; exact le_trans ( h_upper_bound N ) ( le_trans ( le_abs_self _ ) hN ) ;

/-
$H_A(N) = \sum_{a \in A, a \le N} 1/a$.
-/
noncomputable def log_density_sum (A : Set ℕ) (N : ℕ) : ℝ :=
  ∑ a ∈ (Finset.range (N + 1)).filter (· ∈ A), (1 : ℝ) / a

/-
Definitions of upper and lower logarithmic density.
-/
noncomputable def upper_log_density (A : Set ℕ) : ℝ :=
  (Filter.atTop).limsup (fun N => log_density_sum A N / Real.log N)

noncomputable def lower_log_density (A : Set ℕ) : ℝ :=
  (Filter.atTop).liminf (fun N => log_density_sum A N / Real.log N)

/-
If a set has positive lower density, it has positive lower logarithmic density.
-/
lemma lower_log_density_pos (A : Set ℕ) (hA : lowerDensity A > 0) :
    lower_log_density A > 0 := by
      -- By `harmonic_lower_bound`, there exists $c > 0$ such that for large $N$, $\sum_{a \in A, a \le N} 1/a \ge c \log N$.
      obtain ⟨c, hc_pos, hc⟩ : ∃ c > 0, ∀ᶠ N in Filter.atTop, log_density_sum A N ≥ c * Real.log N := by
        obtain ⟨N0, c, hc_pos, hc⟩ : ∃ N0 c, c > 0 ∧ ∀ N ≥ N0, ∑ a ∈ (Finset.Icc 1 N).filter (· ∈ A), (1 : ℝ) / a ≥ c * Real.log N := by
          convert harmonic_lower_bound A hA using 1;
        refine' ⟨ c, hc_pos, Filter.eventually_atTop.mpr ⟨ N0 + 1, fun N hN => le_trans ( hc N ( by linarith ) ) _ ⟩ ⟩;
        refine' Finset.sum_le_sum_of_subset_of_nonneg _ _;
        · exact fun x hx => Finset.mem_filter.mpr ⟨ Finset.mem_range.mpr ( by linarith [ Finset.mem_Icc.mp ( Finset.mem_filter.mp hx |>.1 ) ] ), Finset.mem_filter.mp hx |>.2 ⟩;
        · exact fun _ _ _ => by positivity;
      refine' lt_of_lt_of_le ( half_pos hc_pos ) _;
      refine' le_csSup _ _ <;> norm_num;
      · use 1 + ∑ a ∈ Finset.range ( Nat.succ 1 ), ( 1 : ℝ ) / a + 1;
        rintro x ⟨ N, hN ⟩ ; specialize hN ( N + 2 ) ( by linarith ) ; norm_num [ Finset.sum_range_succ ] at *;
        refine le_trans hN ?_;
        refine' div_le_of_le_mul₀ _ _ _ <;> norm_num;
        · exact Real.log_nonneg ( by linarith );
        · refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.filter_subset _ _ ) fun _ _ _ => by positivity ) _;
          induction' N with N ih <;> norm_num [ Finset.sum_range_succ ] at *;
          · have := Real.log_two_gt_d9 ; norm_num at * ; linarith;
          · refine' le_trans ( add_le_add_right ( show ∑ x ∈ Finset.range N, ( x : ℝ ) ⁻¹ + ( N : ℝ ) ⁻¹ + ( N + 1 : ℝ ) ⁻¹ + ( N + 2 : ℝ ) ⁻¹ ≤ 3 * Real.log ( N + 2 ) from _ ) _ ) _;
            · refine' Nat.recOn N _ _ <;> norm_num [ Finset.sum_range_succ ] at *;
              · have := Real.log_two_gt_d9 ; norm_num at * ; linarith;
              · intro n hn; rw [ show ( n : ℝ ) + 1 + 2 = ( n + 2 ) * ( 1 + 1 / ( n + 2 ) ) by rw [ mul_add, mul_div_cancel₀ _ ( by positivity ) ] ; ring ] ; rw [ Real.log_mul ( by positivity ) ( by positivity ) ] ; ring_nf at *;
                refine' add_le_add hn _;
                rw [ inv_eq_one_div, div_le_iff₀ ] <;> nlinarith only [ Real.log_inv ( 1 + ( 2 + n : ℝ ) ⁻¹ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by positivity : 0 < ( 1 + ( 2 + n : ℝ ) ⁻¹ ) ) ), Real.log_le_sub_one_of_pos ( by positivity : 0 < ( 1 + ( 2 + n : ℝ ) ⁻¹ ) ), inv_pos.mpr ( by positivity : 0 < ( 1 + ( 2 + n : ℝ ) ⁻¹ ) ), mul_inv_cancel₀ ( by positivity : ( 1 + ( 2 + n : ℝ ) ⁻¹ ) ≠ 0 ), inv_pos.mpr ( by positivity : 0 < ( 2 + n : ℝ ) ), mul_inv_cancel₀ ( by positivity : ( 2 + n : ℝ ) ≠ 0 ) ];
            · rw [ show ( N + 1 + 2 : ℝ ) = ( N + 2 ) * ( 1 + 1 / ( N + 2 ) ) by rw [ mul_add, mul_div_cancel₀ _ ( by linarith ) ] ; ring, Real.log_mul ( by linarith ) ( by positivity ) ] ; ring_nf ; norm_num;
              nlinarith [ Real.log_inv ( 1 + ( 2 + N : ℝ ) ⁻¹ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by positivity : 0 < ( 1 + ( 2 + N : ℝ ) ⁻¹ ) ) ), inv_mul_cancel₀ ( by positivity : ( 1 + ( 2 + N : ℝ ) ⁻¹ ) ≠ 0 ), inv_pos.mpr ( by positivity : 0 < ( 2 + N : ℝ ) ), mul_inv_cancel₀ ( by positivity : ( 2 + N : ℝ ) ≠ 0 ), inv_pos.mpr ( by positivity : 0 < ( 3 + N : ℝ ) ), mul_inv_cancel₀ ( by positivity : ( 3 + N : ℝ ) ≠ 0 ) ];
      · exact Filter.eventually_atTop.mp ( hc.and ( Filter.eventually_gt_atTop 1 ) ) |> fun ⟨ N, hN ⟩ => ⟨ N + 2, fun n hn => by rw [ le_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr <| by linarith ) ] ; nlinarith [ hN n ( by linarith ), Real.log_nonneg <| show ( n : ℝ ) ≥ 1 by norm_cast; linarith ] ⟩

/-
The number of integers $n \in \{1, \dots, N\}$ such that $v_2(n) \ge T$ is at most $N/2^T$.
-/
lemma card_v2_ge_T (N T : ℕ) : ((Finset.Icc 1 N).filter (fun n => T ≤ v2 n)).card ≤ N / 2^T := by
  -- The set of numbers with $v_2(n) \geq T$ is exactly the set of multiples of $2^T$ in $\{1, \dots, N\}$.
  have h_mult : Finset.filter (fun n => T ≤ v2 n) (Finset.Icc 1 N) ⊆ Finset.image (fun m => 2^T * m) (Finset.Icc 1 (N / 2^T)) := by
    intro n hnaesop;
    -- Since $T \leq v2 n$, we have $2^T \mid n$.
    have h_div : 2 ^ T ∣ n := by
      exact dvd_trans ( pow_dvd_pow _ ( Finset.mem_filter.mp hnaesop |>.2 ) ) ( Nat.ordProj_dvd _ _ );
    exact Finset.mem_image.mpr ⟨ n / 2 ^ T, Finset.mem_Icc.mpr ⟨ Nat.div_pos ( Nat.le_of_dvd ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hnaesop |>.1 ) |>.1 ) h_div ) ( pow_pos ( by decide ) _ ), Nat.div_le_div_right ( Finset.mem_Icc.mp ( Finset.mem_filter.mp hnaesop |>.1 ) |>.2 ) ⟩, by rw [ Nat.mul_div_cancel' h_div ] ⟩;
  exact le_trans ( Finset.card_le_card h_mult ) ( Finset.card_image_le.trans ( by simp ) )

/-
If the counting function of A is at least the counting function of B minus C*N, then the lower density of A is at least the lower density of B minus C.
-/
lemma lowerDensity_diff_bound (A B : Set ℕ) (C : ℝ)
    (h : ∀ N ≥ 1, ((Finset.Icc 1 N).filter (· ∈ A)).card ≥ ((Finset.Icc 1 N).filter (· ∈ B)).card - C * N) :
    lowerDensity A ≥ lowerDensity B - C := by
      -- Then $\frac{|A \cap [1,N]|}{N} \ge \frac{|B \cap [1,N]|}{N} - C$.
      have h_ineq : ∀ N ≥ 1, ((Finset.Icc 1 N).filter (· ∈ A)).card / (N : ℝ) ≥ ((Finset.Icc 1 N).filter (· ∈ B)).card / (N : ℝ) - C := by
        intro N hN; rw [ ge_iff_le ] ; rw [ div_sub', div_le_div_iff_of_pos_right ] <;> first | positivity | linarith [ h N hN ] ;
      -- Taking liminf: $\underline{d}(A) \ge \underline{d}(B) - C$.
      have h_liminf : Filter.liminf (fun N => ((Finset.Icc 1 N).filter (· ∈ A)).card / (N : ℝ)) Filter.atTop ≥ Filter.liminf (fun N => ((Finset.Icc 1 N).filter (· ∈ B)).card / (N : ℝ)) Filter.atTop - C := by
        rw [ Filter.liminf_eq, Filter.liminf_eq ];
        refine' sub_le_iff_le_add.mpr ( csSup_le _ _ );
        · exact ⟨ 0, Filter.eventually_atTop.mpr ⟨ 1, fun N hN => by positivity ⟩ ⟩;
        · intro b hb;
          refine' le_trans _ ( add_le_add_right ( le_csSup _ <| show b - C ∈ _ from _ ) _ );
          · linarith;
          · exact ⟨ 1, fun x hx => by rcases Filter.eventually_atTop.mp hx with ⟨ N, hN ⟩ ; exact le_trans ( hN _ le_rfl ) ( div_le_one_of_le₀ ( mod_cast le_trans ( Finset.card_filter_le _ _ ) ( by norm_num ) ) ( by positivity ) ) ⟩;
          · filter_upwards [ hb, Filter.eventually_ge_atTop 1 ] with n hn hn' using by linarith [ h_ineq n hn' ] ;
      convert h_liminf using 1

/-
The lower density of the union of A_t for t < T is at least the lower density of A minus 1/2^T.
-/
lemma lowerDensity_union_At_ge (A : Set ℕ) (T : ℕ) :
    lowerDensity (⋃ t ∈ Finset.range T, At A t) ≥ lowerDensity A - (1 / 2 ^ T : ℝ) := by
      convert lowerDensity_diff_bound _ _ ( 1 / 2 ^ T ) _ using 1;
      intro N hN
      have h_card_diff : ((Finset.Icc 1 N).filter (· ∈ A)).card ≤ ((Finset.Icc 1 N).filter (· ∈ ⋃ t ∈ Finset.range T, At A t)).card + ((Finset.Icc 1 N).filter (fun n => T ≤ v2 n)).card := by
        have h_card_ge : ((Finset.Icc 1 N).filter (· ∈ A)).card ≤ ((Finset.Icc 1 N).filter (fun n => n ∈ A ∧ v2 n < T)).card + ((Finset.Icc 1 N).filter (fun n => n ∈ A ∧ T ≤ v2 n)).card := by
          rw [ ← Finset.card_union_of_disjoint ];
          · exact Finset.card_mono fun x hx => by by_cases h : v2 x < T <;> aesop;
          · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
        refine le_trans h_card_ge ?_;
        gcongr;
        · intro n hn; simp_all +decide [ At ] ;
        · exact fun x hx => hx.2;
      -- By definition of $At$, we know that $|(A \setminus S) \cap \{1,\dots,N\}| \le |\{n \le N \mid v_2(n) \ge T\}| \le N/2^T$.
      have h_card_diff_le : ((Finset.Icc 1 N).filter (fun n => T ≤ v2 n)).card ≤ N / 2 ^ T := by
        exact card_v2_ge_T N T;
      field_simp;
      rw [ sub_le_iff_le_add ] ; norm_cast ; nlinarith [ Nat.div_mul_le_self N ( 2 ^ T ), pow_pos ( zero_lt_two' ℕ ) T ] ;

/-
If A has positive lower density, there exists T such that the union of A_t for t < T has positive lower density.
-/
lemma exists_T_union_pos (A : Set ℕ) (hA : lowerDensity A > 0) :
    ∃ T, lowerDensity (⋃ t ∈ Finset.range T, At A t) > 0 := by
      obtain ⟨T, hT⟩ : ∃ T : ℕ, (1 / 2 ^ T : ℝ) < lowerDensity A := by
        simpa using exists_pow_lt_of_lt_one hA one_half_lt_one
      generalize_proofs at *; (exact ⟨ T, by
        have := lowerDensity_union_At_ge A T; norm_num at *; linarith; ⟩ )

set_option maxHeartbeats 1000000 in
/-
Upper logarithmic density is finitely subadditive.
-/
lemma upper_log_density_subadd {ι : Type*} (s : Finset ι) (f : ι → Set ℕ) :
    upper_log_density (⋃ i ∈ s, f i) ≤ ∑ i ∈ s, upper_log_density (f i) := by
      unfold upper_log_density;
      -- The logarithmic density sum is subadditive: $S_{\cup A_i}(N) \le \sum S_{A_i}(N)$.
      have h_subadd : ∀ N, log_density_sum (⋃ i ∈ s, f i) N ≤ ∑ i ∈ s, log_density_sum (f i) N := by
        intro N;
        induction s using Finset.induction <;> simp_all +decide [ log_density_sum ];
        refine' le_trans _ ( add_le_add_left ‹_› _ );
        rw [ ← Finset.sum_union_inter ];
        exact le_add_of_le_of_nonneg ( Finset.sum_le_sum_of_subset_of_nonneg ( fun x hx => by aesop ) fun _ _ _ => by positivity ) ( Finset.sum_nonneg fun _ _ => by positivity );
      by_cases h : ∀ i ∈ s, Filter.IsBoundedUnder ( · ≤ · ) Filter.atTop ( fun N => log_density_sum ( f i ) N / Real.log N ) <;> simp_all +decide [ Filter.limsup_eq];
      · -- Since the logarithmic density sum is subadditive, we can apply the fact that the limsup of a sum is less than or equal to the sum of the limsups.
        have h_limsup_subadd : ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, log_density_sum (⋃ i ∈ s, f i) N / Real.log N ≤ ∑ i ∈ s, (sInf {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → log_density_sum (f i) b / Real.log ↑b ≤ a} + ε / s.card) := by
          intro ε ε_pos
          have h_limsup_subadd : ∀ i ∈ s, ∃ N₀, ∀ N ≥ N₀, log_density_sum (f i) N / Real.log N ≤ sInf {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → log_density_sum (f i) b / Real.log ↑b ≤ a} + ε / s.card := by
            intro i hi;
            have := exists_lt_of_csInf_lt ( show { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → log_density_sum ( f i ) b / Real.log b ≤ a }.Nonempty from ?_ ) ( show sInf { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → log_density_sum ( f i ) b / Real.log b ≤ a } < sInf { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → log_density_sum ( f i ) b / Real.log b ≤ a } + ε / s.card from lt_add_of_pos_right _ ( div_pos ε_pos ( Nat.cast_pos.mpr ( Finset.card_pos.mpr ⟨ i, hi ⟩ ) ) ) );
            · rcases this with ⟨ a, ⟨ N₀, hN₀ ⟩, ha ⟩ ; exact ⟨ N₀, fun N hN => le_trans ( hN₀ N hN ) ha.le ⟩ ;
            · obtain ⟨ M, hM ⟩ := h i hi;
              exact ⟨ M, by rcases Filter.eventually_atTop.mp hM with ⟨ N, hN ⟩ ; exact ⟨ ⌈N⌉₊, fun n hn => hN n <| Nat.le_of_ceil_le hn ⟩ ⟩;
          choose! N₀ hN₀ using h_limsup_subadd;
          use Finset.sup s N₀ + 2;
          intro N hN
          have h_sum : log_density_sum (⋃ i ∈ s, f i) N / Real.log N ≤ ∑ i ∈ s, log_density_sum (f i) N / Real.log N := by
            rw [ ← Finset.sum_div _ _ _ ] ; gcongr ; aesop;
          exact h_sum.trans ( Finset.sum_le_sum fun i hi => hN₀ i hi N ( by linarith [ Finset.le_sup ( f := N₀ ) hi ] ) );
        refine' le_of_forall_pos_le_add fun ε εpos => _;
        rcases h_limsup_subadd ε εpos with ⟨ N₀, hN₀ ⟩ ; refine' csInf_le _ _;
        · exact ⟨ 0, by rintro x ⟨ N, hN ⟩ ; exact le_trans ( div_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ) ( Real.log_natCast_nonneg _ ) ) ( hN _ le_rfl ) ⟩;
        · use N₀; intro N hN; specialize hN₀ N hN; simp_all +decide [ Finset.sum_add_distrib ] ;
          by_cases hs : s = ∅ <;> simp_all +decide [ mul_div_cancel₀ ];
          exact le_trans hN₀ εpos.le;
      · rw [ Real.sInf_def ];
        rw [ Real.sSup_def ];
        split_ifs <;> simp_all +decide [ not_le, IsBoundedUnder, IsBounded ];
        · obtain ⟨ x, hx₁, hx₂ ⟩ := h;
          contrapose! hx₂;
          obtain ⟨ M, hM ⟩ := ‹ ( - { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → log_density_sum ( ⋃ i ∈ s, f i ) b / Real.log b ≤ a } ).Nonempty ∧ BddAbove ( - { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → log_density_sum ( ⋃ i ∈ s, f i ) b / Real.log b ≤ a } ) ›.1;
          obtain ⟨ N, hN ⟩ := hM;
          use -M, N + 1;
          intro n hn;
          refine' le_trans _ ( hN n ( by linarith ) );
          gcongr;
          refine' Finset.sum_le_sum_of_subset_of_nonneg _ _;
          · simp +contextual [ Finset.subset_iff ];
            exact fun i hi hi' => ⟨ x, hx₁, hi' ⟩;
          · exact fun _ _ _ => by positivity;
        · exact Finset.sum_nonneg fun i _ => by apply_rules [ Real.sInf_nonneg ] ; rintro x ⟨ N, hN ⟩ ; exact le_trans ( div_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ) ( Real.log_natCast_nonneg _ ) ) ( hN _ le_rfl ) ;

theorem helper2 (a b : ℕ) : Finset.Ico a b.succ = Finset.Icc a b := by
  simp_all only [Nat.succ_eq_add_one]
  rfl

/-
Relation between logarithmic density sums of A_t and B_t.
-/
lemma log_density_sum_Bt_relation (A : Set ℕ) (t N : ℕ) :
    log_density_sum (At A t) N = (1 / 2 ^ t : ℝ) * log_density_sum (Bt A t) (N / 2 ^ t) := by
      -- By definition of $At$ and $Bt$, we can rewrite the left-hand side of the equation.
      have h_rewrite : log_density_sum (At A t) N = ∑ a ∈ (Finset.Icc 1 N).filter (fun a => v2 a = t ∧ a ∈ A), (1 : ℝ) / a := by
        unfold log_density_sum At;
        rw [ Finset.range_eq_Ico, helper2 ];
        simp +decide [ and_comm, Finset.sum_filter ];
        rw [ Finset.Icc_eq_cons_Ioc, Finset.sum_cons ] <;> aesop;
      -- Let's rewrite the sum over $B_t$ in terms of the sum over $A_t$.
      have h_rewrite_Bt : ∑ b ∈ (Finset.Icc 1 (N / 2^t)).filter (fun b => Odd b ∧ ∃ a ∈ A, v2 a = t ∧ a = 2^t * b), (1 : ℝ) / b = ∑ a ∈ (Finset.Icc 1 N).filter (fun a => v2 a = t ∧ a ∈ A), (2^t : ℝ) / a := by
        apply Finset.sum_bij (fun b hb => 2^t * b);
        · simp +zetaDelta at *;
          exact fun a ha₁ ha₂ ha₃ ha₄ ha₅ => ⟨ ⟨ Nat.mul_pos ( pow_pos ( by decide ) _ ) ha₁, by nlinarith [ Nat.div_mul_le_self N ( 2 ^ t ), pow_pos ( by decide : 0 < 2 ) t ] ⟩, ha₅, ha₄ ⟩;
        · aesop;
        · intro b hb
          obtain ⟨hb_range, hb_prop⟩ := Finset.mem_filter.mp hb
          obtain ⟨hb_v2, hb_A⟩ := hb_prop
          have hb_div : b % 2^t = 0 := by
            exact Nat.mod_eq_zero_of_dvd <| hb_v2 ▸ Nat.ordProj_dvd _ _
          have hb_odd : Odd (b / 2^t) := by
            have hb_odd : ¬(2 ∣ b / 2^t) := by
              rw [ Nat.dvd_div_iff_mul_dvd ];
              · rw [ ← hb_v2 ] ; exact Nat.pow_succ_factorization_not_dvd ( by linarith [ Finset.mem_Icc.mp hb_range ] ) Nat.prime_two;
              · exact Nat.dvd_of_mod_eq_zero hb_div;
            simpa [ ← even_iff_two_dvd ] using hb_odd
          have hb_lt : b / 2^t ≤ N / 2^t := by
            exact Nat.div_le_div_right ( Finset.mem_Icc.mp hb_range |>.2 )
          use b / 2^t
          simp [hb_odd, hb_lt];
          exact ⟨ ⟨ Nat.div_pos ( Nat.le_of_dvd ( Finset.mem_Icc.mp hb_range |>.1 ) ( Nat.dvd_of_mod_eq_zero hb_div ) ) ( pow_pos ( by decide ) _ ), by rwa [ Nat.mul_div_cancel' ( Nat.dvd_of_mod_eq_zero hb_div ) ], by rw [ Nat.mul_div_cancel' ( Nat.dvd_of_mod_eq_zero hb_div ) ] ; exact hb_v2 ⟩, Nat.mul_div_cancel' ( Nat.dvd_of_mod_eq_zero hb_div ) ⟩;
        · simp +contextual [ div_eq_mul_inv, mul_comm, mul_left_comm ];
      -- By definition of $Bt$, we can rewrite the left-hand side of the equation.
      have h_rewrite_Bt : log_density_sum (Bt A t) (N / 2^t) = ∑ b ∈ (Finset.Icc 1 (N / 2^t)).filter (fun b => Odd b ∧ ∃ a ∈ A, v2 a = t ∧ a = 2^t * b), (1 : ℝ) / b := by
        have h_rewrite_Bt : Finset.filter (fun b => b ∈ Bt A t) (Finset.Icc 1 (N / 2^t)) = Finset.filter (fun b => Odd b ∧ ∃ a ∈ A, v2 a = t ∧ a = 2^t * b) (Finset.Icc 1 (N / 2^t)) := by
          ext; simp [Bt, At];
          intro _ _; constructor <;> intro h <;> rcases h with ⟨ x, hx₁, hx₂ ⟩ <;> simp_all +decide
          · rw [ ← hx₂, Nat.mul_div_cancel' ];
            · have h_odd : ¬(2 ∣ x / 2 ^ t) := by
                rw [ Nat.Prime.dvd_iff_one_le_factorization ] <;> norm_num;
                · rw [ Nat.factorization_div ] <;> norm_num;
                  · exact Nat.sub_eq_zero_of_le ( hx₁.2 ▸ Nat.le_refl _ );
                  · exact hx₁.2 ▸ Nat.ordProj_dvd _ _;
                · exact Nat.le_of_not_lt fun h => by rw [ Nat.div_eq_of_lt h ] at hx₂; linarith;
              exact ⟨ Nat.odd_iff.mpr ( Nat.mod_two_ne_zero.mp fun h => h_odd <| Nat.dvd_of_mod_eq_zero h ), hx₁ ⟩;
            · exact hx₁.2 ▸ Nat.ordProj_dvd _ _;
          · exact ⟨ _, ⟨ hx₁, hx₂ ⟩, Nat.mul_div_cancel_left _ ( pow_pos ( by decide ) _ ) ⟩;
        convert congr_arg ( fun s : Finset ℕ => ∑ b ∈ s, ( 1 : ℝ ) / b ) h_rewrite_Bt using 1;
        unfold log_density_sum;
        erw [ Finset.sum_filter, Finset.sum_filter ] ; erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ] ;
      simp_all +decide [ div_eq_mul_inv, Finset.mul_sum _ _ _ ]

/-
The limsup of a stretched sequence is equal to the limsup of the original sequence.
-/
lemma limsup_stretch {α : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    (u : ℕ → α) (k : ℕ) (hk : k > 0) :
    Filter.limsup (fun n => u (n / k)) Filter.atTop = Filter.limsup u Filter.atTop := by
      rw [ Filter.limsup_eq, Filter.limsup_eq ];
      congr! 3;
      simp +zetaDelta at *;
      constructor <;> rintro ⟨ a, ha ⟩;
      · exact ⟨ a * k, fun b hb => by simpa using ha ( b * k ) ( by nlinarith ) |> le_trans ( by simp +decide [hk] ) ⟩;
      · exact ⟨ a * k, fun b hb => ha _ ( Nat.le_div_iff_mul_le hk |>.2 ( by linarith ) ) ⟩

/-
The ratio of log(N/k) to log N tends to 1.
-/
lemma log_ratio_tendsto_one (k : ℕ) (hk : k > 0) :
    Filter.Tendsto (fun N => Real.log (N / k) / Real.log N) Filter.atTop (nhds 1) := by
      -- We can use the fact that $\log(N/k) = \log N - \log k$ to rewrite the limit expression.
      suffices h_log_div : Filter.Tendsto (fun N => (Real.log N - Real.log k) / Real.log N) Filter.atTop (nhds 1) by
        refine h_log_div.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN using by rw [ Real.log_div hN.ne' ( by positivity ) ] );
      ring_nf;
      exact le_trans ( Filter.Tendsto.sub ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx; rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos hx ) ) ] ) ) ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop ) ) ) ( by norm_num )

set_option maxHeartbeats 1000000 in
/-
If a sequence u is non-negative and v tends to 1, then limsup (u * v) = limsup u.
-/
lemma limsup_mul_tendsto_one {u v : ℕ → ℝ} (hu : 0 ≤ᶠ[Filter.atTop] u)
    (hv : Filter.Tendsto v Filter.atTop (nhds 1)) :
    Filter.limsup (u * v) Filter.atTop = Filter.limsup u Filter.atTop := by
      by_contra h_contra;
      have h_liminf : ∀ ε > 0, ∃ N, ∀ n ≥ N, (1 - ε) * u n ≤ u n * v n ∧ u n * v n ≤ (1 + ε) * u n := by
        intro ε hε_pos
        obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, |v n - 1| < ε := by
          exact Metric.tendsto_atTop.mp hv ε hε_pos;
        obtain ⟨ M, hM ⟩ := Filter.eventually_atTop.mp hu;
        exact ⟨ Max.max N M, fun n hn => ⟨ by nlinarith [ abs_lt.mp ( hN n ( le_trans ( le_max_left _ _ ) hn ) ), show 0 ≤ u n from hM n ( le_trans ( le_max_right _ _ ) hn ) ], by nlinarith [ abs_lt.mp ( hN n ( le_trans ( le_max_left _ _ ) hn ) ), show 0 ≤ u n from hM n ( le_trans ( le_max_right _ _ ) hn ) ] ⟩ ⟩;
      have h_liminf : ∀ ε > 0, Filter.limsup (u * v) Filter.atTop ≤ (1 + ε) * Filter.limsup u Filter.atTop := by
        intros ε hε_pos
        obtain ⟨N, hN⟩ := h_liminf ε hε_pos;
        by_cases h : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u <;> simp_all +decide [ Filter.limsup_eq ];
        · refine' le_of_forall_pos_le_add fun δ δ_pos => _;
          obtain ⟨a, ha⟩ : ∃ a, (∃ a_1, ∀ (b : ℕ), a_1 ≤ b → u b ≤ a) ∧ a < sInf {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → u b ≤ a} + δ / (1 + ε) := by
            exact exists_lt_of_csInf_lt ( show { a : ℝ | ∃ a_1, ∀ b : ℕ, a_1 ≤ b → u b ≤ a }.Nonempty from by rcases h with ⟨ M, hM ⟩ ; exact ⟨ M, by rcases Filter.eventually_atTop.mp hM with ⟨ N, hN ⟩ ; exact ⟨ N, fun n hn => hN n hn ⟩ ⟩ ) ( lt_add_of_pos_right _ <| div_pos δ_pos <| by positivity );
          refine' le_trans ( csInf_le _ _ ) _;
          exact ( 1 + ε ) * a;
          · obtain ⟨ N', hN' ⟩ := Filter.eventually_atTop.mp ( hu.and ( hv.eventually ( lt_mem_nhds zero_lt_one ) ) );
            exact ⟨ 0, by rintro x ⟨ N, hN ⟩ ; exact le_trans ( mul_nonneg ( hN' _ ( le_max_left _ _ ) |>.1 ) ( hN' _ ( le_max_left _ _ ) |>.2.le ) ) ( hN _ ( le_max_right _ _ ) ) ⟩;
          · exact ⟨ Max.max N ha.1.choose, fun n hn => by nlinarith [ hN n ( le_trans ( le_max_left _ _ ) hn ), ha.1.choose_spec n ( le_trans ( le_max_right _ _ ) hn ) ] ⟩;
          · nlinarith [ mul_div_cancel₀ δ ( by linarith : ( 1 + ε ) ≠ 0 ) ];
        · simp_all +decide [ IsBoundedUnder, IsBounded ];
          rw [ show { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → u b * v b ≤ a } = ∅ from _ ] <;> norm_num;
          · rw [ show { a : ℝ | ∃ a_1 : ℕ, ∀ b : ℕ, a_1 ≤ b → u b ≤ a } = ∅ from _ ] <;> norm_num;
            exact Set.eq_empty_of_forall_notMem fun x hx => by obtain ⟨ N, hN ⟩ := hx; obtain ⟨ n, hn₁, hn₂ ⟩ := h x N; linarith [ hN n hn₁ ] ;
          · ext a;
            contrapose! h_contra;
            obtain ⟨ M, hM ⟩ := h_contra.resolve_right ( by tauto ) |> And.left;
            obtain ⟨ N, hN ⟩ := h_liminf ( 1 / 2 ) ( by norm_num );
            obtain ⟨ n, hn₁, hn₂ ⟩ := h ( a * 2 + 1 ) ( Max.max M N ) ; nlinarith [ hN n ( le_trans ( le_max_right M N ) hn₁ ), hM n ( le_trans ( le_max_left M N ) hn₁ ) ];
      have h_liminf : Filter.limsup (u * v) Filter.atTop ≤ Filter.limsup u Filter.atTop := by
        have h_liminf : Filter.Tendsto (fun ε : ℝ => (1 + ε) * Filter.limsup u Filter.atTop) (nhdsWithin 0 (Set.Ioi 0)) (nhds (Filter.limsup u Filter.atTop)) := by
          exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) );
        exact le_of_tendsto_of_tendsto tendsto_const_nhds h_liminf ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => by aesop );
      have h_liminf : ∀ ε > 0, Filter.limsup u Filter.atTop ≤ (1 + ε) * Filter.limsup (u * v) Filter.atTop := by
        intros ε hε_pos
        have h_liminf : ∀ᶠ n in Filter.atTop, u n ≤ (1 + ε) * (u n * v n) := by
          have h_liminf : ∀ᶠ n in Filter.atTop, v n ≥ 1 / (1 + ε) := by
            exact hv.eventually ( le_mem_nhds <| by rw [ div_lt_iff₀ ] <;> linarith );
          filter_upwards [ hu, h_liminf ] with n hn hn' using by rw [ ge_iff_le, div_le_iff₀ ] at hn' <;> nlinarith [ mul_nonneg hn ( show 0 ≤ ε by linarith ) ] ;
        rw [ Filter.limsup_eq, Filter.limsup_eq ];
        rw [ ← smul_eq_mul, ← Real.sInf_smul_of_nonneg ];
        · refine' le_csInf _ _ <;> norm_num;
          · have h_bdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (u * v) := by
              by_cases h_bdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u;
              · obtain ⟨ M, hM ⟩ := h_bdd;
                have h_bdd_above : ∃ N, ∀ n ≥ N, |v n| ≤ 2 := by
                  exact Filter.eventually_atTop.mp ( hv.eventually ( Metric.closedBall_mem_nhds _ zero_lt_one ) ) |> fun ⟨ N, hN ⟩ => ⟨ N, fun n hn => abs_le.mpr ⟨ by linarith [ abs_le.mp ( hN n hn ) ], by linarith [ abs_le.mp ( hN n hn ) ] ⟩ ⟩;
                obtain ⟨ N, hN ⟩ := h_bdd_above;
                obtain ⟨ N', hN' ⟩ := Filter.eventually_atTop.mp ( hu.and hM );
                exact ⟨ 2 * M, Filter.eventually_atTop.mpr ⟨ Max.max N N', fun n hn => by have := hN' n ( le_trans ( le_max_right _ _ ) hn ) ; have := hN n ( le_trans ( le_max_left _ _ ) hn ) ; norm_num at *; nlinarith [ abs_le.mp this ] ⟩ ⟩;
              · simp_all +decide [ IsBoundedUnder, IsBounded ];
                rw [ Filter.limsup_eq ] at h_contra;
                rw [ Real.sInf_def ] at h_contra;
                rw [ Real.sSup_def ] at h_contra ; aesop;
            obtain ⟨ M, hM ⟩ := h_bdd; exact ⟨ M, by rcases Filter.eventually_atTop.mp hM with ⟨ N, hN ⟩ ; exact ⟨ N, fun n hn => hN n hn ⟩ ⟩ ;
          · rintro _ ⟨ a, ⟨ N, hN ⟩, rfl ⟩;
            refine' csInf_le _ _;
            · exact ⟨ 0, by rintro x ⟨ M, hM ⟩ ; exact le_trans ( hu.and ( Filter.eventually_ge_atTop M ) |> Filter.Eventually.exists |> Classical.choose_spec |> And.left ) ( hM _ ( hu.and ( Filter.eventually_ge_atTop M ) |> Filter.Eventually.exists |> Classical.choose_spec |> And.right ) ) ⟩;
            · exact Filter.eventually_atTop.mp ( h_liminf.and ( Filter.eventually_ge_atTop N ) ) |> fun ⟨ M, hM ⟩ => ⟨ M, fun n hn => by have := hM n hn; norm_num at *; nlinarith [ hN n ( by linarith ) ] ⟩;
        · positivity;
      have h_liminf : Filter.limsup u Filter.atTop ≤ Filter.limsup (u * v) Filter.atTop := by
        have h_liminf : Filter.Tendsto (fun ε : ℝ => (1 + ε) * Filter.limsup (u * v) Filter.atTop) (nhdsWithin 0 (Set.Ioi 0)) (nhds (Filter.limsup (u * v) Filter.atTop)) := by
          exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) );
        exact le_of_tendsto_of_tendsto tendsto_const_nhds h_liminf ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => by aesop );
      exact h_contra <| le_antisymm ‹_› ‹_›

theorem helper3 (a b : ℕ) : Finset.Icc a.succ b = Finset.Ioc a b := by
  simp_all only [Nat.succ_eq_add_one]
  ext a_1 : 1
  simp_all only [Finset.mem_Icc, Finset.mem_Ioc, and_congr_left_iff]
  intro a_2
  rfl

/-
The logarithmic density sum is bounded by log N + 1.
-/
lemma log_density_sum_le_log (A : Set ℕ) (N : ℕ) (hN : N ≥ 1) :
    log_density_sum A N ≤ Real.log N + 1 := by
      -- The sum of reciprocals of natural numbers up to $N$ is at most $\log N + 1$.
      have h_harmonic_bound : ∀ N : ℕ, N ≥ 1 → ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n ≤ Real.log N + 1 := by
        intro N hN
        induction' hN with N hN ih;
        · norm_num +zetaDelta at *;
        · norm_num [ Finset.sum_Ioc_succ_top, helper3 ] at *;
          rw [ show ( N : ℝ ) + 1 = N * ( 1 + ( N : ℝ ) ⁻¹ ) by nlinarith only [ mul_inv_cancel₀ ( by positivity : ( N : ℝ ) ≠ 0 ) ], Real.log_mul ( by positivity ) ( by positivity ) ];
          nlinarith [ inv_pos.mpr ( by positivity : 0 < ( N : ℝ ) * ( 1 + ( N : ℝ ) ⁻¹ ) ), mul_inv_cancel₀ ( by positivity : ( N : ℝ ) * ( 1 + ( N : ℝ ) ⁻¹ ) ≠ 0 ), Real.log_inv ( 1 + ( N : ℝ ) ⁻¹ ), Real.log_le_sub_one_of_pos ( inv_pos.mpr ( by positivity : 0 < ( 1 + ( N : ℝ ) ⁻¹ ) ) ), mul_inv_cancel₀ ( by positivity : ( N : ℝ ) ≠ 0 ), mul_inv_cancel₀ ( by positivity : ( 1 + ( N : ℝ ) ⁻¹ ) ≠ 0 ) ];
      refine le_trans ?_ ( h_harmonic_bound N hN );
      refine' le_trans _ ( Finset.sum_le_sum_of_subset_of_nonneg _ _ );
      rotate_left;
      exact Finset.filter ( fun n => n ∈ A ) ( Finset.Icc 1 N );
      · exact Finset.filter_subset _ _;
      · exact fun _ _ _ => by positivity;
      · unfold log_density_sum;
        erw [ Finset.sum_filter, Finset.sum_filter ] ; erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ]

/-
If A has positive lower density, there exists t such that A_t has positive upper logarithmic density.
-/
lemma exists_t_upper_log_density_At_pos (A : Set ℕ) (h : lowerDensity A > 0) :
    ∃ t, upper_log_density (At A t) > 0 := by
      -- Obtain `T` from `exists_T_union_pos`.
      obtain ⟨T, hT⟩ : ∃ T, lowerDensity (⋃ t ∈ Finset.range T, At A t) > 0 := exists_T_union_pos A h
      generalize_proofs at *;
      set U : Set ℕ := ⋃ t ∈ Finset.range T, At A t
      generalize_proofs at *; (
      -- By `lower_log_density_pos`, `lower_log_density U > 0`.
      have h_lower_log_density_U_pos : lower_log_density U > 0 := by
        exact lower_log_density_pos U hT;
      -- Since `lower_log_density U ≤ upper_log_density U` (liminf ≤ limsup), `upper_log_density U > 0`.
      have h_upper_log_density_U_pos : upper_log_density U > 0 := by
        refine' lt_of_lt_of_le h_lower_log_density_U_pos _;
        -- By definition of `lower_log_density` and `upper_log_density`, we know that `lower_log_density U ≤ upper_log_density U`.
        apply Filter.liminf_le_limsup; exact (by
        use 1 + 1 / Real.log 2;
        simp +zetaDelta at *;
        refine' ⟨ 2, fun n hn => _ ⟩ ; rw [ div_le_iff₀ ( Real.log_pos <| by norm_cast ) ] ; have := log_density_sum_le_log ( ⋃ t, ⋃ ( _ : t < T ), At A t ) n ( by linarith ) ; norm_num at *;
        nlinarith [ inv_pos.mpr ( Real.log_pos one_lt_two ), mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos one_lt_two ) ), Real.log_le_log ( by positivity ) ( by norm_cast : ( 2 : ℝ ) ≤ n ) ]);
        refine' ⟨ 0, Filter.eventually_atTop.mpr ⟨ 2, fun N hN => div_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ) ( Real.log_nonneg ( by norm_cast; linarith ) ) ⟩ ⟩;
      exact not_forall_not.mp fun h' => h_upper_log_density_U_pos.not_ge <| le_trans ( upper_log_density_subadd ( Finset.range T ) ( fun t => At A t ) ) <| by simpa using Finset.sum_nonpos fun t ht => le_of_not_gt <| h' t;)

/-
If a set of odd integers has positive upper logarithmic density, it contains an lcm-triple.
-/
lemma lcm_triple_of_upper_log_density_pos (A : Set ℕ) (hA_odd : ∀ a ∈ A, Odd a)
    (h_pos : upper_log_density A > 0) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ Nat.lcm a b = c := by
      by_contra h_contra
      have h_upper_log_density : upper_log_density A = 0 := by
        have h_upper_log_density : Filter.Tendsto (fun N => log_density_sum A N / Real.log N) Filter.atTop (nhds 0) := by
          have h_I_N_zero : (fun N => (I_N A N : ℝ)) =o[Filter.atTop] (fun N => (N : ℝ) * Real.log N) := by
            apply_rules [ I_N_upper_bound_asymptotic ];
            exact fun a ha b hb c hc hab hbc hca => fun h => h_contra ⟨ a, ha, b, hb, c, hc, hab, hbc, hca, h ⟩;
          have h_I_N_bound : ∀ N ≥ 1, (I_N A N : ℝ) ≥ (N / 2 : ℝ) * log_density_sum A N - N := by
            intros N hN
            have h_I_N_bound : (I_N A N : ℝ) ≥ ∑ a ∈ (Finset.range (N + 1)).filter (· ∈ A), ((N / a : ℝ) / 2 - 1) := by
              convert I_N_lower_bound A hA_odd N using 1;
            simp_all +decide [ log_density_sum ];
            convert h_I_N_bound.trans _ using 1;
            · rw [ Finset.mul_sum _ _ _ ] ; exact Finset.sum_congr rfl fun _ _ => by ring;
            · exact add_le_add_left ( mod_cast le_trans ( Finset.card_le_card ( show Finset.filter ( fun x => x ∈ A ) ( Finset.range ( N + 1 ) ) ⊆ Finset.Icc 1 N from fun x hx => Finset.mem_Icc.mpr ⟨ Nat.pos_of_ne_zero fun h => by simpa [ h ] using hA_odd x <| Finset.mem_filter.mp hx |>.2, Nat.le_of_lt_succ <| Finset.mem_range.mp <| Finset.mem_filter.mp hx |>.1 ⟩ ) ) <| by simp +arith +decide ) _;
          have h_I_N_bound : ∀ᶠ N in Filter.atTop, (log_density_sum A N : ℝ) ≤ 2 * (I_N A N : ℝ) / N + 2 := by
            filter_upwards [ Filter.eventually_ge_atTop 1 ] with N hN using by rw [ div_add', le_div_iff₀ ] <;> first | positivity | nlinarith [ h_I_N_bound N hN ] ;
          have h_I_N_bound : Filter.Tendsto (fun N => (2 * (I_N A N : ℝ) / N + 2) / Real.log N) Filter.atTop (nhds 0) := by
            have h_I_N_bound : Filter.Tendsto (fun N => (2 * (I_N A N : ℝ) / N) / Real.log N) Filter.atTop (nhds 0) := by
              rw [ Asymptotics.isLittleO_iff_tendsto' ] at h_I_N_zero;
              · convert h_I_N_zero.const_mul 2 using 2 <;> ring;
              · filter_upwards [ Filter.eventually_gt_atTop 1 ] with N hN hN' using absurd hN' <| ne_of_gt <| mul_pos ( Nat.cast_pos.mpr <| pos_of_gt hN ) <| Real.log_pos <| Nat.one_lt_cast.mpr hN;
            simpa [ add_div ] using h_I_N_bound.add ( tendsto_const_nhds.mul ( tendsto_inv_atTop_zero.comp ( Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop ) ) );
          refine' squeeze_zero_norm' _ h_I_N_bound;
          filter_upwards [ ‹∀ᶠ N in Filter.atTop, log_density_sum A N ≤ 2 * ↑ ( I_N A N ) / ↑ N + 2›, Filter.eventually_ge_atTop 1 ] with N hN₁ hN₂ using by rw [ Real.norm_of_nonneg ( div_nonneg ( show 0 ≤ log_density_sum A N from Finset.sum_nonneg fun _ _ => by positivity ) ( Real.log_natCast_nonneg _ ) ) ] ; exact div_le_div_of_nonneg_right hN₁ ( Real.log_natCast_nonneg _ ) ;
        convert h_upper_log_density.limsup_eq using 1;
      linarith

/-
The ratio of the logarithmic density sum to log N is bounded.
-/
lemma log_density_ratio_bounded (A : Set ℕ) :
    Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun N => log_density_sum A N / Real.log N) := by
      refine' ⟨ 2, Filter.eventually_atTop.mpr ⟨ 3, fun N hN => _ ⟩ ⟩;
      have := log_density_sum_le_log A N ( by linarith );
      exact div_le_of_le_mul₀ ( Real.log_nonneg ( by norm_cast; linarith ) ) ( by positivity ) ( by linarith [ show 1 ≤ Real.log N from by rw [ Real.le_log_iff_exp_le ( by positivity ) ] ; exact Real.exp_one_lt_d9.le.trans ( by norm_num; linarith [ show ( N : ℝ ) ≥ 3 by norm_cast ] ) ] )

/-
The limsup of `log_density_sum A (N/k) / log(N/k)` is equal to the upper logarithmic density of A.
-/
lemma limsup_log_density_stretch_aux (A : Set ℕ) (k : ℕ) (hk : k > 0) :
    Filter.limsup (fun N => log_density_sum A (N / k) / Real.log (N / k)) Filter.atTop = upper_log_density A := by
      -- Extend the sequence to be defined for real numbers by taking the floor of N/k.
      set u : ℕ → ℝ := fun N => log_density_sum A N / Real.log N;
      -- Apply `limsup_stretch` to the sequence `u(N) = log_density_sum A N / log N`.
      have h_limsup_stretch : Filter.limsup (fun N => u (Nat.floor (N / k))) Filter.atTop = Filter.limsup u Filter.atTop := by
        convert limsup_stretch u k hk using 1;
      have h_limsup_stretch : Filter.limsup (fun N => u (Nat.floor (N / k)) * (Real.log (Nat.floor (N / k)) / Real.log (N / k))) Filter.atTop = Filter.limsup u Filter.atTop := by
        have h_limsup_stretch : Filter.Tendsto (fun N => Real.log (Nat.floor (N / k)) / Real.log (N / k)) Filter.atTop (nhds 1) := by
          have h_log_floor : Filter.Tendsto (fun x : ℝ => Real.log (Nat.floor x) / Real.log x) Filter.atTop (nhds 1) := by
            have h_log_floor : Filter.Tendsto (fun x : ℝ => Real.log (x - 1) / Real.log x) Filter.atTop (nhds 1) := by
              have h_log_floor : Filter.Tendsto (fun x : ℝ => (Real.log x + Real.log (1 - 1 / x)) / Real.log x) Filter.atTop (nhds 1) := by
                ring_nf;
                exact le_trans ( Filter.Tendsto.add ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ mul_inv_cancel₀ ( ne_of_gt ( Real.log_pos hx ) ) ] ) ) ( Filter.Tendsto.mul ( Filter.Tendsto.log ( tendsto_const_nhds.sub ( tendsto_inv_atTop_zero ) ) ( by norm_num ) ) ( tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop ) ) ) ( by norm_num );
              refine h_log_floor.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using by rw [ one_sub_div ( by linarith ) ] ; rw [ Real.log_div ] <;> ring_nf <;> linarith );
            refine' tendsto_of_tendsto_of_tendsto_of_le_of_le' h_log_floor tendsto_const_nhds _ _;
            · filter_upwards [ Filter.eventually_gt_atTop 2 ] with x hx using div_le_div_of_nonneg_right ( Real.log_le_log ( by linarith ) ( by linarith [ Nat.lt_floor_add_one x ] ) ) ( Real.log_nonneg ( by linarith ) );
            · filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx using div_le_one_of_le₀ ( Real.log_le_log ( Nat.cast_pos.mpr <| Nat.floor_pos.mpr <| by linarith ) <| Nat.floor_le <| by linarith ) <| Real.log_nonneg <| by linarith;
          convert h_log_floor.comp ( show Filter.Tendsto ( fun N : ℕ => ( N : ℝ ) / k ) Filter.atTop Filter.atTop from Filter.Tendsto.atTop_div_const ( Nat.cast_pos.mpr hk ) tendsto_natCast_atTop_atTop ) using 2;
          norm_num [ Nat.floor_div_natCast ];
        have h_limsup_stretch : Filter.limsup (fun N => u (Nat.floor (N / k)) * (Real.log (Nat.floor (N / k)) / Real.log (N / k))) Filter.atTop = Filter.limsup (fun N => u (Nat.floor (N / k))) Filter.atTop := by
          have h_bdd : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop (fun N => u (Nat.floor (N / k))) := by
            have h_limsup_stretch : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop u := by
              exact log_density_ratio_bounded A;
            obtain ⟨ M, hM ⟩ := h_limsup_stretch;
            norm_num +zetaDelta at *;
            obtain ⟨ N, hN ⟩ := hM;
            exact ⟨ M, Filter.eventually_atTop.mpr ⟨ N * k, fun n hn => hN _ <| Nat.le_div_iff_mul_le hk |>.2 <| by nlinarith ⟩ ⟩
          apply_rules [ limsup_mul_tendsto_one ];
          filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN using div_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ) ( Real.log_natCast_nonneg _ );
        linarith;
      convert h_limsup_stretch using 1;
      refine' Filter.limsup_congr _;
      filter_upwards [ Filter.eventually_gt_atTop ( k * 2 ) ] with N hN ; rw [ div_mul_div_cancel₀ ] ; aesop;
      exact ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr <| Nat.le_floor <| Nat.le_div_iff_mul_le hk |>.2 <| by linarith;

/-
The upper logarithmic density of a set A is equal to the limsup of `log_density_sum A (N/k) / log N`.
-/
lemma limsup_log_density_stretch (A : Set ℕ) (k : ℕ) (hk : k > 0) :
    Filter.limsup (fun N => log_density_sum A (N / k) / Real.log N) Filter.atTop = upper_log_density A := by
      have h_stretch : Filter.limsup (fun N => log_density_sum A (N / k) / Real.log (N / k) * (Real.log (N / k) / Real.log N)) Filter.atTop = upper_log_density A := by
        have h_stretch : Filter.limsup (fun N => log_density_sum A (N / k) / Real.log (N / k)) Filter.atTop = upper_log_density A := by
          convert limsup_log_density_stretch_aux A k hk using 1;
        convert limsup_mul_tendsto_one _ _ using 2;
        · exact h_stretch.symm;
        · filter_upwards [ Filter.eventually_gt_atTop ( k : ℕ ) ] with N hN using div_nonneg ( Finset.sum_nonneg fun _ _ => by positivity ) ( Real.log_nonneg <| by rw [ le_div_iff₀ <| by positivity ] ; norm_cast ; linarith );
        · have := log_ratio_tendsto_one k hk;
          exact this.comp tendsto_natCast_atTop_atTop;
      refine' h_stretch ▸ Filter.limsup_congr ( by filter_upwards [ Filter.eventually_gt_atTop k ] with N hN using by rw [ div_mul_div_cancel₀ ( ne_of_gt <| Real.log_pos <| by rw [ lt_div_iff₀ <| by positivity ] ; norm_cast ; linarith ) ] )

/-
The upper logarithmic density of $B_t$ is $2^t$ times the upper logarithmic density of $A_t$.
-/
lemma upper_log_density_Bt (A : Set ℕ) (t : ℕ) :
    upper_log_density (Bt A t) = (2^t : ℝ) * upper_log_density (At A t) := by
      -- We have `log_density_sum (At A t) N = (1/2^t) * log_density_sum (Bt A t) (N/2^t)`.
      -- Dividing by `log N`, we get `(1/2^t) * (log_density_sum (Bt A t) (N/2^t) / log N)`.
      have h_div : ∀ N ≥ 1, log_density_sum (At A t) N = (1 / 2^t : ℝ) * log_density_sum (Bt A t) (N / 2^t) := by
        intros N hN
        rw [log_density_sum_Bt_relation];
      -- Taking limsup, we get `upper_log_density (At A t) = (1/2^t) * limsup (log_density_sum (Bt A t) (N/2^t) / log N)`.
      have h_limsup : Filter.limsup (fun N => log_density_sum (At A t) N / Real.log N) Filter.atTop = (1 / 2^t : ℝ) * Filter.limsup (fun N => log_density_sum (Bt A t) (N / 2^t) / Real.log N) Filter.atTop := by
        have h_limsup : Filter.limsup (fun N => (1 / 2^t : ℝ) * (log_density_sum (Bt A t) (N / 2^t) / Real.log N)) Filter.atTop = (1 / 2^t : ℝ) * Filter.limsup (fun N => log_density_sum (Bt A t) (N / 2^t) / Real.log N) Filter.atTop := by
          norm_num [ Filter.limsup_eq ];
          rw [ ← smul_eq_mul, ← Real.sInf_smul_of_nonneg ];
          · congr with x ; simp +decide [ div_eq_inv_mul ];
            constructor <;> rintro ⟨ a, ha ⟩;
            · exact ⟨ x / ( 2 ^ t ) ⁻¹, ⟨ a, fun b hb => by rw [ le_div_iff₀ ( by positivity ) ] ; linarith [ ha b hb ] ⟩, by simp +decide [ div_eq_inv_mul ] ⟩;
            · exact ⟨ ha.1.choose, fun n hn => by rw [ ← ha.2 ] ; exact mul_le_mul_of_nonneg_left ( ha.1.choose_spec n hn ) ( by positivity ) ⟩;
          · positivity;
        exact Eq.trans ( Filter.limsup_congr <| by filter_upwards [ Filter.eventually_ge_atTop 1 ] with N hN using by rw [ h_div N hN ] ; ring ) h_limsup;
      -- By `limsup_log_density_stretch`, the limsup is `upper_log_density (Bt A t)`.
      have h_limsup_final : Filter.limsup (fun N => log_density_sum (Bt A t) (N / 2^t) / Real.log N) Filter.atTop = upper_log_density (Bt A t) := by
        convert limsup_log_density_stretch ( Bt A t ) ( 2 ^ t ) ( by positivity ) using 1;
      unfold upper_log_density at * ; aesop

/-
If a set A has positive lower density, it contains an lcm-triple.
-/
theorem erdos_487 (A : Set ℕ) (hA : lowerDensity A > 0) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ Nat.lcm a b = c := by
      by_contra! h;
      -- Let $A' = A \setminus \{0\}$. Then $\ldens(A') = \ldens(A) > 0$.
      set A' : Set ℕ := A \ {0}
      have hA'_pos : lowerDensity A' > 0 := by
        convert hA using 1;
        refine' Filter.liminf_congr _;
        norm_num +zetaDelta at *;
        exact ⟨ 1, fun n hn => by rw [ Finset.filter_congr fun x hx => by aesop ] ⟩;
      -- By `exists_t_upper_log_density_At_pos`, there exists $t$ such that `upper_log_density (At A' t) > 0`.
      obtain ⟨t, ht⟩ : ∃ t, upper_log_density (At A' t) > 0 := by
        -- Apply `exists_t_upper_log_density_At_pos` to `A'` with the given `hA'_pos`.
        apply exists_t_upper_log_density_At_pos; assumption;
      -- Since $A'$ has no zero, `Bt A' t` consists of odd integers by `Bt_odd`.
      have hBt_odd : ∀ b ∈ Bt A' t, Odd b := by
        apply Bt_odd; aesop;
      -- By `lcm_triple_of_upper_log_density_pos`, `Bt A' t` contains distinct $x,y,z$ with $[x,y]=z$.
      obtain ⟨x, hx, y, hy, z, hz, hxyz⟩ : ∃ x ∈ Bt A' t, ∃ y ∈ Bt A' t, ∃ z ∈ Bt A' t, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ Nat.lcm x y = z := by
        apply lcm_triple_of_upper_log_density_pos;
        · assumption;
        · rw [ upper_log_density_Bt ] ; aesop;
      -- By `lcm_triple_preservation`, $A'$ contains distinct $a,b,c$ with $[a,b]=c$.
      obtain ⟨a, ha, b, hb, c, hc, habc⟩ : ∃ a ∈ A', ∃ b ∈ A', ∃ c ∈ A', a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ v2 a = t ∧ v2 b = t ∧ v2 c = t ∧ Nat.lcm a b = c := by
        obtain ⟨a, ha, b, hb, c, hc, habc⟩ : ∃ a ∈ A', ∃ b ∈ A', ∃ c ∈ A', a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ v2 a = t ∧ v2 b = t ∧ v2 c = t ∧ Nat.lcm a b = c := by
          have := lcm_triple_preservation A' t
          grind;
        exact ⟨ a, ha, b, hb, c, hc, habc ⟩;
      exact h a ha.1 b hb.1 c hc.1 habc.1 habc.2.1 habc.2.2.1 habc.2.2.2.2.2.2

#print axioms erdos_487
-- 'Erdos487.erdos_487' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos487
