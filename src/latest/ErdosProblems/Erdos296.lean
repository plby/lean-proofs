/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/-
Note: this file has been modified.
-/

/-
Copyright (c) 2026 John Jennings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Jennings, Aristotle (Harmonic)
-/
import ErdosProblems.Axioms
import Mathlib

namespace Erdos296

/-!
Erdős Problem 296: https://www.erdosproblems.com/296

Let N ≥ 1 and let k(N) be maximal such that there are k disjoint
A₁, ..., Aₖ ⊆ {1, ..., N} with ∑_{n ∈ Aᵢ} 1/n = 1 for all i.
Estimate k(N). Is it true that k(N) = o(log N)?

Answer: No — k(N) = (1 − o(1)) log N.

The upper bound k(N) ≤ ⌊∑_{n=1}^{N} 1/n⌋ is elementary: disjoint subsets
with reciprocal sum 1 each consume at least 1 from the total harmonic sum.
The lower bound k(N) ≥ (1 − o(1)) log N follows from the quantitative
density theorem of Bloom (Theorem 3, arXiv:2112.03726) via a greedy argument,
as observed by Hunter and Sawhney.

Solution attribution:
  T. F. Bloom, "On a density conjecture about unit fractions,"
    arXiv:2112.03726 (2021).
  Hunter–Sawhney observation coupling Bloom's Theorem 3 with greedy
    extraction.

Autoformalization: Aristotle (Harmonic)
-/

/-! # Erdős Problem 296

We formalize the solution to Erdős Problem 296, which asks for the
asymptotic behavior of `k(N)`, the maximum number of pairwise disjoint
subsets of `{1, …, N}` whose reciprocal sums each equal 1.

## Main results

- `erdos296_upper_bound`: `k ≤ ∑_{n ∈ Icc 1 N} 1/n` (elementary).
- `bloom_density_theorem`: the Erdős–Graham conjecture (Bloom, Thm 2).
- `bloom_quantitative`: the quantitative refinement (Bloom, Thm 3).
- `erdos296_answer`: `k(N) = (1 − o(1)) log N`, answering the problem.
-/

open Finset Filter

noncomputable section

-- ================================================================
-- § 0. Definitions
-- ================================================================

/-- The reciprocal sum `R(A) = ∑_{n ∈ A} 1/n` for a finite set of
natural numbers. -/
def recipSum (A : Finset ℕ) : ℚ :=
  ∑ n ∈ A, (1 : ℚ) / n

/-- There exist `k` pairwise disjoint subsets of `{1, …, N}`, each
with reciprocal sum 1. -/
def HasDisjointUnitDecomps (N k : ℕ) : Prop :=
  ∃ f : Fin k → Finset ℕ,
    (∀ i, f i ⊆ Icc 1 N) ∧
    (∀ i, recipSum (f i) = 1) ∧
    (∀ i j : Fin k, i ≠ j → Disjoint (f i) (f j))

-- ================================================================
-- § 1. Elementary upper bound
-- ================================================================

/-- The reciprocal sum of a biUnion of pairwise disjoint families
equals the sum of the individual reciprocal sums. -/
lemma recipSum_biUnion {ι : Type*}
    (s : Finset ι) (f : ι → Finset ℕ)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j)) :
    recipSum (s.biUnion f) = ∑ i ∈ s, recipSum (f i) := by
  classical
  simp only [recipSum]
  rw [Finset.sum_biUnion hd]

/-- **Upper bound on k(N).**
If there are `k` pairwise disjoint subsets of `{1, …, N}` each with
reciprocal sum 1, then `k ≤ R({1, …, N})`. -/
theorem erdos296_upper_bound (N k : ℕ)
    (h : HasDisjointUnitDecomps N k) :
    (k : ℚ) ≤ recipSum (Icc 1 N) := by
  obtain ⟨f, hf_sub, hf_sum, hf_disj⟩ := h
  calc (k : ℚ)
      = ∑ i : Fin k, 1 := by simp
    _ = ∑ i : Fin k, recipSum (f i) := by
        congr 1; ext i; exact (hf_sum i).symm
    _ = recipSum (Finset.univ.biUnion f) := by
        rw [recipSum_biUnion _ _
          (fun i _ j _ hij => hf_disj i j hij)]
    _ ≤ recipSum (Icc 1 N) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact biUnion_subset.mpr fun i _ => hf_sub i
        · intro n _ _; positivity

-- ================================================================
-- § 2. Bloom's theorem (a deep result, stated axiomatically)
-- ================================================================

-- The Bloom–Mehta Lean 3 formalization (Theorem 3) is imported from
-- `ErdosProblems.Axioms` as `unit_fractions_upper_log_density`.

/-- The ℝ-cast of `recipSum` equals the real-valued reciprocal sum. -/
lemma recipSum_cast_real (A : Finset ℕ) :
    (recipSum A : ℝ) = ∑ n ∈ A, (1 : ℝ) / (n : ℝ) := by
  simp only [recipSum, Rat.cast_sum, Rat.cast_div, Rat.cast_one,
    Rat.cast_natCast]

/-- `∑ n ∈ S, (1 / n : ℚ) = 1` is equivalent to `recipSum S = 1`. -/
lemma sum_one_div_eq_recipSum (S : Finset ℕ) :
    ∑ n ∈ S, (1 / n : ℚ) = recipSum S := by
  simp [recipSum]

/-
**Bloom's quantitative theorem (Theorem 3, arXiv:2112.03726).**
There exists `C > 0` such that for all sufficiently large `N`, any
`A ⊆ {1, …, N}` with
`R(A) ≥ C · (log log log N / log log N) · log N`
contains a subset `S` with `R(S) = 1`.

Proved from `unit_fractions_upper_log_density` by taking
`C' = max C 1 > 0` and observing that a larger threshold gives a
stronger hypothesis.
-/
theorem bloom_quantitative :
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ N : ℕ in atTop,
      ∀ A ⊆ Icc 1 N,
        C * Real.log (Real.log (Real.log N)) /
          Real.log (Real.log N) * Real.log N
          ≤ ↑(recipSum A) →
        ∃ S ⊆ A, recipSum S = 1 := by
  obtain ⟨C, hC⟩ := unit_fractions_upper_log_density
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
  have h_nonneg : ∀ᶠ b : ℕ in atTop,
      0 ≤ Real.log (Real.log (Real.log b)) / Real.log (Real.log b) ∧
        0 ≤ Real.log b := by
    obtain ⟨a', ha'⟩ : ∃ a' : ℝ, ∀ b ≥ a',
        0 ≤ Real.log (Real.log (Real.log b)) / Real.log (Real.log b) ∧
          0 ≤ Real.log b := by
      refine ⟨Real.exp (Real.exp 1), fun b hb => ?_⟩
      constructor
      · exact div_nonneg
          (Real.log_nonneg <| by
            rw [Real.le_log_iff_exp_le <|
              Real.log_pos <| lt_of_lt_of_le (by norm_num [Real.exp_pos]) hb]
            rw [Real.le_log_iff_exp_le <| by
              linarith [Real.exp_pos (Real.exp 1)]]
            linarith [Real.add_one_le_exp 1, Real.add_one_le_exp (Real.exp 1)])
          (Real.log_nonneg <| by
            rw [Real.le_log_iff_exp_le <| by
              linarith [Real.exp_pos (Real.exp 1)]]
            linarith [Real.add_one_le_exp 1, Real.add_one_le_exp (Real.exp 1)])
      · exact Real.log_nonneg (le_trans (by norm_num [Real.exp_nonneg]) hb)
    filter_upwards [Filter.eventually_ge_atTop ⌈a'⌉₊] with b hb
    exact ha' b (Nat.le_of_ceil_le hb)
  filter_upwards [hC, h_nonneg] with b hbloom hb_nonneg A hA h
  have h_real_sum :
      C * (Real.log (Real.log (Real.log b)) / Real.log (Real.log b)) *
          Real.log b
        ≤ ∑ n ∈ A, (1 : ℝ) / n := by
    rw [← recipSum_cast_real A]
    refine le_trans ?_ h
    simpa only [mul_div_assoc] using
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C 1) hb_nonneg.1)
        hb_nonneg.2)
  obtain ⟨S, hS_sub, hS_sum⟩ := hbloom A hA h_real_sum
  exact ⟨S, hS_sub, by simpa only [sum_one_div_eq_recipSum] using hS_sum⟩

-- ================================================================
-- § 3. Helper lemmas for the greedy extraction
-- ================================================================

/-- The reciprocal sum of `A \ S` equals `R(A) - R(S)` when
`S ⊆ A`. -/
lemma recipSum_sdiff {A S : Finset ℕ} (hSA : S ⊆ A) :
    recipSum (A \ S) = recipSum A - recipSum S :=
  eq_tsub_of_add_eq <| Finset.sum_sdiff hSA

/-- `HasDisjointUnitDecomps` is monotone in `k`. -/
lemma HasDisjointUnitDecomps.mono {N k₁ k₂ : ℕ}
    (h : HasDisjointUnitDecomps N k₂) (hle : k₁ ≤ k₂) :
    HasDisjointUnitDecomps N k₁ :=
  ⟨fun i => h.choose (Fin.castLE hle i),
   fun i => h.choose_spec.1 _,
   fun i => h.choose_spec.2.1 _,
   fun i j hij => h.choose_spec.2.2 _ _
     (by simpa [Fin.ext_iff] using hij)⟩

-- ================================================================
-- § 4. Answer to Erdős Problem 296
-- ================================================================

/-- **Answer to Erdős Problem 296.**
For every `ε > 0`, for all sufficiently large `N`, there exist at
least `⌊(1 − ε) · log N⌋` pairwise disjoint subsets of `{1, …, N}`
each with reciprocal sum 1. Combined with the upper bound, this gives
`k(N) = (1 − o(1)) log N`, so `k(N)` is **not** `o(log N)`.

*Proof.* By `bloom_quantitative`, for large `N`, any `A ⊆ {1,…,N}`
with `R(A) ≥ o(log N)` has a subset `S` with `R(S) = 1`. Greedily
extract such subsets; each reduces `R` by 1, so we get at least
`⌊(1−ε) log N⌋` before the remaining sum drops below the
threshold. -/
theorem erdos296_answer (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᶠ N : ℕ in atTop,
      HasDisjointUnitDecomps N ⌊(1 - ε) * Real.log N⌋₊ := by
  obtain ⟨ C, hC₀, hC ⟩ := bloom_quantitative;
  -- For large $N$, the threshold is less than $\epsilon / 2 * \log N$.
  have h_threshold : ∀ᶠ N in Filter.atTop,
      C * Real.log (Real.log (Real.log N)) /
          Real.log (Real.log N) * Real.log N ≤
        ε / 2 * Real.log N := by
    -- The factor before `log N` tends to `0`.
    have h_lim : Filter.Tendsto
        (fun N : ℝ =>
          C * Real.log (Real.log (Real.log N)) / Real.log (Real.log N))
        Filter.atTop (nhds 0) := by
      -- Let $y = \log \log N$.
      suffices h_log_log : Filter.Tendsto
          (fun y : ℝ => C * Real.log y / y) Filter.atTop (nhds 0) by
        exact h_log_log.comp ( Real.tendsto_log_atTop.comp ( Real.tendsto_log_atTop ) );
      -- Let $z = \frac{1}{y}$.
      suffices h_log_z : Filter.Tendsto
          (fun z : ℝ => -C * z * Real.log z)
          (Filter.map (fun y => 1 / y) Filter.atTop) (nhds 0) by
        exact h_log_z.congr (by
          simp +contextual [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm])
      norm_num;
      exact tendsto_nhdsWithin_of_tendsto_nhds ( by
        simpa [ mul_assoc ] using
          Filter.Tendsto.neg
            (tendsto_const_nhds.mul (Real.continuous_mul_log.tendsto 0)) );
    filter_upwards [
        h_lim.eventually (gt_mem_nhds <| show 0 < ε / 2 by positivity),
        Filter.eventually_gt_atTop 1]
      with N hN₁ hN₂ using
        mul_le_mul_of_nonneg_right hN₁.le <| Real.log_nonneg <| by linarith;
  -- For large $N$, the harmonic sum $H_N$ is at least $(1 - \epsilon / 2) \log N$.
  have h_harmonic : ∀ᶠ N in Filter.atTop,
      recipSum (Finset.Icc 1 N) ≥ (1 - ε / 2) * Real.log N := by
    have h_harmonic : Filter.Tendsto
        (fun N : ℕ => recipSum (Finset.Icc 1 N) / Real.log N)
        Filter.atTop (nhds 1) := by
      -- We'll use the fact that the harmonic series grows logarithmically.
      have h_harmonic_growth : Filter.Tendsto (fun N : ℕ =>
          (∑ n ∈ Finset.range N, (1 : ℝ) / (n + 1)) / Real.log N)
          Filter.atTop (nhds 1) := by
        -- The harmonic series grows logarithmically.
        have h_harmonic_growth : Filter.Tendsto (fun N : ℕ =>
            (∑ n ∈ Finset.range N, (1 : ℝ) / (n + 1)) - Real.log N)
            Filter.atTop (nhds (Real.eulerMascheroniConstant)) := by
          convert Real.tendsto_harmonic_sub_log using 1;
          norm_num [ harmonic ];
        have := h_harmonic_growth.div_atTop
          (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
        simpa using this.add_const 1 |> Filter.Tendsto.congr' ( by
          filter_upwards [ Filter.eventually_gt_atTop 1 ] with x hx
          rw [Function.comp_apply, sub_div,
            div_self <| ne_of_gt <| Real.log_pos <| Nat.one_lt_cast.mpr hx]
          ring_nf )
      convert h_harmonic_growth using 2 ; norm_num [ recipSum ];
      erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ];
    filter_upwards [
      h_harmonic.eventually (lt_mem_nhds <| show 1 > 1 - ε / 2 by linarith),
      Filter.eventually_gt_atTop 1 ] with N hN₁ hN₂ using
      by rw [ lt_div_iff₀ ( Real.log_pos <| Nat.one_lt_cast.mpr hN₂ ) ] at hN₁; linarith;
  -- By combining the results, we can conclude that for large $N$, there exist at least
  -- $\lfloor (1 - \epsilon) \log N \rfloor$ disjoint subsets of $\{1, \ldots, N\}$
  -- each with reciprocal sum 1.
  have h_combined : ∀ᶠ N in Filter.atTop,
      recipSum (Finset.Icc 1 N) ≥
        ⌊(1 - ε) * Real.log N⌋₊ +
          C * Real.log (Real.log (Real.log N)) /
            Real.log (Real.log N) * Real.log N := by
    filter_upwards [ h_harmonic, h_threshold.natCast_atTop, Filter.eventually_gt_atTop 1 ] with
      N hN₁ hN₂ hN₃ using
      by nlinarith [ Nat.floor_le ( show 0 ≤ ( 1 - ε ) * Real.log N by
        exact mul_nonneg ( sub_nonneg.2 hε1.le )
          ( Real.log_nonneg ( Nat.one_le_cast.2 hN₃.le ) ) ),
        Real.log_pos ( show ( N :ℝ ) > 1 by exact Nat.one_lt_cast.2 hN₃ ) ] ;
  filter_upwards [ hC, h_combined ] with N hN₁ hN₂;
  -- By induction on $k$, we can extract $k$ disjoint subsets from $A$ each with reciprocal sum 1.
  have h_induction : ∀ k ≤ ⌊(1 - ε) * Real.log N⌋₊,
      ∀ A ⊆ Finset.Icc 1 N,
        recipSum A ≥ k +
          C * Real.log (Real.log (Real.log N)) /
            Real.log (Real.log N) * Real.log N →
        ∃ f : Fin k → Finset ℕ,
          (∀ i, f i ⊆ A) ∧ (∀ i, recipSum (f i) = 1) ∧
          (∀ i j, i ≠ j → Disjoint (f i) (f j)) := by
    intro k hk
    induction k with
    | zero =>
        intro A hA hA'
        refine ⟨Fin.elim0, ?_, ?_, ?_⟩
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
        · intro i
          exact Fin.elim0 i
    | succ k ih =>
        intro A hA hA'
        obtain ⟨S, hS₁, hS₂⟩ := hN₁ A hA (by linarith)
        obtain ⟨f, hf₁, hf₂, hf₃⟩ :=
          ih (Nat.le_trans (Nat.le_succ k) hk) (A \ S)
            (Finset.sdiff_subset.trans hA) (by
              have h_goal :
                  (recipSum A : ℝ) - 1 ≥
                    (k : ℝ) +
                      C * Real.log (Real.log (Real.log N)) /
                        Real.log (Real.log N) * Real.log N := by
                norm_num at hA' ⊢
                linarith
              simpa [recipSum_sdiff hS₁, hS₂] using h_goal)
        refine ⟨Fin.cons S f, ?_, ?_, ?_⟩
        · exact Fin.forall_fin_succ.mpr
            ⟨hS₁, fun i => (hf₁ i).trans Finset.sdiff_subset⟩
        · exact Fin.forall_fin_succ.mpr ⟨hS₂, hf₂⟩
        · intro i j hij
          cases i using Fin.cases with
          | zero =>
              cases j using Fin.cases with
              | zero => exact False.elim (hij rfl)
              | succ j =>
                  exact Finset.disjoint_left.mpr fun x hxS hxfj =>
                    (Finset.mem_sdiff.mp (hf₁ j hxfj)).2 hxS
          | succ i =>
              cases j using Fin.cases with
              | zero =>
                  exact Finset.disjoint_left.mpr fun x hxfi hxS =>
                    (Finset.mem_sdiff.mp (hf₁ i hxfi)).2 hxS
              | succ j =>
                  exact hf₃ i j fun h => hij (by cases h; rfl)
  exact Exists.elim ( h_induction _ le_rfl _ ( Finset.Subset.refl _ ) hN₂ ) fun f hf =>
    ⟨ f, fun i => hf.1 i, hf.2.1, hf.2.2 ⟩

-- ================================================================
-- § 5. Corollary: k(N) is not o(log N)
-- ================================================================

/-- **k(N) is not o(log N).**
Since `erdos296_answer` gives `k(N) ≥ ⌊(1-ε) log N⌋` for every
`ε > 0`, we can take `ε = 1/2` to obtain `k(N) ≥ ⌊(1/2) log N⌋`
for all large `N`.  In particular `k(N) / log N ≥ 1/2 - o(1)`,
which is incompatible with `k(N) = o(log N)`. -/
theorem erdos296 :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ N : ℕ in atTop,
      HasDisjointUnitDecomps N ⌊ c * Real.log N ⌋₊ := by
  exact ⟨1 / 2, by norm_num, by
    have := erdos296_answer (1/2) (by norm_num) (by norm_num)
    simp only [one_div] at this ⊢; convert this using 2; ring_nf⟩

#print axioms erdos296
--'Erdos296.erdos296' depends on axioms: [propext, Classical.choice,
-- unit_fractions_upper_log_density, Quot.sound]

end
end Erdos296
