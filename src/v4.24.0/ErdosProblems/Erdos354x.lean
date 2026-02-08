/-

This is a Lean solution to a MISFORMALIZATION of Erdős Problem 354.
https://www.erdosproblems.com/354

The statement is from the Formal Conjectures project.

The proof was found by Aristotle from Harmonic.

The issue is FloorMultiples.interleave doesn't properly interleave:
https://github.com/google-deepmind/formal-conjectures/blob/f33f5ddb49f6077e34025917965bcd1bbd920d73/FormalConjectures/ErdosProblems/354.lean#L29-L34

The proof is verified by Lean.  The following version numbers were
used:

Lean Toolchain version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7 (v4.24.0)

-/

import Mathlib

namespace Erdos354x

open Filter Set Topology

variable {M : Type*} [AddCommMonoid M]

/-- The set of subset sums of a sequence `ℕ → M`, where repetition is allowed. -/
def subseqSums' (A : ℕ → M) : Set M :=
  {n | ∃ B : Finset ℕ, n = ∑ i ∈ B, A i}

/-- A sequence `A` is complete if every sufficiently large element of `M` is a sum of
(not necessarily distinct) terms of `A`. -/
def IsAddCompleteNatSeq' [Preorder M] (A : ℕ → M) : Prop :=
  ∀ᶠ k in Filter.atTop, k ∈ subseqSums' A

/-- The sequence `⌊a⌋, ⌊γ * a⌋, ⌊γ ^ 2 * a⌋, ..., ⌊γ ^ i * a⌋, ...`. -/
noncomputable def FloorMultiples (a γ : ℝ) (n : ℕ) : ℤ := ⌊γ ^ n * a⌋

/-- The sequence `⌊a⌋, ⌊b⌋, ⌊γ * a⌋, ⌊γ * b⌋, ... ⌊γ ^ i * a⌋, ⌊γ ^ i * b⌋, ...` -/
noncomputable def FloorMultiples.interleave (a b γ : ℝ) (n : ℕ) : ℤ :=
  if n % 2 = 0 then
    FloorMultiples a γ n
  else
    FloorMultiples b γ n

/- Let $\alpha,\beta\in \mathbb{R}_{>0}$ such that $\alpha/\beta$ is irrational. Is
\[\{ \lfloor \alpha\rfloor,\lfloor \gamma\alpha\rfloor,\lfloor \gamma^2\alpha\rfloor,\ldots\}\cup
\{ \lfloor \beta\rfloor,\lfloor \gamma\beta\rfloor,\lfloor \gamma^2\beta\rfloor,\ldots\}\] complete?-/

/-
If a monotone sequence of positive integers has infinitely many gaps where the next term is larger than 1 plus the sum of all previous terms, then the sequence of subset sums is not complete (misses infinitely many integers).
-/
lemma not_complete_of_freq_gaps {A : ℕ → ℤ} (h_pos : ∀ n, 0 < A n) (h_mono : Monotone A)
    (h_gap : ∃ᶠ k in Filter.atTop, 1 + ∑ i ∈ Finset.range k, A i < A k) :
    ¬ IsAddCompleteNatSeq' A := by
      -- For each $k$ where the gap condition holds, $1 + \sum_{i<k} A_i$ cannot be formed as a subset sum.
      have h_not_in_subset_sums : ∀ k, 1 + ∑ i ∈ Finset.range k, A i < A k → ¬(1 + ∑ i ∈ Finset.range k, A i ∈ subseqSums' A) := by
        unfold subseqSums'; aesop;
        -- Since $A$ is monotone, all elements in $x$ must be less than $k$. Otherwise, if there's an element in $x$ that's $k$ or larger, the sum would be at least $A k$, which contradicts the gap condition.
        have h_x_lt_k : ∀ i ∈ x, i < k := by
          -- Assume there exists $i \in x$ such that $i \geq k$. Then, since $A$ is monotone, $A i \geq A k$.
          by_contra h_contra
          obtain ⟨i, hi⟩ : ∃ i ∈ x, i ≥ k := by
            aesop;
          linarith [ h_mono hi.2, Finset.single_le_sum ( fun i _ => le_of_lt ( h_pos i ) ) hi.1 ];
        linarith [ show ∑ i ∈ x, A i ≤ ∑ i ∈ Finset.range k, A i from Finset.sum_le_sum_of_subset_of_nonneg ( fun i hi => Finset.mem_range.mpr ( h_x_lt_k i hi ) ) fun _ _ _ => le_of_lt ( h_pos _ ) ];
      bound;
      rw [ Filter.frequently_atTop ] at *;
      cases' Filter.eventually_atTop.1 a with N hN;
      rcases h_gap ( Int.toNat N ) with ⟨ k, hk₁, hk₂ ⟩ ; specialize hN ( 1 + ∑ i ∈ Finset.range k, A i ) ( by linarith [ Int.self_le_toNat N, show ∑ i ∈ Finset.range k, A i ≥ N by linarith [ Int.self_le_toNat N, show ∑ i ∈ Finset.range k, A i ≥ k by exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun _ _ => h_pos _ ) ] ] ) ; aesop

/-
The sum of the first 2k terms of the interleaved sequence is bounded by a geometric series formula.
-/
lemma sum_interleave_le (α β : ℝ) (k : ℕ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
  (∑ i ∈ Finset.range (2 * k), FloorMultiples.interleave α β 2 i : ℝ) ≤ (α + 2 * β) * ((4 : ℝ) ^ k - 1) / 3 := by
    -- Split the sum into even and odd indices.
    have h_split : ∑ i ∈ Finset.range (2 * k), (FloorMultiples.interleave α β 2 i : ℝ) = ∑ j ∈ Finset.range k, (⌊2 ^ (2 * j) * α⌋ : ℝ) + ∑ j ∈ Finset.range k, (⌊2 ^ (2 * j + 1) * β⌋ : ℝ) := by
      -- We can split the sum into two parts: one over even indices and one over odd indices.
      have h_split : Finset.range (2 * k) = Finset.image (fun j => 2 * j) (Finset.range k) ∪ Finset.image (fun j => 2 * j + 1) (Finset.range k) := by
        -- To prove the equality of finite sets, we can show each set is a subset of the other.
        apply Finset.ext
        intro x
        simp [Finset.mem_range, Finset.mem_image];
        exact ⟨ fun h => by rcases Nat.even_or_odd' x with ⟨ c, rfl | rfl ⟩ <;> [ left; right ] <;> exact ⟨ _, by linarith, rfl ⟩, fun h => by rcases h with ( ⟨ c, hc, rfl ⟩ | ⟨ c, hc, rfl ⟩ ) <;> linarith ⟩;
      rw [ h_split, Finset.sum_union ];
      · unfold FloorMultiples.interleave; aesop;
      · -- To prove disjointness, assume there exists an element in both images. This would imply there exist $j$ and $j'$ such that $2j = 2j' + 1$, which is impossible since $2j$ is even and $2j' + 1$ is odd.
        simp [Finset.disjoint_left, Finset.mem_image];
        intros; omega;
    -- Apply the inequalities to the sums and then combine them using the geometric series formula.
    have h_even_odd : ∑ j ∈ Finset.range k, (⌊2 ^ (2 * j) * α⌋ : ℝ) ≤ α * (∑ j ∈ Finset.range k, 4 ^ j) ∧ ∑ j ∈ Finset.range k, (⌊2 ^ (2 * j + 1) * β⌋ : ℝ) ≤ 2 * β * (∑ j ∈ Finset.range k, 4 ^ j) := by
      norm_num [ pow_add, pow_mul, mul_assoc, mul_left_comm, Finset.mul_sum _ _ _ ];
      exact ⟨ Finset.sum_le_sum fun _ _ => by linarith [ Int.floor_le ( 4 ^ ‹_› * α ) ], Finset.sum_le_sum fun _ _ => by linarith [ Int.floor_le ( 2 * ( 4 ^ ‹_› * β ) ) ] ⟩;
    nlinarith [ geom_sum_mul_neg ( 4 : ℝ ) k ]

theorem erdos_354.parts.i : (∀ᵉ (α > 0) (β > 0), Irrational (α / β) →
    IsAddCompleteNatSeq' (FloorMultiples.interleave α β 2)) ↔ false := by
  -- Let's choose α = 1 and β = sqrt(2). We need to show that the sequence has infinitely many gaps.
  have h_gaps : ∃ᶠ m in Filter.atTop, 1 + ∑ i ∈ Finset.range (2 * m + 1), FloorMultiples.interleave 1 (Real.sqrt 2) 2 i < FloorMultiples.interleave 1 (Real.sqrt 2) 2 (2 * m + 1) := by
    -- We show that the sum of the terms up to $A_{2m}$ is approximately $(1 + 2\sqrt{2})/3 (4^m) + 4^m \approx 2.276 \cdot 4^m$.
    have h_sum_approx : ∀ m : ℕ, (∑ i ∈ Finset.range (2 * m + 1), FloorMultiples.interleave 1 (Real.sqrt 2) 2 i : ℝ) ≤ (1 + 2 * Real.sqrt 2) * (4 ^ m - 1) / 3 + 4 ^ m := by
      -- Apply the sum_interleave_le lemma to bound the sum.
      have h_sum_bound : ∀ m : ℕ, (∑ i ∈ Finset.range (2 * m), FloorMultiples.interleave 1 (Real.sqrt 2) 2 i : ℝ) ≤ (1 + 2 * Real.sqrt 2) * ((4 : ℝ) ^ m - 1) / 3 := by
        intro m;
        convert sum_interleave_le 1 ( Real.sqrt 2 ) m ( by norm_num ) ( by positivity ) using 1;
      norm_num [ Finset.sum_range_succ ];
      intro m; gcongr;
      · exact h_sum_bound m;
      · unfold FloorMultiples.interleave;
        unfold FloorMultiples; norm_num [ pow_mul ] ;
        exact Int.floor_le _;
    -- Since $A_{2m+1} \approx 2.828 \cdot 4^m$, there is a gap.
    have h_gap_approx : ∀ m : ℕ, FloorMultiples.interleave 1 (Real.sqrt 2) 2 (2 * m + 1) ≥ 2 * Real.sqrt 2 * 4 ^ m - 1 := by
      norm_num [ FloorMultiples.interleave, pow_succ', pow_mul ];
      exact fun m => le_trans ( by norm_num [ pow_add, pow_mul ] ; ring_nf; norm_num ) ( add_le_add_right ( Int.sub_one_lt_floor _ |> le_of_lt ) _ );
    -- By combining the approximations, we can see that for sufficiently large $m$, the gap between $A_{2m+1}$ and the sum of the terms up to $A_{2m}$ becomes significant.
    have h_gap_significant : ∃ M : ℕ, ∀ m ≥ M, 1 + (∑ i ∈ Finset.range (2 * m + 1), FloorMultiples.interleave 1 (Real.sqrt 2) 2 i : ℝ) < FloorMultiples.interleave 1 (Real.sqrt 2) 2 (2 * m + 1) := by
      use 100;
      intro m hm; nlinarith [ h_sum_approx m, h_gap_approx m, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 4 ) hm ] ;
    norm_cast at * ; aesop;
    exact Filter.frequently_atTop.mpr fun m => ⟨ _, le_max_left _ _, h _ ( le_max_right _ _ ) ⟩;
  aesop;
  use 1, by norm_num, Real.sqrt 2, by norm_num, by simpa using irrational_sqrt_two;
  apply not_complete_of_freq_gaps;
  · unfold FloorMultiples.interleave; aesop;
    · exact Int.floor_pos.mpr ( by exact one_le_mul_of_one_le_of_one_le ( one_le_pow₀ ( by norm_num ) ) ( by norm_num ) );
    · exact Int.floor_pos.mpr ( by exact one_le_mul_of_one_le_of_one_le ( one_le_pow₀ ( by norm_num ) ) ( Real.le_sqrt_of_sq_le ( by norm_num ) ) );
  · refine' monotone_nat_of_le_succ fun n => _;
    unfold FloorMultiples.interleave; aesop;
    · omega;
    · unfold FloorMultiples; norm_num [ pow_succ', h ];
      exact Int.floor_mono <| by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, pow_pos ( zero_lt_two' ℝ ) n ] ;
    · unfold FloorMultiples; norm_num [ pow_succ', mul_assoc ];
      exact Int.floor_mono <| by nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, pow_pos ( zero_lt_two' ℝ ) n ] ;
    · omega;
  · rw [ Filter.frequently_atTop ] at *;
    exact fun n => by obtain ⟨ m, hm₁, hm₂ ⟩ := h_gaps n; exact ⟨ 2 * m + 1, by linarith, hm₂ ⟩ ;
