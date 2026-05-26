/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
/- Original license: Apache 2.0. Note: This file has been modified. -/
/-
This is a Lean formalization of a solution to Erdős Problem 268.
https://www.erdosproblems.com/forum/thread/268

Informal authors:
- Vjekoslav Kovač

Formal authors:
- Aristotle
- Matteo Del Vecchio

URLs:
- https://www.erdosproblems.com/forum/thread/268#post-5359
- https://gist.githubusercontent.com/madeve-unipi/62a8f68cdb4864b85b81a6752dcb0aa4/raw/5793aaa51089c25c37d8d63f60540367f6abe506/Erdos268.lean
- https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/268.lean
-/
/-
Released under Apache 2.0 license.
Authors: Matteo Del Vecchio, Aristotle (Harmonic)
-/

import Mathlib.Algebra.Order.Ring.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.CategoryTheory.Category.Basic

namespace Erdos268

/-! # The Erdős–Graham Problem on Harmonic Subseries Points

We prove that the set of points
  X = { (∑_{n∈A} 1/n, ∑_{n∈A} 1/(n+1), ∑_{n∈A} 1/(n+2)) :
        A ⊆ ℕ⁺ infinite, ∑_{n∈A} 1/n < ∞ }
has non-empty interior, following Kovač's answer (2024) to a question of Erdős and Graham (1980).

## Reference
V. Kovač, "On the set of points represented by harmonic subseries"
-/

open Set Filter Topology Matrix
open scoped BigOperators

/-! ## Main Definition -/

/-- The set of points representable by harmonic subseries. -/
def harmonicSubseriesSet : Set (Fin 3 → ℝ) :=
  { p | ∃ A : Set ℕ, A.Infinite ∧ (∀ n ∈ A, 0 < n) ∧
    Summable (fun (n : A) => (1 : ℝ) / (n : ℕ)) ∧
    ∀ i : Fin 3, p i = ∑' (n : A), 1 / (((n : ℕ) : ℝ) + ((i : ℕ) : ℝ)) }

/-! ## Arithmetic Setup (Section 3 of Kovač) -/

/-- The change-of-basis matrix from equation (6). -/
def M_mat : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 3, -4, 1; 1, -2, 1]

/-- The inverse of `M_mat`. -/
noncomputable def M_inv : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 1, -(1/2), 1/2; 1, -1, 2]

/-- `S_j` sets indexed by `j : Fin 3`. -/
def S₁ : Finset ℕ := {45, 72, 144, 160, 432, 480}
def T₁ : Finset ℕ := {48, 60, 120, 720, 1440, 4320}
def S₂ : Finset ℕ := {176, 220, 2640}
def T₂ : Finset ℕ := {165, 264, 1320}
def S₃ : Finset ℕ := {70, 210, 420}
def T₃ : Finset ℕ := {84, 105}

def Ssets : Fin 3 → Finset ℕ := ![S₁, S₂, S₃]
def Tsets : Fin 3 → Finset ℕ := ![T₁, T₂, T₃]

def m_const : ℕ := 2310

noncomputable def c_coeff : Fin 3 → ℝ := ![1/180, 1/348480, 1/1029000]

/-! ### Verified arithmetic properties -/

lemma M_inv_mul_mat : M_inv * M_mat = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [M_mat, M_inv, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

lemma M_mat_mul_inv : M_mat * M_inv = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
  simp [M_mat, M_inv, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

lemma c_coeff_pos : ∀ j : Fin 3, 0 < c_coeff j := by
  intro j; fin_cases j <;> simp [c_coeff]

lemma primeFactors_union_dvd_m_const :
    ∀ a ∈ S₁ ∪ T₁ ∪ S₂ ∪ T₂ ∪ S₃ ∪ T₃,
      ∀ p ∈ Nat.primeFactors a, p ∣ m_const := by
  intro a ha p hp
  have ha_dvd : a ∣ m_const ^ 5 := by
    fin_cases ha <;> norm_num [m_const]
  exact (Nat.prime_of_mem_primeFactors hp).dvd_of_dvd_pow
    ((Nat.dvd_of_mem_primeFactors hp).trans ha_dvd)

set_option linter.flexible false in
/-- Every positive integer has at most one representation as `a * (k² * m + 1)`
  for `a ∈ U` and `k ∈ ℕ`, because all prime factors of `a` divide `m`,
  hence `gcd(a, k² * m + 1) = 1`. -/
lemma unique_representation (a₁ a₂ k₁ k₂ : ℕ)
    (ha₁ : a₁ ∈ S₁ ∪ T₁ ∪ S₂ ∪ T₂ ∪ S₃ ∪ T₃)
    (ha₂ : a₂ ∈ S₁ ∪ T₁ ∪ S₂ ∪ T₂ ∪ S₃ ∪ T₃)
    (heq : a₁ * (k₁ ^ 2 * m_const + 1) = a₂ * (k₂ ^ 2 * m_const + 1)) :
    a₁ = a₂ ∧ k₁ = k₂ := by
  have h_coprime : Nat.gcd a₁ (k₂ ^ 2 * m_const + 1) = 1 ∧
      Nat.gcd a₂ (k₁ ^ 2 * m_const + 1) = 1 := by
    have h : ∀ a ∈ S₁ ∪ T₁ ∪ S₂ ∪ T₂ ∪ S₃ ∪ T₃, ∀ k : ℕ,
        Nat.gcd a (k ^ 2 * m_const + 1) = 1 := by
      intro a ha k
      have hpf : ∀ p, Nat.Prime p → p ∣ a → p ∣ m_const := by
        intro p hp hpa
        have : p ∈ Nat.primeFactors a :=
          Nat.mem_primeFactors.mpr ⟨hp, hpa, by fin_cases ha <;> trivial⟩
        exact primeFactors_union_dvd_m_const a ha p ‹_›
      exact Nat.coprime_of_dvd' fun p pp dp dk => by
        simpa [Nat.dvd_add_right (dvd_mul_of_dvd_right (hpf p pp dp) _)] using dk
    exact ⟨h a₁ ha₁ k₂, h a₂ ha₂ k₁⟩
  have h_eq_a : a₁ = a₂ :=
    Nat.dvd_antisymm
      (Nat.Coprime.dvd_of_dvd_mul_right h_coprime.1 <| heq ▸ dvd_mul_right _ _)
      (Nat.Coprime.dvd_of_dvd_mul_right h_coprime.2 <| heq.symm ▸ dvd_mul_right _ _)
  simp_all +decide [m_const]
  exact heq.resolve_right (by rintro rfl; contradiction)

/-! ## The Set A Construction

Given game choices `ε : ℕ → Fin 3 → Bool` (where `ε k j = true` means Alice
includes the term at step `k` in coordinate `j`), we construct the set
`A = ⋃_{k≥K, j} (ε-dependent union of S_j or T_j scaled by k²m+1)`. -/

/-- The set A constructed from game choices, starting from round K. -/
def constructA (K : ℕ) (ε : ℕ → Fin 3 → Bool) : Set ℕ :=
  ⋃ k ≥ K, ⋃ j : Fin 3,
    if ε k j then
      ↑((Ssets j).image (· * (k ^ 2 * m_const + 1)))
    else
      ↑((Tsets j).image (· * (k ^ 2 * m_const + 1)))

/-- All elements of `constructA` are positive. -/
lemma constructA_pos (K : ℕ) (ε : ℕ → Fin 3 → Bool) :
    ∀ n ∈ constructA K ε, 0 < n := by
  intro n hn;
  /- By definition of constructA, there exists some k ≥ K and j such that n is in the image of S_j
    or T_j scaled by k² * m_const + 1.-/
  obtain ⟨k, hk_ge_K, j, hj⟩ : ∃ k ≥ K, ∃ j : Fin 3,
    n ∈ if ε k j then ↑((Ssets j).image (· * (k ^ 2 * m_const + 1)))
    else ↑((Tsets j).image (· * (k ^ 2 * m_const + 1))) := by
    unfold constructA at hn; aesop;
  split_ifs at hj <;>
    obtain ⟨ x, hx, rfl ⟩ := Finset.mem_image.mp hj <;>
    fin_cases j <;>
    fin_cases hx <;>
    norm_num [ m_const ]

set_option linter.flexible false in
/-- The set `constructA` is infinite (since each k contributes at least 2 elements,
and different k's give different elements by unique representation). -/
lemma constructA_infinite (K : ℕ) (ε : ℕ → Fin 3 → Bool) :
    (constructA K ε).Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_;
  intro a
  obtain ⟨k, hk⟩ : ∃ k ≥ K, a < k^2 * m_const + 1 :=
    ⟨ a + K + 1, by linarith, by
      nlinarith [
        Nat.mul_le_mul_left ( a + K + 1 ) ( show m_const ≥ 1 by decide )]⟩;
  -- Choose $j$ such that $a < k^2 * m_const + 1$.
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, a < (if ε k j then (Ssets j).min' (by
  fin_cases j <;> decide) else (Tsets j).min' (by
  fin_cases j <;> decide)) * (k ^ 2 * m_const + 1) := by
    use 0; split_ifs <;> simp_all +decide [ Finset.min' ] ;
    · have hS : ( Ssets 0 |> Finset.inf' ) ( by decide ) ( fun x => x ) > 0 := by
        decide
      exact lt_of_le_of_lt hk.2 ( by nlinarith [ hS ] );
    · have hT :
          0 <
            ( Tsets 0 |> Finset.inf' )
              ( Finset.nonempty_of_ne_empty ( by decide ) ) fun x => x := by
        decide
      exact lt_of_le_of_lt hk.2 ( by nlinarith [ hT ] )
  generalize_proofs at *;
  refine ⟨ _, ?_, hj ⟩
  refine Set.mem_iUnion₂.mpr ⟨ k, hk.1, Set.mem_iUnion.mpr ⟨ j, ?_ ⟩ ⟩
  split_ifs <;> exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.min'_mem _ _))

set_option linter.flexible false in
/-
The sum `∑_{n ∈ A} 1/n` converges, because each term is O(1/k²).
-/
lemma constructA_summable (K : ℕ) (ε : ℕ → Fin 3 → Bool) :
    Summable (fun (n : constructA K ε) => (1 : ℝ) / (n : ℕ)) := by
  /- Let's choose any $n \in \text{constructA } K \epsilon$. By definition, there exists $k \geq K$
    and $j$ such that $n = a * (k^2 * m_const + 1)$ where $a \in S_j$ or $a \in T_j$.-/
  have h_bound :
      ∀ n ∈ constructA K ε,
        ∃ k ≥ K, ∃ a ∈ S₁ ∪ T₁ ∪ S₂ ∪ T₂ ∪ S₃ ∪ T₃,
          n = a * (k^2 * m_const + 1) := by
    intro n hn; unfold constructA at hn; simp_all +decide;
    rcases hn with ⟨ k, hk, j, hj ⟩ ; split_ifs at hj <;> simp_all +decide [ Ssets, Tsets ] ;
    · fin_cases j <;> aesop;
    · fin_cases j <;> aesop;
  -- By comparison, it suffices to show that the corresponding double series converges.
  suffices h_summable :
      Summable (fun (p : ℕ × ℕ) =>
        if p.1 ≥ K ∧ p.2 ∈ S₁ ∪ T₁ ∪ S₂ ∪ T₂ ∪ S₃ ∪ T₃ then
          (1 : ℝ) / (p.2 * (p.1^2 * m_const + 1))
        else 0) by
    refine summable_of_sum_le
      (c := ∑' p : ℕ × ℕ,
        if p.1 ≥ K ∧ p.2 ∈ S₁ ∪ T₁ ∪ S₂ ∪ T₂ ∪ S₃ ∪ T₃ then
          ( 1 : ℝ ) / ( p.2 * ( p.1 ^ 2 * m_const + 1 ) )
        else 0) ?_ ?_
    · exact fun _ => by positivity;
    · intro u;
      -- Map each element `n ∈ u` to a pair `(k, a)` with the represented value.
      have h_map :
          ∃ v : Finset (ℕ × ℕ),
            (∀ p ∈ v, p.1 ≥ K ∧ p.2 ∈ S₁ ∪ T₁ ∪ S₂ ∪ T₂ ∪ S₃ ∪ T₃) ∧
              (∑ x ∈ u, (1 : ℝ) / x) ≤
                (∑ p ∈ v, (1 : ℝ) / (p.2 * (p.1^2 * m_const + 1))) := by
        choose! k hk a ha h using h_bound;
        refine ⟨
          Finset.image ( fun x : ↑ ( constructA K ε ) => ( k x, a x ) ) u,
          ?_, ?_ ⟩ <;>
          norm_num;
        · grind;
        · rw [ Finset.sum_image ];
          · gcongr;
            rw [ ← mul_inv, inv_le_inv₀ ] <;> norm_cast <;> norm_num;
            · grind;
            · exact constructA_pos K ε _ ( Subtype.mem _ );
            · rename_i i hi;
              have := ha i i.2;
              exact Nat.pos_of_ne_zero fun hi' => by simp +decide [ hi' ] at this;
          · intro x hx y hy; have := h x x.2; have := h y y.2; norm_num at *;
            grind;
      obtain ⟨ v, hv₁, hv₂ ⟩ := h_map;
      refine le_trans hv₂ (le_trans ?_ (Summable.sum_le_tsum v ?_ h_summable))
      · exact Finset.sum_le_sum fun p hp => by specialize hv₁ p hp; aesop
      · exact fun _ _ => by positivity
  -- We can bound the sum by considering the sum over $k$ and the sum over $a$ separately.
  have h_bound :
      ∀ k ≥ K,
        (∑' a : ℕ,
          if a ∈ S₁ ∪ T₁ ∪ S₂ ∪ T₂ ∪ S₃ ∪ T₃ then
            (1 : ℝ) / (a * (k^2 * m_const + 1))
          else 0) ≤
        (∑' a : ℕ,
          if a ∈ S₁ ∪ T₁ ∪ S₂ ∪ T₂ ∪ S₃ ∪ T₃ then (1 : ℝ) / a else 0) /
          (k^2 * m_const + 1) := by
    intro k hk; rw [ ← tsum_div_const ] ; refine Summable.tsum_le_tsum ?_ ?_ ?_;
    · intro i; split_ifs <;> norm_num [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ] ;
    · exact summable_of_ne_finset_zero (s := S₁ ∪ T₁ ∪ S₂ ∪ T₂ ∪ S₃ ∪ T₃) fun b hb => if_neg hb
    · exact Summable.mul_right _ (summable_of_ne_finset_zero
        (s := S₁ ∪ T₁ ∪ S₂ ∪ T₂ ∪ S₃ ∪ T₃) fun n hn => if_neg hn)
  have h_summable :
      Summable (fun k : ℕ =>
        (∑' a : ℕ,
          if a ∈ S₁ ∪ T₁ ∪ S₂ ∪ T₂ ∪ S₃ ∪ T₃ then (1 : ℝ) / a else 0) /
          (k^2 * m_const + 1)) := by
    refine Summable.mul_left _ ?_;
    rw [ ← summable_nat_add_iff 1 ];
    exact Summable.of_nonneg_of_le
      ( fun n => by positivity )
      ( fun n => by
        rw [ inv_le_comm₀ ] <;>
          norm_num <;>
          ring_nf <;>
          nlinarith [
            show ( m_const : ℝ ) ≥ 1 by
              exact_mod_cast Nat.one_le_iff_ne_zero.mpr <| by decide ] )
      <| summable_nat_add_iff 1 |>.2
      <| Real.summable_one_div_nat_pow.2 one_lt_two;
  rw [ summable_prod_of_nonneg ];
  · constructor
    · exact fun k => summable_of_ne_finset_zero
        (s := S₁ ∪ T₁ ∪ S₂ ∪ T₂ ∪ S₃ ∪ T₃) (fun b hb => by aesop)
    · rw [← summable_nat_add_iff K]
      exact Summable.of_nonneg_of_le (fun n => tsum_nonneg fun _ => by positivity)
        (fun n => by simpa using h_bound (n + K) (by linarith))
        (h_summable.comp_injective (add_left_injective K))
  · exact fun _ => by positivity;

/-! ## Topological Lemma: Invertible Linear Map Preserves Interior -/

/-- `M_inv.mulVec` is a continuous linear map. -/
lemma M_inv_mulVec_continuous : Continuous (M_inv.mulVec : (Fin 3 → ℝ) → (Fin 3 → ℝ)) := by
  fun_prop

/-
If a nonempty open set maps into `harmonicSubseriesSet` via `M_inv.mulVec`,
then `harmonicSubseriesSet` contains a ball.
-/
lemma image_open_contains_ball
    (Q : Set (Fin 3 → ℝ)) (hQ_open : IsOpen Q) (hQ_ne : Q.Nonempty)
    (hQ_sub : ∀ q ∈ Q, M_inv.mulVec q ∈ harmonicSubseriesSet) :
    ∃ (center : Fin 3 → ℝ) (radius : ℝ), 0 < radius ∧
    Metric.ball center radius ⊆ harmonicSubseriesSet := by
  -- Since $M_inv.mulVec$ is a homeomorphism, its image of $Q$ under this map is open.
  have hQ_image_open : IsOpen (M_inv.mulVec '' Q) := by
    convert hQ_open.preimage ( show Continuous fun q => M_mat.mulVec q from ?_ ) using 1;
    · ext; constructor <;> intro h;
      · obtain ⟨ q, hq, rfl ⟩ := h; simp_all +decide [ M_mat_mul_inv ]
      · use M_mat.mulVec ‹_›;
        simp_all +decide [ M_inv_mul_mat ]
    · fun_prop;
  exact Exists.elim ( hQ_ne ) fun x hx => by
    rcases Metric.mem_nhds_iff.1
        ( hQ_image_open.mem_nhds ( Set.mem_image_of_mem _ hx ) ) with
      ⟨ ε, εpos, hε ⟩
    exact ⟨ _, ε, εpos, hε.trans ( Set.image_subset_iff.2 hQ_sub ) ⟩ ;
/-! # One-Dimensional Convergence Game

We formalize the "convergence game" from Kovač's paper (Section 4, Claims 1 and 2) starting
from the one-dimensional version of the game.
Alice uses a cautious greedy strategy to converge to a target value `q`, while Bob
introduces bounded perturbations. The key result is that under appropriate
domination conditions, Alice's strategy always converges to `q`.

## Overview

The game proceeds in rounds `k = 0, 1, 2, …`. At each round:
- **Alice** adds `a(k)` to the running sum if doing so keeps `x + 3a(k) ≤ q`
  (the "cautious greedy" condition), and does nothing otherwise.
- **Bob** applies a perturbation `δ(k)` bounded by an error sequence `e(k)`.

The main theorem `game_converges_to_target` shows that if the main terms `a(k)`
and error bounds `e(k)` satisfy appropriate domination conditions, the game
sequence converges to `q` regardless of Bob's moves.
-/

noncomputable section

/-! ## Definition of the game sequence -/

/-- The sequence produced by Alice's cautious greedy strategy in the 1D convergence game.
At each step `k`, Alice adds `a k` to the current value if `x_k + 3 * a k ≤ q`,
then Bob perturbs by `δ k`. -/
def gameSeq (a : ℕ → ℝ) (q : ℝ) (δ : ℕ → ℝ) (x₀ : ℝ) : ℕ → ℝ
  | 0 => x₀
  | k + 1 =>
    let xk := gameSeq a q δ x₀ k
    xk + (if xk + 3 * a k ≤ q then a k else 0) + δ k

/-- Alice's choice at step `k`: whether to include the main term.
`aliceChoice a q δ x₀ k` holds iff Alice adds `a k` at step `k`. -/
def aliceChoice (a : ℕ → ℝ) (q : ℝ) (δ : ℕ → ℝ) (x₀ : ℝ) (k : ℕ) : Prop :=
  gameSeq a q δ x₀ k + 3 * a k ≤ q

instance (a : ℕ → ℝ) (q : ℝ) (δ : ℕ → ℝ) (x₀ : ℝ) (k : ℕ) :
    Decidable (aliceChoice a q δ x₀ k) :=
  inferInstanceAs (Decidable (_ ≤ _))

@[simp] lemma gameSeq_zero (a : ℕ → ℝ) (q : ℝ) (δ : ℕ → ℝ) (x₀ : ℝ) :
    gameSeq a q δ x₀ 0 = x₀ := rfl

lemma gameSeq_succ (a : ℕ → ℝ) (q : ℝ) (δ : ℕ → ℝ) (x₀ : ℝ) (k : ℕ) :
    gameSeq a q δ x₀ (k + 1) =
    gameSeq a q δ x₀ k +
      (if aliceChoice a q δ x₀ k then a k else 0) + δ k := by
  simp [gameSeq, aliceChoice]

/-! ## Basic step bounds

These lemmas express how the game sequence changes in a single step,
depending on Alice's decision. -/

/-- In Case 1 (Alice includes), the step is `a k + δ k`. -/
lemma gameSeq_step_include (a : ℕ → ℝ) (q : ℝ) (δ : ℕ → ℝ) (x₀ : ℝ) (k : ℕ)
    (h : aliceChoice a q δ x₀ k) :
    gameSeq a q δ x₀ (k + 1) - gameSeq a q δ x₀ k = a k + δ k := by
  rw [gameSeq_succ, if_pos h]; ring

/-- In Case 2 (Alice skips), the step is just `δ k`. -/
lemma gameSeq_step_skip (a : ℕ → ℝ) (q : ℝ) (δ : ℕ → ℝ) (x₀ : ℝ) (k : ℕ)
    (h : ¬aliceChoice a q δ x₀ k) :
    gameSeq a q δ x₀ (k + 1) - gameSeq a q δ x₀ k = δ k := by
  rw [gameSeq_succ, if_neg h]; ring

/-- Each step changes the game value by at most `a k + |δ k|`.
Used to establish summability of step sizes, yielding the Cauchy property. -/
lemma gameSeq_step_abs_bound (a : ℕ → ℝ) (q : ℝ) (δ : ℕ → ℝ) (x₀ : ℝ) (k : ℕ)
    (ha : 0 ≤ a k) :
    |gameSeq a q δ x₀ (k + 1) - gameSeq a q δ x₀ k| ≤ a k + |δ k| := by
  by_cases h : aliceChoice a q δ x₀ k
  · rw [gameSeq_step_include _ _ _ _ _ h, abs_le]
    constructor <;> cases abs_cases (δ k) <;> linarith
  · rw [gameSeq_step_skip _ _ _ _ _ h]
    linarith [abs_nonneg (δ k)]

/-! ## Telescoping and Cauchy property

We show the game sequence is Cauchy (hence convergent) when the main terms
and error bounds are summable. -/

/-- The game sequence converges when the main terms `a` and error bounds `e`
are both summable. The proof telescopes the steps and uses absolute summability. -/
lemma gameSeq_convergent
    (a e : ℕ → ℝ) (q x₀ : ℝ)
    (ha : ∀ k, 0 ≤ a k)
    (h_summ_a : Summable a)
    (h_summ_e : Summable e)
    (δ : ℕ → ℝ) (hδ : ∀ k, |δ k| ≤ e k) :
    ∃ L : ℝ, Tendsto (gameSeq a q δ x₀) atTop (nhds L) := by
  have h_step_summable : Summable (fun k =>
      |gameSeq a q δ x₀ (k + 1) - gameSeq a q δ x₀ k|) :=
    .of_nonneg_of_le (fun k => abs_nonneg _)
      (fun k => gameSeq_step_abs_bound a q δ x₀ k (ha k))
      (h_summ_a.add (.of_nonneg_of_le (fun k => abs_nonneg _) hδ h_summ_e))
  have h_cauchy : CauchySeq (fun n =>
      ∑ k ∈ Finset.range n, (gameSeq a q δ x₀ (k + 1) - gameSeq a q δ x₀ k)) :=
    h_step_summable.of_abs.hasSum.tendsto_sum_nat.cauchySeq
  exact ⟨_, by
    convert h_cauchy.tendsto_limUnder.add_const (gameSeq a q δ x₀ 0) using 1
    ext n; rw [Finset.sum_range_sub (fun k => gameSeq a q δ x₀ k)]; ring⟩

/-! ## Claims 1 and 2

These are the heart of the convergence argument. Claim 1 shows Alice includes
infinitely often (otherwise the sequence stays too far from `q`). Claim 2
shows Alice skips infinitely often (otherwise the sequence overshoots `q`).
Together they squeeze the limit to exactly `q`. -/

/-- Splitting the error tail sum: `∑' e(L+l) = e(L) + ∑' e(L+l+1)`. Separates
the immediate error from the future error when analyzing Alice's decisions. -/
lemma error_tail_split (e : ℕ → ℝ) (h_summ_e : Summable e) (L : ℕ) :
    ∑' l, e (L + l) = e L + ∑' l, e (L + l + 1) := by
  rw [Summable.tsum_eq_zero_add, add_comm]
  · simp [add_assoc, add_comm]
  · exact h_summ_e.comp_injective fun a b h => by simpa using h

/-- If Alice never includes, the game sequence equals x₀ plus cumulative perturbations. -/
lemma gameSeq_no_include (a : ℕ → ℝ) (q : ℝ) (δ : ℕ → ℝ) (x₀ : ℝ)
    (h : ∀ k, ¬aliceChoice a q δ x₀ k) :
    ∀ k, gameSeq a q δ x₀ k = x₀ + ∑ i ∈ Finset.range k, δ i := by
  intro k
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ, gameSeq_succ, if_neg (h _)]; linarith

/-- For n > L where L is the last inclusion, the sequence is determined by perturbations. -/
lemma gameSeq_after_last_include (a : ℕ → ℝ) (q : ℝ) (δ : ℕ → ℝ) (x₀ : ℝ) (L : ℕ)
    (hL : ∀ k > L, ¬aliceChoice a q δ x₀ k) :
    ∀ n > L, gameSeq a q δ x₀ n =
      gameSeq a q δ x₀ (L + 1) + ∑ i ∈ Finset.Ico (L + 1) n, δ i := by
  intro n hn; induction hn <;> simp_all +decide [ Finset.sum_Ico_succ_top, gameSeq_succ ] ;
  ring

/-- **Claim 1** (Kovač, Section 4): Alice includes the term infinitely often.

If Alice eventually stops including, let `L` be the last inclusion step.
Then for `n > L`, the sequence is driven by perturbations only. The error
domination hypothesis `∑' e(k+l) < a(k)` ensures that the perturbations
cannot push the sequence far enough from `q` to prevent future inclusions,
yielding a contradiction. -/
lemma game_infinitely_many_inclusions
    (a e : ℕ → ℝ) (q x₀ : ℝ)
    (h_summ_a : Summable a)
    (h_summ_e : Summable e)
    (he_nonneg : ∀ k, 0 ≤ e k)
    (h_error_dom : ∀ k, ∑' l, e (k + l) < a k)
    (hq_lo : x₀ + a 0 ≤ q)
    (δ : ℕ → ℝ) (hδ : ∀ k, |δ k| ≤ e k) :
    {k | aliceChoice a q δ x₀ k}.Infinite := by
  by_contra h_contra;
  -- Step 1: show there is some `L` where Alice includes.
  -- Otherwise `gameSeq(k) = x₀ + ∑ δ`, whose limiting inequalities contradict `hq_lo`.
  obtain ⟨L, hL⟩ : ∃ L, aliceChoice a q δ x₀ L := by
    by_cases h_no_choice : ∀ k, ¬aliceChoice a q δ x₀ k;
    · have h_limit :
          Filter.Tendsto (fun k => gameSeq a q δ x₀ k + 3 * a k)
            Filter.atTop (nhds (x₀ + ∑' k, δ k)) := by
        have h_limit :
            Filter.Tendsto (fun k => gameSeq a q δ x₀ k)
              Filter.atTop (nhds (x₀ + ∑' k, δ k)) := by
          have h_limit :
              Filter.Tendsto (fun k => x₀ + ∑ i ∈ Finset.range k, δ i)
                Filter.atTop (nhds (x₀ + ∑' k, δ k)) := by
            exact tendsto_const_nhds.add
              ( Summable.hasSum ( show Summable δ from
                  Summable.of_norm <| by
                    exact Summable.of_nonneg_of_le
                      ( fun k => abs_nonneg _ ) ( fun k => hδ k ) h_summ_e )
                |> HasSum.tendsto_sum_nat );
          exact h_limit.congr fun k => by rw [ gameSeq_no_include a q δ x₀ h_no_choice ] ;
        simpa using h_limit.add ( tendsto_const_nhds.mul h_summ_a.tendsto_atTop_zero );
      have h_limit_ge_q : x₀ + ∑' k, δ k ≥ q := by
        exact le_of_tendsto_of_tendsto' tendsto_const_nhds h_limit fun k =>
          le_of_not_gt fun hk => h_no_choice k <| by
            unfold aliceChoice
            linarith;
      have h_abs_sum_le_sum_e : |∑' k, δ k| ≤ ∑' k, e k := by
        calc |∑' k, δ k| = ‖∑' k, δ k‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑' k, ‖δ k‖ := norm_tsum_le_tsum_norm
            (Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hδ k) h_summ_e)
        _ ≤ ∑' k, e k := Summable.tsum_le_tsum (fun k => hδ k)
            (Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => hδ k) h_summ_e)
            h_summ_e
      have := h_error_dom 0; norm_num at this; linarith [ abs_le.mp h_abs_sum_le_sum_e ] ;
    · exact not_forall_not.mp h_no_choice;
  -- Let $L$ be the largest index where Alice includes.
  obtain ⟨L, hL⟩ : ∃ L, (∀ k > L, ¬aliceChoice a q δ x₀ k) ∧ aliceChoice a q δ x₀ L := by
    exact ⟨
      Finset.max' ( Set.Finite.toFinset ( Classical.not_not.mp h_contra ) )
        ⟨ L, by simpa using hL ⟩,
      fun k hk => fun hk' =>
        not_lt_of_ge ( Finset.le_max' _ _ <| by simpa using hk' ) hk,
      by
        simpa using Finset.max'_mem
          ( Set.Finite.toFinset ( Classical.not_not.mp h_contra ) )
          ⟨ L, by simpa using hL ⟩ ⟩;
  -- For n > L, the sequence is determined by perturbations alone.
  have h_gameSeq_after_last_include := gameSeq_after_last_include a q δ x₀ L hL.1
  -- Step 3: gameSeq(L+1) ≤ q - 2a(L) + e(L) (Alice included at L, |δ L| ≤ e L).
  have h_gameSeq_L1 : gameSeq a q δ x₀ (L + 1) ≤ q - 2 * a L + e L := by
    rw [ gameSeq_succ ];
    rw [ if_pos hL.2 ];
    linarith [ abs_le.mp ( hδ L ), show gameSeq a q δ x₀ L + 3 * a L ≤ q from hL.2 ];
  -- Step 4: Find N > L with 3a(N) small: use h_summ_a.tendsto_atTop_zero.
  obtain ⟨N, hN⟩ : ∃ N > L, 3 * a N < a L - ∑' l, e (L + l + 1) := by
    have h_lim_zero : Filter.Tendsto (fun n => 3 * a n) Filter.atTop (nhds 0) := by
      simpa using h_summ_a.tendsto_atTop_zero.const_mul 3;
    have := h_lim_zero.eventually ( gt_mem_nhds <| show 0 < a L - ∑' l, e ( L + l + 1 ) from ?_ );
    · rw [ Filter.eventually_atTop ] at this
      rcases this with ⟨ N, hN ⟩
      exact ⟨ N + L + 1, by linarith, hN _ <| by linarith ⟩ ;
    · have := h_error_dom L;
      rw [ Summable.tsum_eq_zero_add ] at this;
      · linarith! [ he_nonneg L ];
      · exact h_summ_e.comp_injective ( add_right_injective L );
  -- Step 5: bound |∑ δ over Ico| ≤ ∑ e over Ico ≤ ∑' e(L+l+1).
  have h_sum_delta_bound : |∑ i ∈ Finset.Ico (L + 1) N, δ i| ≤ ∑' l, e (L + l + 1) := by
    calc |∑ i ∈ Finset.Ico (L + 1) N, δ i|
        ≤ ∑ i ∈ Finset.Ico (L + 1) N, |δ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Ico (L + 1) N, e i := Finset.sum_le_sum fun i _ => hδ i
      _ ≤ _ := by
        rw [Finset.sum_Ico_eq_sum_range]
        simpa only [add_right_comm] using Summable.sum_le_tsum (Finset.range (N - (L + 1)))
          (fun _ _ => he_nonneg _)
          (h_summ_e.comp_injective (by intros m n h; simpa using h))
  -- Therefore, gameSeq(N) + 3a(N) ≤ q, meaning aliceChoice at N holds, contradiction.
  have h_contradiction : gameSeq a q δ x₀ N + 3 * a N ≤ q := by
    linarith [
      h_gameSeq_after_last_include N hN.1,
      abs_le.mp h_sum_delta_bound,
      show ∑' l : ℕ, e ( L + l ) =
          e L + ∑' l : ℕ, e ( L + l + 1 ) from
        error_tail_split e h_summ_e L,
      h_error_dom L ];
  exact hL.1 N hN.1 h_contradiction

/-- If Alice always includes from step `L+1` onward (and skipped at `L`), the game
sequence telescopes as `gameSeq(L) + δ(L) + ∑_{k<N-L-1} (a(L+1+k) + δ(L+1+k))`.
This structural decomposition is the key input for Claim 2. -/
lemma gameSeq_include_run (a : ℕ → ℝ) (q : ℝ) (δ : ℕ → ℝ) (x₀ : ℝ) (L : ℕ)
    (hL_skip : ¬aliceChoice a q δ x₀ L)
    (hL_last : ∀ k, L < k → aliceChoice a q δ x₀ k) (N : ℕ) (hN : L < N) :
    gameSeq a q δ x₀ N = gameSeq a q δ x₀ L + δ L +
      ∑ k ∈ Finset.range (N - L - 1), (a (L + 1 + k) + δ (L + 1 + k)) := by
  induction hN with
  | refl => simp [gameSeq_succ, if_neg hL_skip]
  | @step N hN ih =>
    have hN' : L + 1 ≤ N := hN
    rw [show gameSeq a q δ x₀ (N + 1) = gameSeq a q δ x₀ N + a N + δ N from
          by rw [gameSeq_succ, if_pos (hL_last N hN)],
        ih, show N + 1 - L - 1 = (N - L - 1) + 1 from by omega,
        Finset.sum_range_succ, show L + 1 + (N - L - 1) = N from by omega]
    ring

/-- **Claim 2** (Kovač, Section 4): Alice skips the term infinitely often.

If Alice eventually always includes, the sequence grows by `a(k) + δ(k)` at each step.
The tail domination hypothesis ensures the accumulated main terms exceed the current
term, while perturbations are controlled. This forces the sequence past `q`,
contradicting the cautious greedy condition. -/
lemma game_infinitely_many_skips
    (a e : ℕ → ℝ) (q x₀ : ℝ)
    (ha_pos : ∀ k, 0 < a k)
    (h_summ_a : Summable a)
    (h_summ_e : Summable e)
    (h_error_dom : ∀ k, ∑' l, e (k + l) < a k)
    (h_tail_dom : ∀ k, 4 * a k < ∑' l, a (k + 1 + l))
    (hq_hi : q ≤ x₀ + 2 * a 0)
    (δ : ℕ → ℝ) (hδ : ∀ k, |δ k| ≤ e k) :
    {k | ¬aliceChoice a q δ x₀ k}.Infinite := by
  -- By contradiction, assume there are only finitely many skips.
  by_contra h_contra;
  -- Let $L$ be the largest index where Alice skips.
  obtain ⟨L, hL_skip⟩ : ∃ L, ¬aliceChoice a q δ x₀ L ∧ ∀ k > L, aliceChoice a q δ x₀ k := by
    have h_finite : {k | ¬aliceChoice a q δ x₀ k}.Finite := by
      exact Classical.not_not.mp h_contra;
    obtain ⟨L, hL⟩ : ∃ L, ¬aliceChoice a q δ x₀ L := by
      by_cases h_empty : {k | ¬aliceChoice a q δ x₀ k} = ∅;
      · exfalso
        have h0 : aliceChoice a q δ x₀ 0 := by
          by_contra hk; exact (h_empty ▸ Set.mem_empty_iff_false 0).mp hk
        -- x₀ + 3a(0) ≤ q but q ≤ x₀ + 2a(0), contradicting a(0) > 0.
        simp only [aliceChoice, gameSeq_zero] at h0; linarith [ha_pos 0]
      · exact Set.nonempty_iff_ne_empty.mpr h_empty;
    exact ⟨
      Finset.max' ( h_finite.toFinset ) ⟨ L, h_finite.mem_toFinset.mpr hL ⟩,
      h_finite.mem_toFinset.mp ( Finset.max'_mem _ _ ),
      fun k hk => Classical.not_not.1 fun hk' =>
        not_lt_of_ge
          ( Finset.le_max' _ _ ( h_finite.mem_toFinset.mpr hk' ) ) hk ⟩;
  -- By definition of `L`, the sequence is a tail sum for all `N > L`.
  have h_seq_eq :
      ∀ N > L,
        gameSeq a q δ x₀ N =
          gameSeq a q δ x₀ L + δ L +
            ∑ k ∈ Finset.range (N - L - 1),
              (a (L + 1 + k) + δ (L + 1 + k)) := by
    intros N hN;
    apply gameSeq_include_run;
    · tauto;
    · exact hL_skip.2;
    · linarith;
  -- Taking the limit as `N → ∞` gives the corresponding upper bound by `q`.
  have h_lim_ge :
      q ≥ gameSeq a q δ x₀ L + δ L +
        ∑' k, (a (L + 1 + k) + δ (L + 1 + k)) := by
    have h_lim_ge :
        Filter.Tendsto (fun N => gameSeq a q δ x₀ N) Filter.atTop
          (nhds (gameSeq a q δ x₀ L + δ L +
            ∑' k, (a (L + 1 + k) + δ (L + 1 + k)))) := by
      rw [ Filter.tendsto_congr'
        ( Filter.eventuallyEq_of_mem ( Filter.Ioi_mem_atTop L ) h_seq_eq ) ];
      have hδ_summable : Summable fun k => δ (L + 1 + k) :=
        .of_norm_bounded (g := fun k => e (L + 1 + k))
          (h_summ_e.comp_injective (add_right_injective (L + 1))) fun _ => hδ _
      have ha_summable :=
        h_summ_a.comp_injective
          (add_right_injective (L + 1) : Function.Injective (L + 1 + ·))
      refine tendsto_const_nhds.add ((ha_summable.add hδ_summable).hasSum.tendsto_sum_nat
        |>.comp (Filter.tendsto_sub_atTop_nat _) |>.comp (Filter.tendsto_sub_atTop_nat _))
    refine le_of_tendsto h_lim_ge ?_
    filter_upwards [ Filter.eventually_gt_atTop L ] with N hN;
    have := hL_skip.2 N hN;
    unfold aliceChoice at this; linarith [ ha_pos N ] ;
  -- By definition of $L$, we have $gameSeq a q δ x₀ L + 3 * a L > q$.
  have h_gameSeq_L : gameSeq a q δ x₀ L + 3 * a L > q := by
    exact not_le.mp hL_skip.1;
  -- The tail perturbation is bounded below by subtracting the error tail.
  have h_delta_summable : Summable fun k => δ (L + 1 + k) :=
    .of_norm_bounded (g := fun k => e (L + 1 + k))
      (h_summ_e.comp_injective (add_right_injective (L + 1))) fun _ => hδ _
  have h_sum_ge : ∑' k, (a (L + 1 + k) + δ (L + 1 + k)) ≥
      ∑' k, a (L + 1 + k) - ∑' k, e (L + 1 + k) := by
    rw [← Summable.tsum_sub]
    · exact Summable.tsum_le_tsum
        (fun k => by linarith [abs_le.mp (hδ (L + 1 + k))])
        (.sub (h_summ_a.comp_injective (add_right_injective _))
          (h_summ_e.comp_injective (add_right_injective _)))
        (.add (h_summ_a.comp_injective fun m n h => by simpa using h) h_delta_summable)
    · exact h_summ_a.comp_injective fun x y hxy => by simpa using hxy
    · exact h_summ_e.comp_injective fun x y hxy => by simpa using hxy
  -- The tail error at L+1 controls ∑' e(L+1+l), which also equals ∑' e(L+l) - e(L).
  have h_eL := h_error_dom L
  have h_tail := h_tail_dom L
  have h_eL1 : ∑' l, e (L + (l + 1)) < a (L + 1) := by
    have := h_error_dom (L + 1)
    rwa [show (fun l => e (L + 1 + l)) = fun l => e (L + (l + 1)) from
      funext fun l => by ring_nf] at this
  have h_split : ∑' l, e (L + (l + 1)) = ∑' l, e (L + l) - e L := by
    have h := error_tail_split e h_summ_e L
    have : ∑' l, e (L + l + 1) = ∑' l, e (L + (l + 1)) :=
      tsum_congr fun l => by ring_nf
    linarith
  -- Connect the notation: ∑' e(L+1+k) = ∑' e(L+(k+1))
  have h_e_eq : ∑' k, e (L + 1 + k) = ∑' l, e (L + (l + 1)) :=
    tsum_congr fun l => by ring_nf
  linarith [abs_le.mp (hδ L)]

/-! ## Main convergence theorem -/

/-
**1D Game Convergence Theorem** (Kovač, Section 4):
Alice's cautious greedy strategy converges to the target value `q`,
regardless of Bob's bounded perturbations.

The argument proceeds by squeezing:
- The limit `L` exists by summability (Cauchy property).
- **Claim 1** forces `L ≤ q`: at each inclusion step,
  `gameSeq(k) + 3a(k) ≤ q`, and `a(k) → 0`, so `L ≤ q`.
- **Claim 2** forces `L ≥ q`: at each skip step,
  `gameSeq(k) + 3a(k) > q`, and `a(k) → 0`, so `L ≥ q`.
- Hence `L = q`.
-/
theorem game_converges_to_target
    (a e : ℕ → ℝ) (q x₀ : ℝ)
    (ha_pos : ∀ k, 0 < a k)
    (he_nonneg : ∀ k, 0 ≤ e k)
    (h_summ_a : Summable a)
    (h_summ_e : Summable e)
    (h_error_dom : ∀ k, ∑' l, e (k + l) < a k)
    (h_tail_dom : ∀ k, 4 * a k < ∑' l, a (k + 1 + l))
    (hq_lo : x₀ + a 0 ≤ q)
    (hq_hi : q ≤ x₀ + 2 * a 0)
    (δ : ℕ → ℝ) (hδ : ∀ k, |δ k| ≤ e k) :
    Tendsto (gameSeq a q δ x₀) atTop (nhds q) := by
  obtain ⟨ L, hL ⟩ :=
    gameSeq_convergent a e q x₀
      ( fun k => by linarith [ ha_pos k ] ) h_summ_a h_summ_e δ hδ;
  -- By Claim 1, there are infinitely many inclusion steps, so $L \leq q$.
  have hL_le_q : L ≤ q := by
    -- Claim 1 gives a subsequence of inclusion steps.
    obtain ⟨k_n, hk_n_infinite, hk_n_subseq⟩ :
        ∃ k_n : ℕ → ℕ, StrictMono k_n ∧
          ∀ n, gameSeq a q δ x₀ (k_n n) + 3 * a (k_n n) ≤ q := by
      have :=
        game_infinitely_many_inclusions
          a e q x₀ h_summ_a h_summ_e he_nonneg h_error_dom hq_lo δ hδ;
      exact ⟨
        (fun n =>
          Nat.recOn n ( Nat.find <| this.nonempty ) fun n ih =>
            Nat.find <| this.exists_gt ih),
        strictMono_nat_of_lt_succ fun n =>
          Nat.find_spec ( this.exists_gt _ ) |>.2,
        fun n =>
          Nat.recOn n ( Nat.find_spec <| this.nonempty ) fun n ih =>
            Nat.find_spec ( this.exists_gt _ ) |>.1 ⟩;
    -- Since $a(k_n) \to 0$ as $n \to \infty$, we have $L \leq q$.
    have hL_le_q_subseq :
        Filter.Tendsto (fun n => gameSeq a q δ x₀ (k_n n) + 3 * a (k_n n))
          Filter.atTop (nhds (L + 0)) := by
      simpa using Filter.Tendsto.add
        ( hL.comp hk_n_infinite.tendsto_atTop )
        ( tendsto_const_nhds.mul
          ( h_summ_a.tendsto_atTop_zero.comp hk_n_infinite.tendsto_atTop ) );
    simpa using le_of_tendsto_of_tendsto' hL_le_q_subseq tendsto_const_nhds hk_n_subseq;
  -- By Claim 2, there are infinitely many skip steps, so $L \geq q$.
  have hL_ge_q : q ≤ L := by
    -- Claim 2 gives a subsequence of skip steps.
    obtain ⟨subseq, hsubseq⟩ :
        ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
          ∀ k, ¬aliceChoice a q δ x₀ (subseq k) := by
      have :=
        game_infinitely_many_skips
          a e q x₀ ha_pos h_summ_a h_summ_e h_error_dom h_tail_dom hq_hi δ hδ;
      exact ⟨
        (fun k =>
          Nat.recOn k ( Nat.find <| this.nonempty ) fun k ih =>
            Nat.find <| this.exists_gt ih),
        strictMono_nat_of_lt_succ fun k =>
          Nat.find_spec ( this.exists_gt _ ) |>.2,
        fun k =>
          Nat.recOn k ( Nat.find_spec <| this.nonempty ) fun k ih =>
            Nat.find_spec ( this.exists_gt _ ) |>.1 ⟩;
    -- At each skip step, the cautious condition fails.
    have h_skip : ∀ k, gameSeq a q δ x₀ (subseq k) + 3 * a (subseq k) > q := by
      exact fun k => not_le.mp fun hk => hsubseq.2 k hk;
    -- Since $a (subseq k) \to 0$ as $k \to \infty$, we have $3 * a (subseq k) \to 0$.
    have h_a_zero : Filter.Tendsto (fun k => 3 * a (subseq k)) Filter.atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul
        ( h_summ_a.tendsto_atTop_zero.comp hsubseq.1.tendsto_atTop );
    exact le_of_tendsto_of_tendsto'
      tendsto_const_nhds
      ( by
        simpa using
          ( hL.comp hsubseq.1.tendsto_atTop |> Filter.Tendsto.add <| h_a_zero ) )
      fun k => le_of_lt <| h_skip k;
  exact le_antisymm hL_le_q hL_ge_q ▸ hL

end

/-! # Application of the Convergence Game to the Harmonic Subseries Problem

1. Define game parameters `a_j(k) = c_j / (k²m+1)^(j+1)` for each coordinate `j`
2. Show these satisfy the hypotheses of `game_converges_to_target`
3. Connect the game sequence to the M-transformed harmonic sums of `constructA`
4. Conclude that the image covers an open box

We use `K₀ = 500` as the starting round (the paper uses `K = 14` with
tighter estimates; any sufficiently large `K` works).
-/

noncomputable section

/-- The starting round for the game. Any sufficiently large value works. -/
abbrev K₀ : ℕ := 500

/-! ## Scale function and basic properties -/

/-- The scale at round k: `n_k = k² * m + 1`. -/
def nScale (k : ℕ) : ℕ := k ^ 2 * m_const + 1

lemma nScale_pos (k : ℕ) : 0 < nScale k := by
  unfold nScale m_const; omega

lemma nScale_cast_pos (k : ℕ) : (0 : ℝ) < (nScale k : ℝ) :=
  Nat.cast_pos.mpr (nScale_pos k)

lemma nScale_mono {a b : ℕ} (h : a ≤ b) : nScale a ≤ nScale b := by
  unfold nScale; nlinarith [Nat.pow_le_pow_left h 2]

/-! ## Game parameters -/

/-- Main term for coordinate `j` at game step `n` (starting from round `K`). -/
def aGameSeq (j : Fin 3) (K : ℕ) (n : ℕ) : ℝ :=
  c_coeff j / ((nScale (K + n) : ℝ)) ^ ((j : ℕ) + 1)

/-- Error bound per step. -/
def eGameSeq (K : ℕ) (n : ℕ) : ℝ :=
  1 / ((nScale (K + n) : ℝ)) ^ 4

/-! ## Summability and positivity -/

lemma aGameSeq_pos (j : Fin 3) (K n : ℕ) : 0 < aGameSeq j K n := by
  unfold aGameSeq; exact div_pos (c_coeff_pos j) (pow_pos (nScale_cast_pos _) _)

lemma eGameSeq_nonneg (K n : ℕ) : 0 ≤ eGameSeq K n := by
  unfold eGameSeq; positivity

set_option linter.style.multiGoal false in
set_option linter.style.refine false in
lemma aGameSeq_summable (j : Fin 3) (K : ℕ) : Summable (aGameSeq j K) := by
  refine' Summable.of_nonneg_of_le ?_ ?_ ?_
  exact fun n => c_coeff j / ( ( n : ℝ ) + K + 1 ) ^ 2
  · exact fun n => le_of_lt ( aGameSeq_pos j K n );
  · intro n; rw [ aGameSeq ] ; gcongr ; norm_cast ;
    · fin_cases j <;> norm_num [ c_coeff ];
    · refine' le_trans ?_
        ( pow_le_pow_right₀ ?_ ( show ( j : ℕ ) + 1 ≥ 1 by linarith ) ) <;>
        norm_cast <;>
        ring_nf
      · exact Nat.le_of_lt_succ <| by
          rw [ show nScale ( n + K ) = ( n + K ) ^ 2 * 2310 + 1 by rfl ]
          nlinarith
      · exact_mod_cast nScale_pos _;
  · exact Summable.mul_left _ <| by
      exact_mod_cast summable_nat_add_iff ( K + 1 ) |>.2
        <| Real.summable_nat_pow_inv.2 one_lt_two;

lemma eGameSeq_summable (K : ℕ) : Summable (eGameSeq K) := by
  unfold eGameSeq;
  -- We can compare our series to the convergent p-series $\sum_{n=1}^{\infty} \frac{1}{n^4}$.
  have h_comparison : ∀ n : ℕ, (1 : ℝ) / (nScale (K + n))^4 ≤ 1 / (n + 1)^4 := by
    intro n; gcongr; norm_cast;
    exact Nat.succ_le_of_lt ( by
      exact lt_add_of_le_of_pos
        ( Nat.le_trans ( Nat.le_add_left _ _ )
          ( Nat.le_trans ( Nat.le_self_pow ( by norm_num ) _ )
            ( Nat.le_mul_of_pos_right _ ( by decide ) ) ) )
        ( by decide ) );
  exact Summable.of_nonneg_of_le
    ( fun n => by positivity ) h_comparison
    ( by
      simpa using summable_nat_add_iff 1 |>.2
        <| Real.summable_one_div_nat_pow.2 <| by norm_num )

/-! ## Error domination and tail domination -/

/-
Error domination: the total future error is smaller than the current main term.
-/
set_option maxHeartbeats 400000 in
-- The integral comparison and final rational inequality need extra arithmetic search.
set_option linter.style.refine false in
set_option linter.flexible false in
/-- The total future error `∑' e(k+l)` is smaller than the current main term `a_j(k)`.
This is the key analytic estimate ensuring that Bob's perturbations are negligible
compared to Alice's moves. The proof bounds the error tail by an integral. -/
lemma error_domination (j : Fin 3) (k : ℕ) :
    ∑' l, eGameSeq K₀ (k + l) < aGameSeq j K₀ k := by
  -- We'll use the fact that the sum of a geometric series is less than the first term.
  have h_geo_sum :
      (∑' l, (1 : ℝ) / ((nScale (K₀ + k + l))^4)) <
        (1 : ℝ) / ((nScale (K₀ + k))^3) * (1 / 1029000) := by
    -- Split off the first term of the tail.
    have h_geo_series :
        (∑' l : ℕ, (1 : ℝ) / ((nScale (K₀ + k + l))^4)) ≤
          (1 : ℝ) / ((nScale (K₀ + k))^4) +
            ∑' l : ℕ, (1 : ℝ) / ((nScale (K₀ + k + l + 1))^4) := by
      rw [ Summable.tsum_eq_zero_add ];
      · norm_num [ add_assoc ];
      · refine' Summable.of_nonneg_of_le
          ( fun l => by positivity ) ( fun l => ?_ )
          ( summable_nat_add_iff 1 |>.2
            <| Real.summable_one_div_nat_pow.2 one_lt_two );
        gcongr;
        exact_mod_cast Nat.le_trans
          ( Nat.pow_le_pow_left
            ( show l + 1 ≤ nScale ( K₀ + k + l ) from by
              unfold nScale
              nlinarith [
                show K₀ + k ≥ 0 by positivity,
                show m_const ≥ 1 by decide ] ) 2 )
          ( Nat.pow_le_pow_right
            ( by
              unfold nScale
              nlinarith [
                show K₀ + k ≥ 0 by positivity,
                show m_const ≥ 1 by decide ] )
            ( show 2 ≤ 4 by decide ) );
    -- Compare the tail against a p-series.
    have h_geo_series_tail :
        (∑' l : ℕ, (1 : ℝ) / ((nScale (K₀ + k + l + 1))^4)) ≤
          ∑' l : ℕ, (1 : ℝ) / ((K₀ + k + l + 1)^8 * m_const^4) := by
      refine' Summable.tsum_le_tsum ?_ ?_ ?_;
      · intro l; rw [ div_le_div_iff₀ ] <;> norm_cast <;> norm_num [ nScale ];
        · calc _ = ((500 + k + l + 1) ^ 2 * m_const) ^ 4 := by ring
            _ ≤ _ := Nat.pow_le_pow_left (Nat.le_succ _) 4
        · norm_num [m_const]
      · have h_geo_series_tail :
            Summable (fun l : ℕ =>
              (1 : ℝ) / ((K₀ + k + l + 1)^8 * m_const^4)) := by
          norm_num +zetaDelta at *;
          exact Summable.mul_left _ <| by
            exact_mod_cast Summable.comp_injective
              ( Real.summable_nat_pow_inv.2 <| by norm_num )
              fun a b h => by simpa using h;
        refine' h_geo_series_tail.of_nonneg_of_le ( fun l => by positivity ) ( fun l => ?_ );
        rw [ div_le_div_iff₀ ] <;> norm_cast <;> norm_num [ nScale ];
        · calc _ = ((500 + k + l + 1) ^ 2 * m_const) ^ 4 := by ring
            _ ≤ _ := Nat.pow_le_pow_left (Nat.le_succ _) 4
        · norm_num [m_const]
      · norm_num +zetaDelta at *;
        exact Summable.mul_left _ <| by
          exact_mod_cast Summable.comp_injective
            ( Real.summable_nat_pow_inv.2 <| by norm_num )
            fun a b h => by simpa using h;
    -- Bound the p-series tail by an improper integral.
    have h_pseries :
        (∑' l : ℕ, (1 : ℝ) / ((K₀ + k + l + 1)^8)) ≤
          ∫ x in Set.Ioi (K₀ + k : ℝ), (1 : ℝ) / x^8 := by
      have h_pseries :
          ∀ l : ℕ,
            (1 : ℝ) / ((K₀ + k + l + 1)^8) ≤
              ∫ x in (K₀ + k + l : ℝ).. (K₀ + k + l + 1 : ℝ),
                (1 : ℝ) / x^8 := by
        intro l
        have h_integral_bound :
            (∫ x in (K₀ + k + l : ℝ).. (K₀ + k + l + 1 : ℝ),
              (1 : ℝ) / x^8) ≥
              ∫ x in (K₀ + k + l : ℝ).. (K₀ + k + l + 1 : ℝ),
                (1 : ℝ) / ((K₀ + k + l + 1 : ℝ)^8) := by
          refine' intervalIntegral.integral_mono_on ?_ ?_ ?_ ?_ <;> norm_num;
          · exact ContinuousOn.intervalIntegrable ( by
              exact continuousOn_of_forall_continuousAt fun x hx =>
                ContinuousAt.inv₀ ( continuousAt_id.pow 8 )
                  ( pow_ne_zero _ <| by
                    linarith [
                      Set.mem_Icc.mp <| by
                        norm_num [ add_assoc ] at hx
                        exact hx ] ) ) ..;
          · exact fun x hx₁ hx₂ =>
              inv_anti₀ ( pow_pos ( by linarith ) _ )
                ( pow_le_pow_left₀ ( by linarith ) ( by linarith ) _ );
        aesop;
      have h_pseries_sum :
          ∀ N : ℕ,
            ∑ l ∈ Finset.range N, (1 : ℝ) / ((K₀ + k + l + 1)^8) ≤
              ∫ x in (K₀ + k : ℝ).. (K₀ + k + N : ℝ), (1 : ℝ) / x^8 := by
        intro N
        induction N with
        | zero => norm_num [add_assoc, Finset.sum_range_succ]
        | succ N ih =>
          norm_num [add_assoc, Finset.sum_range_succ] at *
          convert add_le_add ih (h_pseries N) using 1
          rw [intervalIntegral.integral_add_adjacent_intervals] <;>
            apply_rules [ContinuousOn.intervalIntegrable] <;>
            exact continuousOn_of_forall_continuousAt fun x hx =>
              ContinuousAt.inv₀ (continuousAt_id.pow _)
                (pow_ne_zero _ <| by linarith [Set.mem_Icc.mp <| by simpa [add_assoc] using hx])
      have h_pseries_sum :
          Filter.Tendsto
            (fun N : ℕ =>
              ∫ x in (K₀ + k : ℝ).. (K₀ + k + N : ℝ), (1 : ℝ) / x^8)
            Filter.atTop
            (nhds (∫ x in Set.Ioi (K₀ + k : ℝ), (1 : ℝ) / x^8)) := by
        apply_rules [ MeasureTheory.intervalIntegral_tendsto_integral_Ioi ];
        · have h_integrable :
              MeasureTheory.IntegrableOn
                (fun x : ℝ => x ^ (-8 : ℝ)) (Set.Ioi (K₀ + k : ℝ)) := by
            rw [ integrableOn_Ioi_rpow_iff ] <;>
              norm_num
            linarith [ show ( K₀ : ℝ ) ≥ 200 by norm_cast ];
          norm_cast at * ; aesop;
        · exact Filter.tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop;
      exact le_of_tendsto_of_tendsto'
        ( Summable.hasSum ( by
          exact_mod_cast Summable.comp_injective
            ( Real.summable_one_div_nat_pow.2 <| by norm_num )
            <| by intros a b; aesop )
          |> HasSum.tendsto_sum_nat )
        h_pseries_sum
        fun N => by aesop;
    -- Evaluate the integral $\int_{K₀ + k}^{\infty} \frac{1}{x^8} \, dx$.
    have h_integral : ∫ x in Set.Ioi (K₀ + k : ℝ), (1 : ℝ) / x^8 = 1 / (7 * (K₀ + k : ℝ)^7) := by
      have h_integral :
          (∫ x in Set.Ioi (K₀ + k : ℝ), (1 : ℝ) / x^8) =
            ∫ x in Set.Ioi (K₀ + k : ℝ), x^(-8 : ℝ) := by
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => by norm_cast; aesop;
      rw [ h_integral, integral_Ioi_rpow_of_lt ] <;> norm_num;
      · norm_cast ; ring;
      · positivity;
    -- Combine the inequalities to conclude the proof.
    have h_final :
        (1 : ℝ) / ((nScale (K₀ + k))^4) +
            (1 : ℝ) / (7 * (K₀ + k : ℝ)^7) * (1 / m_const^4) <
          (1 : ℝ) / ((nScale (K₀ + k))^3) * (1 / 1029000) := by
      norm_num [ nScale, m_const ];
      field_simp;
      exact lt_of_sub_pos ( by ring_nf; positivity );
    simp_all +decide;
    exact h_geo_series.trans_lt ( by
      rw [ tsum_mul_left ] at *
      nlinarith [
        inv_pos.mpr ( show 0 < ( m_const : ℝ ) ^ 4 by norm_num [ m_const ] ) ] );
  refine' lt_of_le_of_lt ?_ ( h_geo_sum.trans_le ?_ ) <;> norm_num [ Fin.forall_fin_succ ] at *;
  · unfold eGameSeq; norm_num [ add_comm, add_left_comm, add_assoc ] ;
  · fin_cases j <;> norm_num [ aGameSeq ];
    · rw [ inv_mul_eq_div, div_le_div_iff₀ ] <;>
        norm_num [ c_coeff ] <;>
        norm_cast <;>
        norm_num [ nScale ];
      exact mul_le_mul
        ( by norm_num )
        ( mod_cast Nat.le_self_pow ( by norm_num ) _ )
        ( by positivity ) ( by positivity );
    · unfold c_coeff; norm_num [ nScale ] ; ring_nf; norm_num;
      rw [ inv_mul_eq_div, inv_mul_eq_div, div_le_div_iff₀ ] <;>
        first | positivity | exact le_of_sub_nonneg ( by ring_nf; positivity ) ;
    · unfold c_coeff; norm_num [ div_eq_mul_inv, mul_comm ] ;

/-
Tail domination: the sum of future main terms exceeds 4 times the current.
-/
set_option maxHeartbeats 400000 in
-- The finite lower-bound comparison checks 100 explicit nonlinear cases.
set_option linter.style.refine false in
set_option linter.flexible false in
set_option linter.style.multiGoal false in
/-- The tail sum of future main terms exceeds 4 times the current term.
This ensures Alice has enough "room" for future moves, which is needed
to show she eventually skips (Claim 2). Proved by comparing against 100 explicit terms. -/
lemma tail_domination (j : Fin 3) (k : ℕ) :
    4 * aGameSeq j K₀ k < ∑' l, aGameSeq j K₀ (k + 1 + l) := by
  refine'
    lt_of_lt_of_le ?_
      (Summable.sum_le_tsum (Finset.range 100) (fun _ _ => ?_) ?_)
  · fin_cases j <;> norm_num [ aGameSeq ];
    · norm_num [ nScale ];
      norm_num [ m_const, c_coeff ];
      rw [ Finset.sum_range_succ ];
      refine' lt_add_of_le_of_pos ?_ ?_;
      · refine'
          le_trans ?_
            (Finset.sum_le_sum fun i hi =>
              mul_le_mul_of_nonneg_left
                (inv_anti₀ (by positivity) <|
                  show
                    (500 + (k + 1 + i) : ℝ) ^ 2 * 2310 + 1 ≤
                      (500 + k) ^ 2 * 2310 + 1 +
                        99 * 2 * (500 + k) * 2310 + 99 ^ 2 * 2310 by
                    nlinarith only [
                      show (i : ℝ) ≤ 98 by
                        norm_cast
                        linarith [Finset.mem_range.mp hi]])
                (by positivity))
        norm_num
        field_simp;
        nlinarith;
      · positivity;
    · unfold c_coeff nScale;
      norm_num [ m_const ];
      refine'
        lt_of_lt_of_le ?_
          (Finset.sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_left
              (inv_anti₀ (by positivity) <|
                pow_le_pow_left₀ (by positivity)
                  (show
                    (500 + (k + 1 + i) : ℝ) ^ 2 * 2310 + 1 ≤
                      (500 + k) ^ 2 * 2310 + 1 +
                        100 * 2 * (500 + k) * 2310 + 100 ^ 2 * 2310 by
                    ring_nf
                    nlinarith [
                      show (i : ℝ) ≤ 99 by
                        norm_cast
                        linarith [Finset.mem_range.mp hi]])
                  2)
              (by positivity))
      norm_num
      field_simp;
      nlinarith [ sq ( k : ℝ ) ];
    · unfold nScale c_coeff;
      norm_num [ m_const ];
      refine'
        lt_of_lt_of_le ?_
          (Finset.sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_left
              (inv_anti₀ (by positivity) <|
                pow_le_pow_left₀ (by positivity)
                  (show
                    (500 + (k + 1 + i) : ℝ) ^ 2 * 2310 + 1 ≤
                      (500 + k) ^ 2 * 2310 + 1 +
                        100 * 2 * (500 + k) * 2310 + 100 ^ 2 * 2310 by
                    ring_nf
                    nlinarith only [
                      show (i : ℝ) ≤ 99 by
                        norm_cast
                        linarith [Finset.mem_range.mp hi]])
                  3)
              (by positivity))
      norm_num
      ring_nf
      norm_num
      rw [inv_mul_eq_div, inv_mul_eq_div, div_lt_div_iff₀] <;> first
        | positivity
        | nlinarith [
            pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 3,
            pow_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) 4]
  · exact le_of_lt ( aGameSeq_pos _ _ _ );
  · exact aGameSeq_summable j K₀ |> Summable.comp_injective <| by aesop_cat;

/-
Auxiliary numeric inequality for the j=2 case of `error_domination_3x`.
Shows that the combined error bound (from the integral + first term) is less than
the main term coefficient 1/1029000 of `nScale^3`.
-/
lemma error_dom_3x_aux (k : ℕ) :
    (3 * (7 * (500 + k) ^ 7 * 28473963210000) + ((500 + k) ^ 2 * 2310 + 1) ^ 4 * 3) *
      (1029000 * ((500 + k) ^ 2 * 2310 + 1) ^ 3) <
    ((500 + k) ^ 2 * 2310 + 1) ^ 4 * (7 * (500 + k) ^ 7 * 28473963210000) := by
  lia

/-
Stronger error domination: 3 times the total future error is smaller than the current main term.
Needed because each coordinate's perturbation in the 3D game has 3 contributing sources.
-/
set_option maxHeartbeats 400000 in
-- This combines the earlier domination estimate with three explicit coordinate checks.
set_option linter.style.refine false in
set_option linter.flexible false in
set_option linter.style.multiGoal false in
/-- Strengthened error domination: `3 · ∑' e < a_j(k)`. Each coordinate's perturbation in the
3D game receives contributions from all 3 swap operations, hence the factor of 3. -/
lemma error_domination_3x (j : Fin 3) (k : ℕ) :
    3 * ∑' l, eGameSeq K₀ (k + l) < aGameSeq j K₀ k := by
  fin_cases j <;> norm_num [ Fin.forall_fin_succ ] at *;
  · refine' lt_of_lt_of_le ( mul_lt_mul_of_pos_left ( error_domination 2 k ) zero_lt_three ) ?_;
    unfold aGameSeq;
    unfold c_coeff; norm_num; ring_nf; norm_num;
    erw [ Matrix.cons_val_succ' ] ; norm_num ; ring_nf ; norm_num;
    exact
      mul_le_mul
        (inv_anti₀ (by norm_cast; exact nScale_pos _)
          (mod_cast Nat.le_self_pow (by norm_num) _))
        (by norm_num) (by norm_num) (by positivity)
  · refine' lt_of_lt_of_le ( mul_lt_mul_of_pos_left ( error_domination 2 k ) zero_lt_three ) ?_;
    unfold aGameSeq;
    unfold c_coeff nScale; norm_num; ring_nf;
    unfold m_const; norm_num; ring_nf;
    erw [ Matrix.cons_val_succ' ] ; norm_num ; ring_nf;
    rw [inv_mul_eq_div, inv_mul_eq_div, div_le_div_iff₀] <;> first
      | positivity
      | nlinarith [sq ((k : ℝ) ^ 2), sq ((k : ℝ) ^ 3)]
  · -- We'll use that $\sum_{l=0}^{\infty} \frac{1}{(nScale (K₀ + k + l))^4}$ is bounded above.
    have h_bound :
        ∑' l, (1 : ℝ) / (nScale (500 + k + l)) ^ 4 ≤
          1 / (nScale (500 + k)) ^ 4 +
            1 / (7 * (500 + k) ^ 7 * 2310 ^ 4) := by
      -- The tail of `1 / nScale ^ 4` is controlled by the first term and an integral.
      have h_integral_bound :
          ∑' l, (1 : ℝ) / (nScale (500 + k + l)) ^ 4 ≤
            1 / (nScale (500 + k)) ^ 4 +
              ∑' l : ℕ, (1 : ℝ) / ((500 + k + l + 1) ^ 8 * 2310 ^ 4) := by
        rw [ Summable.tsum_eq_zero_add ];
        · refine' add_le_add le_rfl ( Summable.tsum_le_tsum ?_ ?_ ?_ );
          · intro i; rw [ div_le_div_iff₀ ] <;> norm_cast <;> norm_num [ nScale ];
            norm_num [ m_const ] ; ring_nf;
            lia;
          · refine'
              Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_)
                (summable_nat_add_iff 1 |>.2 <|
                  Real.summable_one_div_nat_pow.2 one_lt_two)
            gcongr;
            norm_cast ; ring_nf;
            unfold nScale;
            unfold m_const; ring_nf;
            lia
          · norm_num +zetaDelta at *;
            exact
              Summable.mul_left _ <| by
                exact_mod_cast
                  Summable.comp_injective
                    (Real.summable_nat_pow_inv.2 <| by norm_num)
                    fun x y h => by simpa using h
        · refine'
            Summable.of_nonneg_of_le (fun _ => by positivity) (fun l => ?_)
              (summable_nat_add_iff 1 |>.2 <|
                Real.summable_one_div_nat_pow.2 one_lt_two)
          gcongr ; norm_cast ; ring_nf;
          unfold nScale m_const; ring_nf;
          lia
      -- The tail of `1 / (x + l + 1) ^ 8` is bounded by `1 / (7 * x ^ 7)`.
      have h_sum_bound :
          ∀ x : ℝ, 0 < x →
            ∑' l : ℕ, (1 : ℝ) / ((x + l + 1) ^ 8) ≤ 1 / (7 * x ^ 7) := by
        intros x hx_pos
        have h_integral_bound :
            ∀ l : ℕ,
              (1 : ℝ) / ((x + l + 1) ^ 8) ≤
                ∫ t in (x + l).. (x + l + 1), (1 : ℝ) / t ^ 8 := by
          intros l
          have h_integral_bound :
              ∫ t in (x + l).. (x + l + 1), (1 : ℝ) / t ^ 8 ≥
                ∫ t in (x + l).. (x + l + 1),
                  (1 : ℝ) / ((x + l + 1) ^ 8) := by
            refine' intervalIntegral.integral_mono_on ?_ ?_ ?_ ?_ <;> norm_num;
            · exact
                ContinuousOn.intervalIntegrable
                  (by
                    exact continuousOn_of_forall_continuousAt fun t ht =>
                      ContinuousAt.inv₀ (continuousAt_id.pow 8)
                        (pow_ne_zero _ <| by
                          linarith [Set.mem_Icc.mp <| by simpa using ht])) ..
            · exact fun y hy₁ hy₂ =>
                inv_anti₀ (pow_pos (by linarith) _)
                  (pow_le_pow_left₀ (by linarith) (by linarith) _)
          aesop;
        -- By summing the integral bounds, we get the desired inequality.
        have h_sum_integral_bound :
            ∀ N : ℕ,
              ∑ l ∈ Finset.range N, (1 : ℝ) / ((x + l + 1) ^ 8) ≤
                ∫ t in (x).. (x + N), (1 : ℝ) / t ^ 8 := by
          intro N;
          induction N with
          | zero => norm_num [add_assoc, Finset.sum_range_succ]
          | succ N ih =>
            norm_num [add_assoc, Finset.sum_range_succ] at *
            convert add_le_add ih (h_integral_bound N) using 1
            rw [intervalIntegral.integral_add_adjacent_intervals] <;>
              apply_rules [ContinuousOn.intervalIntegrable] <;>
              exact continuousOn_of_forall_continuousAt fun t ht =>
                ContinuousAt.inv₀ (continuousAt_id.pow 8)
                  (pow_ne_zero _ <| by cases Set.mem_uIcc.mp ht <;> linarith)
        -- Taking the limit of the integral bound gives the desired inequality.
        have h_limit_integral_bound :
            Filter.Tendsto
              (fun N : ℕ => ∫ t in (x).. (x + N), (1 : ℝ) / t ^ 8)
              Filter.atTop
              (nhds (1 / (7 * x ^ 7))) := by
          -- Evaluate the integral $\int_{x}^{x+N} \frac{1}{t^8} \, dt$.
          have h_integral_eval :
              ∀ N : ℕ,
                ∫ t in (x).. (x + N), (1 : ℝ) / t ^ 8 =
                  (1 / 7) * (1 / x ^ 7 - 1 / (x + N) ^ 7) := by
            intro N; group
            rw [integral_zpow (by right; exact ⟨by norm_num, fun h => by simp at h; linarith⟩)]
            norm_num; field_simp; ring
          simp_all +decide [ mul_comm ];
          exact
            le_trans
              (Filter.Tendsto.mul
                (tendsto_const_nhds.sub <|
                  tendsto_inv_atTop_zero.comp <|
                    Filter.tendsto_pow_atTop (by positivity) |>
                      Filter.Tendsto.comp <|
                        Filter.tendsto_atTop_add_const_left _ _
                          tendsto_natCast_atTop_atTop)
                tendsto_const_nhds)
              (by norm_num)
        exact
          le_of_tendsto_of_tendsto'
            ((Summable.hasSum
              (by
                exact_mod_cast
                  Summable.of_nonneg_of_le
                    (fun _ => by positivity)
                    (fun n => by
                      simpa using
                        inv_anti₀ (by positivity) <|
                          pow_le_pow_left₀ (by positivity)
                            (show x + n + 1 ≥ n + 1 by linarith) _)
                    (summable_nat_add_iff 1 |>.2 <|
                      Real.summable_one_div_nat_pow.2 <| by norm_num))) |>
              HasSum.tendsto_sum_nat)
            h_limit_integral_bound
            h_sum_integral_bound
      refine' le_trans h_integral_bound ?_;
      norm_num [ tsum_mul_right ];
      rw [tsum_mul_left]
      specialize h_sum_bound (500 + k) (by positivity)
      norm_num at *
      ring_nf at *
      aesop
    -- This numerical bound compares the total future error with the current main term.
    have h_ineq :
        3 / (nScale (500 + k) : ℝ) ^ 4 +
            3 / (7 * (500 + k) ^ 7 * 2310 ^ 4) <
          1 / (1029000 * (nScale (500 + k)) ^ 3) := by
      rw [ div_add_div, div_lt_div_iff₀ ] <;> norm_cast <;> norm_num [ nScale ];
      unfold m_const;
      exact error_dom_3x_aux k
    unfold eGameSeq aGameSeq;
    convert
      lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left
          (show
            ∑' l : ℕ, (1 : ℝ) / (nScale (500 + (k + l))) ^ 4 ≤
              1 / (nScale (500 + k) : ℝ) ^ 4 +
                1 / (7 * (500 + k) ^ 7 * 2310 ^ 4) from ?_)
          zero_le_three)
        _ using 1
    · simpa only [ add_assoc ] using h_bound;
    · convert h_ineq using 1 ; ring!;
      unfold c_coeff; norm_num; ring;

/-! ## The swap contribution and its bound -/

/-- The swap contribution at step `n` in coordinate `i`. -/
def swapContribM (K n : ℕ) (j i : Fin 3) : ℝ :=
  ∑ a ∈ Ssets j,
    (M_mat.mulVec (fun l : Fin 3 =>
      1 / (((a * nScale (K + n) : ℕ) : ℝ) + ((l : ℕ) : ℝ)))) i -
  ∑ a ∈ Tsets j,
    (M_mat.mulVec (fun l : Fin 3 =>
      1 / (((a * nScale (K + n) : ℕ) : ℝ) + ((l : ℕ) : ℝ)))) i

set_option maxHeartbeats 1000000 in
-- This proof is a finite rational inequality check over nine explicit cases.
set_option linter.flexible false in
/-- The swap contribution approximates the diagonal: for `i = j` it equals `a_j(k)` up to
error `e(k)`, and for `i ≠ j` it is bounded by `e(k)`. This is the 9-way case analysis
over pairs `(j, i) ∈ Fin 3 × Fin 3`, each requiring rational arithmetic in `nScale`. -/
lemma swapContrib_bound (n : ℕ) (j i : Fin 3) :
    |swapContribM K₀ n j i - if i = j then aGameSeq j K₀ n else 0| ≤ eGameSeq K₀ n := by
  unfold swapContribM aGameSeq eGameSeq;
  unfold M_mat;
  fin_cases i;
  · simp +decide only [Nat.cast_mul, one_div, Fin.zero_eta, Fin.isValue, cons_mulVec,
      cons_dotProduct, one_mul, zero_mul, dotProduct_of_isEmpty, add_zero, neg_mul,
      empty_mulVec, cons_val_zero];
    fin_cases j <;> norm_num [Ssets, Tsets, c_coeff, vecHead];
    · unfold S₁ T₁; norm_num [Finset.sum]; ring_nf; norm_num [abs_le];
    · unfold S₂ T₂; norm_num [Finset.sum]; ring_nf; norm_num;
    · unfold S₃ T₃ nScale; norm_num [Finset.sum]; ring_nf; norm_num;
      positivity;
  · simp +decide only [Nat.cast_mul, one_div, Fin.mk_one, Fin.isValue, cons_mulVec,
      cons_dotProduct, one_mul, zero_mul, dotProduct_of_isEmpty, add_zero, neg_mul,
      empty_mulVec, cons_val_one, cons_val_zero];
    fin_cases j <;> simp +decide [Ssets, Tsets];
    · simp +decide [S₁, T₁, vecHead, vecTail];
      rw [abs_le]; constructor <;> norm_num [nScale] <;> ring_nf <;> norm_num;
      · norm_num [m_const] at *;
        field_simp;
        exact le_of_sub_nonneg (by ring_nf; positivity);
      · unfold m_const; norm_num; ring_nf;
        field_simp;
        exact le_of_sub_nonneg (by ring_nf; positivity);
    · unfold S₂ T₂ c_coeff; norm_num [Fin.sum_univ_succ, vecHead, vecTail]; ring_nf; norm_num;
      unfold nScale; norm_num [abs_le]; ring_nf; norm_num;
      unfold m_const; norm_num; ring_nf;
      field_simp;
      exact ⟨by exact le_of_sub_nonneg (by ring_nf; positivity),
        by exact le_of_sub_nonneg (by ring_nf; positivity)⟩;
    · norm_num [S₃, T₃, vecHead, vecTail];
      norm_num [nScale];
      rw [abs_le]; constructor <;> norm_num [m_const] <;> ring_nf;
      · field_simp;
        exact le_of_sub_nonneg (by ring_nf; positivity);
      · field_simp;
        exact le_of_sub_nonneg (by ring_nf; positivity);
  · simp +decide only [Nat.cast_mul, one_div, Fin.reduceFinMk, cons_mulVec,
      cons_dotProduct, one_mul, zero_mul, dotProduct_of_isEmpty, add_zero, neg_mul,
      empty_mulVec, Fin.isValue, cons_val];
    unfold Ssets Tsets; norm_num [Fin.ext_iff];
    fin_cases j <;> norm_num [Fin.ext_iff, vecHead, vecTail];
    · unfold S₁ T₁; ring_nf;
      unfold nScale; norm_num [abs_le]; ring_nf; norm_num;
      unfold m_const; norm_num; ring_nf; norm_num;
      constructor;
      · field_simp;
        nontriviality;
        exact le_of_sub_nonneg (by ring_nf; positivity);
      · field_simp;
        nontriviality;
        exact le_of_sub_nonneg (by ring_nf; positivity);
    · unfold nScale; norm_num [S₂, T₂]; ring_nf; norm_num [abs_le];
      unfold m_const; norm_num; ring_nf;
      field_simp;
      exact ⟨by exact le_of_sub_nonneg (by ring_nf; positivity),
        by exact le_of_sub_nonneg (by ring_nf; positivity)⟩;
    · unfold S₃ T₃ c_coeff nScale; norm_num [Finset.sum]; ring_nf; norm_num;
      unfold m_const; norm_num; ring_nf;
      field_simp;
      rw [abs_of_nonpos] <;> ring_nf;
      · field_simp;
        exact le_of_sub_nonneg (by ring_nf; positivity);
      · exact le_of_sub_nonneg (by ring_nf; positivity)

/-! ## The base point and harmonic sum decomposition -/

/-- The base point in M-coordinates. -/
def basePointM (K : ℕ) (i : Fin 3) : ℝ :=
  ∑' n, ∑ j : Fin 3, ∑ a ∈ Tsets j,
    (M_mat.mulVec (fun l : Fin 3 =>
      1 / (((a * nScale (K + n) : ℕ) : ℝ) + ((l : ℕ) : ℝ)))) i

/-- The active set at round k for coordinate j. -/
def ActiveSet (ε : ℕ → Fin 3 → Bool) (k : ℕ) (j : Fin 3) : Finset ℕ :=
  if ε k j then Ssets j else Tsets j

/-- The embedding from structured indices to natural numbers. -/
def structEmbed (K : ℕ) (ε : ℕ → Fin 3 → Bool) :
    (Σ (n : ℕ), Σ (j : Fin 3), ↑(ActiveSet ε (K + n) j)) → ℕ :=
  fun ⟨n, _, ⟨a, _⟩⟩ => a * nScale (K + n)

lemma structEmbed_mem_constructA (K : ℕ) (ε : ℕ → Fin 3 → Bool)
    (p : Σ (n : ℕ), Σ (j : Fin 3), ↑(ActiveSet ε (K + n) j)) :
    structEmbed K ε p ∈ constructA K ε := by
  obtain ⟨ n, j, a ⟩ := p;
  refine Set.mem_iUnion₂.mpr ⟨ K + n, ?_, ?_ ⟩
  · omega
  · unfold ActiveSet at *; unfold structEmbed at *; aesop;

lemma constructA_subset_range (K : ℕ) (ε : ℕ → Fin 3 → Bool) :
    constructA K ε ⊆ Set.range (structEmbed K ε) := by
  -- Expand membership in `constructA` into a structured index.
  intro m hm
  obtain ⟨k, hk, j, hj⟩ :
      ∃ k ≥ K, ∃ j : Fin 3,
        m ∈
          (if ε k j then
            (Ssets j).image (· * nScale k)
          else
            (Tsets j).image (· * nScale k)) := by
    unfold constructA at hm
    simp only [Set.mem_iUnion] at hm
    obtain ⟨k, hk, j, hj⟩ := hm
    exact ⟨k, hk, j, by split_ifs at hj ⊢ <;> exact hj⟩
  obtain ⟨a, ha⟩ : ∃ a ∈ ActiveSet ε k j, m = a * nScale k := by
    unfold ActiveSet; aesop;
  use ⟨k - K, j, ⟨a, by
    lia⟩⟩
  generalize_proofs at *;
  unfold structEmbed; aesop;

set_option linter.flexible false in
lemma structEmbed_injective (K : ℕ) (ε : ℕ → Fin 3 → Bool) :
    Function.Injective (structEmbed K ε) := by
  intro p₁ p₂ h_eq;
  obtain ⟨ n₁, j₁, ⟨ a₁, ha₁ ⟩ ⟩ := p₁
  obtain ⟨ n₂, j₂, ⟨ a₂, ha₂ ⟩ ⟩ := p₂
  simp [structEmbed] at h_eq;
  have := unique_representation a₁ a₂ ( K + n₁ ) ( K + n₂ ) ?_ ?_ ?_;
  · fin_cases j₁ <;> fin_cases j₂ <;> simp_all +decide [ ActiveSet ];
    all_goals unfold ActiveSet at *; simp_all +decide;
    all_goals subst_vars; simp_all +decide [ Ssets, Tsets ];
    all_goals split_ifs at * <;> simp_all +decide only [Ssets, Tsets] ;
    all_goals simp_all +decide [ S₁, S₂, S₃, T₁, T₂, T₃ ];
    all_goals omega;
  · fin_cases j₁ <;> fin_cases j₂ <;> simp_all +decide [ ActiveSet ];
    all_goals split_ifs at ha₁ <;> simp_all +decide [ Ssets, Tsets ] ;
  · unfold ActiveSet at ha₂; fin_cases j₂ <;> simp +decide at ha₂ ⊢;
    · split_ifs at ha₂ <;> simp_all +decide [ Ssets, Tsets ];
    · split_ifs at ha₂ <;> simp_all +decide [ Ssets, Tsets ];
    · unfold Ssets Tsets at ha₂; aesop;
  · exact h_eq

/-
Key rearrangement: the tsum over constructA equals the structured double sum.
-/
set_option linter.flexible false in
set_option linter.style.multiGoal false in
set_option linter.style.refine false in
lemma tsum_constructA_eq (ε : ℕ → Fin 3 → Bool) (f : ℕ → ℝ)
    (hf : Summable (fun m : ↑(constructA K₀ ε) => f m)) :
    ∑' (m : ↑(constructA K₀ ε)), f m =
    ∑' n, ∑ j : Fin 3, ∑ a ∈ ActiveSet ε (K₀ + n) j, f (a * nScale (K₀ + n)) := by
  have h_tsum_range :
      (∑' m : (Set.range (structEmbed K₀ ε)), f m) =
        ∑' p : (Σ n, Σ j, ↑(ActiveSet ε (K₀ + n) j)),
          f (structEmbed K₀ ε p) := by
    rw [ ← Equiv.tsum_eq ( Equiv.ofInjective _ ( structEmbed_injective K₀ ε ) ) ];
    rfl;
  convert h_tsum_range using 1;
  · rw [ show constructA K₀ ε = Set.range ( structEmbed K₀ ε ) from ?_ ];
    exact
      Set.Subset.antisymm (constructA_subset_range K₀ ε)
        (Set.range_subset_iff.mpr fun p => structEmbed_mem_constructA K₀ ε p)
  · erw [ Summable.tsum_sigma ];
    · refine' tsum_congr fun n => ?_;
      erw [ tsum_fintype ];
      erw [ Finset.sum_sigma' ];
      refine' Finset.sum_bij ( fun x hx => ⟨ x.1, x.2, by
        exact Finset.mem_sigma.mp hx |>.2 ⟩ ) _ _ _ _ <;> simp +decide [ structEmbed ];
      · intro ⟨j1, a1⟩ _ ⟨j2, a2⟩ _ hj heq; simp at hj; subst hj; simpa using heq
      · exact fun b => ⟨ b.1, b.2.1, b.2.2, rfl ⟩;
    · convert hf.comp_injective _;
      rotate_left;
      use fun p => ⟨ structEmbed K₀ ε p, structEmbed_mem_constructA K₀ ε p ⟩;
      · exact fun p q h => by simpa using structEmbed_injective K₀ ε <| Subtype.ext_iff.mp h;
      · rfl

/-
Algebraic simplification: the structured sum equals basePointM + swap sums.
-/
set_option linter.flexible false in
set_option linter.style.multiGoal false in
set_option linter.style.refine false in
lemma structured_sum_eq_base_plus_swap (ε : ℕ → Fin 3 → Bool) (i : Fin 3) :
    (∑' n, ∑ j : Fin 3, ∑ a ∈ ActiveSet ε (K₀ + n) j,
      (M_mat.mulVec (fun l : Fin 3 =>
        1 / (((a * nScale (K₀ + n) : ℕ) : ℝ) + ((l : ℕ) : ℝ)))) i) =
    basePointM K₀ i +
    ∑' n, ∑ j : Fin 3, if ε (K₀ + n) j then swapContribM K₀ n j i else 0 := by
  unfold ActiveSet swapContribM basePointM;
  rw [← Summable.tsum_add]
  congr
  ext n
  rw [← Finset.sum_add_distrib]
  congr
  ext j
  split_ifs <;> norm_num
  · refine' summable_sum fun j _ => ?_;
    -- Each term is a fixed multiple of a summable sequence.
    have h_summable : Summable (fun n : ℕ => (1 : ℝ) / (nScale (K₀ + n) : ℝ)) := by
      norm_num [ nScale ];
      exact
        Summable.of_nonneg_of_le
          (fun n => by positivity)
          (fun n => by
            rw [inv_le_comm₀] <;> norm_num <;> ring_nf <;>
              nlinarith [
                show (m_const : ℝ) ≥ 1 by
                  exact_mod_cast by decide])
          (summable_nat_add_iff 1 |>.2 <|
            Real.summable_one_div_nat_pow.2 one_lt_two)
    refine' summable_sum fun a ha => ?_;
    simp_all +decide [ Matrix.mulVec, dotProduct ];
    refine' summable_sum fun x _ => ?_;
    refine' Summable.mul_left ?_ ?_;
    refine'
      Summable.of_nonneg_of_le
        (fun n => inv_nonneg.2 <| by positivity) (fun n => ?_) h_summable
    gcongr;
    · exact Nat.cast_pos.mpr ( nScale_pos _ );
    · exact
        le_add_of_le_of_nonneg
          (le_mul_of_one_le_left (Nat.cast_nonneg _)
            (mod_cast Nat.one_le_iff_ne_zero.mpr <|
              by fin_cases j <;> fin_cases ha <;> trivial))
          (Nat.cast_nonneg _)
  · have h_summable :
        Summable
          (fun n =>
            ∑ j : Fin 3,
              |if ε (K₀ + n) j then swapContribM K₀ n j i else 0|) := by
      have h_summable : Summable (fun n => ∑ j : Fin 3, |swapContribM K₀ n j i|) := by
        have h_summable :
            ∀ n,
              ∑ j : Fin 3, |swapContribM K₀ n j i| ≤
                3 * eGameSeq K₀ n + ∑ j : Fin 3, |aGameSeq j K₀ n| := by
          intro n
          have h_summable : ∀ j, |swapContribM K₀ n j i| ≤ eGameSeq K₀ n + |aGameSeq j K₀ n| := by
            intros j
            have h_swap_bound :
                |swapContribM K₀ n j i -
                    if i = j then aGameSeq j K₀ n else 0| ≤
                  eGameSeq K₀ n := by
              convert swapContrib_bound n j i using 1;
            split_ifs at h_swap_bound <;>
              exact abs_le.mpr
                ⟨ by
                    cases abs_cases (aGameSeq j K₀ n) <;>
                      linarith [abs_le.mp h_swap_bound],
                  by
                    cases abs_cases (aGameSeq j K₀ n) <;>
                      linarith [abs_le.mp h_swap_bound] ⟩
          generalize_proofs at *; (
          exact
            le_trans
              (Finset.sum_le_sum fun _ _ => h_summable _)
              (by simp +decide [Finset.sum_add_distrib]));
        refine'
          Summable.of_nonneg_of_le
            (fun n => Finset.sum_nonneg fun _ _ => abs_nonneg ?_)
            (fun n => h_summable n) ?_
        refine' Summable.add ?_ ?_;
        · exact Summable.mul_left _ ( eGameSeq_summable K₀ );
        · exact summable_sum fun j _ => Summable.abs ( aGameSeq_summable j K₀ );
      exact
        Summable.of_nonneg_of_le
          (fun n => Finset.sum_nonneg fun _ _ => abs_nonneg _)
          (fun n => Finset.sum_le_sum fun _ _ => by split_ifs <;> norm_num)
          h_summable
    refine' .of_norm ?_;
    exact h_summable.of_nonneg_of_le ( fun n => norm_nonneg _ ) fun n => norm_sum_le _ _

/-
**Harmonic Sum Decomposition**: The M-transformed harmonic sums of `constructA`
equal the base point plus the sum of swap contributions.
-/
lemma MHarmonicSums_decompose (ε : ℕ → Fin 3 → Bool) (i : Fin 3) :
    (M_mat.mulVec (fun l : Fin 3 =>
      ∑' (m : constructA K₀ ε), 1 / (((m : ℕ) : ℝ) + ((l : ℕ) : ℝ)))) i =
    basePointM K₀ i +
    ∑' n, ∑ j : Fin 3, if ε (K₀ + n) j then swapContribM K₀ n j i else 0 := by
  have h_sum :
      ∑ l : Fin 3,
        M_mat i l * ∑' m : ↑(constructA K₀ ε), 1 / ((m : ℝ) + l) =
      ∑' m : ↑(constructA K₀ ε),
        ∑ l : Fin 3, M_mat i l / ((m : ℝ) + l) := by
    have h_sum : ∀ l : Fin 3, Summable (fun m : ↑(constructA K₀ ε) => (1 : ℝ) / ((m : ℝ) + l)) := by
      intro l
      have h_summable : Summable (fun m : ↑(constructA K₀ ε) => (1 : ℝ) / (m : ℝ)) := by
        convert constructA_summable K₀ ε using 1
      have h_summable_l : Summable (fun m : ↑(constructA K₀ ε) => (1 : ℝ) / ((m : ℝ) + l)) := by
        exact
          Summable.of_nonneg_of_le
            (fun m => by positivity)
            (fun m => by
              simpa using
                inv_anti₀
                  (by exact Nat.cast_pos.mpr <| constructA_pos K₀ ε m m.2) <|
                    by
                      linarith [
                        show (m : ℝ) ≥ 1 from
                          Nat.one_le_cast.mpr <| constructA_pos K₀ ε m m.2])
            h_summable
      exact h_summable_l;
    have h_sum :
        ∀ {f : Fin 3 → (constructA K₀ ε) → ℝ},
          (∀ l, Summable (f l)) →
            ∑ l, ∑' m, f l m = ∑' m, ∑ l, f l m :=
      fun {f} a => (Summable.tsum_finsetSum fun i _ => a i).symm
    convert h_sum _ using 3;
    · simp +decide [ div_eq_mul_inv, tsum_mul_left ];
    · exact fun l =>
        Summable.mul_left _
          (by
            simpa using
              ‹∀ l : Fin 3,
                Summable fun m : ↑(constructA K₀ ε) => 1 / (m + l : ℝ)› l)
  convert tsum_constructA_eq ε ( fun m => ∑ l : Fin 3, M_mat i l / ( m + l : ℝ ) ) ?_ using 1;
  · rw [ ← structured_sum_eq_base_plus_swap ];
    simp +decide [ div_eq_mul_inv, Matrix.mulVec, dotProduct ];
  · have h_summable : Summable (fun m : ↑(constructA K₀ ε) => (1 : ℝ) / (m : ℝ)) := by
      convert constructA_summable K₀ ε using 1;
    have h_summable :
        ∀ l : Fin 3,
          Summable (fun m : ↑(constructA K₀ ε) => (1 : ℝ) / ((m : ℝ) + l)) := by
      intro l
      have h_summable : Summable (fun m : ↑(constructA K₀ ε) => (1 : ℝ) / (m : ℝ)) := by
        convert h_summable using 1
      have h_summable : Summable (fun m : ↑(constructA K₀ ε) => (1 : ℝ) / ((m : ℝ) + l)) := by
        exact
          Summable.of_nonneg_of_le
            (fun m => by positivity)
            (fun m => by
              simpa using
                inv_anti₀
                  (by
                    norm_cast
                    linarith [constructA_pos K₀ ε m m.2])
                  (by
                    linarith [
                      show (m : ℝ) ≥ 1 from
                        mod_cast constructA_pos K₀ ε m m.2]))
            h_summable
      exact h_summable;
    exact summable_sum fun l _ => by
      simpa [div_eq_mul_inv] using h_summable l |> Summable.mul_left _

/-! ## Target box -/

/-- The target box in M-coordinates. -/
def targetBoxM (K : ℕ) : Set (Fin 3 → ℝ) :=
  { q | ∀ j : Fin 3,
    basePointM K j + aGameSeq j K 0 < q j ∧
    q j < basePointM K j + 2 * aGameSeq j K 0 }

lemma targetBoxM_isOpen (K : ℕ) : IsOpen (targetBoxM K) := by
  unfold targetBoxM
  simp only [setOf_forall]
  exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (continuous_apply i)

lemma targetBoxM_nonempty (K : ℕ) : (targetBoxM K).Nonempty :=
  ⟨fun j => basePointM K j + 3 / 2 * aGameSeq j K 0,
   fun j => ⟨by linarith [aGameSeq_pos j K 0], by linarith [aGameSeq_pos j K 0]⟩⟩

/-! ## 3D Game and Main Construction -/

/-- The 3D game state from Kovač's paper.
At each step n, for each coordinate j, Alice decides whether to include the swap
based on the cautious greedy condition. -/
def game3D (q : Fin 3 → ℝ) : ℕ → Fin 3 → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun i =>
    game3D q n i + ∑ j : Fin 3,
      if game3D q n j + 3 * aGameSeq j K₀ n ≤ q j - basePointM K₀ j
      then swapContribM K₀ n j i else 0

/-- The game choices derived from the 3D game state. -/
def gameEpsilon (q : Fin 3 → ℝ) (n : ℕ) (j : Fin 3) : Bool :=
  if K₀ ≤ n then
    decide (game3D q (n - K₀) j + 3 * aGameSeq j K₀ (n - K₀) ≤ q j - basePointM K₀ j)
  else false

/-- The perturbation for coordinate j in the 3D game. -/
def gameDelta (q : Fin 3 → ℝ) (j : Fin 3) (n : ℕ) : ℝ :=
  game3D q (n + 1) j - game3D q n j -
    (if game3D q n j + 3 * aGameSeq j K₀ n ≤ q j - basePointM K₀ j
     then aGameSeq j K₀ n else 0)

set_option linter.flexible false in
set_option linter.style.multiGoal false in
set_option linter.style.refine false in
lemma gameDelta_bound (q : Fin 3 → ℝ) (j : Fin 3) (n : ℕ) :
    |gameDelta q j n| ≤ 3 * eGameSeq K₀ n := by
  -- By definition of `gameDelta`, we have:
  have h_gameDelta_def :
      gameDelta q j n =
        ∑ l : Fin 3,
          (if game3D q n l + 3 * aGameSeq l K₀ n ≤ q l - basePointM K₀ l then
            swapContribM K₀ n l j
          else
            0) -
        (if game3D q n j + 3 * aGameSeq j K₀ n ≤ q j - basePointM K₀ j then
          aGameSeq j K₀ n
        else
          0) := by
    unfold gameDelta;
    rw [
      show game3D q (n + 1) =
          fun i =>
            game3D q n i + ∑ l : Fin 3,
              (if game3D q n l + 3 * aGameSeq l K₀ n ≤ q l - basePointM K₀ l then
                swapContribM K₀ n l i
              else
                0) from rfl]
    norm_num
  -- By definition of `swapContribM`, we have:
  have h_swapContribM_bound :
      ∀ l : Fin 3, ∀ j : Fin 3,
        |swapContribM K₀ n l j -
          if l = j then aGameSeq j K₀ n else 0| ≤ eGameSeq K₀ n := by
    intro l i
    have := swapContrib_bound n l i
    rwa [show (if l = i then aGameSeq i K₀ n else 0) =
         (if i = l then aGameSeq l K₀ n else 0) from by
      by_cases h : l = i <;> simp only [h, ite_true, ite_false, eq_comm] at *]
  rw [ h_gameDelta_def ];
  refine'
    le_trans (?_ : ?_ ≤ ?_)
      (le_trans
        (Finset.sum_le_sum fun i _ =>
          show
            |if game3D q n i + 3 * aGameSeq i K₀ n ≤ q i - basePointM K₀ i then
                swapContribM K₀ n i j -
                  if i = j then aGameSeq j K₀ n else 0
              else
                0| ≤ eGameSeq K₀ n from ?_)
        ?_)
  nontriviality;
  convert Finset.abs_sum_le_sum_abs _ _ using 2;
  any_goals exact Finset.univ;
  · split_ifs <;> simp +decide [ *, Finset.sum_ite ];
  · infer_instance;
  · split_ifs <;> simp_all +decide [ abs_le ];
    · simpa using h_swapContribM_bound j j;
    · have := h_swapContribM_bound i j; simp [if_neg ‹_›] at this; exact ⟨by linarith, by linarith⟩
    · exact eGameSeq_nonneg K₀ n;
  · norm_num

lemma game3D_eq_gameSeq (q : Fin 3 → ℝ) (j : Fin 3) (n : ℕ) :
    game3D q n j = gameSeq (aGameSeq j K₀) (q j - basePointM K₀ j)
      (gameDelta q j) 0 n := by
  -- By definition of gameDelta, we have:
  have h_delta : ∀ n,
      game3D q (n + 1) j - game3D q n j -
          (if game3D q n j + 3 * aGameSeq j K₀ n ≤ q j - basePointM K₀ j then
            aGameSeq j K₀ n
          else
            0) =
        gameDelta q j n :=
    fun n => Real.ext_cauchy rfl
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [gameSeq_succ]
    unfold aliceChoice at *
    simp only [← ih]; linarith [h_delta n]

lemma game3D_converges (q : Fin 3 → ℝ) (hq : q ∈ targetBoxM K₀) (j : Fin 3) :
    Tendsto (fun n => game3D q n j) atTop (nhds (q j - basePointM K₀ j)) := by
  rw [
    show (fun n => game3D q n j) =
        fun n =>
          gameSeq (aGameSeq j K₀) (q j - basePointM K₀ j)
            (gameDelta q j) 0 n from
      funext fun n => game3D_eq_gameSeq q j n]
  apply_rules [ game_converges_to_target ];
  any_goals intro k; exact mul_nonneg zero_le_three ( eGameSeq_nonneg K₀ k );
  any_goals intro k; exact aGameSeq_pos j K₀ k;
  any_goals intro k; rw [ tsum_mul_left ] ; exact error_domination_3x j k;
  any_goals intro k; exact gameDelta_bound q j k;
  · exact aGameSeq_summable j K₀
  · exact Summable.mul_left _ (eGameSeq_summable K₀)
  · exact fun k => tail_domination j k
  · linarith [ hq j |>.1 ];
  · linarith [ hq j |>.2 ]

set_option linter.flexible false in
set_option linter.style.refine false in
lemma game3D_limit_eq_tsum (q : Fin 3 → ℝ) (hq : q ∈ targetBoxM K₀) (i : Fin 3) :
    (∑' n, ∑ j : Fin 3,
      if gameEpsilon q (K₀ + n) j = true then swapContribM K₀ n j i else 0) =
    q i - basePointM K₀ i := by
  -- Expand `game3D` as the partial sums of the chosen swap contributions.
  have h_game3D_sum :
      ∀ N,
        game3D q N i =
          ∑ n ∈ Finset.range N,
            (fun n =>
              ∑ j,
                if gameEpsilon q (K₀ + n) j = true then
                  swapContribM K₀ n j i
                else
                  0) n := by
    intro N;
    induction N <;> simp_all +decide [ Finset.sum_range_succ ];
    · rfl;
    · rw [ ← ‹game3D q _ i = ∑ x ∈ Finset.range _, _›, game3D ];
      unfold gameEpsilon; aesop;
  refine' HasSum.tsum_eq ?_;
  rw [ hasSum_iff_tendsto_nat_of_summable_norm ];
  · simpa only [ ← h_game3D_sum ] using game3D_converges q hq i;
  · -- Bound each chosen swap contribution by a summable majorant.
    have h_swapContribM_bound :
        ∀ n j i,
          |swapContribM K₀ n j i| ≤ aGameSeq j K₀ n + eGameSeq K₀ n := by
      intro n j i;
      have := swapContrib_bound n j i;
      have h_nonneg : 0 ≤ aGameSeq j K₀ n := by
        exact
          div_nonneg
            (show 0 ≤ c_coeff j from by
              fin_cases j <;> norm_num [c_coeff])
            (pow_nonneg (Nat.cast_nonneg _) _)
      split_ifs at this <;>
        exact abs_le.mpr
          ⟨by linarith [abs_le.mp this, h_nonneg],
           by linarith [abs_le.mp this, h_nonneg]⟩
    refine'
      Summable.of_nonneg_of_le
        (fun n => norm_nonneg ?_) (fun n => ?_)
        (show
          Summable fun n =>
            ∑ j : Fin 3, aGameSeq j K₀ n + ∑ j : Fin 3, eGameSeq K₀ n from ?_)
    · exact
        le_trans (norm_sum_le _ _)
          (le_trans
            (Finset.sum_le_sum fun _ _ => by aesop)
            (by
              simpa only [Finset.sum_add_distrib] using
                Finset.sum_le_sum fun _ _ => h_swapContribM_bound _ _ _))
    · exact
        Summable.add
          (summable_sum fun j _ => aGameSeq_summable j K₀)
          (summable_sum fun j _ => eGameSeq_summable K₀)

/-- The box is covered: for each point in the target box, the game produces
choices that converge to that point. -/
theorem exists_box_covered :
    ∃ (B : Set (Fin 3 → ℝ)), IsOpen B ∧ B.Nonempty ∧
    ∀ q ∈ B, ∃ ε : ℕ → Fin 3 → Bool,
      M_mat.mulVec (fun j : Fin 3 =>
        ∑' (n : constructA K₀ ε), 1 / (((n : ℕ) : ℝ) + ((j : ℕ) : ℝ))) = q := by
  refine ⟨targetBoxM K₀, targetBoxM_isOpen K₀, targetBoxM_nonempty K₀, ?_⟩
  intro q hq
  refine ⟨gameEpsilon q, ?_⟩
  ext i
  have h1 := MHarmonicSums_decompose (gameEpsilon q) i
  have h2 := game3D_limit_eq_tsum q hq i
  linarith

/-! ## Final Theorems -/

/-- There exists a nonempty open set `Q` such that `M_inv · Q ⊆ harmonicSubseriesSet`. -/
lemma exists_open_set_maps_to_harmonicSet :
    ∃ Q : Set (Fin 3 → ℝ), IsOpen Q ∧ Q.Nonempty ∧
    ∀ q ∈ Q, M_inv.mulVec q ∈ harmonicSubseriesSet := by
  obtain ⟨B, hB_open, hB_ne, hB_cover⟩ := exists_box_covered
  exact ⟨B, hB_open, hB_ne, fun q hq => by
    obtain ⟨ε, hε⟩ := hB_cover q hq
    exact ⟨constructA K₀ ε, constructA_infinite K₀ ε, constructA_pos K₀ ε,
           constructA_summable K₀ ε, fun i => by
      have h := congr_arg M_inv.mulVec hε.symm
      rw [Matrix.mulVec_mulVec, M_inv_mul_mat, Matrix.one_mulVec] at h
      exact congr_fun h i⟩⟩

/-- The set of harmonic subseries points contains an open ball. -/
lemma exists_ball_in_harmonicSubseriesSet :
    ∃ (center : Fin 3 → ℝ) (radius : ℝ), 0 < radius ∧
    Metric.ball center radius ⊆ harmonicSubseriesSet := by
  obtain ⟨Q, hQ_open, hQ_ne, hQ_sub⟩ := exists_open_set_maps_to_harmonicSet
  exact image_open_contains_ball Q hQ_open hQ_ne hQ_sub

/-- **Theorem 1** (Kovač, answering Erdős–Graham 1980):
The set of harmonic subseries points has non-empty interior. -/
theorem harmonicSubseriesSet_interior_nonempty :
    (interior harmonicSubseriesSet).Nonempty := by
  obtain ⟨center, radius, hr, hball⟩ := exists_ball_in_harmonicSubseriesSet
  exact ⟨center, interior_mono hball (mem_interior.mpr ⟨Metric.ball center radius,
    Subset.refl _, Metric.isOpen_ball, Metric.mem_ball_self hr⟩)⟩

#print axioms harmonicSubseriesSet_interior_nonempty
-- 'Erdos268.harmonicSubseriesSet_interior_nonempty' depends on axioms: [propext, Classical.choice,
-- Quot.sound]

end
end Erdos268
