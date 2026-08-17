/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The fixed-edge estimate in the DGK argument

This file isolates the finite calculation used after exposing the initial
colours outside one fixed edge in the Duraj--Gutowski--Kozik random-greedy
argument.  There are no measure-theoretic assumptions hidden in the result:
`outsideWeight` is the mass of an exposed outside configuration and
`redGood` is the conditional mass of the event that the fixed edge finishes
red while the two global good events hold.

For a fixed outside configuration, let `penalty v` be `d / j` when `v` is
endangered with severity `j`, and zero otherwise.  Independence of the
initial colour and priority of each vertex gives

`redGood ≤ 2⁻ˢ (∏ v in e, (1 + penalty v) - 1)`.

The subtraction of one is the excluded initially-all-red colouring.  The
product is at most `exp X`, where `X` is the sum of the penalties.  On the
good event `X ≤ M`, and `exp X - 1 ≤ X exp M`.  Averaging and the standard
severity-class estimate `E X ≤ q*d/r` gives the claimed bound

`P(e finishes red, good) ≤ 2⁻ˢ exp(M) q*d/r`.

The lemmas below also formalize the two elementary combinatorial steps which
produce the severity-class estimate: severity vertices inject into their
certifying threat edges, and rank-wise bounds sum with cost `d/j`.
-/

open scoped BigOperators

namespace Erdos1027.DGKFixedEdge

open Finset

/-- The real number denoted informally by `2⁻ⁿ`. -/
noncomputable def invTwoPow (n : ℕ) : ℝ := ((2 : ℝ)⁻¹) ^ n

@[simp] lemma invTwoPow_zero : invTwoPow 0 = 1 := by
  simp [invTwoPow]

lemma invTwoPow_nonneg (n : ℕ) : 0 ≤ invTwoPow n := by
  unfold invTwoPow
  exact pow_nonneg (inv_nonneg.mpr (by positivity)) n

/-- Expanding independent red-or-high-priority choices over a finite edge.

The empty subset is the initially-all-red choice.  Thus the sum over
nonempty sets of exceptional (blue, high-priority) vertices is the full
product minus one. -/
lemma sum_nonempty_subsets_prod_eq_prod_one_add_sub_one
    {V : Type*} [DecidableEq V] (edge : Finset V) (penalty : V → ℝ) :
    (∑ t ∈ edge.powerset.filter Finset.Nonempty, ∏ v ∈ t, penalty v) =
      (∏ v ∈ edge, (1 + penalty v)) - 1 := by
  classical
  have hexpand :
      (∏ v ∈ edge, (1 + penalty v)) =
        ∑ t ∈ edge.powerset, ∏ v ∈ t, penalty v := by
    simpa using (Finset.prod_one_add (R := ℝ) (f := penalty) edge)
  rw [hexpand]
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := edge.powerset) (p := Finset.Nonempty)
    (f := fun t ↦ ∏ v ∈ t, penalty v)]
  simp only [Finset.not_nonempty_iff_eq_empty]
  have hemptyFilter :
      edge.powerset.filter (fun t ↦ t = ∅) = {∅} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    constructor
    · rintro ⟨_, ht⟩
      exact ht
    · intro ht
      subst t
      exact ⟨Finset.empty_subset _, rfl⟩
  rw [hemptyFilter]
  simp

/-- For `x ≥ 0`, the exponential excess is bounded by its tangent bound
at the right endpoint: `exp x - 1 ≤ x * exp M` whenever `x ≤ M`. -/
lemma exp_sub_one_le_mul_exp_of_nonneg_of_le {x M : ℝ}
    (hx : 0 ≤ x) (hxM : x ≤ M) :
    Real.exp x - 1 ≤ x * Real.exp M := by
  have hneg := Real.add_one_le_exp (-x)
  have hmul := mul_le_mul_of_nonneg_left hneg (Real.exp_pos x).le
  have hcancel : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hlocal : Real.exp x - 1 ≤ x * Real.exp x := by
    rw [hcancel] at hmul
    nlinarith
  have hexp : Real.exp x ≤ Real.exp M := Real.exp_le_exp.mpr hxM
  exact hlocal.trans (mul_le_mul_of_nonneg_left hexp hx)

/-- The pointwise product/exponential estimate used for one exposed outside
configuration. -/
lemma prod_one_add_sub_one_le_exp_cap_mul_sum
    {V : Type*} [DecidableEq V] (edge : Finset V) (penalty : V → ℝ) {M : ℝ}
    (hpenalty : ∀ v ∈ edge, 0 ≤ penalty v)
    (hcap : ∑ v ∈ edge, penalty v ≤ M) :
    (∏ v ∈ edge, (1 + penalty v)) - 1 ≤
      Real.exp M * ∑ v ∈ edge, penalty v := by
  let X : ℝ := ∑ v ∈ edge, penalty v
  have hX : 0 ≤ X := Finset.sum_nonneg fun v hv ↦ hpenalty v hv
  have hprod :
      ∏ v ∈ edge, (1 + penalty v) ≤ Real.exp X := by
    calc
      ∏ v ∈ edge, (1 + penalty v) ≤
          ∏ v ∈ edge, Real.exp (penalty v) := by
        exact Finset.prod_le_prod
          (fun v hv ↦ add_nonneg zero_le_one (hpenalty v hv))
          (fun v _ ↦ (add_comm 1 (penalty v)).le.trans
            (Real.add_one_le_exp (penalty v)))
      _ = Real.exp X := by
        simpa only [X] using (Real.exp_sum edge penalty).symm
  calc
    (∏ v ∈ edge, (1 + penalty v)) - 1 ≤ Real.exp X - 1 := sub_le_sub_right hprod 1
    _ ≤ X * Real.exp M :=
      exp_sub_one_le_mul_exp_of_nonneg_of_le hX hcap
    _ = Real.exp M * ∑ v ∈ edge, penalty v := by
      simp only [X]
      ring

/-! ## Threat certificates and severity classes -/

/-- Severity-`j` vertices inject into the severity-`j` certifying threats.

This is the precise cardinality statement behind `R_j ≤ T_j`.  The caller
supplies the certifying threat of each endangered vertex, the fact that it
has the same rank as the vertex's severity, and injectivity of certificates.
-/
lemma severityClass_card_le_threatClass_card
    {V E : Type*} [DecidableEq V] [DecidableEq E]
    (vertices : Finset V) (threats : Finset E)
    (severity : V → ℕ) (rank : E → ℕ) (certificate : V → E)
    (hcertificate : ∀ v ∈ vertices, certificate v ∈ threats)
    (hrank : ∀ v ∈ vertices, rank (certificate v) = severity v)
    (hinj : Set.InjOn certificate (vertices : Set V)) (j : ℕ) :
    (vertices.filter fun v ↦ severity v = j).card ≤
      (threats.filter fun f ↦ rank f = j).card := by
  apply Finset.card_le_card_of_injOn certificate
  · intro v hv
    obtain ⟨hvVertices, hvSeverity⟩ := Finset.mem_filter.mp hv
    apply Finset.mem_filter.mpr
    exact ⟨hcertificate v hvVertices,
      (hrank v hvVertices).trans hvSeverity⟩
  · intro v₁ hv₁ v₂ hv₂ heq
    exact hinj (Finset.mem_filter.mp hv₁).1 (Finset.mem_filter.mp hv₂).1 heq

/-- Rank-wise domination, followed by the lower rank cutoff `r ≤ j`,
gives the expected-severity estimate.

In the application `expectedCount j = E R_j`, `threatWeight j = q_j`, and
the conclusion is `E X ≤ q*d/r`. -/
lemma sum_expected_severityCost_le
    (ranks : Finset ℕ) (r : ℕ) (d q : ℝ)
    (expectedCount threatWeight : ℕ → ℝ)
    (hr : 0 < r) (hd : 0 ≤ d)
    (hrank : ∀ j ∈ ranks, r ≤ j)
    (hcount : ∀ j ∈ ranks, 0 ≤ expectedCount j)
    (hthreat : ∀ j ∈ ranks, 0 ≤ threatWeight j)
    (hdom : ∀ j ∈ ranks, expectedCount j ≤ threatWeight j)
    (hsum : ∑ j ∈ ranks, threatWeight j ≤ q) :
    ∑ j ∈ ranks, expectedCount j * (d / (j : ℝ)) ≤ q * d / r := by
  have hrReal : (0 : ℝ) < r := by exact_mod_cast hr
  calc
    ∑ j ∈ ranks, expectedCount j * (d / (j : ℝ)) ≤
        ∑ j ∈ ranks, threatWeight j * (d / (j : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjReal : (0 : ℝ) < j :=
        hrReal.trans_le (by exact_mod_cast hrank j hj)
      exact mul_le_mul_of_nonneg_right (hdom j hj) (div_nonneg hd hjReal.le)
    _ ≤ ∑ j ∈ ranks, threatWeight j * (d / (r : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjReal : (0 : ℝ) < j :=
        hrReal.trans_le (by exact_mod_cast hrank j hj)
      have hdiv : d / (j : ℝ) ≤ d / (r : ℝ) := by
        exact div_le_div_of_nonneg_left hd hrReal
          (by exact_mod_cast hrank j hj)
      exact mul_le_mul_of_nonneg_left hdiv (hthreat j hj)
    _ = (∑ j ∈ ranks, threatWeight j) * (d / (r : ℝ)) := by
      rw [Finset.sum_mul]
    _ ≤ q * (d / (r : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hsum (div_nonneg hd hrReal.le)
    _ = q * d / r := by ring

/-- Interchange the finite outside-configuration and severity-rank sums.
This is useful for rewriting `E X` as `∑_j (E R_j) d/j`. -/
lemma sum_weight_mul_severityCost
    {O : Type*} [DecidableEq O] (outcomes : Finset O) (ranks : Finset ℕ)
    (outsideWeight : O → ℝ) (count : O → ℕ → ℕ) (d : ℝ) :
    ∑ ω ∈ outcomes, outsideWeight ω *
        (∑ j ∈ ranks, (count ω j : ℝ) * (d / (j : ℝ))) =
      ∑ j ∈ ranks, (∑ ω ∈ outcomes, outsideWeight ω * count ω j) *
        (d / (j : ℝ)) := by
  calc
    _ = ∑ ω ∈ outcomes, ∑ j ∈ ranks,
        outsideWeight ω * ((count ω j : ℝ) * (d / (j : ℝ))) := by
      apply Finset.sum_congr rfl
      intro ω hω
      rw [Finset.mul_sum]
    _ = ∑ j ∈ ranks, ∑ ω ∈ outcomes,
        outsideWeight ω * ((count ω j : ℝ) * (d / (j : ℝ))) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        _ = ∑ ω ∈ outcomes,
            (outsideWeight ω * (count ω j : ℝ)) * (d / (j : ℝ)) := by
          apply Finset.sum_congr rfl
          intro ω hω
          ring
        _ = _ := by rw [Finset.sum_mul]

/-! ## Fixed-edge probability estimates -/

/-- The fixed-edge estimate once the expected total severity penalty has
been bounded.  This is deliberately a finite weighted-sum statement, so it
can be applied equally to a finite probability space represented by counts
or by rational/real masses.

The hypothesis `hconditional` is precisely what the direct exposure of the
colours and priorities on the fixed edge proves. -/
theorem fixedEdge_finalRed_good_le_of_expectedPenalty
    {O V : Type*} [DecidableEq O] [DecidableEq V]
    (outcomes : Finset O) (edge : Finset V)
    (outsideWeight redGood : O → ℝ) (penalty : O → V → ℝ)
    (M expectedPenaltyBound : ℝ)
    (hweight : ∀ ω ∈ outcomes, 0 ≤ outsideWeight ω)
    (hpenalty : ∀ ω ∈ outcomes, ∀ v ∈ edge, 0 ≤ penalty ω v)
    (hcap : ∀ ω ∈ outcomes, ∑ v ∈ edge, penalty ω v ≤ M)
    (hconditional : ∀ ω ∈ outcomes,
      redGood ω ≤ invTwoPow edge.card *
        ((∏ v ∈ edge, (1 + penalty ω v)) - 1))
    (hexpectation :
      ∑ ω ∈ outcomes, outsideWeight ω * (∑ v ∈ edge, penalty ω v) ≤
        expectedPenaltyBound) :
    ∑ ω ∈ outcomes, outsideWeight ω * redGood ω ≤
      invTwoPow edge.card * Real.exp M * expectedPenaltyBound := by
  have hconstant : 0 ≤ invTwoPow edge.card * Real.exp M :=
    mul_nonneg (invTwoPow_nonneg _) (Real.exp_pos _).le
  calc
    ∑ ω ∈ outcomes, outsideWeight ω * redGood ω ≤
        ∑ ω ∈ outcomes, outsideWeight ω *
          (invTwoPow edge.card * Real.exp M * ∑ v ∈ edge, penalty ω v) := by
      apply Finset.sum_le_sum
      intro ω hω
      apply mul_le_mul_of_nonneg_left _ (hweight ω hω)
      calc
        redGood ω ≤ invTwoPow edge.card *
            ((∏ v ∈ edge, (1 + penalty ω v)) - 1) := hconditional ω hω
        _ ≤ invTwoPow edge.card *
            (Real.exp M * ∑ v ∈ edge, penalty ω v) := by
          exact mul_le_mul_of_nonneg_left
            (prod_one_add_sub_one_le_exp_cap_mul_sum edge (penalty ω)
              (hpenalty ω hω) (hcap ω hω))
            (invTwoPow_nonneg _)
        _ = invTwoPow edge.card * Real.exp M *
            ∑ v ∈ edge, penalty ω v := by ring
    _ = (invTwoPow edge.card * Real.exp M) *
        ∑ ω ∈ outcomes, outsideWeight ω * (∑ v ∈ edge, penalty ω v) := by
      calc
        _ = ∑ ω ∈ outcomes, (invTwoPow edge.card * Real.exp M) *
            (outsideWeight ω * (∑ v ∈ edge, penalty ω v)) := by
          apply Finset.sum_congr rfl
          intro ω hω
          ring
        _ = _ := by rw [Finset.mul_sum]
    _ ≤ (invTwoPow edge.card * Real.exp M) * expectedPenaltyBound :=
      mul_le_mul_of_nonneg_left hexpectation hconstant
    _ = invTwoPow edge.card * Real.exp M * expectedPenaltyBound := by ring

/-- The advertised DGK fixed-edge estimate, with the expected-penalty bound
supplied rank by rank.  Here `count ω j` is `R_j` for the exposed outside
configuration `ω`, while `threatWeight j` is `q_j`.

The conclusion is exactly
`P(e final red, good) ≤ 2^{-|e|} exp(M) q*d/r`.
-/
theorem fixedEdge_finalRed_good_le
    {O V : Type*} [DecidableEq O] [DecidableEq V]
    (outcomes : Finset O) (edge : Finset V) (ranks : Finset ℕ)
    (outsideWeight redGood : O → ℝ) (penalty : O → V → ℝ)
    (count : O → ℕ → ℕ) (threatWeight : ℕ → ℝ)
    (M q d : ℝ) (r : ℕ)
    (hr : 0 < r) (hd : 0 ≤ d)
    (hweight : ∀ ω ∈ outcomes, 0 ≤ outsideWeight ω)
    (hpenalty : ∀ ω ∈ outcomes, ∀ v ∈ edge, 0 ≤ penalty ω v)
    (hcap : ∀ ω ∈ outcomes, ∑ v ∈ edge, penalty ω v ≤ M)
    (hconditional : ∀ ω ∈ outcomes,
      redGood ω ≤ invTwoPow edge.card *
        ((∏ v ∈ edge, (1 + penalty ω v)) - 1))
    (hpenaltyByRank : ∀ ω ∈ outcomes,
      ∑ v ∈ edge, penalty ω v =
        ∑ j ∈ ranks, (count ω j : ℝ) * (d / (j : ℝ)))
    (hrank : ∀ j ∈ ranks, r ≤ j)
    (hthreat : ∀ j ∈ ranks, 0 ≤ threatWeight j)
    (hcount : ∀ j ∈ ranks,
      0 ≤ ∑ ω ∈ outcomes, outsideWeight ω * count ω j)
    (hdom : ∀ j ∈ ranks,
      ∑ ω ∈ outcomes, outsideWeight ω * count ω j ≤ threatWeight j)
    (hsum : ∑ j ∈ ranks, threatWeight j ≤ q) :
    ∑ ω ∈ outcomes, outsideWeight ω * redGood ω ≤
      invTwoPow edge.card * Real.exp M * (q * d / r) := by
  apply fixedEdge_finalRed_good_le_of_expectedPenalty
    outcomes edge outsideWeight redGood penalty M (q * d / r)
    hweight hpenalty hcap hconditional
  calc
    ∑ ω ∈ outcomes, outsideWeight ω * (∑ v ∈ edge, penalty ω v) =
        ∑ ω ∈ outcomes, outsideWeight ω *
          (∑ j ∈ ranks, (count ω j : ℝ) * (d / (j : ℝ))) := by
      apply Finset.sum_congr rfl
      intro ω hω
      rw [hpenaltyByRank ω hω]
    _ = ∑ j ∈ ranks,
        (∑ ω ∈ outcomes, outsideWeight ω * count ω j) * (d / (j : ℝ)) :=
      sum_weight_mul_severityCost outcomes ranks outsideWeight count d
    _ ≤ q * d / r := by
      exact sum_expected_severityCost_le ranks r d q
        (fun j ↦ ∑ ω ∈ outcomes, outsideWeight ω * count ω j)
        threatWeight hr hd hrank hcount hthreat hdom hsum

/-! ## Uniform finite-probability-space interfaces

The Beck development uses Mathlib's `𝔼` notation on the finite type of DGK
trials.  The following two wrappers are the forms intended for direct use
there.  In particular, no conversion to an explicitly weighted `Finset` is
needed at the call site. -/

/-- Uniform-expectation version of
`fixedEdge_finalRed_good_le_of_expectedPenalty`. -/
theorem fixedEdge_finalRed_good_expect_le_of_expectedPenalty
    {O V : Type*} [Fintype O] [DecidableEq V]
    (edge : Finset V) (redGood : O → ℝ) (penalty : O → V → ℝ)
    (M expectedPenaltyBound : ℝ)
    (hpenalty : ∀ ω, ∀ v ∈ edge, 0 ≤ penalty ω v)
    (hcap : ∀ ω, ∑ v ∈ edge, penalty ω v ≤ M)
    (hconditional : ∀ ω,
      redGood ω ≤ invTwoPow edge.card *
        ((∏ v ∈ edge, (1 + penalty ω v)) - 1))
    (hexpectation :
      (𝔼 ω : O, ∑ v ∈ edge, penalty ω v) ≤ expectedPenaltyBound) :
    (𝔼 ω : O, redGood ω) ≤
      invTwoPow edge.card * Real.exp M * expectedPenaltyBound := by
  let C : ℝ := invTwoPow edge.card * Real.exp M
  have hC : 0 ≤ C :=
    mul_nonneg (invTwoPow_nonneg _) (Real.exp_pos _).le
  calc
    (𝔼 ω : O, redGood ω) ≤
        𝔼 ω : O, C * (∑ v ∈ edge, penalty ω v) := by
      apply Finset.expect_le_expect
      intro ω hω
      calc
        redGood ω ≤ invTwoPow edge.card *
            ((∏ v ∈ edge, (1 + penalty ω v)) - 1) := hconditional ω
        _ ≤ invTwoPow edge.card *
            (Real.exp M * ∑ v ∈ edge, penalty ω v) := by
          exact mul_le_mul_of_nonneg_left
            (prod_one_add_sub_one_le_exp_cap_mul_sum edge (penalty ω)
              (hpenalty ω) (hcap ω))
            (invTwoPow_nonneg _)
        _ = C * (∑ v ∈ edge, penalty ω v) := by
          simp only [C]
          ring
    _ = C * (𝔼 ω : O, ∑ v ∈ edge, penalty ω v) := by
      exact (Finset.mul_expect Finset.univ
        (fun ω : O ↦ ∑ v ∈ edge, penalty ω v) C).symm
    _ ≤ C * expectedPenaltyBound :=
      mul_le_mul_of_nonneg_left hexpectation hC
    _ = invTwoPow edge.card * Real.exp M * expectedPenaltyBound := by
      simp only [C]

/-- Uniform-expectation form of the complete rank-wise fixed-edge estimate.

This is the strongest generic theorem needed by the exposed-fiber assembly:
instantiate `O`
with `Trial α L`, `count ω j` with the number `R_j` of endangered vertices of
severity `j`, and `threatWeight j` with `q_j`. -/
theorem fixedEdge_finalRed_good_expect_le
    {O V : Type*} [Fintype O] [DecidableEq V]
    (edge : Finset V) (ranks : Finset ℕ)
    (redGood : O → ℝ) (penalty : O → V → ℝ)
    (count : O → ℕ → ℕ) (threatWeight : ℕ → ℝ)
    (M q d : ℝ) (r : ℕ)
    (hr : 0 < r) (hd : 0 ≤ d)
    (hpenalty : ∀ ω, ∀ v ∈ edge, 0 ≤ penalty ω v)
    (hcap : ∀ ω, ∑ v ∈ edge, penalty ω v ≤ M)
    (hconditional : ∀ ω,
      redGood ω ≤ invTwoPow edge.card *
        ((∏ v ∈ edge, (1 + penalty ω v)) - 1))
    (hpenaltyByRank : ∀ ω,
      ∑ v ∈ edge, penalty ω v =
        ∑ j ∈ ranks, (count ω j : ℝ) * (d / (j : ℝ)))
    (hrank : ∀ j ∈ ranks, r ≤ j)
    (hthreat : ∀ j ∈ ranks, 0 ≤ threatWeight j)
    (hcount : ∀ j ∈ ranks, 0 ≤ 𝔼 ω : O, (count ω j : ℝ))
    (hdom : ∀ j ∈ ranks,
      (𝔼 ω : O, (count ω j : ℝ)) ≤ threatWeight j)
    (hsum : ∑ j ∈ ranks, threatWeight j ≤ q) :
    (𝔼 ω : O, redGood ω) ≤
      invTwoPow edge.card * Real.exp M * (q * d / r) := by
  apply fixedEdge_finalRed_good_expect_le_of_expectedPenalty
    edge redGood penalty M (q * d / r) hpenalty hcap hconditional
  calc
    (𝔼 ω : O, ∑ v ∈ edge, penalty ω v) =
        𝔼 ω : O, ∑ j ∈ ranks,
          (count ω j : ℝ) * (d / (j : ℝ)) := by
      apply Finset.expect_congr rfl
      intro ω hω
      exact hpenaltyByRank ω
    _ = ∑ j ∈ ranks,
        𝔼 ω : O, (count ω j : ℝ) * (d / (j : ℝ)) := by
      exact Finset.expect_sum_comm Finset.univ ranks
        (fun ω j ↦ (count ω j : ℝ) * (d / (j : ℝ)))
    _ = ∑ j ∈ ranks,
        (𝔼 ω : O, (count ω j : ℝ)) * (d / (j : ℝ)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (Finset.expect_mul Finset.univ
        (fun ω : O ↦ (count ω j : ℝ)) (d / (j : ℝ))).symm
    _ ≤ q * d / r := by
      exact sum_expected_severityCost_le ranks r d q
        (fun j ↦ 𝔼 ω : O, (count ω j : ℝ)) threatWeight
        hr hd hrank hcount hthreat hdom hsum

end Erdos1027.DGKFixedEdge
