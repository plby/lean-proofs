/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos182.KeyRestriction

/-!
# The conditional product estimate in the Janzer--Sudakov restriction

Condition on all the neighbours of a fixed right vertex `v` having survived
independent vertex sampling.  A second right vertex `w` then survives with
conditional probability

`prod x in N(w) \ N(v), p x`.

The lemma below isolates the deterministic inequality used in JS Lemma 4.1.
The terms for which `N(w) ∩ N(v) = {u}` contribute at most `M`; the terms
with a second common neighbour contribute at most `M`, by the codegree
estimate and the elementary bound that a product of probabilities is at most
one.  Its last conclusion is the unnormalised expectation bound, obtained by
multiplying by `q(v)`.
-/

open Finset Fintype
open scoped BigOperators

namespace Erdos182

section ConditionalProduct

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- The right vertices in `B₀` incident with `u` which share a second
neighbour with `v`. -/
def collidingRight (R : A → B → Prop) [DecidableRel R]
    (B₀ : Finset B) (u : A) (v : B) : Finset B :=
  (B₀.filter (R u)).filter fun w ↦
    ∃ x, x ≠ u ∧ R x v ∧ R x w

/-- The conditional contribution of the possible right neighbours of `u`.
This is exactly the sum which occurs after conditioning on `N(v) ⊆ S`. -/
noncomputable def conditionalDegreeFactor (R : A → B → Prop)
    [DecidableRel R] (p : A → ℝ) (B₀ : Finset B) (u : A) (v : B) : ℝ :=
  ∑ w ∈ B₀.filter (R u),
    ∏ x ∈ (bipNeighborsB R w \ bipNeighborsB R v), p x

/-- The probability that all neighbours of a right vertex survive. -/
noncomputable def rightSurvivalProbability (R : A → B → Prop)
    [DecidableRel R] (p : A → ℝ) (v : B) : ℝ :=
  ∏ x ∈ bipNeighborsB R v, p x

/-- The vertex-retention probabilities in JS Lemma 4.1.  Writing the
probability as a quotient of natural powers avoids truncated subtraction in
the exponent. -/
noncomputable def dyadicProbability (alpha : A → ℕ) (t : ℕ) (x : A) : ℝ :=
  (2 : ℝ) ^ alpha x / (2 : ℝ) ^ t

/-- The common one-half of the conditional estimate. -/
noncomputable def dyadicConditionalScale (gamma r t : ℕ) : ℝ :=
  (2 : ℝ) ^ gamma / (2 : ℝ) ^ ((r - 1) * t)

/-- Quotient form of the exponent
`2^(gamma - (r-1)t + 1)`, valid without asking Lean to truncate a natural
subtraction. -/
theorem two_mul_dyadicConditionalScale (gamma r t : ℕ) :
    2 * dyadicConditionalScale gamma r t =
      (2 : ℝ) ^ (gamma + 1) / (2 : ℝ) ^ ((r - 1) * t) := by
  unfold dyadicConditionalScale
  rw [pow_succ]
  ring

theorem dyadicProbability_mem_unitInterval (alpha : A → ℕ) (t : ℕ)
    (halpha : ∀ x, alpha x ≤ t) (x : A) :
    0 ≤ dyadicProbability alpha t x ∧ dyadicProbability alpha t x ≤ 1 := by
  constructor
  · exact div_nonneg (by positivity) (by positivity)
  · exact (div_le_one (by positivity)).2
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (halpha x))

/-- Product of the dyadic probabilities over a finite vertex set. -/
theorem prod_dyadicProbability (alpha : A → ℕ) (t : ℕ) (S : Finset A) :
    ∏ x ∈ S, dyadicProbability alpha t x =
      (2 : ℝ) ^ (∑ x ∈ S, alpha x) / (2 : ℝ) ^ (t * S.card) := by
  classical
  simp only [dyadicProbability, Finset.prod_div_distrib,
    Finset.prod_pow_eq_pow_sum]
  congr 1
  simp [pow_mul, Nat.mul_comm]

/-- The elementary estimate `n ≤ 2^n`, kept local to the restriction
argument so its use in the collision calculation is explicit. -/
theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 ≤ 2 ^ n + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add_left (Nat.one_le_two_pow) _
        _ = 2 ^ (n + 1) := by rw [pow_succ]; omega

/-- Cancellation of the sampling probability at the distinguished common
neighbour. -/
theorem dyadic_cancellation (a gamma r t : ℕ) (hr : 1 ≤ r) :
    (2 : ℝ) ^ a *
        (((2 : ℝ) ^ gamma / (2 : ℝ) ^ (t * r)) /
          ((2 : ℝ) ^ a / (2 : ℝ) ^ t)) =
      dyadicConditionalScale gamma r t := by
  have htr : t * r = t + (r - 1) * t := by
    conv_lhs => rw [← Nat.sub_add_cancel hr]
    simp [Nat.mul_add, Nat.add_comm, Nat.mul_comm]
  rw [htr, pow_add]
  unfold dyadicConditionalScale
  field_simp

/-- The numerical codegree term in JS Lemma 4.1 is at most the dyadic
conditional scale. -/
theorem dyadic_codegree_term_le (r s t gamma : ℕ)
    (hexp : (r - 1) * t ≤ r * s)
    (hgamma : r * (s + 1) ≤ gamma) :
    ((r * 2 ^ (r * s - (r - 1) * t) : ℕ) : ℝ) ≤
      dyadicConditionalScale gamma r t := by
  let d := (r - 1) * t
  have hnat : r * 2 ^ (r * s - d) * 2 ^ d ≤ 2 ^ gamma := by
    calc
      r * 2 ^ (r * s - d) * 2 ^ d = r * 2 ^ (r * s) := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (show d ≤ r * s from hexp)]
      _ ≤ 2 ^ r * 2 ^ (r * s) :=
        Nat.mul_le_mul_right _ (nat_le_two_pow r)
      _ = 2 ^ (r + r * s) := by rw [pow_add]
      _ ≤ 2 ^ gamma := by
        apply pow_le_pow_right₀ (by omega : 1 ≤ (2 : ℕ))
        simpa [Nat.mul_add, Nat.add_comm] using hgamma
  unfold dyadicConditionalScale
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ ((r - 1) * t))]
  exact_mod_cast hnat

@[simp] theorem mem_collidingRight {R : A → B → Prop} [DecidableRel R]
    {B₀ : Finset B} {u : A} {v w : B} :
    w ∈ collidingRight R B₀ u v ↔
      w ∈ B₀ ∧ R u w ∧ ∃ x, x ≠ u ∧ R x v ∧ R x w := by
  simp [collidingRight, and_assoc]

/-- The codegree hypothesis bounds the number of right vertices which share
a second neighbour with a fixed incidence.  The harmless factor `r`, rather
than `r - 1`, is the form used in JS Lemma 4.1. -/
theorem card_collidingRight_le_mul_codegree
    (R : A → B → Prop) [DecidableRel R]
    (B₀ : Finset B) (u : A) (v : B) (r Q : ℕ)
    (hdeg : (bipNeighborsB R v).card = r)
    (hcodeg : ∀ x, x ≠ u → bipCodegree R u x ≤ Q) :
    (collidingRight R B₀ u v).card ≤ r * Q := by
  classical
  let X := (bipNeighborsB R v).erase u
  have hsub : collidingRight R B₀ u v ⊆
      X.biUnion fun x ↦ bipNeighborsA R u ∩ bipNeighborsA R x := by
    intro w hw
    obtain ⟨hwB, huw, x, hxu, hxv, hxw⟩ := mem_collidingRight.mp hw
    rw [Finset.mem_biUnion]
    refine ⟨x, ?_, ?_⟩
    · simp [X, hxu, hxv]
    · simp [huw, hxw]
  calc
    (collidingRight R B₀ u v).card
        ≤ (X.biUnion fun x ↦ bipNeighborsA R u ∩ bipNeighborsA R x).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ x ∈ X, (bipNeighborsA R u ∩ bipNeighborsA R x).card :=
      Finset.card_biUnion_le
    _ = ∑ x ∈ X, bipCodegree R u x := by
      apply Finset.sum_congr rfl
      intro x hx
      unfold bipCodegree
      apply congrArg Finset.card
      ext y
      simp [bipNeighborsA]
    _ ≤ ∑ x ∈ X, Q := by
      apply Finset.sum_le_sum
      intro x hx
      apply hcodeg x
      exact (Finset.mem_erase.mp hx).1
    _ = X.card * Q := by simp
    _ ≤ r * Q := by
      gcongr
      rw [← hdeg]
      exact Finset.card_erase_le

/-- Products of numbers in `[0,1]` are at most one. -/
theorem prod_probability_le_one (p : A → ℝ)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) (s : Finset A) :
    ∏ x ∈ s, p x ≤ 1 := by
  classical
  exact Finset.prod_le_one (fun x _ ↦ (hp x).1) (fun x _ ↦ (hp x).2)

/-- Pure finite-product form of the conditional estimate.

`hsingle` is the estimate for right vertices whose neighbourhood meets
`N(v)` only at `u`.  It is separated out because in the dyadic application
it is the one-line cancellation
`2^alpha(u) * 2^(gamma-alpha(u)-(r-1)t) = 2^(gamma-(r-1)t)`.
The collision term is proved here from pair-codegrees. -/
theorem conditionalDegreeFactor_le_two_mul
    (R : A → B → Prop) [DecidableRel R]
    (p : A → ℝ) (B₀ : Finset B) (u : A) (v : B)
    (r Q : ℕ) (M : ℝ)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (hM : 0 ≤ M)
    (hdeg : (bipNeighborsB R v).card = r)
    (hcodeg : ∀ x, x ≠ u → bipCodegree R u x ≤ Q)
    (hcollision : (r * Q : ℝ) ≤ M)
    (hsingle :
      ∑ w ∈ (B₀.filter (R u)).filter
          (fun w ↦ ¬ ∃ x, x ≠ u ∧ R x v ∧ R x w),
          ∏ x ∈ (bipNeighborsB R w \ bipNeighborsB R v), p x ≤ M) :
    conditionalDegreeFactor R p B₀ u v ≤ 2 * M := by
  classical
  let W := B₀.filter (R u)
  let C : B → Prop := fun w ↦ ∃ x, x ≠ u ∧ R x v ∧ R x w
  have hprod_nonneg : ∀ w,
      0 ≤ ∏ x ∈ (bipNeighborsB R w \ bipNeighborsB R v), p x := by
    intro w
    exact Finset.prod_nonneg fun x hx ↦ (hp x).1
  have hsplit : conditionalDegreeFactor R p B₀ u v =
      (∑ w ∈ W.filter (¬ C ·),
        ∏ x ∈ (bipNeighborsB R w \ bipNeighborsB R v), p x) +
      ∑ w ∈ W.filter C,
        ∏ x ∈ (bipNeighborsB R w \ bipNeighborsB R v), p x := by
    unfold conditionalDegreeFactor
    change (∑ w ∈ W, ∏ x ∈ (bipNeighborsB R w \ bipNeighborsB R v), p x) = _
    rw [← Finset.sum_filter_add_sum_filter_not W C]
    ac_rfl
  rw [hsplit]
  have hsingle' :
      ∑ w ∈ W.filter (¬ C ·),
          ∏ x ∈ (bipNeighborsB R w \ bipNeighborsB R v), p x ≤ M := by
    simpa [W, C] using hsingle
  have hcoll_card : (W.filter C).card ≤ r * Q := by
    simpa [W, C, collidingRight] using
      card_collidingRight_le_mul_codegree R B₀ u v r Q hdeg hcodeg
  have hcoll :
      ∑ w ∈ W.filter C,
          ∏ x ∈ (bipNeighborsB R w \ bipNeighborsB R v), p x ≤ M := by
    calc
      (∑ w ∈ W.filter C,
          ∏ x ∈ (bipNeighborsB R w \ bipNeighborsB R v), p x)
          ≤ ∑ _w ∈ W.filter C, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro w hw
            exact prod_probability_le_one p hp _
      _ = ((W.filter C).card : ℝ) := by simp
      _ ≤ (r * Q : ℝ) := by exact_mod_cast hcoll_card
      _ ≤ M := hcollision
  linarith

/-- Unnormalised form: multiplying by the probability `q(v)` gives the
weighted product bound which is used before conditional Markov. -/
theorem survival_mul_conditionalDegreeFactor_le
    (R : A → B → Prop) [DecidableRel R]
    (p : A → ℝ) (B₀ : Finset B) (u : A) (v : B)
    (M : ℝ)
    (hq : 0 ≤ rightSurvivalProbability R p v)
    (hcond : conditionalDegreeFactor R p B₀ u v ≤ 2 * M) :
    rightSurvivalProbability R p v * conditionalDegreeFactor R p B₀ u v ≤
      rightSurvivalProbability R p v * (2 * M) := by
  exact mul_le_mul_of_nonneg_left hcond hq

/-- **JS Lemma 4.1, conditional product estimate.**

The hypotheses are the exact dyadic data used in the paper.  In particular,
the natural exponent in the codegree bound is protected by `hexp`, so no
subtraction is silently truncated.  The first conclusion is the conditional
expectation factor.  The second is its unnormalised version, whose left side
is

`E[1_{N(v) ⊆ S} * deg_{B'}(u)]`.

Since `2 * dyadicConditionalScale gamma r t` is
`2^(gamma-(r-1)t+1)` in integer-exponent notation, this is precisely the
bound displayed in JS Lemma 4.1. -/
theorem js_conditional_product_bound
    (R : A → B → Prop) [DecidableRel R]
    (B₀ : Finset B) (alpha : A → ℕ) (r s t gamma : ℕ)
    (u : A) (v : B)
    (hvB : v ∈ B₀) (huv : R u v)
    (halpha_upper : ∀ x, alpha x ≤ t)
    (halpha_lower : ∀ x, s + 1 ≤ alpha x)
    (hdegreeA : ∀ x, bipDegreeA R x ≤ 2 ^ alpha x)
    (hdegreeB : ∀ w ∈ B₀, bipDegreeB R w = r)
    (hbeta : ∀ w ∈ B₀, ∑ x ∈ bipNeighborsB R w, alpha x = gamma)
    (hexp : (r - 1) * t ≤ r * s)
    (hcodeg : ∀ x, x ≠ u →
      bipCodegree R u x ≤ 2 ^ (r * s - (r - 1) * t)) :
    conditionalDegreeFactor R (dyadicProbability alpha t) B₀ u v ≤
        2 * dyadicConditionalScale gamma r t ∧
      rightSurvivalProbability R (dyadicProbability alpha t) v *
          conditionalDegreeFactor R (dyadicProbability alpha t) B₀ u v ≤
        rightSurvivalProbability R (dyadicProbability alpha t) v *
          (2 * dyadicConditionalScale gamma r t) := by
  classical
  let p := dyadicProbability alpha t
  let M := dyadicConditionalScale gamma r t
  let Q := 2 ^ (r * s - (r - 1) * t)
  have hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1 := by
    intro x
    exact dyadicProbability_mem_unitInterval alpha t halpha_upper x
  have hdeg_v : (bipNeighborsB R v).card = r := by
    simpa [bipDegreeB] using hdegreeB v hvB
  have hr : 1 ≤ r := by
    have hu_mem : u ∈ bipNeighborsB R v := by simp [huv]
    rw [← hdeg_v]
    exact Finset.one_le_card.mpr ⟨u, hu_mem⟩
  have hgamma : r * (s + 1) ≤ gamma := by
    calc
      r * (s + 1) = ∑ x ∈ bipNeighborsB R v, (s + 1) := by simp [hdeg_v]
      _ ≤ ∑ x ∈ bipNeighborsB R v, alpha x := by
        exact Finset.sum_le_sum fun x hx ↦ halpha_lower x
      _ = gamma := hbeta v hvB
  have hcollision : ((r * Q : ℕ) : ℝ) ≤ M := by
    simpa [Q, M] using dyadic_codegree_term_le r s t gamma hexp hgamma
  have hsingle :
      ∑ w ∈ (B₀.filter (R u)).filter
          (fun w ↦ ¬ ∃ x, x ≠ u ∧ R x v ∧ R x w),
          ∏ x ∈ (bipNeighborsB R w \ bipNeighborsB R v), p x ≤ M := by
    let W := (B₀.filter (R u)).filter
      (fun w ↦ ¬ ∃ x, x ≠ u ∧ R x v ∧ R x w)
    let q₀ := (2 : ℝ) ^ gamma / (2 : ℝ) ^ (t * r)
    have hterm : ∀ w ∈ W,
        ∏ x ∈ (bipNeighborsB R w \ bipNeighborsB R v), p x = q₀ / p u := by
      intro w hw
      have hw' := hw
      simp only [W, Finset.mem_filter] at hw'
      obtain ⟨⟨hwB₀, huw⟩, hno⟩ := hw'
      have hinter : bipNeighborsB R w ∩ bipNeighborsB R v = {u} := by
        ext x
        constructor
        · intro hx
          have hxmem := Finset.mem_inter.mp hx
          have hxw : R x w := by simpa using hxmem.1
          have hxv : R x v := by simpa using hxmem.2
          by_cases hxu : x = u
          · simpa [hxu]
          · exact False.elim (hno ⟨x, hxu, hxv, hxw⟩)
        · intro hx
          have hxu : x = u := by simpa using hx
          subst x
          simp [huw, huv]
      have hdecomp :
          (bipNeighborsB R w \ bipNeighborsB R v) ∪ {u} = bipNeighborsB R w := by
        rw [← hinter]
        exact Finset.sdiff_union_inter _ _
      have hdisj : Disjoint (bipNeighborsB R w \ bipNeighborsB R v) {u} := by
        simp [huv]
      have hprod_decomp :
          (∏ x ∈ (bipNeighborsB R w \ bipNeighborsB R v), p x) * p u =
            ∏ x ∈ bipNeighborsB R w, p x := by
        calc
          (∏ x ∈ (bipNeighborsB R w \ bipNeighborsB R v), p x) * p u =
              (∏ x ∈ (bipNeighborsB R w \ bipNeighborsB R v), p x) *
                ∏ x ∈ ({u} : Finset A), p x := by simp
          _ = ∏ x ∈ ((bipNeighborsB R w \ bipNeighborsB R v) ∪ {u}), p x :=
            (Finset.prod_union hdisj).symm
          _ = ∏ x ∈ bipNeighborsB R w, p x := by rw [hdecomp]
      have hprod_total : ∏ x ∈ bipNeighborsB R w, p x = q₀ := by
        simp only [p, q₀]
        rw [prod_dyadicProbability, hbeta w hwB₀]
        simp only [bipDegreeB] at hdegreeB
        rw [hdegreeB w hwB₀]
      apply (eq_div_iff (show p u ≠ 0 by
        simp [p, dyadicProbability])).2
      exact hprod_decomp.trans hprod_total
    have hcard : W.card ≤ 2 ^ alpha u := by
      calc
        W.card ≤ (bipNeighborsA R u).card := by
          apply Finset.card_le_card
          intro w hw
          have hw' := hw
          simp only [W, Finset.mem_filter] at hw'
          exact mem_bipNeighborsA.mpr hw'.1.2
        _ = bipDegreeA R u := rfl
        _ ≤ 2 ^ alpha u := hdegreeA u
    change (∑ w ∈ W,
      ∏ x ∈ (bipNeighborsB R w \ bipNeighborsB R v), p x) ≤ M
    calc
      (∑ w ∈ W,
          ∏ x ∈ (bipNeighborsB R w \ bipNeighborsB R v), p x) =
          (W.card : ℝ) * (q₀ / p u) := by
        calc
          (∑ w ∈ W,
              ∏ x ∈ (bipNeighborsB R w \ bipNeighborsB R v), p x) =
              ∑ w ∈ W, q₀ / p u := by
                apply Finset.sum_congr rfl
                intro w hw
                rw [hterm w hw]
          _ = (W.card : ℝ) * (q₀ / p u) := by simp
      _ ≤ ((2 ^ alpha u : ℕ) : ℝ) * (q₀ / p u) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast hcard
        · dsimp [q₀, p, dyadicProbability]
          positivity
      _ = M := by
        simp only [q₀, p, M, Nat.cast_pow, Nat.cast_ofNat]
        exact dyadic_cancellation (alpha u) gamma r t hr
  have hcond : conditionalDegreeFactor R p B₀ u v ≤ 2 * M :=
    conditionalDegreeFactor_le_two_mul R p B₀ u v r Q M hp
      (by dsimp [M, dyadicConditionalScale]; positivity) hdeg_v hcodeg
      (by simpa [Nat.cast_mul] using hcollision) hsingle
  constructor
  · simpa [p, M] using hcond
  · have hq : 0 ≤ rightSurvivalProbability R p v := by
      unfold rightSurvivalProbability
      exact Finset.prod_nonneg fun x hx ↦ (hp x).1
    simpa [p, M] using
      survival_mul_conditionalDegreeFactor_le R p B₀ u v M hq hcond

end ConditionalProduct

end Erdos182
