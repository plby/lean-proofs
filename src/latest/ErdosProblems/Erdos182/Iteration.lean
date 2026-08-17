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
import ErdosProblems.Erdos182.KeyRestrictionCore
import ErdosProblems.Erdos182.KeyRestrictionActive
import ErdosProblems.Erdos182.Roof
import ErdosProblems.Erdos182.AlmostRegularExtraction

/-!
# The integer iteration in Janzer--Sudakov

This file isolates the well-founded and rounding part of Lemmas 4.2, 5.1,
and 5.2 of Janzer--Sudakov.  The graph-theoretic one-step restriction lemma
is deliberately represented by a predicate `P` and a step hypothesis.  This
has two advantages in the formal proof: subgraph containment can be built
into `P`, and the termination argument is entirely independent of the
representation chosen for bipartite graphs.

All levels here are natural numbers.  The linear expression
`2 r s - (2 r - 1) t` is evaluated in `ℤ`, so no truncated subtraction is
silently introduced at the most important arithmetic invariant.
-/

namespace Erdos182

/-- The two dyadic exponents attached to a half-regular bipartite graph.
The intended hypotheses are `2^s |A| ≤ e(G)` and `Δ_A(G) ≤ 2^t`. -/
structure DyadicState where
  s : ℕ
  t : ℕ
  deriving DecidableEq

namespace DyadicState

/-- The (natural-number) gap between maximum-degree and density exponents. -/
def gap (x : DyadicState) : ℕ := x.t - x.s

/-- The codegree exponent preserved by JS Lemma 4.2.

Written in terms of the gap this is `t - 2 r (t-s)`.  The expanded form is
the one appearing in the paper. -/
def invariant (r : ℕ) (x : DyadicState) : ℤ :=
  (2 * r * x.s : ℕ) - (2 * r - 1) * x.t

@[simp] theorem gap_mk (s t : ℕ) : gap ⟨s, t⟩ = t - s := rfl

@[simp] theorem invariant_mk (r s t : ℕ) :
    invariant r ⟨s, t⟩ =
      (2 * r * s : ℕ) - (2 * r - 1) * t := rfl

/-- Rewriting the invariant in terms of the gap.  This is the identity used
in both JS Lemmas 4.2 and 5.1. -/
theorem invariant_eq_t_sub_twice_mul_gap (r : ℕ) (x : DyadicState)
    (_hr : 1 ≤ r) (hst : x.s ≤ x.t) :
    invariant r x = (x.t : ℤ) - 2 * (r : ℤ) * (gap x : ℤ) := by
  simp only [invariant, gap]
  rw [Nat.cast_sub hst]
  push_cast
  ring

/-- Equivalent form with `s` as its leading term. -/
theorem invariant_eq_s_sub_pred_twice_mul_gap (r : ℕ) (x : DyadicState)
    (hr : 1 ≤ r) (hst : x.s ≤ x.t) :
    invariant r x =
      (x.s : ℤ) - (2 * (r : ℤ) - 1) * (gap x : ℤ) := by
  rw [invariant_eq_t_sub_twice_mul_gap r x hr hst]
  simp only [gap]
  rw [Nat.cast_sub hst]
  ring

/-- A nonnegative gap makes the invariant no larger than the density level. -/
theorem invariant_le_s (r : ℕ) (x : DyadicState) (hst : x.s ≤ x.t)
    (hr : 1 ≤ r) : invariant r x ≤ (x.s : ℤ) := by
  rw [invariant_eq_s_sub_pred_twice_mul_gap r x hr hst]
  have hcoeff : 0 ≤ 2 * (r : ℤ) - 1 := by omega
  have hgap : 0 ≤ (x.gap : ℤ) := by positivity
  exact sub_le_self _ (mul_nonneg hcoeff hgap)

end DyadicState

/-- Abstract, exact form of the iteration step furnished by JS Lemma 4.1.
Besides strict decrease of the integer gap, it records preservation of the
codegree exponent. -/
def IsDyadicImprovement (r : ℕ) (x y : DyadicState) : Prop :=
  y.gap < x.gap ∧ x.invariant r ≤ y.invariant r

/-- **JS Lemma 4.2, well-founded iteration.**

If every nonterminal witness admits a one-step restriction with smaller gap
and no smaller invariant, repeated restriction reaches gap at most `cutoff`.
The conclusion also remembers the cumulative invariant inequality.  Taking
`cutoff = 5 * Nat.clog 2 r` is the floor/ceiling-safe version used by the
graph-theoretic application. -/
theorem js_lemma_4_2_iteration
    (r cutoff : ℕ) (P : DyadicState → Prop) (x : DyadicState)
    (hx : P x)
    (step : ∀ y, P y → cutoff < y.gap →
      ∃ z, P z ∧ IsDyadicImprovement r y z) :
    ∃ y, P y ∧ y.gap ≤ cutoff ∧ x.invariant r ≤ y.invariant r := by
  induction hgap : x.gap using Nat.strong_induction_on generalizing x with
  | h n ih =>
      by_cases hterminal : x.gap ≤ cutoff
      · exact ⟨x, hx, hterminal, le_rfl⟩
      · have hnonterminal : cutoff < x.gap := Nat.lt_of_not_ge hterminal
        obtain ⟨z, hzP, hzxgap, hxzinv⟩ := step x hx hnonterminal
        obtain ⟨y, hyP, hygap, hzyinv⟩ :=
          ih z.gap (by simpa [hgap] using hzxgap) z hzP rfl
        exact ⟨y, hyP, hygap, hxzinv.trans hzyinv⟩

/-- A version of the iteration theorem which exposes the two component
conditions rather than the bundled improvement predicate. -/
theorem js_lemma_4_2_iteration'
    (r cutoff : ℕ) (P : DyadicState → Prop) (x : DyadicState)
    (hx : P x)
    (step : ∀ y, P y → cutoff < y.gap →
      ∃ z, P z ∧ z.gap < y.gap ∧ y.invariant r ≤ z.invariant r) :
    ∃ y, P y ∧ y.gap ≤ cutoff ∧ x.invariant r ≤ y.invariant r := by
  apply js_lemma_4_2_iteration r cutoff P x hx
  intro y hy hgap
  obtain ⟨z, hz, hzgap, hzinv⟩ := step y hy hgap
  exact ⟨z, hz, hzgap, hzinv⟩

/-- The shifted codegree exponent in JS Lemma 5.1 is nonnegative only if the
unshifted invariant is at least `r`.  Stating this over `ℤ` makes the
integrality argument literal. -/
theorem invariant_ge_of_shifted_nonneg {r : ℕ} {x : DyadicState}
    (h : 0 ≤ x.invariant r - (r : ℤ)) : (r : ℤ) ≤ x.invariant r := by
  omega

/-- **The level arithmetic in JS Lemma 5.1.**

The initial codegree condition has exponent `invariant - r`.  Once a
nonempty codegree shows this exponent is nonnegative, Lemma 4.2 preserves an
invariant at least `r`.  Since the invariant of a state with `s ≤ t` is at
most `s`, the terminal density level is at least `r`. -/
theorem js_lemma_5_1_levels {r : ℕ} {x y : DyadicState}
    (hr : 1 ≤ r) (hy : y.s ≤ y.t)
    (hshift : 0 ≤ x.invariant r - (r : ℤ))
    (hmono : x.invariant r ≤ y.invariant r) :
    r ≤ y.s := by
  have hry : (r : ℤ) ≤ y.invariant r :=
    (invariant_ge_of_shifted_nonneg hshift).trans hmono
  have hys : y.invariant r ≤ (y.s : ℤ) :=
    DyadicState.invariant_le_s r y hy hr
  exact_mod_cast hry.trans hys

/-- The exact ceiling used when JS Lemma 5.2 trims the surviving right-side
degrees to `ceil (r / (2(k+1)))`. -/
def jsTrimmedDegree (r k : ℕ) : ℕ := (r + (2 * (k + 1) - 1)) / (2 * (k + 1))

theorem jsTrimmedDegree_eq_ceilDiv (r k : ℕ) :
    jsTrimmedDegree r k = r ⌈/⌉ (2 * (k + 1)) := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  simp only [jsTrimmedDegree]
  congr 1

/-- The trimmed degree really is a ceiling: multiplying it by the denominator
covers the original degree. -/
theorem le_mul_jsTrimmedDegree (r k : ℕ) :
    r ≤ 2 * (k + 1) * jsTrimmedDegree r k := by
  rw [jsTrimmedDegree_eq_ceilDiv]
  exact (ceilDiv_le_iff_le_mul (by omega)).1 le_rfl

/-- Upper half of the ceiling estimate, in a division-free form. -/
theorem mul_jsTrimmedDegree_lt_add (r k : ℕ) :
    2 * (k + 1) * jsTrimmedDegree r k < r + 2 * (k + 1) := by
  simp only [jsTrimmedDegree]
  have h := Nat.div_mul_le_self (r + (2 * (k + 1) - 1)) (2 * (k + 1))
  rw [mul_comm] at h
  omega

/-- A convenient explicit large-`r` condition which absorbs the additive one
in the ceiling.  This is the exact version of `r' ≤ r/k` used in the printed
proof of JS Lemma 5.2. -/
theorem jsTrimmedDegree_le_div {r k : ℕ} (hk : 1 ≤ k)
    (hr : 2 * k ≤ r) : jsTrimmedDegree r k ≤ r / k := by
  apply (Nat.le_div_iff_mul_le (by omega)).2
  have hceil := mul_jsTrimmedDegree_lt_add r k
  have hpos : 0 < jsTrimmedDegree r k := by
    have hcover := le_mul_jsTrimmedDegree r k
    nlinarith
  nlinarith

/-- The algebraic identity at the heart of JS Lemma 5.2.  It is stated over
the integers to avoid truncated subtraction. -/
theorem trimmed_invariant_identity (r' s t : ℕ) (hr' : 1 ≤ r') :
    ((2 * r' * s : ℕ) : ℤ) - (((2 * r' - 1) * t : ℕ) : ℤ) - (r' : ℤ) =
      (t : ℤ) - (r' : ℤ) * (2 * ((t : ℤ) - s) + 1) := by
  rw [Nat.cast_mul ((2 * r' - 1)) t]
  rw [Nat.cast_sub (by omega : 1 ≤ 2 * r')]
  push_cast
  ring

/-- **The exponent estimate in JS Lemma 5.2.**

This is a completely integral replacement for
`t-r'(2t-2s+1) ≥ (1-1/(2k))t`.  The assumptions are precisely the three
rounding inequalities used in the paper: `r' ≤ r/k`,
`2(t-s)+1 ≤ 3(t-s)`, and `6r(t-s) ≤ t`. -/
theorem js_lemma_5_2_exponent {k r r' s t : ℕ}
    (hk : 1 ≤ k) (hr'pos : 1 ≤ r') (hst : s ≤ t)
    (hr' : k * r' ≤ r)
    (hgap : 2 * (t - s) + 1 ≤ 3 * (t - s))
    (hclose : 6 * r * (t - s) ≤ t) :
    (((t - t / (2 * k) : ℕ) : ℤ) ≤
      ((2 * r' * s : ℕ) : ℤ) - (((2 * r' - 1) * t : ℕ) : ℤ) - (r' : ℤ)) := by
  rw [trimmed_invariant_identity r' s t hr'pos]
  have hmul : 2 * k * (r' * (2 * (t - s) + 1)) ≤ t := by
    calc
      2 * k * (r' * (2 * (t - s) + 1))
          = 2 * (k * r') * (2 * (t - s) + 1) := by ring
      _ ≤ 2 * r * (3 * (t - s)) := by gcongr
      _ = 6 * r * (t - s) := by ring
      _ ≤ t := hclose
  have hdiv : r' * (2 * (t - s) + 1) ≤ t / (2 * k) :=
    (Nat.le_div_iff_mul_le (by omega)).2 (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hmul)
  have hdivZ :
      (r' : ℤ) * (2 * (((t - s : ℕ) : ℤ)) + 1) ≤ (t / (2 * k) : ℕ) := by
    exact_mod_cast hdiv
  rw [Nat.cast_sub hst] at hdivZ
  rw [Nat.cast_sub (Nat.div_le_self t (2 * k))]
  push_cast at hdivZ ⊢
  omega

/-- JS Lemma 5.2 with its actual trimmed degree substituted. -/
theorem js_lemma_5_2_trimmed_exponent {k r s t : ℕ}
    (hk : 1 ≤ k) (hr : 2 * k ≤ r) (hst : s < t)
    (hclose : 6 * r * (t - s) ≤ t) :
    (((t - t / (2 * k) : ℕ) : ℤ) ≤
      ((2 * jsTrimmedDegree r k * s : ℕ) : ℤ) -
        (((2 * jsTrimmedDegree r k - 1) * t : ℕ) : ℤ) -
          (jsTrimmedDegree r k : ℤ)) := by
  have hcover := le_mul_jsTrimmedDegree r k
  have hpos : 1 ≤ jsTrimmedDegree r k := by nlinarith
  have hdegree' : jsTrimmedDegree r k * k ≤ r :=
    (Nat.le_div_iff_mul_le (by omega)).1 (jsTrimmedDegree_le_div hk hr)
  have hdegree : k * jsTrimmedDegree r k ≤ r := by
    simpa [mul_comm] using hdegree'
  have hgap : 2 * (t - s) + 1 ≤ 3 * (t - s) := by omega
  exact js_lemma_5_2_exponent hk hpos hst.le hdegree hgap hclose

/-- The final denominator calculation in JS Lemma 5.2.  It transports the
integer average-degree inequality returned for the trimmed degree `r'` back
to the original degree `r`, including monotonicity of the rounded binary
logarithm. -/
theorem js_lemma_5_2_average_transfer {k r v e : ℕ}
    (hk : 1 ≤ k) (hr : 2 * k ≤ r)
    (havg : jsTrimmedDegree r k * v ≤
      160 * Nat.clog 2 (jsTrimmedDegree r k) * e) :
    r * v ≤ 320 * (k + 1) * Nat.clog 2 r * e := by
  let r' := jsTrimmedDegree r k
  have hcover : r ≤ 2 * (k + 1) * r' := le_mul_jsTrimmedDegree r k
  have hr'le : r' ≤ r := by
    calc
      r' ≤ r / k := jsTrimmedDegree_le_div hk hr
      _ ≤ r := Nat.div_le_self _ _
  have hlog : Nat.clog 2 r' ≤ Nat.clog 2 r :=
    Nat.clog_mono_right 2 hr'le
  calc
    r * v ≤ (2 * (k + 1) * r') * v := by gcongr
    _ = 2 * (k + 1) * (r' * v) := by ring
    _ ≤ 2 * (k + 1) * (160 * Nat.clog 2 r' * e) := by gcongr
    _ ≤ 2 * (k + 1) * (160 * Nat.clog 2 r * e) := by gcongr
    _ = 320 * (k + 1) * Nat.clog 2 r * e := by ring

section RestrictionBridge

variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable local instance graphAdjDecidable (G : BipartiteGraph A B) : DecidableRel G.Adj :=
  fun _ _ ↦ Classical.propDecidable _

/-- The relation-level and graph-level left degrees agree literally. -/
@[simp] theorem bipDegreeA_adj (G : BipartiteGraph A B) (a : A) :
    bipDegreeA G.Adj a = G.leftDegree a := by
  classical
  simp only [bipDegreeA, bipNeighborsA, BipartiteGraph.leftDegree,
    BipartiteGraph.rightNeighbors]

/-- The relation-level and graph-level right degrees agree literally. -/
@[simp] theorem bipDegreeB_adj (G : BipartiteGraph A B) (b : B) :
    bipDegreeB G.Adj b = G.rightDegree b := by
  classical
  simp only [bipDegreeB, bipNeighborsB, BipartiteGraph.rightDegree,
    BipartiteGraph.leftNeighbors]

/-- The relation-level incidence count agrees with the graph edge count. -/
@[simp] theorem bipEdgeCount_adj (G : BipartiteGraph A B) :
    bipEdgeCount G.Adj = G.edgeCount := by
  classical
  rw [bipEdgeCount, G.edgeCount_eq_sum_leftDegree]
  simp

/-- Restrict a bipartite relation to two finite vertex sets. -/
def bipartiteRestriction (R : A → B → Prop) (A' : Finset A) (B' : Finset B) :
    BipartiteGraph A B :=
  ⟨fun a b ↦ R a b ∧ a ∈ A' ∧ b ∈ B'⟩

@[simp] theorem bipartiteRestriction_adj (R : A → B → Prop)
    (A' : Finset A) (B' : Finset B) (a : A) (b : B) :
    (bipartiteRestriction R A' B').Adj a b ↔
      R a b ∧ a ∈ A' ∧ b ∈ B' :=
  Iff.rfl

theorem bipartiteRestriction_supportedOn (R : A → B → Prop)
    (A' : Finset A) (B' : Finset B) :
    (bipartiteRestriction R A' B').SupportedOn A' B' := by
  intro a b hab
  exact ⟨hab.2.1, hab.2.2⟩

theorem bipartiteRestriction_leftDegree (R : A → B → Prop) [DecidableRel R]
    (A' : Finset A) (B' : Finset B) (a : A) (ha : a ∈ A') :
    (bipartiteRestriction R A' B').leftDegree a =
      bipRestrictedDegreeA R B' a := by
  classical
  unfold BipartiteGraph.leftDegree BipartiteGraph.rightNeighbors
    bipRestrictedDegreeA
  congr 1
  ext b
  simp [bipartiteRestriction, ha, and_comm]

theorem bipartiteRestriction_leftDegree_of_not_mem
    (R : A → B → Prop) [DecidableRel R]
    (A' : Finset A) (B' : Finset B) (a : A) (ha : a ∉ A') :
    (bipartiteRestriction R A' B').leftDegree a = 0 := by
  classical
  simp [BipartiteGraph.leftDegree, BipartiteGraph.rightNeighbors,
    bipartiteRestriction, ha]

theorem bipartiteRestriction_edgeCount (R : A → B → Prop) [DecidableRel R]
    (A' : Finset A) (B' : Finset B) :
    (bipartiteRestriction R A' B').edgeCount =
      bipRestrictedEdgeCount R A' B' := by
  classical
  rw [BipartiteGraph.edgeCount_eq_sum_leftDegree]
  simp only [bipRestrictedEdgeCount]
  rw [← Finset.sum_subset (Finset.subset_univ A')]
  · apply Finset.sum_congr rfl
    intro a ha
    exact bipartiteRestriction_leftDegree R A' B' a ha
  · intro a _ ha
    exact bipartiteRestriction_leftDegree_of_not_mem R A' B' a ha

/-- If restriction does not remove any neighbor of a displayed right
vertex, its right degree is unchanged. -/
theorem bipartiteRestriction_rightDegree
    (R : A → B → Prop) [DecidableRel R]
    (A' : Finset A) (B' : Finset B)
    (hclosed : ∀ v : ↑B', ∀ u, R u v.1 → u ∈ A')
    (b : B) (hb : b ∈ B') :
    (bipartiteRestriction R A' B').rightDegree b = bipDegreeB R b := by
  classical
  simp only [BipartiteGraph.rightDegree, BipartiteGraph.leftNeighbors,
    bipDegreeB, bipNeighborsB]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (R a b ∧ a ∈ A' ∧ b ∈ B') ↔ R a b
  constructor
  · exact fun h ↦ h.1
  · intro hab
    exact ⟨hab, hclosed ⟨b, hb⟩ a hab, hb⟩

/-- A key restriction is already `(40 x r²,r)`-almost-biregular as soon as
the restriction lemma's density lower bound is at least `r`.  The last
condition is written without division as `10 x r² ≤ Q`. -/
theorem IsKeyRestriction.isAlmostBiregularOn
    (R : A → B → Prop) [DecidableRel R]
    {r x Q : ℕ} {A' : Finset A} {B' : Finset B}
    (h : IsKeyRestriction R r x Q A' B')
    (hr : 0 < r) (hx : 0 < x) (hQD : 10 * x * r ^ 2 ≤ Q)
    (hregular : ∀ b ∈ B', bipDegreeB R b = r) :
    (bipartiteRestriction R A' B').IsAlmostBiregularOn A' B'
      (40 * x * r ^ 2) r := by
  classical
  let D := 10 * x * r
  have hD : 0 < D := by positivity
  have hAcard : 0 < A'.card := Finset.card_pos.mpr h.1
  have hedgeRestricted : 0 < bipRestrictedEdgeCount R A' B' := by
    have hQA : 0 < Q * A'.card := by
      have hDr : D ≤ 10 * x * r ^ 2 := by
        have hrr : r ≤ r * r := by nlinarith
        simpa [D, pow_two, mul_assoc] using
          (Nat.mul_le_mul_left (10 * x) hrr)
      have hQ : 0 < Q := lt_of_lt_of_le hD (hDr.trans hQD)
      positivity
    have hbound := h.2.2.1
    by_contra he
    have hezero : bipRestrictedEdgeCount R A' B' = 0 := Nat.eq_zero_of_not_pos he
    rw [hezero, mul_zero] at hbound
    omega
  have hB' : B'.Nonempty := by
    by_contra hB
    have hBzero : B' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    subst B'
    simp [bipRestrictedEdgeCount] at hedgeRestricted
  refine ⟨bipartiteRestriction_supportedOn R A' B', h.1, hB', ?_, ?_, ?_⟩
  · intro b hb
    rw [bipartiteRestriction_rightDegree R A' B' h.2.1 b hb]
    exact hregular b hb
  · rw [bipartiteRestriction_edgeCount]
    have hmul : D * (r * A'.card) ≤
        D * bipRestrictedEdgeCount R A' B' := by
      calc
        D * (r * A'.card) = (10 * x * r ^ 2) * A'.card := by
          simp [D, pow_two]
          ring
        _ ≤ Q * A'.card := by gcongr
        _ ≤ D * bipRestrictedEdgeCount R A' B' := by
          simpa [D, mul_assoc] using h.2.2.1
    have := Nat.le_of_mul_le_mul_left hmul hD
    simpa [D] using this
  · intro a ha
    rw [bipartiteRestriction_leftDegree R A' B' a ha,
      bipartiteRestriction_edgeCount]
    exact h.2.2.2 a ha

/-- The rounded state produced from a key restriction. -/
def keyRestrictionNextState (r gap e a : ℕ) : DyadicState where
  s := Nat.log 2 (e / a)
  t := Nat.clog 2 (40 * gap * r ^ 2 * (e / a + 1))

/-- The rounded maximum level is at most the rounded density level plus the
binary logarithm of the loss factor and one rounding bit. -/
theorem keyRestrictionNextState_gap_le {r gap e a : ℕ}
    (hr : 0 < r) (hgap : 0 < gap) (hd : 0 < e / a) :
    (keyRestrictionNextState r gap e a).gap ≤
      Nat.clog 2 (40 * gap * r ^ 2) + 1 := by
  let d := e / a
  let C := 40 * gap * r ^ 2
  let s' := Nat.log 2 d
  let t' := Nat.clog 2 (C * (d + 1))
  have hC : 0 < C := by positivity
  have hCle : C ≤ 2 ^ Nat.clog 2 C := Nat.le_pow_clog Nat.one_lt_two C
  have hdle : d + 1 ≤ 2 ^ (s' + 1) := by
    exact Nat.add_one_le_iff.mpr (Nat.lt_pow_succ_log_self Nat.one_lt_two d)
  have hprod : C * (d + 1) ≤ 2 ^ (Nat.clog 2 C + s' + 1) := by
    calc
      C * (d + 1) ≤ 2 ^ Nat.clog 2 C * 2 ^ (s' + 1) := by gcongr
      _ = 2 ^ (Nat.clog 2 C + s' + 1) := by
        rw [← pow_add]
        simp only [add_assoc]
  have ht : t' ≤ Nat.clog 2 C + s' + 1 := by
    exact Nat.clog_le_of_le_pow hprod
  change t' - s' ≤ Nat.clog 2 C + 1
  omega

/-- Taking rounded binary logarithms in the key restriction's density
inequality, with every floor/ceiling bit retained. -/
theorem log_density_lower_of_pow_mul_le {E D e a : ℕ}
    (ha : 0 < a) (hD : 0 < D) (hbound : 2 ^ E * a ≤ D * e) :
    E ≤ Nat.clog 2 D + Nat.log 2 (e / a) := by
  let d := e / a
  let s' := Nat.log 2 d
  let l := Nat.clog 2 D
  have heUpper : e < (d + 1) * a := by
    have hrem := Nat.lt_div_mul_add (a := e) ha
    change e < e / a * a + a at hrem
    simpa [d, add_mul, add_comm] using hrem
  have hstrictMul : 2 ^ E * a < (D * (d + 1)) * a := by
    calc
      2 ^ E * a ≤ D * e := hbound
      _ < D * ((d + 1) * a) := Nat.mul_lt_mul_of_pos_left heUpper hD
      _ = (D * (d + 1)) * a := by ring
  have hstrict : 2 ^ E < D * (d + 1) :=
    Nat.lt_of_mul_lt_mul_right hstrictMul
  have hDle : D ≤ 2 ^ l := Nat.le_pow_clog Nat.one_lt_two D
  have hdle : d + 1 ≤ 2 ^ (s' + 1) :=
    Nat.add_one_le_iff.mpr (Nat.lt_pow_succ_log_self Nat.one_lt_two d)
  have hpow : D * (d + 1) ≤ 2 ^ (l + s' + 1) := by
    calc
      D * (d + 1) ≤ 2 ^ l * 2 ^ (s' + 1) := by gcongr
      _ = 2 ^ (l + s' + 1) := by
        rw [← pow_add]
        simp only [add_assoc]
  have hexp : E < l + s' + 1 :=
    (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp (hstrict.trans_le hpow)
  have hle : E ≤ l + s' := by omega
  simpa [l, s', d] using hle

/-- Exact sufficient arithmetic for one rounded restriction to improve a
dyadic state.  The two displayed numerical assumptions are precisely the
strict-gap and invariant-slack estimates verified for large `r` in JS
Lemma 4.2. -/
theorem keyRestrictionNextState_improves
    {r gap e a E D : ℕ} {x : DyadicState}
    (hr : 1 ≤ r) (hgap : 0 < gap) (ha : 0 < a) (hD : 0 < D)
    (hd : 0 < e / a) (hbound : 2 ^ E * a ≤ D * e)
    (hgapSlack : Nat.clog 2 (40 * gap * r ^ 2) + 1 < x.gap)
    (hinvariantSlack :
      x.invariant r + (Nat.clog 2 D : ℤ) +
          (2 * (r : ℤ) - 1) *
            (Nat.clog 2 (40 * gap * r ^ 2) + 1 : ℕ) ≤ (E : ℤ)) :
    IsDyadicImprovement r x (keyRestrictionNextState r gap e a) := by
  let y := keyRestrictionNextState r gap e a
  let c := Nat.clog 2 (40 * gap * r ^ 2)
  let l := Nat.clog 2 D
  have hygap : y.gap ≤ c + 1 :=
    keyRestrictionNextState_gap_le (r := r) (gap := gap) (e := e) (a := a)
      hr hgap hd
  refine ⟨hygap.trans_lt (by simpa [c] using hgapSlack), ?_⟩
  have hE : E ≤ l + y.s := by
    simpa [l, y, keyRestrictionNextState] using
      (log_density_lower_of_pow_mul_le ha hD hbound)
  have hys_le : y.s ≤ y.t := by
    dsimp [y, keyRestrictionNextState]
    apply (Nat.log_le_clog 2 (e / a)).trans
    apply Nat.clog_mono_right 2
    have hC : 0 < 40 * gap * r ^ 2 := by positivity
    nlinarith
  rw [DyadicState.invariant_eq_s_sub_pred_twice_mul_gap r y hr hys_le]
  have hcoeff : 0 ≤ 2 * (r : ℤ) - 1 := by omega
  have hygapZ : (y.gap : ℤ) ≤ (c + 1 : ℕ) := by exact_mod_cast hygap
  have hEZ : (E : ℤ) ≤ (l : ℤ) + (y.s : ℤ) := by exact_mod_cast hE
  push_cast at hygapZ hEZ
  have hmul := mul_le_mul_of_nonneg_left hygapZ hcoeff
  dsimp [c, l] at hinvariantSlack hmul hEZ
  omega

/-- The concrete graph predicate carried through JS Lemma 4.2.  Maximum
degree is stated directly, while density is cross-multiplied. -/
def IsDyadicallyBiregularOn (G : BipartiteGraph A B)
    (A₀ : Finset A) (B₀ : Finset B) (r : ℕ) (x : DyadicState) : Prop :=
  G.SupportedOn A₀ B₀ ∧ A₀.Nonempty ∧ B₀.Nonempty ∧
    G.IsRightRegularOn B₀ r ∧
    2 ^ x.s * A₀.card ≤ G.edgeCount ∧
    (∀ a ∈ A₀, G.leftDegree a ≤ 2 ^ x.t) ∧ x.s ≤ x.t

/-- The complete graph-valued rounding step following JS Lemma 4.1.  No real
division occurs: `Nat.div` and its remainder inequalities establish the
density and maximum-degree bounds. -/
theorem IsKeyRestriction.toDyadicRestriction
    (R : A → B → Prop) [DecidableRel R]
    {r gap Q : ℕ} {A' : Finset A} {B' : Finset B}
    (h : IsKeyRestriction R r gap Q A' B')
    (hr : 0 < r) (hgap : 0 < gap) (hQD : 10 * gap * r ≤ Q)
    (hregular : ∀ b ∈ B', bipDegreeB R b = r) :
    IsDyadicallyBiregularOn (bipartiteRestriction R A' B') A' B' r
      (keyRestrictionNextState r gap
        (bipRestrictedEdgeCount R A' B') A'.card) := by
  classical
  let e := bipRestrictedEdgeCount R A' B'
  let a := A'.card
  let D := 10 * gap * r
  let C := 40 * gap * r ^ 2
  let d := e / a
  have ha : 0 < a := Finset.card_pos.mpr h.1
  have hD : 0 < D := by positivity
  have hQ : 0 < Q := lt_of_lt_of_le hD hQD
  have he : 0 < e := by
    have hQA : 0 < Q * a := mul_pos hQ ha
    have hbound := h.2.2.1
    change Q * a ≤ D * e at hbound
    by_contra he0
    have hez : e = 0 := Nat.eq_zero_of_not_pos he0
    simp [hez] at hbound
    omega
  have hae : a ≤ e := by
    have hmul : D * a ≤ D * e := by
      calc
        D * a ≤ Q * a := by gcongr
        _ ≤ D * e := by simpa [D, e, a] using h.2.2.1
    exact Nat.le_of_mul_le_mul_left hmul hD
  have hd : 0 < d := Nat.div_pos hae ha
  have hB : B'.Nonempty := by
    by_contra hB0
    have hBempty : B' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB0
    subst B'
    simp [e, bipRestrictedEdgeCount] at he
  refine ⟨bipartiteRestriction_supportedOn R A' B', h.1, hB, ?_, ?_, ?_, ?_⟩
  · intro b hb
    rw [bipartiteRestriction_rightDegree R A' B' h.2.1 b hb]
    exact hregular b hb
  · rw [bipartiteRestriction_edgeCount]
    change 2 ^ Nat.log 2 d * a ≤ e
    calc
      2 ^ Nat.log 2 d * a ≤ d * a := by
        gcongr
        exact Nat.pow_log_le_self 2 hd.ne'
      _ ≤ e := by simpa [d] using Nat.div_mul_le_self e a
  · intro u hu
    rw [bipartiteRestriction_leftDegree R A' B' u hu]
    change bipRestrictedDegreeA R B' u ≤ 2 ^ Nat.clog 2 (C * (d + 1))
    have hC : 0 < C := by positivity
    have heUpper : e < (d + 1) * a := by
      have hrem := Nat.lt_div_mul_add (a := e) ha
      change e < e / a * a + a at hrem
      simpa [d, add_mul, add_comm] using hrem
    have hdegMul : bipRestrictedDegreeA R B' u * a ≤ C * e := by
      simpa [C, e, a] using h.2.2.2 u hu
    have hstrict : bipRestrictedDegreeA R B' u * a < C * (d + 1) * a := by
      calc
        bipRestrictedDegreeA R B' u * a ≤ C * e := hdegMul
        _ < C * ((d + 1) * a) := Nat.mul_lt_mul_of_pos_left heUpper hC
        _ = C * (d + 1) * a := by ring
    have hdeg : bipRestrictedDegreeA R B' u < C * (d + 1) :=
      Nat.lt_of_mul_lt_mul_right hstrict
    exact hdeg.le.trans (Nat.le_pow_clog Nat.one_lt_two _)
  · exact (Nat.log_le_clog 2 d).trans
      (Nat.clog_mono_right 2 (by
        have hC : 0 < C := by positivity
        nlinarith : d ≤ C * (d + 1)))

/-- Active-set form of the graph restriction step.  Unlike the core theorem
on full finite types, this theorem can be applied repeatedly: vertices no
longer belonging to `A₀` or `B₀` are simply inactive, and the returned
graph is an actual subgraph of `G`. -/
theorem exists_dyadicRestriction_active
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B)
    (r : ℕ) (x : DyadicState)
    (hr : 0 < r) (hs : 0 < x.s) (hst : x.s < x.t)
    (hx : IsDyadicallyBiregularOn G A₀ B₀ r x)
    (hcodeg : ∀ u ∈ A₀, ∀ w ∈ A₀, u ≠ w →
      bipCodegree G.Adj u w ≤
        2 ^ (r * x.s - (r - 1) * x.t))
    (hQD : 10 * x.gap * r ≤
      2 ^ (r * x.s - (r - 1) * x.t)) :
    ∃ A' B', A' ⊆ A₀ ∧ B' ⊆ B₀ ∧
      bipartiteRestriction G.Adj A' B' ≤ G ∧
      IsKeyRestriction G.Adj r x.gap
        (2 ^ (r * x.s - (r - 1) * x.t)) A' B' ∧
      IsDyadicallyBiregularOn (bipartiteRestriction G.Adj A' B') A' B' r
        (keyRestrictionNextState r x.gap
          (bipRestrictedEdgeCount G.Adj A' B') A'.card) := by
  classical
  obtain ⟨A', B', hA', hB', hkey⟩ :=
    exists_keyRestriction_active G.Adj A₀ B₀ r x.s x.t hr hs hst
      hx.1 hx.2.1
      (fun b hb ↦ by simpa using hx.2.2.2.1 b hb)
      (fun a ha ↦ by simpa using hx.2.2.2.2.2.1 a ha)
      hcodeg (by simpa using hx.2.2.2.2.1)
  have hsub : bipartiteRestriction G.Adj A' B' ≤ G := by
    intro a b hab
    exact hab.1
  have hregular' : ∀ b ∈ B', bipDegreeB G.Adj b = r := by
    intro b hb
    simpa using hx.2.2.2.1 b (hB' hb)
  refine ⟨A', B', hA', hB', hsub, hkey, ?_⟩
  exact hkey.toDyadicRestriction G.Adj hr
    (by simpa [DyadicState.gap] using Nat.sub_pos_iff_lt.mpr hst)
    (by simpa [DyadicState.gap] using hQD) hregular'

/-- Active-set, graph-valued JS Lemma 4.1 with all floor/ceiling losses
displayed.  This is the literal one-step operation used by JS Lemma 4.2. -/
theorem exists_dyadicImprovement_active
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B)
    (r : ℕ) (x : DyadicState)
    (hr : 1 ≤ r) (hs : 0 < x.s) (hst : x.s < x.t)
    (hx : IsDyadicallyBiregularOn G A₀ B₀ r x)
    (hcodeg : ∀ u ∈ A₀, ∀ w ∈ A₀, u ≠ w →
      bipCodegree G.Adj u w ≤
        2 ^ (r * x.s - (r - 1) * x.t))
    (hQD : 10 * x.gap * r ≤
      2 ^ (r * x.s - (r - 1) * x.t))
    (hgapSlack :
      Nat.clog 2 (40 * x.gap * r ^ 2) + 1 < x.gap)
    (hinvariantSlack :
      x.invariant r + (Nat.clog 2 (10 * x.gap * r) : ℤ) +
          (2 * (r : ℤ) - 1) *
            (Nat.clog 2 (40 * x.gap * r ^ 2) + 1 : ℕ) ≤
        (r * x.s - (r - 1) * x.t : ℕ)) :
    ∃ (K : BipartiteGraph A B) (A' : Finset A) (B' : Finset B)
      (y : DyadicState),
      A' ⊆ A₀ ∧ B' ⊆ B₀ ∧ K ≤ G ∧
      IsDyadicallyBiregularOn K A' B' r y ∧
      IsDyadicImprovement r x y := by
  obtain ⟨A', B', hA', hB', hsub, hkey, hdyadic⟩ :=
    exists_dyadicRestriction_active G A₀ B₀ r x hr hs hst hx hcodeg hQD
  let e := bipRestrictedEdgeCount G.Adj A' B'
  let a := A'.card
  let D := 10 * x.gap * r
  let y := keyRestrictionNextState r x.gap e a
  have ha : 0 < a := Finset.card_pos.mpr hkey.1
  have hgap : 0 < x.gap := by
    simpa [DyadicState.gap] using Nat.sub_pos_iff_lt.mpr hst
  have hD : 0 < D := by positivity
  have hae : a ≤ e := by
    have hmul : D * a ≤ D * e := by
      calc
        D * a ≤ 2 ^ (r * x.s - (r - 1) * x.t) * a := by
          gcongr
        _ ≤ D * e := by
          simpa [D, e, a, DyadicState.gap] using hkey.2.2.1
    exact Nat.le_of_mul_le_mul_left hmul hD
  have hd : 0 < e / a := Nat.div_pos hae ha
  have himprove : IsDyadicImprovement r x y := by
    apply keyRestrictionNextState_improves (x := x) hr hgap ha hD hd
    · simpa [D, e, a, DyadicState.gap] using hkey.2.2.1
    · simpa [D, e, a, y] using hgapSlack
    · simpa [D] using hinvariantSlack
  exact ⟨bipartiteRestriction G.Adj A' B', A', B', y,
    hA', hB', hsub, by simpa [y, e, a] using hdyadic, himprove⟩

/-- The unconditional graph-restriction step obtained by composing JS
Lemma 4.1 with the integer rounding lemma above. -/
theorem exists_dyadicRestriction_core
    (R : A → B → Prop) [DecidableRel R]
    (r s t : ℕ) (hr : 0 < r) (hs : 0 < s) (hst : s < t)
    (hA : Nonempty A)
    (hregular : ∀ v, bipDegreeB R v = r)
    (hmax : ∀ u, bipDegreeA R u ≤ 2 ^ t)
    (hcodeg : ∀ u w, u ≠ w →
      bipCodegree R u w ≤ 2 ^ (r * s - (r - 1) * t))
    (hdensity : 2 ^ s * Fintype.card A ≤ bipEdgeCount R)
    (hQD : 10 * (t - s) * r ≤ 2 ^ (r * s - (r - 1) * t)) :
    ∃ A' B',
      IsKeyRestriction R r (t - s) (2 ^ (r * s - (r - 1) * t)) A' B' ∧
      IsDyadicallyBiregularOn (bipartiteRestriction R A' B') A' B' r
        (keyRestrictionNextState r (t - s)
          (bipRestrictedEdgeCount R A' B') A'.card) := by
  obtain ⟨A', B', hkey⟩ := exists_keyRestriction_core R r s t hr hs hst hA
    hregular hmax hcodeg hdensity
  refine ⟨A', B', hkey, ?_⟩
  exact hkey.toDyadicRestriction R hr (Nat.sub_pos_iff_lt.mpr hst) hQD
    (fun b _ ↦ hregular b)

/-- JS Lemma 4.1 plus the exact two numerical estimates needed by the
well-founded iteration.  This is the concrete one-step input to
`js_lemma_4_2_graph_iteration`. -/
theorem exists_dyadicImprovement_core
    (R : A → B → Prop) [DecidableRel R]
    (r s t : ℕ) (hr : 0 < r) (hs : 0 < s) (hst : s < t)
    (hA : Nonempty A)
    (hregular : ∀ v, bipDegreeB R v = r)
    (hmax : ∀ u, bipDegreeA R u ≤ 2 ^ t)
    (hcodeg : ∀ u w, u ≠ w →
      bipCodegree R u w ≤ 2 ^ (r * s - (r - 1) * t))
    (hdensity : 2 ^ s * Fintype.card A ≤ bipEdgeCount R)
    (hQD : 10 * (t - s) * r ≤ 2 ^ (r * s - (r - 1) * t))
    (hgapSlack :
      Nat.clog 2 (40 * (t - s) * r ^ 2) + 1 < t - s)
    (hinvariantSlack :
      (DyadicState.invariant r ⟨s, t⟩) +
          (Nat.clog 2 (10 * (t - s) * r) : ℤ) +
          (2 * (r : ℤ) - 1) *
            (Nat.clog 2 (40 * (t - s) * r ^ 2) + 1 : ℕ) ≤
        (r * s - (r - 1) * t : ℕ)) :
    ∃ A' B',
      IsKeyRestriction R r (t - s) (2 ^ (r * s - (r - 1) * t)) A' B' ∧
      IsDyadicallyBiregularOn (bipartiteRestriction R A' B') A' B' r
        (keyRestrictionNextState r (t - s)
          (bipRestrictedEdgeCount R A' B') A'.card) ∧
      IsDyadicImprovement r ⟨s, t⟩
        (keyRestrictionNextState r (t - s)
          (bipRestrictedEdgeCount R A' B') A'.card) := by
  obtain ⟨A', B', hkey, hdyadic⟩ :=
    exists_dyadicRestriction_core R r s t hr hs hst hA hregular hmax
      hcodeg hdensity hQD
  refine ⟨A', B', hkey, hdyadic, ?_⟩
  let e := bipRestrictedEdgeCount R A' B'
  let a := A'.card
  let D := 10 * (t - s) * r
  have ha : 0 < a := Finset.card_pos.mpr hkey.1
  have hD : 0 < D := by
    dsimp [D]
    exact mul_pos (mul_pos (by norm_num) (Nat.sub_pos_iff_lt.mpr hst)) hr
  have hae : a ≤ e := by
    have hmul : D * a ≤ D * e := by
      calc
        D * a ≤ 2 ^ (r * s - (r - 1) * t) * a := by gcongr
        _ ≤ D * e := by simpa [D, e, a] using hkey.2.2.1
    exact Nat.le_of_mul_le_mul_left hmul hD
  have hd : 0 < e / a := Nat.div_pos hae ha
  apply keyRestrictionNextState_improves (x := (⟨s, t⟩ : DyadicState))
      hr (Nat.sub_pos_iff_lt.mpr hst) ha hD hd
  · simpa [D, e, a] using hkey.2.2.1
  · simpa using hgapSlack
  · simpa [D] using hinvariantSlack

private theorem self_le_two_pow : ∀ n : ℕ, n ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega

/-- A terminal dyadic witness is an almost-biregular graph.  The invariant
lower bound supplies the otherwise easy-to-miss inequality `r ≤ 2^s`; the
power identity turns the dyadic gap into the almost-biregularity constant. -/
theorem IsDyadicallyBiregularOn.isAlmostBiregularOn
    {G : BipartiteGraph A B} {A₀ : Finset A} {B₀ : Finset B}
    {r : ℕ} {x : DyadicState}
    (h : IsDyadicallyBiregularOn G A₀ B₀ r x)
    (_hr : 1 ≤ r) (hrs : r ≤ x.s) :
    G.IsAlmostBiregularOn A₀ B₀ (2 ^ x.gap) r := by
  have hst : x.s ≤ x.t := h.2.2.2.2.2.2
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, ?_⟩
  · calc
      r * A₀.card ≤ 2 ^ x.s * A₀.card := by
        gcongr
        exact hrs.trans (self_le_two_pow x.s)
      _ ≤ G.edgeCount := h.2.2.2.2.1
  · intro a ha
    have hmax := h.2.2.2.2.2.1 a ha
    calc
      G.leftDegree a * A₀.card ≤ 2 ^ x.t * A₀.card := by gcongr
      _ = 2 ^ x.gap * (2 ^ x.s * A₀.card) := by
        rw [DyadicState.gap, ← mul_assoc, ← pow_add,
          Nat.sub_add_cancel hst]
      _ ≤ 2 ^ x.gap * G.edgeCount := by
        gcongr
        exact h.2.2.2.2.1

/-- Increasing the loss parameter preserves almost-biregularity. -/
theorem BipartiteGraph.IsAlmostBiregularOn.mono_loss
    {G : BipartiteGraph A B} {A₀ : Finset A} {B₀ : Finset B}
    {L L' d : ℕ} (h : G.IsAlmostBiregularOn A₀ B₀ L d)
    (hLL' : L ≤ L') : G.IsAlmostBiregularOn A₀ B₀ L' d := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_⟩
  intro a ha
  exact (h.2.2.2.2.2 a ha).trans (Nat.mul_le_mul_right G.edgeCount hLL')

/-- The numerical and codegree hypotheses needed at every nonterminal state. -/
structure DyadicImprovementBounds
    (G : BipartiteGraph A B) (r cutoff : ℕ) : Prop where
  level_pos : ∀ (H : BipartiteGraph A B) (A₁ : Finset A) (B₁ : Finset B)
      (y : DyadicState), H ≤ G → IsDyadicallyBiregularOn H A₁ B₁ r y →
      cutoff < y.gap → 0 < y.s
  codegree : ∀ (H : BipartiteGraph A B) (A₁ : Finset A) (B₁ : Finset B)
      (y : DyadicState), H ≤ G → IsDyadicallyBiregularOn H A₁ B₁ r y →
      cutoff < y.gap → ∀ u ∈ A₁, ∀ w ∈ A₁, u ≠ w →
        bipCodegree H.Adj u w ≤ 2 ^ (r * y.s - (r - 1) * y.t)
  density : ∀ (H : BipartiteGraph A B) (A₁ : Finset A) (B₁ : Finset B)
      (y : DyadicState), H ≤ G → IsDyadicallyBiregularOn H A₁ B₁ r y →
      cutoff < y.gap →
        10 * y.gap * r ≤ 2 ^ (r * y.s - (r - 1) * y.t)
  gap_slack : ∀ (H : BipartiteGraph A B) (A₁ : Finset A) (B₁ : Finset B)
      (y : DyadicState), H ≤ G → IsDyadicallyBiregularOn H A₁ B₁ r y →
      cutoff < y.gap → Nat.clog 2 (40 * y.gap * r ^ 2) + 1 < y.gap
  invariant_slack : ∀ (H : BipartiteGraph A B) (A₁ : Finset A) (B₁ : Finset B)
      (y : DyadicState), H ≤ G → IsDyadicallyBiregularOn H A₁ B₁ r y →
      cutoff < y.gap →
        y.invariant r + (Nat.clog 2 (10 * y.gap * r) : ℤ) +
            (2 * (r : ℤ) - 1) *
              (Nat.clog 2 (40 * y.gap * r ^ 2) + 1 : ℕ) ≤
          (r * y.s - (r - 1) * y.t : ℕ)

/-- The packaged bounds furnish an actual active graph restriction step. -/
theorem DyadicImprovementBounds.exists_step
    {G : BipartiteGraph A B} {r cutoff : ℕ}
    (hb : DyadicImprovementBounds G r cutoff) (hr : 1 ≤ r)
    (H : BipartiteGraph A B) (A₁ : Finset A) (B₁ : Finset B)
    (y : DyadicState) (hHG : H ≤ G)
    (hy : IsDyadicallyBiregularOn H A₁ B₁ r y)
    (hnonterminal : cutoff < y.gap) :
    ∃ (K : BipartiteGraph A B) (A₂ : Finset A) (B₂ : Finset B)
      (z : DyadicState),
      K ≤ H ∧ IsDyadicallyBiregularOn K A₂ B₂ r z ∧
        IsDyadicImprovement r y z := by
  have hgap : 0 < y.gap := lt_of_le_of_lt (Nat.zero_le cutoff) hnonterminal
  have hst : y.s < y.t := by
    simpa [DyadicState.gap] using (Nat.sub_pos_iff_lt.mp hgap)
  obtain ⟨K, A₂, B₂, z, _hA₂, _hB₂, hKH, hz, himprove⟩ :=
    exists_dyadicImprovement_active H A₁ B₁ r y hr
      (hb.level_pos H A₁ B₁ y hHG hy hnonterminal) hst hy
      (hb.codegree H A₁ B₁ y hHG hy hnonterminal)
      (hb.density H A₁ B₁ y hHG hy hnonterminal)
      (hb.gap_slack H A₁ B₁ y hHG hy hnonterminal)
      (hb.invariant_slack H A₁ B₁ y hHG hy hnonterminal)
  exact ⟨K, A₂, B₂, z, hKH, hz, himprove⟩

/-- Concrete graph-valued JS 4.2 iteration, parameterized only by its
one-step graph restriction.  Containment is composed at every recursive
call, so the terminal graph remains a subgraph of the original graph. -/
theorem js_lemma_4_2_graph_iteration
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B)
    (r cutoff : ℕ) (x : DyadicState)
    (hx : IsDyadicallyBiregularOn G A₀ B₀ r x)
    (step : ∀ (H : BipartiteGraph A B) (A₁ : Finset A) (B₁ : Finset B)
      (y : DyadicState), H ≤ G → IsDyadicallyBiregularOn H A₁ B₁ r y →
      cutoff < y.gap →
      ∃ (K : BipartiteGraph A B) (A₂ : Finset A) (B₂ : Finset B)
        (z : DyadicState),
        K ≤ H ∧ IsDyadicallyBiregularOn K A₂ B₂ r z ∧
          IsDyadicImprovement r y z) :
    ∃ (H : BipartiteGraph A B) (A₁ : Finset A) (B₁ : Finset B)
      (y : DyadicState),
      H ≤ G ∧ IsDyadicallyBiregularOn H A₁ B₁ r y ∧
        y.gap ≤ cutoff ∧ x.invariant r ≤ y.invariant r := by
  let P : DyadicState → Prop := fun y ↦
    ∃ (H : BipartiteGraph A B) (A₁ : Finset A) (B₁ : Finset B),
      H ≤ G ∧ IsDyadicallyBiregularOn H A₁ B₁ r y
  have hxP : P x := ⟨G, A₀, B₀, le_rfl, hx⟩
  have hstep : ∀ y, P y → cutoff < y.gap →
      ∃ z, P z ∧ IsDyadicImprovement r y z := by
    intro y hy hgap
    obtain ⟨H, A₁, B₁, hHG, hyH⟩ := hy
    obtain ⟨K, A₂, B₂, z, hKH, hzK, hyz⟩ :=
      step H A₁ B₁ y hHG hyH hgap
    exact ⟨z, ⟨K, A₂, B₂, hKH.trans hHG, hzK⟩, hyz⟩
  obtain ⟨y, ⟨H, A₁, B₁, hHG, hyH⟩, hygap, hxy⟩ :=
    js_lemma_4_2_iteration r cutoff P x hxP hstep
  exact ⟨H, A₁, B₁, y, hHG, hyH, hygap, hxy⟩

/-- **JS Lemma 4.2, concrete active-graph form.**

The only hypotheses beyond the current dyadic graph are the five explicit
integer/codegree bounds in `DyadicImprovementBounds`.  The existential graph
step is constructed internally by `exists_keyRestriction_active`; it is not
assumed as an oracle. -/
theorem js_lemma_4_2_active
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B)
    (r cutoff : ℕ) (x : DyadicState) (hr : 1 ≤ r)
    (hx : IsDyadicallyBiregularOn G A₀ B₀ r x)
    (hb : DyadicImprovementBounds G r cutoff) :
    ∃ (H : BipartiteGraph A B) (A₁ : Finset A) (B₁ : Finset B)
      (y : DyadicState),
      H ≤ G ∧ IsDyadicallyBiregularOn H A₁ B₁ r y ∧
        y.gap ≤ cutoff ∧ x.invariant r ≤ y.invariant r := by
  exact js_lemma_4_2_graph_iteration G A₀ B₀ r cutoff x hx
    (fun H A₁ B₁ y hHG hy hnonterminal ↦
      hb.exists_step hr H A₁ B₁ y hHG hy hnonterminal)

/-- Concrete JS 5.1 reduction from the graph-valued iteration to the
almost-biregular extraction lemma.  The shifted codegree exponent is used
exactly once, to show that the terminal density level is at least `r`. -/
theorem js_lemma_5_1_to_almostBiregular
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B)
    (r cutoff : ℕ) (x : DyadicState)
    (hr : 1 ≤ r) (hx : IsDyadicallyBiregularOn G A₀ B₀ r x)
    (hshift : 0 ≤ x.invariant r - (r : ℤ))
    (step : ∀ (H : BipartiteGraph A B) (A₁ : Finset A) (B₁ : Finset B)
      (y : DyadicState), H ≤ G → IsDyadicallyBiregularOn H A₁ B₁ r y →
      cutoff < y.gap →
      ∃ (K : BipartiteGraph A B) (A₂ : Finset A) (B₂ : Finset B)
        (z : DyadicState),
        K ≤ H ∧ IsDyadicallyBiregularOn K A₂ B₂ r z ∧
          IsDyadicImprovement r y z) :
    ∃ (H : BipartiteGraph A B) (A₁ : Finset A) (B₁ : Finset B)
      (y : DyadicState),
      H ≤ G ∧ H.IsAlmostBiregularOn A₁ B₁ (2 ^ y.gap) r ∧
        y.gap ≤ cutoff ∧ r ≤ y.s := by
  obtain ⟨H, A₁, B₁, y, hHG, hyH, hygap, hxy⟩ :=
    js_lemma_4_2_graph_iteration G A₀ B₀ r cutoff x hx step
  have hrs : r ≤ y.s := js_lemma_5_1_levels hr
    hyH.2.2.2.2.2.2 hshift hxy
  exact ⟨H, A₁, B₁, y, hHG,
    hyH.isAlmostBiregularOn hr hrs, hygap, hrs⟩

/-- **JS Lemma 5.1, concrete active-graph form.**

At the terminal state the preserved shifted invariant forces density level
at least `r`; consequently the dyadic graph is
`(2^gap,r)`-almost-biregular.  In particular a cutoff of
`Nat.clog 2 64` gives the constant required by the standard 64-almost-
regular extraction. -/
theorem js_lemma_5_1_active
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B)
    (r cutoff : ℕ) (x : DyadicState) (hr : 1 ≤ r)
    (hx : IsDyadicallyBiregularOn G A₀ B₀ r x)
    (hshift : 0 ≤ x.invariant r - (r : ℤ))
    (hb : DyadicImprovementBounds G r cutoff) :
    ∃ (H : BipartiteGraph A B) (A₁ : Finset A) (B₁ : Finset B)
      (y : DyadicState),
      H ≤ G ∧ H.IsAlmostBiregularOn A₁ B₁ (2 ^ y.gap) r ∧
        y.gap ≤ cutoff ∧ r ≤ y.s := by
  exact js_lemma_5_1_to_almostBiregular G A₀ B₀ r cutoff x hr hx hshift
    (fun H A₁ B₁ y hHG hy hnonterminal ↦
      hb.exists_step hr H A₁ B₁ y hHG hy hnonterminal)

/-- **JS Lemma 5.1, final 64-almost-regular form.**

The maximum in the logarithm allows the terminal loss parameter to be
enlarged to at least the right degree, exactly matching the hypotheses of
JS Lemma 3.5.  The last premise is the explicit integer estimate that turns
its `32 (log₂ L + 1)` loss into `160 clog₂ r`. -/
theorem js_lemma_5_1_active_almostRegular
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B)
    (r cutoff : ℕ) (x : DyadicState) (hr : 2 ≤ r)
    (hx : IsDyadicallyBiregularOn G A₀ B₀ r x)
    (hshift : 0 ≤ x.invariant r - (r : ℤ))
    (hb : DyadicImprovementBounds G r cutoff)
    (hlog : ∀ y : DyadicState, y.gap ≤ cutoff →
      Nat.log2 (max (2 ^ y.gap) r) + 1 ≤ 5 * Nat.clog 2 r) :
    ∃ H : BipartiteGraph A B, H ≤ G ∧ H.IsAlmostRegular 64 ∧
      r * H.supportCard ≤ 160 * Nat.clog 2 r * H.edgeCount := by
  classical
  obtain ⟨F, A₁, B₁, y, hFG, hF, hygap, _hrs⟩ :=
    js_lemma_5_1_active G A₀ B₀ r cutoff x (by omega) hx hshift hb
  let L := max (2 ^ y.gap) r
  have hFL : F.IsAlmostBiregularOn A₁ B₁ L r :=
    hF.mono_loss (le_max_left _ _)
  obtain ⟨H, hHF, hHalmost, hHavg⟩ :=
    BipartiteGraph.exists_almostRegular_subgraph hFL hr (le_max_right _ _)
  refine ⟨H, hHF.trans hFG, hHalmost, ?_⟩
  calc
    r * H.supportCard ≤
        32 * (Nat.log2 L + 1) * H.edgeCount := hHavg
    _ ≤ 32 * (5 * Nat.clog 2 r) * H.edgeCount := by
      gcongr
      exact hlog y hygap
    _ = 160 * Nat.clog 2 r * H.edgeCount := by ring

/-- **JS Lemma 5.2, final graph-valued form.**

The input graph is the cleaned graph after right degrees have been trimmed
to `ceil (r/(2(k+1)))`.  The integral exponent lemma supplies the shifted
invariant required by JS Lemma 5.1; its output is then transported back to
the original degree `r`, retaining every ceiling and logarithm. -/
theorem js_lemma_5_2_active_almostRegular
    (G : BipartiteGraph A B) (A₀ : Finset A) (B₀ : Finset B)
    (k r cutoff : ℕ) (x : DyadicState)
    (hk : 1 ≤ k) (hrLarge : 4 * (k + 1) ≤ r)
    (hst : x.s < x.t) (hclose : 6 * r * x.gap ≤ x.t)
    (hx : IsDyadicallyBiregularOn G A₀ B₀ (jsTrimmedDegree r k) x)
    (hb : DyadicImprovementBounds G (jsTrimmedDegree r k) cutoff)
    (hlog : ∀ y : DyadicState, y.gap ≤ cutoff →
      Nat.log2 (max (2 ^ y.gap) (jsTrimmedDegree r k)) + 1 ≤
        5 * Nat.clog 2 (jsTrimmedDegree r k)) :
    ∃ H : BipartiteGraph A B, H ≤ G ∧ H.IsAlmostRegular 64 ∧
      r * H.supportCard ≤
        320 * (k + 1) * Nat.clog 2 r * H.edgeCount := by
  classical
  have hr : 2 * k ≤ r := by omega
  let r' := jsTrimmedDegree r k
  have hcover : r ≤ 2 * (k + 1) * r' := by
    simpa [r'] using le_mul_jsTrimmedDegree r k
  have hr' : 2 ≤ r' := by
    have hmul : 2 * (k + 1) * 2 ≤ 2 * (k + 1) * r' := by
      calc
        2 * (k + 1) * 2 = 4 * (k + 1) := by ring
        _ ≤ r := hrLarge
        _ ≤ 2 * (k + 1) * r' := hcover
    exact Nat.le_of_mul_le_mul_left hmul (by positivity)
  have hshiftBound :
      (((x.t - x.t / (2 * k) : ℕ) : ℤ) ≤ x.invariant r' - (r' : ℤ)) := by
    rw [DyadicState.invariant]
    have hexp := js_lemma_5_2_trimmed_exponent (s := x.s) (t := x.t) hk hr hst
      (by simpa [DyadicState.gap] using hclose)
    dsimp [r'] at hexp ⊢
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * jsTrimmedDegree r k),
      Nat.cast_mul 2 (jsTrimmedDegree r k)] at hexp
    norm_num only [Nat.cast_ofNat, Nat.cast_one] at hexp
    exact hexp
  have hshift : 0 ≤ x.invariant r' - (r' : ℤ) :=
    (Int.ofNat_zero_le _).trans hshiftBound
  obtain ⟨H, hHG, hHalmost, hHavg⟩ :=
    js_lemma_5_1_active_almostRegular G A₀ B₀ r' cutoff x hr' hx hshift hb
      (by simpa [r'] using hlog)
  refine ⟨H, hHG, hHalmost, ?_⟩
  exact js_lemma_5_2_average_transfer hk hr (by simpa [r'] using hHavg)

end RestrictionBridge

end Erdos182
