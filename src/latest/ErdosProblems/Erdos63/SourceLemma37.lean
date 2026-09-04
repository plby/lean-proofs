/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos63.RadiusOneBootstrap
import ErdosProblems.Erdos63.SourceLemma35Numerics

/-!
# The source small/large split in Liu--Montgomery Lemma 3.7

This file specializes the finite, size-correlated Lemma 3.7 interface to the
two samples actually used in the proof of Lemma 3.5 of arXiv:2010.15802:

* a large slow ball is sampled `D ^ 2` times, giving a union of size at most
  `D ^ 3`;
* slow balls of a common small size `r` are sampled `r ^ 2` times, giving a
  union of size exactly `r ^ 3`.

The small/large threshold is the natural-logarithm version of
`(log N)^(1/10)`, and the lower end of the small range is the radius-one
bootstrap scale `max 1 (d / 1024)`.  In particular, this interface does not
use a sample multiplicity of order `d / r`.
-/

open Finset Set SimpleGraph
open scoped BigOperators SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {V : Type u}

/-! ## The literal source samples -/

/-- The retained radius-one scale.  The maximum keeps the finite statement
meaningful for small numerical inputs; applications have large `d`. -/
def lm37SourceMinSize (d : ℕ) : ℕ :=
  SourceLemma35Numerics.minFailedSize d

/-- The source `(log N)^(1/10)` cutoff.  This is definitionally tied to the
arithmetic package used for the Lemma 3.5 pigeonhole estimates. -/
noncomputable def lm37SourceCutoff (N : ℕ) : ℕ :=
  SourceLemma35Numerics.cutoff N

/-- The large-regime sample in Lemma 3.5 consists of `D²` sets. -/
def lm37SourceLargeSample (D : ℕ) : ℕ := D ^ 2

/-- The small-regime sample at common size `r` consists of `r²` sets. -/
def lm37SourceSmallSample (r : ℕ) : ℕ :=
  SourceLemma35Numerics.qSmall r

theorem lm37SourceMinSize_pos (d : ℕ) : 0 < lm37SourceMinSize d := by
  simp [lm37SourceMinSize, SourceLemma35Numerics.minFailedSize]

@[simp] theorem lm37SourceSmallSample_union_size (r : ℕ) :
    lm37SourceSmallSample r * r = r ^ 3 := by
  simp [lm37SourceSmallSample, SourceLemma35Numerics.qSmall, pow_succ]

@[simp] theorem lm37SourceLargeSample_union_bound (D : ℕ) :
    lm37SourceLargeSample D * D = D ^ 3 := by
  simp [lm37SourceLargeSample, pow_succ]

/-! ## A graph-free source package -/

/-- The numerical data for the literal Lemma 3.5 split inside Lemma 3.7.

The functions describe the first-slow comparison curve and its available
neighborhood budgets.  All remaining fields are finite natural- or
real-number inequalities.  The sample sizes, lower scale, cutoff, and
blocked-neighborhood profile are fixed by this structure rather than left as
caller-selectable functions. -/
structure LM37SourceBounds
    (N d Ucap Icard contact radius M degreeIntoU D T : ℕ) where
  growth : ℕ → ℕ
  neighborBudget : ℕ → ℕ
  largeBudget : ℕ → ℕ
  stepLoss : ℕ → ℕ
  cutoff_pos : 0 < lm37SourceCutoff N
  index : T ≤ Icard
  target_le_D : M ≤ D
  target_growth : M ≤ growth radius
  jump : ∀ ell : ℕ, 0 < ell → ell ≤ radius →
    growth ell ≤ growth (ell - 1) + 1 + stepLoss ell
  D_pos : 0 < D
  T_pos : 0 < T
  large_sample : D ^ 3 ≤ (T + 1) / 2
  small_sample :
    ∑ r ∈ Finset.Ico (lm37SourceMinSize d) (lm37SourceCutoff N),
      r * ((((r * degreeIntoU) + 1) *
        (max 1 Ucap) ^ (r * degreeIntoU)) * r ^ 2) ≤ (T + 1) / 2
  large_lower :
    ((1 / 64 : ℝ) * (d : ℝ)) / 2 ≤
      ((D ^ 2 * lm37SourceCutoff N : ℕ) : ℝ)
  large_upper : D ^ 3 ≤ N / 2
  large_rate : ∀ s : ℕ,
    D ^ 2 * lm37SourceCutoff N ≤ s → s ≤ D ^ 3 →
      (((Ucap + largeBudget s : ℕ) : ℝ) <
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ))
  small_lower : ∀ r : ℕ,
    lm37SourceMinSize d ≤ r → r < lm37SourceCutoff N →
      ((1 / 64 : ℝ) * (d : ℝ)) / 2 ≤ ((r ^ 3 : ℕ) : ℝ)
  small_upper : ∀ r : ℕ,
    lm37SourceMinSize d ≤ r → r < lm37SourceCutoff N →
      r ^ 3 ≤ N / 2
  small_rate : ∀ r : ℕ,
    lm37SourceMinSize d ≤ r → r < lm37SourceCutoff N →
      ((((r * degreeIntoU + r ^ 2 * neighborBudget r : ℕ) : ℝ)) <
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) (r ^ 3) *
          ((r ^ 3 : ℕ) : ℝ))

/-- Forget the literal sample notation and obtain the general correlated
Lemma 3.7 scale. -/
noncomputable def LM37SourceBounds.toCorrelatedScale
    {N d Ucap Icard contact radius M degreeIntoU D T : ℕ}
    (b : LM37SourceBounds N d Ucap Icard contact radius M degreeIntoU D T) :
    LM37CorrelatedScale N Ucap Icard contact radius M degreeIntoU
      (1 / 1024) ((1 / 64) * (d : ℝ)) where
  growth := b.growth
  minSize := lm37SourceMinSize d
  cutoff := lm37SourceCutoff N
  D := D
  T := T
  qLarge := D ^ 2
  qSmall := lm37SourceSmallSample
  neighborBudget := b.neighborBudget
  blockedBudget := fun r ↦ r * degreeIntoU
  largeBudget := b.largeBudget
  stepLoss := b.stepLoss
  index := b.index
  target_le_D := b.target_le_D
  target_growth := b.target_growth
  jump := b.jump
  blocked_profile := by
    intro s _ _
    exact le_rfl
  minSize_pos := lm37SourceMinSize_pos d
  cutoff_pos := b.cutoff_pos
  D_pos := b.D_pos
  T_pos := b.T_pos
  qSmall_pos := by
    intro r hr _
    exact pow_pos (lm37SourceMinSize_pos d |>.trans_le hr) 2
  large_sample := by
    simpa [pow_succ] using b.large_sample
  small_sample := by
    simpa [lm37SourceSmallSample, SourceLemma35Numerics.qSmall] using b.small_sample
  large_lower := b.large_lower
  large_upper := by
    have hcast : ((D ^ 3 : ℕ) : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by
      exact_mod_cast b.large_upper
    exact hcast.trans (by
      simpa using (Nat.cast_div_le (α := ℝ) (m := N) (n := 2)))
  large_rate := by
    simpa [pow_succ] using b.large_rate
  small_lower := by
    intro r hr hcut
    simpa [lm37SourceSmallSample, SourceLemma35Numerics.qSmall, pow_succ] using
      b.small_lower r hr hcut
  small_upper := by
    intro r hr hcut
    have hcast : ((r ^ 3 : ℕ) : ℝ) ≤ ((N / 2 : ℕ) : ℝ) := by
      exact_mod_cast b.small_upper r hr hcut
    have hdiv : ((N / 2 : ℕ) : ℝ) ≤ (N : ℝ) / 2 := by
      simpa using (Nat.cast_div_le (α := ℝ) (m := N) (n := 2))
    simpa [lm37SourceSmallSample, SourceLemma35Numerics.qSmall, pow_succ] using
      hcast.trans hdiv
  small_rate := by
    intro r hr hcut
    simpa [lm37SourceSmallSample, SourceLemma35Numerics.qSmall, pow_succ] using
      b.small_rate r hr hcut

/-- The source-indexed package used in Claims 4.5, 4.6, and the final
two-ended application.  Both the contradiction threshold and the certified
family size are `floor(N^(1/8))`. -/
abbrev LM37SourceIndexedBounds
    (N d Ucap contact radius M degreeIntoU D : ℕ) :=
  LM37SourceBounds N d Ucap (SourceLemma35Numerics.indexCard N) contact
    radius M degreeIntoU D (SourceLemma35Numerics.indexCard N)

/-- The Claims 4.5/4.6 specialization, whose target is the requested
expansion order `Dtarget`. -/
abbrev LM37SourceReachBounds
    (N d Ucap contact radius Dtarget degreeIntoU maxSlowSize : ℕ) :=
  LM37SourceIndexedBounds N d Ucap contact radius Dtarget degreeIntoU
    maxSlowSize

/-- The final two-ended Lemma 3.7 specialization.  Its target is the larger
`10 * m^2 * Dtarget` set used to connect an adjuster to the remote reservoir,
not the `Dtarget` target used in Claims 4.5 and 4.6. -/
abbrev LM37SourceFinalTwoEndBounds
    (N d Ucap contact radius m Dtarget degreeIntoU maxSlowSize : ℕ) :=
  LM37SourceIndexedBounds N d Ucap contact radius (10 * m ^ 2 * Dtarget)
    degreeIntoU maxSlowSize

/-! ## The source graph theorem -/

/-- Liu--Montgomery Lemma 3.7 with the literal Lemma 3.5 samples.

The radius-one lower bound is an explicit geometric input.  The source C5
condition is accepted directly and converted internally to disjointness of
the candidate-dependent avoiding balls. -/
theorem exists_large_avoiding_ball_of_LM37SourceBounds
    {I : Type*} [Fintype V] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (A B Cset : I → Finset V)
    (d Ucap Icard contact radius M degreeIntoU D T : ℕ)
    (bounds : LM37SourceBounds (Fintype.card V) d Ucap Icard contact
      radius M degreeIntoU D T)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hU : U.card ≤ Ucap) (hI : Icard ≤ Fintype.card I)
    (hstart : ∀ i : I, bounds.growth 0 < (A i).card)
    (hstartOne : ∀ i : I, bounds.growth 1 < (ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) 1).card)
    (hballOneLower : ∀ i : I, lm37SourceMinSize d ≤ (ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) 1).card)
    (hcontact : ∀ i : I,
      HasLimitedContactAfterDeletion G (A i) (U ∪ B i) (Cset i) contact)
    (hfar : ∀ i j : I, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j,
      ∀ p : G.Walk a b,
        p.IsAvoidingPath (U : Set V) ({a, b} : Set V) →
          radius + radius < p.length)
    (hneighborPoint : ∀ (i : I) (ell : ℕ), 0 < ell → ell ≤ radius →
      bounds.growth (ell - 1) < (ballAvoidingFrom G
        ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V))
        (A i) (ell - 1)).card →
      bounds.stepLoss ell + (B i).card + contact * ell ≤
        bounds.neighborBudget (ballAvoidingFrom G
          ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V))
          (A i) (ell - 1)).card)
    (hdegreeU : ∀ i : I, ∀ v ∈ ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) radius,
        (G.neighborFinset v ∩ U).card ≤ degreeIntoU)
    (hlargeBudgetSum : ∀ (J : Finset I) (f : I → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧ f i ≤ D) →
      ∑ i ∈ J, bounds.neighborBudget (f i) ≤
        bounds.largeBudget (∑ i ∈ J, f i)) :
    ∃ i : I, M ≤ (ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V))
      (A i) radius).card := by
  let scale := bounds.toCorrelatedScale
  apply exists_large_avoiding_ball_of_LM37CorrelatedScale
    G (1 / 1024) ((1 / 64) * (d : ℝ)) hexp U A B Cset
      Ucap Icard contact radius M degreeIntoU scale hU hI
  · simpa [scale, LM37SourceBounds.toCorrelatedScale] using hstart
  · simpa [scale, LM37SourceBounds.toCorrelatedScale] using hstartOne
  · simpa [scale, LM37SourceBounds.toCorrelatedScale] using hballOneLower
  · exact hcontact
  · exact pairwiseDisjoint_ballAvoidingFrom_union_three_of_no_short_path
      G U A B Cset radius hfar
  · simpa [scale, LM37SourceBounds.toCorrelatedScale] using hneighborPoint
  · exact hdegreeU
  · simpa [scale, LM37SourceBounds.toCorrelatedScale] using hlargeBudgetSum

/-- A version whose radius-one hypothesis is discharged by the source local
degree count.  Only neighbors of the root in `U` are charged; `B` is charged
by its cardinality and `C` by limited contact. -/
theorem exists_large_avoiding_ball_of_LM37SourceBounds_bootstrap
    {I : Type*} [Fintype V] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (A B Cset : I → Finset V)
    (d Ucap Icard contact radius M degreeIntoU D T barrierCap : ℕ)
    (bounds : LM37SourceBounds (Fintype.card V) d Ucap Icard contact
      radius M degreeIntoU D T)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hU : U.card ≤ Ucap) (hI : Icard ≤ Fintype.card I)
    (hstart : ∀ i : I, bounds.growth 0 < (A i).card)
    (hstartOne : ∀ i : I, bounds.growth 1 < (ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) 1).card)
    (hroot : ∀ i : I, ∃ x ∈ A i, d ≤ G.degree x)
    (hdisjoint : ∀ i : I, Disjoint (A i) (U ∪ B i ∪ Cset i))
    (hBcard : ∀ i : I, (B i).card ≤ barrierCap)
    (hretained : lm37SourceMinSize d ≤
      d - degreeIntoU - barrierCap - contact)
    (hcontact : ∀ i : I,
      HasLimitedContactAfterDeletion G (A i) (U ∪ B i) (Cset i) contact)
    (hfar : ∀ i j : I, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j,
      ∀ p : G.Walk a b,
        p.IsAvoidingPath (U : Set V) ({a, b} : Set V) →
          radius + radius < p.length)
    (hneighborPoint : ∀ (i : I) (ell : ℕ), 0 < ell → ell ≤ radius →
      bounds.growth (ell - 1) < (ballAvoidingFrom G
        ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V))
        (A i) (ell - 1)).card →
      bounds.stepLoss ell + (B i).card + contact * ell ≤
        bounds.neighborBudget (ballAvoidingFrom G
          ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V))
          (A i) (ell - 1)).card)
    (hdegreeU : ∀ i : I, ∀ v ∈ ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) radius,
        (G.neighborFinset v ∩ U).card ≤ degreeIntoU)
    (hlargeBudgetSum : ∀ (J : Finset I) (f : I → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧ f i ≤ D) →
      ∑ i ∈ J, bounds.neighborBudget (f i) ≤
        bounds.largeBudget (∑ i ∈ J, f i)) :
    ∃ i : I, M ≤ (ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V))
      (A i) radius).card := by
  apply exists_large_avoiding_ball_of_LM37SourceBounds
    G U A B Cset d Ucap Icard contact radius M degreeIntoU D T bounds
      hexp hU hI hstart hstartOne
  · intro i
    obtain ⟨x, hx, hxdegree⟩ := hroot i
    have hxball : x ∈ ballAvoidingFrom G
        ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) radius :=
      subset_ballAvoidingFrom G _ (A i) radius hx
    have hbootstrap :=
      degree_sub_degreeInto_sub_card_sub_contact_le_card_ballAvoidingFrom_one
        G U (B i) (Cset i) (A i) x d degreeIntoU barrierCap contact hx
          (hdisjoint i) hxdegree (hdegreeU i x hxball) (hBcard i) (hcontact i)
    exact hretained.trans hbootstrap
  · exact hcontact
  · exact hfar
  · exact hneighborPoint
  · exact hdegreeU
  · exact hlargeBudgetSum

/-! ## Conditional source packages

For targets no larger than the retained radius-one scale, Lemma 3.7 is not
needed: any member of the family already has a sufficiently large radius-one
ball.  Consequently the numerical source package is required only in the
strictly larger-target branch. -/

/-- Conditional form of the source graph theorem.  The numerical package is
consumed only when `lm37SourceMinSize d < M`; otherwise the explicit
radius-one lower bound proves the conclusion directly. -/
theorem exists_large_avoiding_ball_of_conditional_LM37SourceBounds
    {I : Type*} [Fintype V] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (A B Cset : I → Finset V)
    (d Ucap Icard contact radius M degreeIntoU D T : ℕ)
    (bounds : lm37SourceMinSize d < M →
      LM37SourceBounds (Fintype.card V) d Ucap Icard contact
        radius M degreeIntoU D T)
    (hnonempty : Nonempty I)
    (hradiusPos : 0 < radius)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hU : U.card ≤ Ucap) (hI : Icard ≤ Fintype.card I)
    (hstart : ∀ hM : lm37SourceMinSize d < M, ∀ i : I,
      (bounds hM).growth 0 < (A i).card)
    (hstartOne : ∀ hM : lm37SourceMinSize d < M, ∀ i : I,
      (bounds hM).growth 1 < (ballAvoidingFrom G
        ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) 1).card)
    (hballOneLower : ∀ i : I, lm37SourceMinSize d ≤ (ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) 1).card)
    (hcontact : ∀ i : I,
      HasLimitedContactAfterDeletion G (A i) (U ∪ B i) (Cset i) contact)
    (hfar : ∀ i j : I, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j,
      ∀ p : G.Walk a b,
        p.IsAvoidingPath (U : Set V) ({a, b} : Set V) →
          radius + radius < p.length)
    (hneighborPoint : ∀ hM : lm37SourceMinSize d < M,
      ∀ (i : I) (ell : ℕ), 0 < ell → ell ≤ radius →
      (bounds hM).growth (ell - 1) < (ballAvoidingFrom G
        ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V))
        (A i) (ell - 1)).card →
      (bounds hM).stepLoss ell + (B i).card + contact * ell ≤
        (bounds hM).neighborBudget (ballAvoidingFrom G
          ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V))
          (A i) (ell - 1)).card)
    (hdegreeU : ∀ i : I, ∀ v ∈ ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) radius,
        (G.neighborFinset v ∩ U).card ≤ degreeIntoU)
    (hlargeBudgetSum : ∀ hM : lm37SourceMinSize d < M,
      ∀ (J : Finset I) (f : I → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧ f i ≤ D) →
      ∑ i ∈ J, (bounds hM).neighborBudget (f i) ≤
        (bounds hM).largeBudget (∑ i ∈ J, f i)) :
    ∃ i : I, M ≤ (ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V))
      (A i) radius).card := by
  by_cases hM : lm37SourceMinSize d < M
  · exact exists_large_avoiding_ball_of_LM37SourceBounds
      G U A B Cset d Ucap Icard contact radius M degreeIntoU D T
        (bounds hM) hexp hU hI (hstart hM) (hstartOne hM) hballOneLower
        hcontact hfar (hneighborPoint hM) hdegreeU (hlargeBudgetSum hM)
  · let i : I := Classical.choice hnonempty
    exact ⟨i, (Nat.le_of_not_gt hM).trans
      ((hballOneLower i).trans (Finset.card_le_card
        (ballAvoidingFrom_radius_mono G _ _ (by omega : 1 ≤ radius))))⟩

/-- Conditional form with the radius-one lower bound discharged by the
local minimum-degree count. -/
theorem exists_large_avoiding_ball_of_conditional_LM37SourceBounds_bootstrap
    {I : Type*} [Fintype V] [Fintype I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (A B Cset : I → Finset V)
    (d Ucap Icard contact radius M degreeIntoU D T barrierCap : ℕ)
    (bounds : lm37SourceMinSize d < M →
      LM37SourceBounds (Fintype.card V) d Ucap Icard contact
        radius M degreeIntoU D T)
    (hnonempty : Nonempty I)
    (hradiusPos : 0 < radius)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hU : U.card ≤ Ucap) (hI : Icard ≤ Fintype.card I)
    (hstart : ∀ hM : lm37SourceMinSize d < M, ∀ i : I,
      (bounds hM).growth 0 < (A i).card)
    (hstartOne : ∀ hM : lm37SourceMinSize d < M, ∀ i : I,
      (bounds hM).growth 1 < (ballAvoidingFrom G
        ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) 1).card)
    (hroot : ∀ i : I, ∃ x ∈ A i, d ≤ G.degree x)
    (hdisjoint : ∀ i : I, Disjoint (A i) (U ∪ B i ∪ Cset i))
    (hBcard : ∀ i : I, (B i).card ≤ barrierCap)
    (hretained : lm37SourceMinSize d ≤
      d - degreeIntoU - barrierCap - contact)
    (hcontact : ∀ i : I,
      HasLimitedContactAfterDeletion G (A i) (U ∪ B i) (Cset i) contact)
    (hfar : ∀ i j : I, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j,
      ∀ p : G.Walk a b,
        p.IsAvoidingPath (U : Set V) ({a, b} : Set V) →
          radius + radius < p.length)
    (hneighborPoint : ∀ hM : lm37SourceMinSize d < M,
      ∀ (i : I) (ell : ℕ), 0 < ell → ell ≤ radius →
      (bounds hM).growth (ell - 1) < (ballAvoidingFrom G
        ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V))
        (A i) (ell - 1)).card →
      (bounds hM).stepLoss ell + (B i).card + contact * ell ≤
        (bounds hM).neighborBudget (ballAvoidingFrom G
          ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V))
          (A i) (ell - 1)).card)
    (hdegreeU : ∀ i : I, ∀ v ∈ ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) radius,
        (G.neighborFinset v ∩ U).card ≤ degreeIntoU)
    (hlargeBudgetSum : ∀ hM : lm37SourceMinSize d < M,
      ∀ (J : Finset I) (f : I → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧ f i ≤ D) →
      ∑ i ∈ J, (bounds hM).neighborBudget (f i) ≤
        (bounds hM).largeBudget (∑ i ∈ J, f i)) :
    ∃ i : I, M ≤ (ballAvoidingFrom G
      ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V))
      (A i) radius).card := by
  apply exists_large_avoiding_ball_of_conditional_LM37SourceBounds
    G U A B Cset d Ucap Icard contact radius M degreeIntoU D T bounds
      hnonempty hradiusPos hexp hU hI hstart hstartOne
  · intro i
    obtain ⟨x, hx, hxdegree⟩ := hroot i
    have hxball : x ∈ ballAvoidingFrom G
        ((U : Set V) ∪ (B i : Set V) ∪ (Cset i : Set V)) (A i) radius :=
      subset_ballAvoidingFrom G _ (A i) radius hx
    exact hretained.trans
      (degree_sub_degreeInto_sub_card_sub_contact_le_card_ballAvoidingFrom_one
        G U (B i) (Cset i) (A i) x d degreeIntoU barrierCap contact hx
          (hdisjoint i) hxdegree (hdegreeU i x hxball) (hBcard i) (hcontact i))
  · exact hcontact
  · exact hfar
  · exact hneighborPoint
  · exact hdegreeU
  · exact hlargeBudgetSum

/-! ## Candidate-family interfaces -/

namespace SmallSimpleAdjusterCandidate

/-- The source-specialized Lemma 3.7 interface for the oriented candidates
used in Claims 4.5 and 4.6.  The radius-one lower bound is obtained from the
minimum degree of the actual opposite root.  Both the retained lower bound
and the neighbor loss charge `i.radius`, not the ambient `maxRadius`. -/
theorem exists_large_reachingCandidate_ball_of_LM37SourceBounds
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius ballRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (d deletedCap M degreeInto maxSlowSize : ℕ)
    (bounds : LM37SourceReachBounds (Fintype.card V) d deletedCap 2
      ballRadius M degreeInto maxSlowSize)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdeleted : deleted.card ≤ deletedCap)
    (hindex : SourceLemma35Numerics.indexCard (Fintype.card V) ≤
      (reachingEligibleSubfamily S targetSet connectionRadius).card)
    (hradius : ballRadius + ballRadius ≤ separation)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet)
    (hball : ∀ i :
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius =
        ballAvoidingFrom G
          ((deleted : Set V) ∪ (highDegree : Set V) ∪
            (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius)
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (hstart : bounds.growth 0 < minRadius ^ 2)
    (hstartOne : bounds.growth 1 < lm37SourceMinSize d)
    (hretained : ∀ i :
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      lm37SourceMinSize d ≤
        d - degreeInto - (11 * i.1.1.radius + 1) - 2)
    (hneighbor : ∀
      (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (ell s : ℕ), 0 < ell → ell ≤ ballRadius →
      bounds.growth (ell - 1) < s →
      bounds.stepLoss ell + (11 * i.1.1.radius + 1) + 2 * ell ≤
        bounds.neighborBudget s)
    (hlargeBudgetSum : ∀
      (J : Finset
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius} → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlowSize) →
      ∑ i ∈ J, bounds.neighborBudget (f i) ≤
        bounds.largeBudget (∑ i ∈ J, f i)) :
    ∃ i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      M ≤ (ballAvoidingFrom G
        ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius).card := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  let : DecidableRel G.Adj := originalDecAdj
  let I := {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius}
  let Aseed : I → Finset V := fun i ↦ reachingCandidateSeed i
  let Bset : I → Finset V := fun i ↦ reachingCandidateBarrier i
  let Cset : I → Finset V := fun i ↦ reachingCandidatePath i
  let scale := bounds.toCorrelatedScale
  apply exists_large_avoiding_ball_of_LM37CorrelatedScale
    G (1 / 1024) ((1 / 64) * (d : ℝ)) hexp deleted Aseed Bset Cset
      deletedCap (SourceLemma35Numerics.indexCard (Fintype.card V)) 2
      ballRadius M degreeInto scale hdeleted
  · simpa [I] using hindex
  · intro i
    dsimp [Aseed]
    rw [card_reachingCandidateSeed]
    exact hstart.trans_le (Nat.pow_le_pow_left i.1.1.min_le 2)
  · intro i
    exact hstartOne.trans_le ((hretained i).trans
      (reachingCandidate_radiusOne_bootstrap G i
        (hdegree (reachingCandidateConnectionData i).adjusted.rightRoot)
        hprotected))
  · intro i
    exact (hretained i).trans
      (reachingCandidate_radiusOne_bootstrap G i
        (hdegree (reachingCandidateConnectionData i).adjusted.rightRoot)
        hprotected)
  · intro i
    simpa [Aseed, Bset, Cset] using reachingCandidate_limitedContact_barrier i
  · simpa [I, Aseed, Bset, Cset] using
      pairwiseDisjoint_reachingCandidate_actual_barrier_balls
        (G := G) hpair hradius hball
  · intro i ell hell hellRadius hslow
    dsimp [Bset]
    have hbarrier := card_reachingCandidateBarrier_le i
    have hle : bounds.stepLoss ell + (reachingCandidateBarrier i).card +
        2 * ell ≤ bounds.stepLoss ell + (11 * i.1.1.radius + 1) + 2 * ell := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_left hbarrier (bounds.stepLoss ell)) (2 * ell)
    exact hle.trans (hneighbor i ell _ hell hellRadius hslow)
  · intro i v hv
    dsimp [Aseed, Bset, Cset] at hv ⊢
    exact reachingCandidate_degreeInto_deleted_le G i
      (by omega) hprotected (hball i) v hv
  · change ∀
      (J : Finset
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius} → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlowSize) →
      ∑ i ∈ J, bounds.neighborBudget (f i) ≤
        bounds.largeBudget (∑ i ∈ J, f i)
    exact hlargeBudgetSum

/-- Reaching-candidate source theorem with an already established
radius-one lower bound.  This is the common large-target backend for the
seed-or-bootstrap conditional interface. -/
theorem exists_large_reachingCandidate_ball_of_LM37SourceBounds_of_radiusOneLower
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius ballRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (d deletedCap M degreeInto maxSlowSize : ℕ)
    (bounds : LM37SourceReachBounds (Fintype.card V) d deletedCap 2
      ballRadius M degreeInto maxSlowSize)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdeleted : deleted.card ≤ deletedCap)
    (hindex : SourceLemma35Numerics.indexCard (Fintype.card V) ≤
      (reachingEligibleSubfamily S targetSet connectionRadius).card)
    (hradius : ballRadius + ballRadius ≤ separation)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet)
    (hball : ∀ i :
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius =
        ballAvoidingFrom G
          ((deleted : Set V) ∪ (highDegree : Set V) ∪
            (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius)
    (hstart : bounds.growth 0 < minRadius ^ 2)
    (hstartOne : bounds.growth 1 < lm37SourceMinSize d)
    (hballOneLower : ∀ i :
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      lm37SourceMinSize d ≤ (ballAvoidingFrom G
        ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) 1).card)
    (hneighbor : ∀
      (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (ell s : ℕ), 0 < ell → ell ≤ ballRadius →
      bounds.growth (ell - 1) < s → i.1.1.radius ^ 2 ≤ s →
      bounds.stepLoss ell + (11 * i.1.1.radius + 1) + 2 * ell ≤
        bounds.neighborBudget s)
    (hlargeBudgetSum : ∀
      (J : Finset
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius} → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlowSize) →
      ∑ i ∈ J, bounds.neighborBudget (f i) ≤
        bounds.largeBudget (∑ i ∈ J, f i)) :
    ∃ i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      M ≤ (ballAvoidingFrom G
        ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius).card := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  let : DecidableRel G.Adj := originalDecAdj
  let I := {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius}
  let Aseed : I → Finset V := fun i ↦ reachingCandidateSeed i
  let Bset : I → Finset V := fun i ↦ reachingCandidateBarrier i
  let Cset : I → Finset V := fun i ↦ reachingCandidatePath i
  let scale := bounds.toCorrelatedScale
  apply exists_large_avoiding_ball_of_LM37CorrelatedScale
    G (1 / 1024) ((1 / 64) * (d : ℝ)) hexp deleted Aseed Bset Cset
      deletedCap (SourceLemma35Numerics.indexCard (Fintype.card V)) 2
      ballRadius M degreeInto scale hdeleted
  · simpa [I] using hindex
  · intro i
    dsimp [Aseed]
    rw [card_reachingCandidateSeed]
    exact hstart.trans_le (Nat.pow_le_pow_left i.1.1.min_le 2)
  · intro i
    exact hstartOne.trans_le (hballOneLower i)
  · exact hballOneLower
  · intro i
    simpa [Aseed, Bset, Cset] using reachingCandidate_limitedContact_barrier i
  · simpa [I, Aseed, Bset, Cset] using
      pairwiseDisjoint_reachingCandidate_actual_barrier_balls
        (G := G) hpair hradius hball
  · intro i ell hell hellRadius hslow
    dsimp [Bset]
    have hbarrier := card_reachingCandidateBarrier_le i
    have hle : bounds.stepLoss ell + (reachingCandidateBarrier i).card +
        2 * ell ≤ bounds.stepLoss ell + (11 * i.1.1.radius + 1) + 2 * ell := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_left hbarrier (bounds.stepLoss ell)) (2 * ell)
    have hseedCard : i.1.1.radius ^ 2 ≤ (reachingCandidateSeed i).card := by
      rw [card_reachingCandidateSeed]
    have hseedLower : i.1.1.radius ^ 2 ≤ (ballAvoidingFrom G
        ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) (ell - 1)).card :=
      hseedCard.trans (Finset.card_le_card
        (subset_ballAvoidingFrom G _ (reachingCandidateSeed i) (ell - 1)))
    exact hle.trans (hneighbor i ell _ hell hellRadius hslow hseedLower)
  · intro i v hv
    dsimp [Aseed, Bset, Cset] at hv ⊢
    exact reachingCandidate_degreeInto_deleted_le G i
      (by omega) hprotected (hball i) v hv
  · change ∀
      (J : Finset
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius} → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlowSize) →
      ∑ i ∈ J, bounds.neighborBudget (f i) ≤
        bounds.largeBudget (∑ i ∈ J, f i)
    exact hlargeBudgetSum

/-- Conditional reaching-candidate interface.  If the target is already at
most the retained radius-one scale, one candidate and its actual-root
bootstrap suffice; the source numerical package is requested only above
that scale. -/
theorem exists_large_reachingCandidate_ball_of_conditional_LM37SourceBounds
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius ballRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (d deletedCap M degreeInto maxSlowSize : ℕ)
    (bounds : lm37SourceMinSize d < M →
      LM37SourceReachBounds (Fintype.card V) d deletedCap 2
        ballRadius M degreeInto maxSlowSize)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdeleted : deleted.card ≤ deletedCap)
    (hindexPos : 0 < SourceLemma35Numerics.indexCard (Fintype.card V))
    (hindex : SourceLemma35Numerics.indexCard (Fintype.card V) ≤
      (reachingEligibleSubfamily S targetSet connectionRadius).card)
    (hballRadiusPos : 0 < ballRadius)
    (hradius : ballRadius + ballRadius ≤ separation)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet)
    (hball : ∀ i :
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius =
        ballAvoidingFrom G
          ((deleted : Set V) ∪ (highDegree : Set V) ∪
            (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius)
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (hstart : ∀ hM : lm37SourceMinSize d < M,
      (bounds hM).growth 0 < minRadius ^ 2)
    (hstartOne : ∀ hM : lm37SourceMinSize d < M,
      (bounds hM).growth 1 < lm37SourceMinSize d)
    (hseedOrRetained : ∀ i :
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      lm37SourceMinSize d ≤ i.1.1.radius ^ 2 ∨
        lm37SourceMinSize d ≤
          d - degreeInto - (11 * i.1.1.radius + 1) - 2)
    (hneighbor : ∀ hM : lm37SourceMinSize d < M,
      ∀ (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (ell s : ℕ), 0 < ell → ell ≤ ballRadius →
      (bounds hM).growth (ell - 1) < s → i.1.1.radius ^ 2 ≤ s →
      (bounds hM).stepLoss ell + (11 * i.1.1.radius + 1) + 2 * ell ≤
        (bounds hM).neighborBudget s)
    (hlargeBudgetSum : ∀ hM : lm37SourceMinSize d < M,
      ∀ (J : Finset
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius} → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlowSize) →
      ∑ i ∈ J, (bounds hM).neighborBudget (f i) ≤
        (bounds hM).largeBudget (∑ i ∈ J, f i)) :
    ∃ i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      M ≤ (ballAvoidingFrom G
        ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
          (reachingCandidatePath i : Set V))
        (reachingCandidateSeed i) ballRadius).card := by
  by_cases hM : lm37SourceMinSize d < M
  · have hballOneLower : ∀ i :
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
        lm37SourceMinSize d ≤ (ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) 1).card := by
      intro i
      rcases hseedOrRetained i with hseed | hretained
      · have hseedCard : i.1.1.radius ^ 2 ≤ (reachingCandidateSeed i).card := by
          rw [card_reachingCandidateSeed]
        exact hseed.trans (hseedCard.trans (Finset.card_le_card
          (subset_ballAvoidingFrom G _ (reachingCandidateSeed i) 1)))
      · exact hretained.trans (reachingCandidate_radiusOne_bootstrap G i
          (hdegree (reachingCandidateConnectionData i).adjusted.rightRoot)
          hprotected)
    exact exists_large_reachingCandidate_ball_of_LM37SourceBounds_of_radiusOneLower
      G hpair d deletedCap M degreeInto maxSlowSize (bounds hM) hexp
        hdeleted hindex hradius hprotected hball (hstart hM) (hstartOne hM)
        hballOneLower (hneighbor hM)
        (hlargeBudgetSum hM)
  · have hcardPos : 0 <
        (reachingEligibleSubfamily S targetSet connectionRadius).card :=
      hindexPos.trans_le hindex
    obtain ⟨A, hA⟩ := Finset.card_pos.mp hcardPos
    let i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius} :=
      ⟨A, hA⟩
    rcases hseedOrRetained i with hseed | hretained
    · have hseedCard : i.1.1.radius ^ 2 ≤ (reachingCandidateSeed i).card := by
        rw [card_reachingCandidateSeed]
      exact ⟨i, (Nat.le_of_not_gt hM).trans (hseed.trans
        (hseedCard.trans (Finset.card_le_card
          (subset_ballAvoidingFrom G _ (reachingCandidateSeed i) ballRadius))))⟩
    · have hboot := reachingCandidate_radiusOne_bootstrap G i
        (hdegree (reachingCandidateConnectionData i).adjusted.rightRoot) hprotected
      have hOne : M ≤ (ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) 1).card :=
        (Nat.le_of_not_gt hM).trans (hretained.trans hboot)
      exact ⟨i, hOne.trans (Finset.card_le_card
        (ballAvoidingFrom_radius_mono G _ _ (by omega : 1 ≤ ballRadius)))⟩

/-- Claim 4.5 with the source sample sizes and the source index
`floor(N^(1/8))`. -/
theorem card_reachingEligibleSubfamily_lt_of_no_targetAdjuster_source
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (d targetOrder totalRadius Delta deletedCap degreeInto maxSlowSize : ℕ)
    (bounds : LM37SourceReachBounds (Fintype.card V) d deletedCap 2
      connectionRadius targetOrder degreeInto maxSlowSize)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdeleted : deleted.card ≤ deletedCap)
    (hTargetSet : targetSet ⊆ highDegree \ deleted)
    (hHighDegree : ∀ v ∈ highDegree, Delta ≤ G.degree v)
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (hnoTarget : ¬ ∃ A : Adjuster G targetOrder totalRadius 1,
      Disjoint deleted A.verts)
    (hradius : connectionRadius + connectionRadius ≤ separation)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet)
    (hstart : bounds.growth 0 < minRadius ^ 2)
    (hstartOne : bounds.growth 1 < lm37SourceMinSize d)
    (hretained : ∀ i :
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      lm37SourceMinSize d ≤
        d - degreeInto - (11 * i.1.1.radius + 1) - 2)
    (hneighbor : ∀
      (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (ell s : ℕ), 0 < ell → ell ≤ connectionRadius →
      bounds.growth (ell - 1) < s →
      bounds.stepLoss ell + (11 * i.1.1.radius + 1) + 2 * ell ≤
        bounds.neighborBudget s)
    (hlargeBudgetSum : ∀
      (J : Finset
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius} → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlowSize) →
      ∑ i ∈ J, bounds.neighborBudget (f i) ≤
        bounds.largeBudget (∑ i ∈ J, f i))
    (hTargetPos : 0 < targetOrder)
    (hRightBudget : targetOrder +
      (deletedCap + 10 * maxRadius + (maxRadius + 1) +
        (connectionRadius + 1)) ≤ Delta)
    (hLeftBudget : targetOrder +
      (deletedCap + 10 * maxRadius + targetOrder) ≤ Delta)
    (hTotalRadius : maxRadius + connectionRadius + 1 ≤ totalRadius) :
    (reachingEligibleSubfamily S targetSet connectionRadius).card <
      SourceLemma35Numerics.indexCard (Fintype.card V) := by
  by_contra hcard
  have hindex : SourceLemma35Numerics.indexCard (Fintype.card V) ≤
      (reachingEligibleSubfamily S targetSet connectionRadius).card := by omega
  have hball : ∀ i :
      {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) connectionRadius =
        ballAvoidingFrom G
          ((deleted : Set V) ∪ (highDegree : Set V) ∪
            (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) connectionRadius := by
    intro i
    let P := reachingCandidateConnectionData i
    have hfinishHigh : P.finish ∈ highDegree :=
      (Finset.mem_sdiff.1 (hTargetSet P.finish_mem)).1
    have hnoSecond := no_second_highDegree_connection_of_no_targetAdjuster
      G i targetOrder totalRadius Delta deletedCap hTargetSet hHighDegree
        hnoTarget hTargetPos hdeleted hRightBudget hLeftBudget hTotalRadius
    exact reachingCandidate_ball_eq_highDegree_of_no_second i hfinishHigh hnoSecond
  obtain ⟨i, hiLarge⟩ :=
    exists_large_reachingCandidate_ball_of_LM37SourceBounds
      G hpair d deletedCap targetOrder degreeInto maxSlowSize bounds hexp
        hdeleted hindex hradius hprotected hball hdegree hstart hstartOne
        hretained hneighbor hlargeBudgetSum
  obtain ⟨A, hA⟩ := exists_targetAdjuster_of_large_reachingCandidate_ball
    G i targetOrder totalRadius Delta deletedCap hTargetSet hHighDegree hiLarge
      hTargetPos hdeleted hLeftBudget hTotalRadius (by omega)
  exact hnoTarget ⟨A, hA⟩

/-- Conditional Claim 4.5.  No `LM37SourceBounds` value is required when
`targetOrder ≤ lm37SourceMinSize d`. -/
theorem card_reachingEligibleSubfamily_lt_of_no_targetAdjuster_source_conditional
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (d targetOrder totalRadius Delta deletedCap degreeInto maxSlowSize : ℕ)
    (bounds : lm37SourceMinSize d < targetOrder →
      LM37SourceReachBounds (Fintype.card V) d deletedCap 2
        connectionRadius targetOrder degreeInto maxSlowSize)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdeleted : deleted.card ≤ deletedCap)
    (hindexPos : 0 < SourceLemma35Numerics.indexCard (Fintype.card V))
    (hconnectionRadiusPos : 0 < connectionRadius)
    (hTargetSet : targetSet ⊆ highDegree \ deleted)
    (hHighDegree : ∀ v ∈ highDegree, Delta ≤ G.degree v)
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (hnoTarget : ¬ ∃ A : Adjuster G targetOrder totalRadius 1,
      Disjoint deleted A.verts)
    (hradius : connectionRadius + connectionRadius ≤ separation)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet)
    (hstart : ∀ hM : lm37SourceMinSize d < targetOrder,
      (bounds hM).growth 0 < minRadius ^ 2)
    (hstartOne : ∀ hM : lm37SourceMinSize d < targetOrder,
      (bounds hM).growth 1 < lm37SourceMinSize d)
    (hseedOrRetained : ∀ i :
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      lm37SourceMinSize d ≤ i.1.1.radius ^ 2 ∨
        lm37SourceMinSize d ≤
          d - degreeInto - (11 * i.1.1.radius + 1) - 2)
    (hneighbor : ∀ hM : lm37SourceMinSize d < targetOrder,
      ∀ (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (ell s : ℕ), 0 < ell → ell ≤ connectionRadius →
      (bounds hM).growth (ell - 1) < s → i.1.1.radius ^ 2 ≤ s →
      (bounds hM).stepLoss ell + (11 * i.1.1.radius + 1) + 2 * ell ≤
        (bounds hM).neighborBudget s)
    (hlargeBudgetSum : ∀ hM : lm37SourceMinSize d < targetOrder,
      ∀ (J : Finset
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius} → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlowSize) →
      ∑ i ∈ J, (bounds hM).neighborBudget (f i) ≤
        (bounds hM).largeBudget (∑ i ∈ J, f i))
    (hTargetPos : 0 < targetOrder)
    (hRightBudget : targetOrder +
      (deletedCap + 10 * maxRadius + (maxRadius + 1) +
        (connectionRadius + 1)) ≤ Delta)
    (hLeftBudget : targetOrder +
      (deletedCap + 10 * maxRadius + targetOrder) ≤ Delta)
    (hTotalRadius : maxRadius + connectionRadius + 1 ≤ totalRadius) :
    (reachingEligibleSubfamily S targetSet connectionRadius).card <
      SourceLemma35Numerics.indexCard (Fintype.card V) := by
  by_contra hcard
  have hindex : SourceLemma35Numerics.indexCard (Fintype.card V) ≤
      (reachingEligibleSubfamily S targetSet connectionRadius).card := by omega
  have hball : ∀ i :
      {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) connectionRadius =
        ballAvoidingFrom G
          ((deleted : Set V) ∪ (highDegree : Set V) ∪
            (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) connectionRadius := by
    intro i
    let P := reachingCandidateConnectionData i
    have hfinishHigh : P.finish ∈ highDegree :=
      (Finset.mem_sdiff.1 (hTargetSet P.finish_mem)).1
    have hnoSecond := no_second_highDegree_connection_of_no_targetAdjuster
      G i targetOrder totalRadius Delta deletedCap hTargetSet hHighDegree
        hnoTarget hTargetPos hdeleted hRightBudget hLeftBudget hTotalRadius
    exact reachingCandidate_ball_eq_highDegree_of_no_second i hfinishHigh hnoSecond
  obtain ⟨i, hiLarge⟩ :=
    exists_large_reachingCandidate_ball_of_conditional_LM37SourceBounds
      G hpair d deletedCap targetOrder degreeInto maxSlowSize bounds hexp
        hdeleted hindexPos hindex hconnectionRadiusPos hradius hprotected hball
        hdegree hstart hstartOne hseedOrRetained hneighbor hlargeBudgetSum
  obtain ⟨A, hA⟩ := exists_targetAdjuster_of_large_reachingCandidate_ball
    G i targetOrder totalRadius Delta deletedCap hTargetSet hHighDegree hiLarge
      hTargetPos hdeleted hLeftBudget hTotalRadius (by omega)
  exact hnoTarget ⟨A, hA⟩

/-- Claim 4.6 with the source sample sizes and source index. -/
theorem card_reachingEligibleSubfamily_lt_of_no_targetAdjuster_expansion_source
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius ballRadius highRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (d targetOrder totalRadius deletedCap degreeInto farRadius maxSlowSize : ℕ)
    (bounds : LM37SourceReachBounds (Fintype.card V) d deletedCap 2
      ballRadius targetOrder degreeInto maxSlowSize)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdeleted : deleted.card ≤ deletedCap)
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (hnoTarget : ¬ ∃ A : Adjuster G targetOrder totalRadius 1,
      Disjoint deleted A.verts)
    (hnoHigh : ∀ A ∈ S, ¬ A.1.ReachesAvoidingOwnCore deleted
      (highDegree \ deleted) highRadius)
    (hballHigh : ballRadius ≤ highRadius)
    {center : V} (Z : VertexExpansion G center targetOrder farRadius)
    (hTargetSet : targetSet ⊆ Z.verts)
    (hZWorkspace : ∀ i :
      {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      Disjoint Z.verts
        (deleted ∪ (reachingCandidateConnectionData i).adjusted.core ∪
          ballAvoidingFrom G
            ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
              (reachingCandidatePath i : Set V))
            (reachingCandidateSeed i) ballRadius))
    (hradius : ballRadius + ballRadius ≤ separation)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet)
    (hstart : bounds.growth 0 < minRadius ^ 2)
    (hstartOne : bounds.growth 1 < lm37SourceMinSize d)
    (hretained : ∀ i :
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      lm37SourceMinSize d ≤
        d - degreeInto - (11 * i.1.1.radius + 1) - 2)
    (hneighbor : ∀
      (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (ell s : ℕ), 0 < ell → ell ≤ ballRadius →
      bounds.growth (ell - 1) < s →
      bounds.stepLoss ell + (11 * i.1.1.radius + 1) + 2 * ell ≤
        bounds.neighborBudget s)
    (hlargeBudgetSum : ∀
      (J : Finset
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius} → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlowSize) →
      ∑ i ∈ J, bounds.neighborBudget (f i) ≤
        bounds.largeBudget (∑ i ∈ J, f i))
    (hTargetPos : 0 < targetOrder)
    (hLeftRadius : maxRadius + connectionRadius + 2 * farRadius ≤ totalRadius)
    (hRightRadius : maxRadius + ballRadius ≤ totalRadius) :
    (reachingEligibleSubfamily S targetSet connectionRadius).card <
      SourceLemma35Numerics.indexCard (Fintype.card V) := by
  by_contra hcard
  have hindex : SourceLemma35Numerics.indexCard (Fintype.card V) ≤
      (reachingEligibleSubfamily S targetSet connectionRadius).card := by omega
  have hball : ∀ i :
      {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius =
        ballAvoidingFrom G
          ((deleted : Set V) ∪ (highDegree : Set V) ∪
            (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius := by
    intro i
    have hiS :=
      ((mem_reachingEligibleSubfamily S targetSet connectionRadius i.1).1 i.2).1
    exact reachingCandidate_ball_eq_highDegree_of_no_highConnection i
      (hnoHigh i.1 hiS) hballHigh
  obtain ⟨i, hiLarge⟩ :=
    exists_large_reachingCandidate_ball_of_LM37SourceBounds
      G hpair d deletedCap targetOrder degreeInto maxSlowSize bounds hexp
        hdeleted hindex hradius hprotected hball hdegree hstart hstartOne
        hretained hneighbor hlargeBudgetSum
  have hfinishZ : (reachingCandidateConnectionData i).finish ∈ Z.verts :=
    hTargetSet (reachingCandidateConnectionData i).finish_mem
  obtain ⟨A, hA⟩ :=
    exists_targetAdjuster_of_large_reachingCandidate_ball_expansion
      i targetOrder totalRadius farRadius Z hfinishZ hiLarge (hZWorkspace i)
        hTargetPos hLeftRadius hRightRadius
  exact hnoTarget ⟨A, hA⟩

/-- Conditional Claim 4.6.  The source numerical certificate is required
only when the desired opposite-end ball exceeds the retained radius-one
scale. -/
theorem card_reachingEligibleSubfamily_lt_of_no_targetAdjuster_expansion_source_conditional
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet targetSet : Finset V}
    {separation connectionRadius ballRadius highRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (d targetOrder totalRadius deletedCap degreeInto farRadius maxSlowSize : ℕ)
    (bounds : lm37SourceMinSize d < targetOrder →
      LM37SourceReachBounds (Fintype.card V) d deletedCap 2
        ballRadius targetOrder degreeInto maxSlowSize)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hdeleted : deleted.card ≤ deletedCap)
    (hindexPos : 0 < SourceLemma35Numerics.indexCard (Fintype.card V))
    (hballRadiusPos : 0 < ballRadius)
    (hdegree : ∀ v : V, d ≤ G.degree v)
    (hnoTarget : ¬ ∃ A : Adjuster G targetOrder totalRadius 1,
      Disjoint deleted A.verts)
    (hnoHigh : ∀ A ∈ S, ¬ A.1.ReachesAvoidingOwnCore deleted
      (highDegree \ deleted) highRadius)
    (hballHigh : ballRadius ≤ highRadius)
    {center : V} (Z : VertexExpansion G center targetOrder farRadius)
    (hTargetSet : targetSet ⊆ Z.verts)
    (hZWorkspace : ∀ i :
      {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      Disjoint Z.verts
        (deleted ∪ (reachingCandidateConnectionData i).adjusted.core ∪
          ballAvoidingFrom G
            ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
              (reachingCandidatePath i : Set V))
            (reachingCandidateSeed i) ballRadius))
    (hradius : ballRadius + ballRadius ≤ separation)
    (hprotected : deleted ∪ manyNeighborsInto G deleted degreeInto ⊆
      protectedSet)
    (hstart : ∀ hM : lm37SourceMinSize d < targetOrder,
      (bounds hM).growth 0 < minRadius ^ 2)
    (hstartOne : ∀ hM : lm37SourceMinSize d < targetOrder,
      (bounds hM).growth 1 < lm37SourceMinSize d)
    (hseedOrRetained : ∀ i :
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      lm37SourceMinSize d ≤ i.1.1.radius ^ 2 ∨
        lm37SourceMinSize d ≤
          d - degreeInto - (11 * i.1.1.radius + 1) - 2)
    (hneighbor : ∀ hM : lm37SourceMinSize d < targetOrder,
      ∀ (i : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (ell s : ℕ), 0 < ell → ell ≤ ballRadius →
      (bounds hM).growth (ell - 1) < s → i.1.1.radius ^ 2 ≤ s →
      (bounds hM).stepLoss ell + (11 * i.1.1.radius + 1) + 2 * ell ≤
        (bounds hM).neighborBudget s)
    (hlargeBudgetSum : ∀ hM : lm37SourceMinSize d < targetOrder,
      ∀ (J : Finset
        {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius})
      (f : {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius} → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlowSize) →
      ∑ i ∈ J, (bounds hM).neighborBudget (f i) ≤
        (bounds hM).largeBudget (∑ i ∈ J, f i))
    (hTargetPos : 0 < targetOrder)
    (hLeftRadius : maxRadius + connectionRadius + 2 * farRadius ≤ totalRadius)
    (hRightRadius : maxRadius + ballRadius ≤ totalRadius) :
    (reachingEligibleSubfamily S targetSet connectionRadius).card <
      SourceLemma35Numerics.indexCard (Fintype.card V) := by
  by_contra hcard
  have hindex : SourceLemma35Numerics.indexCard (Fintype.card V) ≤
      (reachingEligibleSubfamily S targetSet connectionRadius).card := by omega
  have hball : ∀ i :
      {A // A ∈ reachingEligibleSubfamily S targetSet connectionRadius},
      ballAvoidingFrom G
          ((deleted : Set V) ∪ (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius =
        ballAvoidingFrom G
          ((deleted : Set V) ∪ (highDegree : Set V) ∪
            (reachingCandidateBarrier i : Set V) ∪
            (reachingCandidatePath i : Set V))
          (reachingCandidateSeed i) ballRadius := by
    intro i
    have hiS :=
      ((mem_reachingEligibleSubfamily S targetSet connectionRadius i.1).1 i.2).1
    exact reachingCandidate_ball_eq_highDegree_of_no_highConnection i
      (hnoHigh i.1 hiS) hballHigh
  obtain ⟨i, hiLarge⟩ :=
    exists_large_reachingCandidate_ball_of_conditional_LM37SourceBounds
      G hpair d deletedCap targetOrder degreeInto maxSlowSize bounds hexp
        hdeleted hindexPos hindex hballRadiusPos hradius hprotected hball hdegree
        hstart hstartOne hseedOrRetained hneighbor hlargeBudgetSum
  have hfinishZ : (reachingCandidateConnectionData i).finish ∈ Z.verts :=
    hTargetSet (reachingCandidateConnectionData i).finish_mem
  obtain ⟨A, hA⟩ :=
    exists_targetAdjuster_of_large_reachingCandidate_ball_expansion
      i targetOrder totalRadius farRadius Z hfinishZ hiLarge (hZWorkspace i)
        hTargetPos hLeftRadius hRightRadius
  exact hnoTarget ⟨A, hA⟩

/-! ## The final two-ended source application -/

/-- A surviving candidate's actual ball is contained in the corresponding
high-degree-deleted ball, using exactly its Claim 4.5 non-reachability
certificate. -/
theorem source_candidate_ball_subset_highDegree_ball_of_no_high
    [Fintype V] (G : SimpleGraph V)
    {deleted highDegree protectedSet : Finset V}
    {separation highRadius ballRadius minRadius maxRadius : ℕ}
    (A : SmallSimpleAdjusterCandidate G minRadius maxRadius)
    (hA : A.Eligible deleted highDegree protectedSet separation)
    (hnoHigh : ¬ A.ReachesAvoidingOwnCore deleted
      (highDegree \ deleted) highRadius)
    (hballHigh : ballRadius ≤ highRadius) :
    ballAvoidingFrom G
        (((deleted ∪ A.adjuster.core : Finset V) : Set V))
        A.ends ballRadius ⊆
      ballAvoidingFrom G
        (((highDegree ∪ A.adjuster.core : Finset V) : Set V))
        A.ends ballRadius := by
  classical
  let X : Finset V := deleted ∪ A.adjuster.core
  have hfar : ¬ HasShortAvoidingConnection G X A.ends highDegree ballRadius := by
    intro hreach
    apply hnoHigh
    obtain ⟨x, hx, y, hy, p, hp, hpAvoid, hpLength⟩ := hreach
    have hyDeleted : y ∉ deleted := by
      intro hyDeleted
      apply hpAvoid y (by simp)
      exact Finset.mem_union_left _ hyDeleted
    exact ⟨x, hx, y, Finset.mem_sdiff.2 ⟨hy, hyDeleted⟩,
      p, hp, hpAvoid, hpLength.trans hballHigh⟩
  have heq := ballAvoidingFrom_union_eq_of_no_shortAvoidingConnection
    G X highDegree A.ends ballRadius
      (A.ends_disjoint_deleted_union_core hA) hfar
  rw [← heq]
  apply ballAvoidingFrom_forbidden_anti G
  intro z hz
  rw [Finset.coe_union] at hz
  change z ∈ (X : Set V) ∪ (highDegree : Set V)
  rcases hz with hzHigh | hzCore
  · exact Or.inr hzHigh
  · exact Or.inl (Finset.mem_union_right _ hzCore)

/-- The final Lemma 3.7 use after Claims 4.5 and 4.6.  It grows the union of
both ends and has the source target `10 * m^2 * D`, distinct from the `D`
target of the two reachability claims. -/
theorem exists_large_twoEnd_ball_of_LM37SourceFinalBounds
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet : Finset V}
    {separation highRadius ballRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (d deletedCap degreeInto m Dtarget maxSlowSize : ℕ)
    (bounds : LM37SourceFinalTwoEndBounds (Fintype.card V) d deletedCap 0
      ballRadius m Dtarget degreeInto maxSlowSize)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hcard : S.card = SourceLemma35Numerics.indexCard (Fintype.card V))
    (hdeleted : deleted.card ≤ deletedCap)
    (hnoHigh : ∀ A ∈ S, ¬ A.1.ReachesAvoidingOwnCore deleted
      (highDegree \ deleted) highRadius)
    (hballHigh : ballRadius ≤ highRadius)
    (hseparation : ballRadius + ballRadius ≤ separation)
    (hdegreeMin : ∀ v : V, d ≤ G.degree v)
    (hstart : bounds.growth 0 < 2 * minRadius ^ 2)
    (hstartOne : bounds.growth 1 < lm37SourceMinSize d)
    (hretained : ∀ i : S, lm37SourceMinSize d ≤
      d - degreeInto - 10 * i.1.1.radius)
    (hneighbor : ∀ (i : S) (ell s : ℕ),
      0 < ell → ell ≤ ballRadius → bounds.growth (ell - 1) < s →
      bounds.stepLoss ell + 10 * i.1.1.radius ≤ bounds.neighborBudget s)
    (hdegree : ∀ i : S, ∀ v ∈ ballAvoidingFrom G
      (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
      i.1.1.ends ballRadius,
        (G.neighborFinset v ∩ deleted).card ≤ degreeInto)
    (hlargeBudgetSum : ∀ (J : Finset S) (f : S → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlowSize) →
      ∑ i ∈ J, bounds.neighborBudget (f i) ≤
        bounds.largeBudget (∑ i ∈ J, f i)) :
    ∃ i : S, 10 * m ^ 2 * Dtarget ≤
      (ballAvoidingFrom G
        (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
        i.1.1.ends ballRadius).card := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  let : DecidableRel G.Adj := originalDecAdj
  let Aseed : S → Finset V := fun i ↦ i.1.1.ends
  let Bset : S → Finset V := fun i ↦ i.1.1.adjuster.core
  let Cset : S → Finset V := fun _ ↦ ∅
  let scale := bounds.toCorrelatedScale
  have hpairHigh :
      ((Finset.univ : Finset S) : Set S).PairwiseDisjoint
        (fun i ↦ ballAvoidingFrom G
          ((highDegree : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
          (Aseed i) ballRadius) :=
    pairwiseDisjoint_candidate_avoidingBalls
      (G := G) hpair hseparation Bset Cset
  have hpairActual :
      ((Finset.univ : Finset S) : Set S).PairwiseDisjoint
        (fun i ↦ ballAvoidingFrom G
          ((deleted : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
          (Aseed i) ballRadius) := by
    intro i hi j hj hij
    apply (hpairHigh hi hj hij).mono
    · simpa [Aseed, Bset, Cset, Set.union_empty] using
        source_candidate_ball_subset_highDegree_ball_of_no_high
          G i.1.1 i.1.2 (hnoHigh i.1 i.2) hballHigh
    · simpa [Aseed, Bset, Cset, Set.union_empty] using
        source_candidate_ball_subset_highDegree_ball_of_no_high
          G j.1.1 j.1.2 (hnoHigh j.1 j.2) hballHigh
  suffices hlarge : ∃ i : S, 10 * m ^ 2 * Dtarget ≤
      (ballAvoidingFrom G
        ((deleted : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
        (Aseed i) ballRadius).card by
    obtain ⟨i, hi⟩ := hlarge
    exact ⟨i, by
      simpa [Aseed, Bset, Cset, Set.union_empty] using hi⟩
  apply exists_large_avoiding_ball_of_LM37CorrelatedScale
    G (1 / 1024) ((1 / 64) * (d : ℝ)) hexp deleted Aseed Bset Cset
      deletedCap (SourceLemma35Numerics.indexCard (Fintype.card V)) 0
      ballRadius (10 * m ^ 2 * Dtarget) degreeInto scale hdeleted
  · simpa [hcard]
  · intro i
    dsimp [Aseed]
    rw [card_ends]
    exact hstart.trans_le (Nat.mul_le_mul_left 2
      (Nat.pow_le_pow_left i.1.1.min_le 2))
  · intro i
    have hx : i.1.1.adjuster.leftRoot ∈ Aseed i := by
      simpa [Aseed] using i.1.1.adjuster.leftEnd.root_mem
    have hdisjoint : Disjoint (Aseed i) (deleted ∪ Bset i ∪ Cset i) := by
      simpa [Aseed, Bset, Cset] using
        i.1.1.ends_disjoint_deleted_union_core i.1.2
    have hcore : (Bset i).card ≤ 10 * i.1.1.radius := by
      simpa [Bset] using i.1.1.adjuster.core_card_le
    have hxBall : i.1.1.adjuster.leftRoot ∈ ballAvoidingFrom G
        ((deleted : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
        (Aseed i) ballRadius := subset_ballAvoidingFrom G _ _ _ hx
    have hboot :=
      degree_sub_degreeInto_sub_card_sub_contact_le_card_ballAvoidingFrom_one
        G deleted (Bset i) (Cset i) (Aseed i) i.1.1.adjuster.leftRoot
          d degreeInto (10 * i.1.1.radius) 0 hx hdisjoint
          (hdegreeMin i.1.1.adjuster.leftRoot)
          (by
            have := hdegree i i.1.1.adjuster.leftRoot (by
              simpa [Aseed, Bset, Cset, Set.union_empty] using hxBall)
            exact this)
          hcore (by
            intro r
            simp [Cset, HasLimitedContactAfterDeletion,
              blockedExternalNeighborhood])
    exact hstartOne.trans_le ((hretained i).trans (by simpa using hboot))
  · intro i
    have hx : i.1.1.adjuster.leftRoot ∈ Aseed i := by
      simpa [Aseed] using i.1.1.adjuster.leftEnd.root_mem
    have hdisjoint : Disjoint (Aseed i) (deleted ∪ Bset i ∪ Cset i) := by
      simpa [Aseed, Bset, Cset] using
        i.1.1.ends_disjoint_deleted_union_core i.1.2
    have hcore : (Bset i).card ≤ 10 * i.1.1.radius := by
      simpa [Bset] using i.1.1.adjuster.core_card_le
    have hxBall : i.1.1.adjuster.leftRoot ∈ ballAvoidingFrom G
        ((deleted : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
        (Aseed i) ballRadius := subset_ballAvoidingFrom G _ _ _ hx
    have hboot :=
      degree_sub_degreeInto_sub_card_sub_contact_le_card_ballAvoidingFrom_one
        G deleted (Bset i) (Cset i) (Aseed i) i.1.1.adjuster.leftRoot
          d degreeInto (10 * i.1.1.radius) 0 hx hdisjoint
          (hdegreeMin i.1.1.adjuster.leftRoot)
          (by
            have := hdegree i i.1.1.adjuster.leftRoot (by
              simpa [Aseed, Bset, Cset, Set.union_empty] using hxBall)
            exact this)
          hcore (by
            intro r
            simp [Cset, HasLimitedContactAfterDeletion,
              blockedExternalNeighborhood])
    exact (hretained i).trans (by simpa using hboot)
  · intro i r
    simp [Cset, HasLimitedContactAfterDeletion, blockedExternalNeighborhood]
  · exact hpairActual
  · intro i ell hell hellRadius hslow
    dsimp [Bset]
    have hcore : i.1.1.adjuster.core.card ≤ 10 * i.1.1.radius := by
      simpa using i.1.1.adjuster.core_card_le
    simpa [scale, LM37SourceBounds.toCorrelatedScale, Cset] using
      (Nat.add_le_add_left hcore (bounds.stepLoss ell)).trans
        (hneighbor i ell _ hell hellRadius hslow)
  · intro i v hv
    have hv' : v ∈ ballAvoidingFrom G
        (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
        i.1.1.ends ballRadius := by
      simpa [Aseed, Bset, Cset, Set.union_empty] using hv
    exact hdegree i v hv'
  · simpa [scale, LM37SourceBounds.toCorrelatedScale] using hlargeBudgetSum

/-- Final two-end source theorem with the radius-one lower bound supplied
explicitly.  The neighbor budget may use the fact that every preceding ball
contains the candidate's end seed. -/
theorem exists_large_twoEnd_ball_of_LM37SourceFinalBounds_of_radiusOneLower
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet : Finset V}
    {separation highRadius ballRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (d deletedCap degreeInto m Dtarget maxSlowSize : ℕ)
    (bounds : LM37SourceFinalTwoEndBounds (Fintype.card V) d deletedCap 0
      ballRadius m Dtarget degreeInto maxSlowSize)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hcard : S.card = SourceLemma35Numerics.indexCard (Fintype.card V))
    (hdeleted : deleted.card ≤ deletedCap)
    (hnoHigh : ∀ A ∈ S, ¬ A.1.ReachesAvoidingOwnCore deleted
      (highDegree \ deleted) highRadius)
    (hballHigh : ballRadius ≤ highRadius)
    (hseparation : ballRadius + ballRadius ≤ separation)
    (hstart : bounds.growth 0 < 2 * minRadius ^ 2)
    (hstartOne : bounds.growth 1 < lm37SourceMinSize d)
    (hballOneLower : ∀ i : S, lm37SourceMinSize d ≤
      (ballAvoidingFrom G
        (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
        i.1.1.ends 1).card)
    (hneighbor : ∀ (i : S) (ell s : ℕ),
      0 < ell → ell ≤ ballRadius → bounds.growth (ell - 1) < s →
      i.1.1.radius ^ 2 ≤ s →
      bounds.stepLoss ell + 10 * i.1.1.radius ≤ bounds.neighborBudget s)
    (hdegree : ∀ i : S, ∀ v ∈ ballAvoidingFrom G
      (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
      i.1.1.ends ballRadius,
        (G.neighborFinset v ∩ deleted).card ≤ degreeInto)
    (hlargeBudgetSum : ∀ (J : Finset S) (f : S → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlowSize) →
      ∑ i ∈ J, bounds.neighborBudget (f i) ≤
        bounds.largeBudget (∑ i ∈ J, f i)) :
    ∃ i : S, 10 * m ^ 2 * Dtarget ≤
      (ballAvoidingFrom G
        (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
        i.1.1.ends ballRadius).card := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  let : DecidableRel G.Adj := originalDecAdj
  let Aseed : S → Finset V := fun i ↦ i.1.1.ends
  let Bset : S → Finset V := fun i ↦ i.1.1.adjuster.core
  let Cset : S → Finset V := fun _ ↦ ∅
  let scale := bounds.toCorrelatedScale
  have hpairHigh :
      ((Finset.univ : Finset S) : Set S).PairwiseDisjoint
        (fun i ↦ ballAvoidingFrom G
          ((highDegree : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
          (Aseed i) ballRadius) :=
    pairwiseDisjoint_candidate_avoidingBalls
      (G := G) hpair hseparation Bset Cset
  have hpairActual :
      ((Finset.univ : Finset S) : Set S).PairwiseDisjoint
        (fun i ↦ ballAvoidingFrom G
          ((deleted : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
          (Aseed i) ballRadius) := by
    intro i hi j hj hij
    apply (hpairHigh hi hj hij).mono
    · simpa [Aseed, Bset, Cset, Set.union_empty] using
        source_candidate_ball_subset_highDegree_ball_of_no_high
          G i.1.1 i.1.2 (hnoHigh i.1 i.2) hballHigh
    · simpa [Aseed, Bset, Cset, Set.union_empty] using
        source_candidate_ball_subset_highDegree_ball_of_no_high
          G j.1.1 j.1.2 (hnoHigh j.1 j.2) hballHigh
  suffices hlarge : ∃ i : S, 10 * m ^ 2 * Dtarget ≤
      (ballAvoidingFrom G
        ((deleted : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
        (Aseed i) ballRadius).card by
    obtain ⟨i, hi⟩ := hlarge
    exact ⟨i, by simpa [Aseed, Bset, Cset, Set.union_empty] using hi⟩
  apply exists_large_avoiding_ball_of_LM37CorrelatedScale
    G (1 / 1024) ((1 / 64) * (d : ℝ)) hexp deleted Aseed Bset Cset
      deletedCap (SourceLemma35Numerics.indexCard (Fintype.card V)) 0
      ballRadius (10 * m ^ 2 * Dtarget) degreeInto scale hdeleted
  · simpa [hcard]
  · intro i
    dsimp [Aseed]
    rw [card_ends]
    exact hstart.trans_le (Nat.mul_le_mul_left 2
      (Nat.pow_le_pow_left i.1.1.min_le 2))
  · intro i
    exact hstartOne.trans_le (by
      simpa [scale, LM37SourceBounds.toCorrelatedScale, Aseed, Bset, Cset,
        Set.union_empty] using hballOneLower i)
  · intro i
    simpa [scale, LM37SourceBounds.toCorrelatedScale, Aseed, Bset, Cset,
      Set.union_empty] using hballOneLower i
  · intro i r
    simp [Cset, HasLimitedContactAfterDeletion, blockedExternalNeighborhood]
  · exact hpairActual
  · intro i ell hell hellRadius hslow
    dsimp [Bset]
    have hcore : i.1.1.adjuster.core.card ≤ 10 * i.1.1.radius := by
      simpa using i.1.1.adjuster.core_card_le
    have hseedCard : i.1.1.radius ^ 2 ≤ (Aseed i).card := by
      dsimp [Aseed]
      rw [card_ends]
      omega
    have hseedLower : i.1.1.radius ^ 2 ≤ (ballAvoidingFrom G
        ((deleted : Set V) ∪ (Bset i : Set V) ∪ (Cset i : Set V))
        (Aseed i) (ell - 1)).card :=
      hseedCard.trans (Finset.card_le_card
        (subset_ballAvoidingFrom G _ (Aseed i) (ell - 1)))
    simpa [scale, LM37SourceBounds.toCorrelatedScale, Cset] using
      (Nat.add_le_add_left hcore (bounds.stepLoss ell)).trans
        (hneighbor i ell _ hell hellRadius hslow hseedLower)
  · intro i v hv
    have hv' : v ∈ ballAvoidingFrom G
        (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
        i.1.1.ends ballRadius := by
      simpa [Aseed, Bset, Cset, Set.union_empty] using hv
    exact hdegree i v hv'
  · simpa [scale, LM37SourceBounds.toCorrelatedScale] using hlargeBudgetSum

/-- Conditional final two-end application.  The costly source package is
needed only if `10 * m^2 * Dtarget` is strictly above the retained
radius-one scale. -/
theorem exists_large_twoEnd_ball_of_conditional_LM37SourceFinalBounds
    [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {deleted highDegree protectedSet : Finset V}
    {separation highRadius ballRadius minRadius maxRadius : ℕ}
    {S : Finset
      {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}}
    (hpair : ((S : Set {A : SmallSimpleAdjusterCandidate G minRadius maxRadius //
        A.Eligible deleted highDegree protectedSet separation}).Pairwise fun A B ↦
      ¬ Conflict A.1 B.1 highDegree separation))
    (d deletedCap degreeInto m Dtarget maxSlowSize : ℕ)
    (bounds : lm37SourceMinSize d < 10 * m ^ 2 * Dtarget →
      LM37SourceFinalTwoEndBounds (Fintype.card V) d deletedCap 0
        ballRadius m Dtarget degreeInto maxSlowSize)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (hindexPos : 0 < SourceLemma35Numerics.indexCard (Fintype.card V))
    (hcard : S.card = SourceLemma35Numerics.indexCard (Fintype.card V))
    (hdeleted : deleted.card ≤ deletedCap)
    (hnoHigh : ∀ A ∈ S, ¬ A.1.ReachesAvoidingOwnCore deleted
      (highDegree \ deleted) highRadius)
    (hballHigh : ballRadius ≤ highRadius)
    (hballRadiusPos : 0 < ballRadius)
    (hseparation : ballRadius + ballRadius ≤ separation)
    (hdegreeMin : ∀ v : V, d ≤ G.degree v)
    (hstart : ∀ hM : lm37SourceMinSize d < 10 * m ^ 2 * Dtarget,
      (bounds hM).growth 0 < 2 * minRadius ^ 2)
    (hstartOne : ∀ hM : lm37SourceMinSize d < 10 * m ^ 2 * Dtarget,
      (bounds hM).growth 1 < lm37SourceMinSize d)
    (hseedOrRetained : ∀ i : S,
      lm37SourceMinSize d ≤ 2 * i.1.1.radius ^ 2 ∨
        lm37SourceMinSize d ≤ d - degreeInto - 10 * i.1.1.radius)
    (hneighbor : ∀ hM : lm37SourceMinSize d < 10 * m ^ 2 * Dtarget,
      ∀ (i : S) (ell s : ℕ), 0 < ell → ell ≤ ballRadius →
      (bounds hM).growth (ell - 1) < s → i.1.1.radius ^ 2 ≤ s →
      (bounds hM).stepLoss ell + 10 * i.1.1.radius ≤
        (bounds hM).neighborBudget s)
    (hdegree : ∀ i : S, ∀ v ∈ ballAvoidingFrom G
      (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
      i.1.1.ends ballRadius,
        (G.neighborFinset v ∩ deleted).card ≤ degreeInto)
    (hlargeBudgetSum :
      ∀ hM : lm37SourceMinSize d < 10 * m ^ 2 * Dtarget,
      ∀ (J : Finset S) (f : S → ℕ),
      (∀ i ∈ J, lm37SourceCutoff (Fintype.card V) ≤ f i ∧
        f i ≤ maxSlowSize) →
      ∑ i ∈ J, (bounds hM).neighborBudget (f i) ≤
        (bounds hM).largeBudget (∑ i ∈ J, f i)) :
    ∃ i : S, 10 * m ^ 2 * Dtarget ≤
      (ballAvoidingFrom G
        (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
        i.1.1.ends ballRadius).card := by
  by_cases hM : lm37SourceMinSize d < 10 * m ^ 2 * Dtarget
  · have hballOneLower : ∀ i : S, lm37SourceMinSize d ≤
        (ballAvoidingFrom G
          (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
          i.1.1.ends 1).card := by
      intro i
      rcases hseedOrRetained i with hseed | hretained
      · have hseedCard : 2 * i.1.1.radius ^ 2 ≤ i.1.1.ends.card := by
          rw [card_ends]
        exact hseed.trans (hseedCard.trans (Finset.card_le_card
          (subset_ballAvoidingFrom G _ i.1.1.ends 1)))
      · have hx : i.1.1.adjuster.leftRoot ∈ i.1.1.ends :=
          i.1.1.leftRoot_mem_ends
        have hdisjoint : Disjoint i.1.1.ends
            (deleted ∪ i.1.1.adjuster.core ∪ (∅ : Finset V)) := by
          simpa using i.1.1.ends_disjoint_deleted_union_core i.1.2
        have hcore : i.1.1.adjuster.core.card ≤ 10 * i.1.1.radius := by
          simpa using i.1.1.adjuster.core_card_le
        have hxBall : i.1.1.adjuster.leftRoot ∈ ballAvoidingFrom G
            (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
            i.1.1.ends ballRadius := subset_ballAvoidingFrom G _ _ _ hx
        have hboot :=
          degree_sub_degreeInto_sub_card_sub_contact_le_card_ballAvoidingFrom_one
            G deleted i.1.1.adjuster.core ∅ i.1.1.ends
              i.1.1.adjuster.leftRoot d degreeInto (10 * i.1.1.radius) 0 hx
              hdisjoint (hdegreeMin i.1.1.adjuster.leftRoot) (hdegree i _ hxBall)
              hcore (by
                intro r
                simp [HasLimitedContactAfterDeletion, blockedExternalNeighborhood])
        exact hretained.trans (by simpa using hboot)
    exact exists_large_twoEnd_ball_of_LM37SourceFinalBounds_of_radiusOneLower
      G hpair d deletedCap degreeInto m Dtarget maxSlowSize (bounds hM) hexp
        hcard hdeleted hnoHigh hballHigh hseparation (hstart hM)
        (hstartOne hM) hballOneLower (hneighbor hM) hdegree
        (hlargeBudgetSum hM)
  · have hScardPos : 0 < S.card := by simpa [hcard] using hindexPos
    obtain ⟨A, hA⟩ := Finset.card_pos.mp hScardPos
    let i : S := ⟨A, hA⟩
    rcases hseedOrRetained i with hseed | hretained
    · have hseedCard : 2 * i.1.1.radius ^ 2 ≤ i.1.1.ends.card := by
        rw [card_ends]
      exact ⟨i, (Nat.le_of_not_gt hM).trans (hseed.trans
        (hseedCard.trans (Finset.card_le_card
          (subset_ballAvoidingFrom G _ i.1.1.ends ballRadius))))⟩
    · have hx : i.1.1.adjuster.leftRoot ∈ i.1.1.ends :=
        i.1.1.leftRoot_mem_ends
      have hdisjoint : Disjoint i.1.1.ends
          (deleted ∪ i.1.1.adjuster.core ∪ (∅ : Finset V)) := by
        simpa using i.1.1.ends_disjoint_deleted_union_core i.1.2
      have hcore : i.1.1.adjuster.core.card ≤ 10 * i.1.1.radius := by
        simpa using i.1.1.adjuster.core_card_le
      have hxBall : i.1.1.adjuster.leftRoot ∈ ballAvoidingFrom G
          (((deleted ∪ i.1.1.adjuster.core : Finset V) : Set V))
          i.1.1.ends ballRadius := subset_ballAvoidingFrom G _ _ _ hx
      have hboot :=
        degree_sub_degreeInto_sub_card_sub_contact_le_card_ballAvoidingFrom_one
          G deleted i.1.1.adjuster.core ∅ i.1.1.ends
            i.1.1.adjuster.leftRoot d degreeInto (10 * i.1.1.radius) 0 hx
            hdisjoint (hdegreeMin i.1.1.adjuster.leftRoot) (hdegree i _ hxBall)
            hcore (by
              intro r
              simp [HasLimitedContactAfterDeletion, blockedExternalNeighborhood])
      have hOne : 10 * m ^ 2 * Dtarget ≤ (ballAvoidingFrom G
          ((deleted : Set V) ∪ (i.1.1.adjuster.core : Set V) ∪
            ((∅ : Finset V) : Set V)) i.1.1.ends 1).card :=
        (Nat.le_of_not_gt hM).trans (hretained.trans (by simpa using hboot))
      exact ⟨i, hOne.trans (by
        simpa using Finset.card_le_card
          (ballAvoidingFrom_radius_mono G
            ((deleted : Set V) ∪ (i.1.1.adjuster.core : Set V) ∪
              ((∅ : Finset V) : Set V)) i.1.1.ends
            (by omega : 1 ≤ ballRadius)))⟩

end SmallSimpleAdjusterCandidate

end Erdos63
