/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.Estimates
import ErdosProblems.Erdos186.PZ.Reduction.FailureEstimates
import ErdosProblems.Erdos186.PZ.Reduction.NoDimensionIncrease
import ErdosProblems.Erdos186.PZ.Reduction.Normalization
import ErdosProblems.Erdos186.PZ.Reduction.InitialEstimates
import ErdosProblems.Erdos186.PZ.Reduction.InitialNoDimensionIncrease
import ErdosProblems.Erdos186.PZ.Reduction.CanonicalScale
import ErdosProblems.Erdos186.PZ.Reduction.CoreFraction
import ErdosProblems.Erdos186.PZ.Reduction.CandidateEligibility
import ErdosProblems.Erdos186.PZ.Reduction.TerminalAbsorption
import ErdosProblems.Erdos186.PZ.Reduction.TerminalClosure
import ErdosProblems.Erdos186.PZ.Reduction.TraceAdapter
import ErdosProblems.Erdos186.PZ.Reduction.GuardedTermination
import ErdosProblems.Erdos186.PZ.Reduction.QuantitativeRanks
import ErdosProblems.Erdos186.PZ.Reduction.QuantitativeOneStep
import ErdosProblems.Erdos186.PZ.Reduction.PopulationAbsorption
import ErdosProblems.Erdos186.PZ.Reduction.FirstCrossingAbsorption
import ErdosProblems.Erdos186.PZ.Reduction.FirstCrossingControl
import ErdosProblems.Erdos186.PZ.Reduction.GuardShrinkAbsorption
import ErdosProblems.Erdos186.PZ.Reduction.EqualRankAbsorption
import ErdosProblems.Erdos186.PZ.Reduction.InitialUniformBounds
import ErdosProblems.Erdos186.PZ.Reduction.QuantitativeTerminal
import ErdosProblems.Erdos186.PZ.Reduction.QuantitativeVolumeCases
import ErdosProblems.Erdos186.PZ.Reduction.TerminalGapAbsorption
import ErdosProblems.Erdos186.PZ.Reduction.Replacement
import ErdosProblems.Erdos186.PZ.Reduction.BoundedContext
import ErdosProblems.Erdos186.PZ.Reduction.CoordinateReplacement
import ErdosProblems.Erdos186.PZ.Reduction.Termination

/-!
# Pham--Zakharov reduction (Lemmas 6--10)

The exact finite inequalities underlying Lemmas 6--8 are exported here,
together with the coordinate form of Definition 9 and the concrete
replacement-chain/termination argument of Lemma 10.  The final proposition
`IrreducibleReplacementStatement` is the composition boundary for the full
source theorem.  Its first premise is the genuine, all-dimensional CFP
corollary; it does not use `HasCFPStructure` or a selector on all finite sets.
-/

namespace Erdos186.PZ.Reduction

open Erdos186.Irreducible

noncomputable section

/-! ## Source-labelled finite estimates -/

/-- **Pham--Zakharov Lemma 6, exact integer form.** -/
theorem phamZakharov_lemma6
    {d s D k loss q : ℕ} {A : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss) (Q : GAP d q)
    (hcore : insert 0 W.core ⊆ Q.carrier) (hrank : q ≤ W.rank) :
    k ^ (W.rank - q) * W.progression.volume ≤
      2 ^ W.rank * (2 * W.scaleDen) ^ q * Q.volume :=
  Estimates.cfpWitness_dimensionIncrease W Q hcore hrank

/-- **Pham--Zakharov Lemma 7, exact certificate consequences.**  The
geometric theorem is used solely through the supplied finite certificate. -/
theorem phamZakharov_lemma7
    {d q factor : ℕ} {points : Finset (LatticePoint d)}
    (C : DiscreteJohn.Certificate points q factor) :
    C.inner.Proper ∧ C.outer.Proper ∧
      C.outer.volume ≤ (2 * factor + 1) ^ q * C.inner.volume ∧
      C.outer.carrier.card ≤ (2 * factor + 1) ^ q * points.card :=
  ⟨C.inner_proper, C.outer_proper, C.outer_volume_le, C.card_outer_le⟩

/-- **Pham--Zakharov Lemma 8, exact certificate form.** -/
theorem phamZakharov_lemma8
    {d s D k loss q factor : ℕ}
    {A points : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness A s D k loss)
    (C : DiscreteJohn.Certificate points q factor)
    (hcore : insert 0 W.core ⊆ C.outer.carrier)
    (hrank : q ≤ W.rank) :
    W.progression.volume ≤
      2 ^ W.rank * (2 * W.scaleDen) ^ q *
        ((2 * factor + 1) ^ q * points.card) :=
  Estimates.cfpWitness_noDimensionIncrease_discreteJohn W C hcore hrank

/-- **Pham--Zakharov Lemma 8 for an actual coordinate replacement.**  This
form uses the proved residue-fibre cancellation and therefore needs neither
a John certificate nor a comparison of the two selected ranks. -/
theorem phamZakharov_lemma8_coordinate
    {β η : ℝ} {C : HigherDimensionalContext β η}
    {selector : BoundedCFPSelector C} {d : ℕ}
    {A : Finset (LatticePoint d)} {hA : selector.Eligible A} {δ γ : ℝ}
    (F : BoundedIrreducibilityFailure selector A hA δ γ) :
    let current := selector.chosen A hA
    let next := selector.chosen F.nextPoints F.shifted_eligible
    next.progression.volume ≤
      2 ^ next.dimension *
        ((2 * next.witness.scaleDen + 1) ^ current.dimension *
          (2 ^ current.dimension * current.progression.volume)) := by
  exact F.noDimensionIncrease

/-- **Pham--Zakharov Lemma 8 at the normalized initial box.**  Translation
of the original box costs no cardinality, and the residue-fibre argument
requires no comparison between the selected rank and the ambient rank. -/
theorem phamZakharov_lemma8_initial
    {d s D k loss : ℕ} (B : CFP.IntegerBox d)
    {A : Finset (LatticePoint d)} (hA : A.Nonempty)
    (hAB : A ⊆ B.carrier)
    (W : CFP.EnhancedCFPWitness (normalizeSet B A) s D k loss) :
    W.progression.volume ≤
      2 ^ W.rank *
        ((2 * W.scaleDen + 1) ^ d * (2 ^ d * B.carrier.card)) :=
  initial_noDimensionIncrease B hA hAB W

/-! ## Exact terminal-state mechanism in Lemma 10 -/

/-- A concrete replacement exists from `S` to `T`. -/
def HasReplacement (p : MoveParameters)
    (S T : ReplacementState) : Prop :=
  Nonempty (ReplacementStep p S T)

/-- A state is terminal when no concrete replacement step leaves it. -/
def IsReplacementTerminal (p : MoveParameters)
    (S : ReplacementState) : Prop :=
  ∀ T, ¬ HasReplacement p S T

/-- Forget a relation trace of actual replacement steps to a concrete
replacement chain. -/
def replacementChainOfTrace {p : MoveParameters} {initial : ReplacementState}
    {length : ℕ}
    (T : RelationTrace (HasReplacement p) initial length) :
    ReplacementChain p length where
  state := T.state
  step i hi := Classical.choice (T.valid i hi)

/-- The abstract maximal-chain step in Lemma 10: a common finite bound for
all concrete chains forces a reachable terminal replacement state. -/
theorem exists_terminalReplacement_of_chain_bound
    (p : MoveParameters) (initial : ReplacementState) (bound : ℕ)
    (chain_bound : ∀ {length : ℕ} (C : ReplacementChain p length),
      C.state 0 = initial → length ≤ bound) :
    ∃ S, Relation.ReflTransGen (HasReplacement p) initial S ∧
      IsReplacementTerminal p S := by
  apply exists_reachable_terminal_of_trace_bound
    (HasReplacement p) (IsReplacementTerminal p) initial bound
  · intro S _hreach hnonterminal
    simp only [IsReplacementTerminal] at hnonterminal
    push Not at hnonterminal
    exact hnonterminal
  · intro length T
    apply chain_bound (replacementChainOfTrace T)
    exact T.state_zero

/-- **Pham--Zakharov Lemma 10, finite bookkeeping and termination form.**

If all replacement chains have bounded total upward rank jump and the
available shrink budget would force the next GAP below volume one, an actual
terminal state is reachable.  Every reachable state retains nonaveraging,
and each concrete chain satisfies the population and GAP product estimates
proved in `Replacement`. -/
theorem phamZakharov_lemma10_terminal
    (p : MoveParameters) (initial : ReplacementState)
    (jumpBound shrinkBound : ℕ)
    (hjump : ∀ {length : ℕ} (C : ReplacementChain p length),
      C.state 0 = initial →
        upwardJump C.toMoveTrace length ≤ jumpBound)
    (hbudget :
      p.cost ^ (initial.rank + 2 * jumpBound) *
          p.shrinkFactor ^ (shrinkBound + 1) *
            (initial.progression.volume : ℝ) < 1) :
    ∃ S, Relation.ReflTransGen (HasReplacement p) initial S ∧
      IsReplacementTerminal p S := by
  apply exists_terminalReplacement_of_chain_bound p initial
    (initial.rank + 2 * jumpBound + shrinkBound)
  intro length C hC0
  have hj := hjump C hC0
  have hrank : (C.state 0).rank = initial.rank :=
    congrArg ReplacementState.rank hC0
  have hvolume : (C.state 0).progression.volume =
      initial.progression.volume :=
    congrArg (fun S : ReplacementState ↦ S.progression.volume) hC0
  have hb :
      p.cost ^ ((C.state 0).rank + 2 * jumpBound) *
          p.shrinkFactor ^ (shrinkBound + 1) *
            ((C.state 0).progression.volume : ℝ) < 1 := by
    calc
      p.cost ^ ((C.state 0).rank + 2 * jumpBound) *
            p.shrinkFactor ^ (shrinkBound + 1) *
              ((C.state 0).progression.volume : ℝ)
          = p.cost ^ (initial.rank + 2 * jumpBound) *
              p.shrinkFactor ^ (shrinkBound + 1) *
                (initial.progression.volume : ℝ) := by
            rw [hvolume]
            exact congrArg
              (fun n : ℕ ↦ p.cost ^ (n + 2 * jumpBound) *
                p.shrinkFactor ^ (shrinkBound + 1) *
                  (initial.progression.volume : ℝ)) hrank
      _ < 1 := hbudget
  have hlength := C.length_le_of_upwardJump_and_budget hj hb
  calc
    length ≤ (C.state 0).rank + 2 * jumpBound + shrinkBound := hlength
    _ = initial.rank + 2 * jumpBound + shrinkBound :=
      congrArg (fun n : ℕ ↦ n + 2 * jumpBound + shrinkBound) hrank

/-! ## Exact composition boundary for the source form of Lemma 10 -/

/-- The data returned by the irreducible-replacement lemma, including all
three rank cases in the source. -/
structure IrreducibleReplacementResult {β η : ℝ}
    {C : HigherDimensionalContext β η}
    (selector : BoundedCFPSelector C) {ℓ : ℕ}
    (B : CFP.IntegerBox ℓ) (A : Finset (LatticePoint ℓ))
    (hA : selector.Eligible (normalizeSet B A)) (ε δ γ : ℝ) (K : ℕ)
    (constant : ℝ) where
  ambientDimension : ℕ
  points : Finset (LatticePoint ambientDimension)
  eligible : selector.Eligible points
  selector_strong_scale : selector.UsesScaleExponent (1 - ε)
  selector_candidate_closed : selector.CandidateClosedAt points eligible δ
  normalized_input_nonaveraging : IsBoxNonaveraging (normalizeSet B A)
  input_card_preserved : (normalizeSet B A).card = A.card
  reachable :
    Relation.ReflTransGen (CoordinateReplacement selector δ γ)
      ⟨ℓ, normalizeSet B A, hA⟩ ⟨ambientDimension, points, eligible⟩
  nonaveraging : IsBoxNonaveraging points
  core_half : (1 / 2 : ℝ) * (points.card : ℝ) ≤
    ((selector.chosen points eligible).identifiedCore.card : ℝ)
  irreducible : IsBoundedCoordinateIrreducible selector points eligible δ γ
  population_large : Real.rpow (A.card : ℝ) (1 - ε) < (points.card : ℝ)
  high_rank_bound :
    ℓ < (selector.chosen points eligible).dimension →
      ((selector.chosen points eligible).progression.volume : ℝ) ≤
        constant * Real.rpow (A.card : ℝ)
          (-(1 - ε) *
            ((selector.chosen points eligible).dimension - ℓ : ℝ)) *
          (B.carrier.card : ℝ)
  equal_rank_bound :
    (selector.chosen points eligible).dimension = ℓ →
      ((selector.chosen points eligible).progression.volume : ℝ) ≤
        constant * ((points.card : ℝ) / (A.card : ℝ)) ^ K *
          (B.carrier.card : ℝ)
  low_rank_bound :
    (selector.chosen points eligible).dimension < ℓ →
      ((selector.chosen points eligible).progression.volume : ℝ) ≤
        constant * (B.carrier.card : ℝ)

/-- Package a quantitative terminal coordinate state into the exact
Lemma-10 result.  Normalization cardinality and nonaveraging transport are
discharged here, leaving the controlled-trace argument responsible only for
reachability, terminal irreducibility, local candidate closure, population,
and the three numerical rank cases. -/
theorem irreducibleReplacementResult_of_terminal {β η : ℝ}
    {C : HigherDimensionalContext β η}
    {selector : BoundedCFPSelector C} {ℓ : ℕ}
    {B : CFP.IntegerBox ℓ} {A : Finset (LatticePoint ℓ)}
    {hA : selector.Eligible (normalizeSet B A)}
    {ε δ γ : ℝ} {K : ℕ} {constant : ℝ}
    (hstrong : selector.UsesScaleExponent (1 - ε))
    (hNA : IsBoxNonaveraging A)
    (S : CoordinateReplacementState selector)
    (hreach : Relation.ReflTransGen (CoordinateReplacement selector δ γ)
      ⟨ℓ, normalizeSet B A, hA⟩ S)
    (hirr : S.Irreducible δ γ)
    (hclosed : selector.CandidateClosedAt S.points S.eligible δ)
    (hcoreHalf : (1 / 2 : ℝ) * (S.points.card : ℝ) ≤
      (S.selected.identifiedCore.card : ℝ))
    (hpopulation : Real.rpow (A.card : ℝ) (1 - ε) <
      (S.points.card : ℝ))
    (hhigh : ℓ < S.selected.dimension →
      (S.selected.progression.volume : ℝ) ≤
        constant * Real.rpow (A.card : ℝ)
          (-(1 - ε) * (S.selected.dimension - ℓ : ℝ)) *
            (B.carrier.card : ℝ))
    (hequal : S.selected.dimension = ℓ →
      (S.selected.progression.volume : ℝ) ≤
        constant * ((S.points.card : ℝ) / (A.card : ℝ)) ^ K *
          (B.carrier.card : ℝ))
    (hlow : S.selected.dimension < ℓ →
      (S.selected.progression.volume : ℝ) ≤
        constant * (B.carrier.card : ℝ)) :
    Nonempty (IrreducibleReplacementResult selector B A hA
      ε δ γ K constant) := by
  refine ⟨{
    ambientDimension := S.ambientDimension
    points := S.points
    eligible := S.eligible
    selector_strong_scale := hstrong
    selector_candidate_closed := hclosed
    normalized_input_nonaveraging := isBoxNonaveraging_normalizeSet B hNA
    input_card_preserved := card_normalizeSet B A
    reachable := hreach
    nonaveraging := nonaveraging_of_coordinateReachable hreach
      (isBoxNonaveraging_normalizeSet B hNA)
    core_half := hcoreHalf
    irreducible := hirr
    population_large := hpopulation
    high_rank_bound := hhigh
    equal_rank_bound := hequal
    low_rank_bound := hlow }⟩

namespace IrreducibleReplacementResult

/-- The three source rank cases always imply a coarser polynomial volume
bound.  This is the exact invariant consumed by the terminal candidate-box
absorption argument. -/
theorem volume_le_coarse {β η β₀ : ℝ}
    {C : HigherDimensionalContext β η}
    {selector : BoundedCFPSelector C} {ℓ : ℕ}
    {B : CFP.IntegerBox ℓ} {A : Finset (LatticePoint ℓ)}
    {hA : selector.Eligible (normalizeSet B A)}
    {ε δ γ : ℝ} {K : ℕ} {constant : ℝ}
    (R : IrreducibleReplacementResult selector B A hA
      ε δ γ K constant)
    (hconstant : 0 ≤ constant) (hε : ε ≤ 1)
    (hcardA : 1 ≤ A.card)
    (hbox : (B.carrier.card : ℝ) ≤ Real.rpow (A.card : ℝ) β₀) :
    ((selector.chosen R.points R.eligible).progression.volume : ℝ) ≤
      constant * Real.rpow (A.card : ℝ) β₀ := by
  have hpoints : R.points.card ≤ A.card := by
    have h := card_le_of_coordinateReachable R.reachable
    simpa using h
  have hmone : (1 : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hcardA
  have hmpos : (0 : ℝ) < (A.card : ℝ) := zero_lt_one.trans_le hmone
  let rank := (selector.chosen R.points R.eligible).dimension
  rcases lt_trichotomy rank ℓ with hlow | hequal | hhigh
  · calc
      ((selector.chosen R.points R.eligible).progression.volume : ℝ) ≤
          constant * (B.carrier.card : ℝ) := R.low_rank_bound hlow
      _ ≤ constant * Real.rpow (A.card : ℝ) β₀ :=
        mul_le_mul_of_nonneg_left hbox hconstant
  · have hratio0 : 0 ≤ (R.points.card : ℝ) / (A.card : ℝ) := by positivity
    have hratio1 : (R.points.card : ℝ) / (A.card : ℝ) ≤ 1 := by
      apply (div_le_one hmpos).2
      exact_mod_cast hpoints
    have hpow : ((R.points.card : ℝ) / (A.card : ℝ)) ^ K ≤ 1 :=
      pow_le_one₀ hratio0 hratio1
    calc
      ((selector.chosen R.points R.eligible).progression.volume : ℝ) ≤
          constant * ((R.points.card : ℝ) / (A.card : ℝ)) ^ K *
            (B.carrier.card : ℝ) := R.equal_rank_bound hequal
      _ ≤ constant * 1 * (B.carrier.card : ℝ) := by gcongr
      _ = constant * (B.carrier.card : ℝ) := by ring
      _ ≤ constant * Real.rpow (A.card : ℝ) β₀ :=
        mul_le_mul_of_nonneg_left hbox hconstant
  · have hrankNat : ℓ ≤
        (selector.chosen R.points R.eligible).dimension :=
      Nat.le_of_lt hhigh
    have hjump : (0 : ℝ) ≤
        ((selector.chosen R.points R.eligible).dimension : ℝ) - (ℓ : ℝ) :=
      sub_nonneg.mpr (by exact_mod_cast hrankNat)
    have honeMinus : 0 ≤ 1 - ε := sub_nonneg.mpr hε
    have hexponent : -(1 - ε) *
        (((selector.chosen R.points R.eligible).dimension : ℝ) - (ℓ : ℝ)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr honeMinus) hjump
    have hrpow : Real.rpow (A.card : ℝ)
        (-(1 - ε) *
          (((selector.chosen R.points R.eligible).dimension : ℝ) - (ℓ : ℝ))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hmone hexponent
    calc
      ((selector.chosen R.points R.eligible).progression.volume : ℝ) ≤
          constant * Real.rpow (A.card : ℝ)
            (-(1 - ε) *
              (((selector.chosen R.points R.eligible).dimension : ℝ) - (ℓ : ℝ))) *
              (B.carrier.card : ℝ) := R.high_rank_bound hhigh
      _ ≤ constant * 1 * (B.carrier.card : ℝ) := by gcongr
      _ = constant * (B.carrier.card : ℝ) := by ring
      _ ≤ constant * Real.rpow (A.card : ℝ) β₀ :=
        mul_le_mul_of_nonneg_left hbox hconstant

end IrreducibleReplacementResult

/-- The exact all-input composition target corresponding to Pham--Zakharov
Lemma 10.  It is deliberately a proposition: the premise is the genuine CFP
corollary, and all structure selection is restricted to analytically eligible
sets through a run-specific `BoundedCFPSelector`.  The returned selector must
use the source scale `|A|^(1-epsilon)` throughout the run, and its domain must
be closed under every dense coordinate candidate at the terminal set.  Thus
the irreducibility conclusion cannot be made vacuous by omitting one of its
candidates from the analytic domain.

`K0` and `constant` are uniform in the input box and set. -/
def IrreducibleReplacementStatement : Prop :=
  CFP.NonemptyHigherDimensionalCorollary5 →
  ∀ (ℓ : ℕ) (β η : ℝ),
    1 < β → 0 < η → η < 1 →
    ∃ C : HigherDimensionalContext (2 * (β + 1)) η,
    ∀ ε : ℝ, 0 < ε → ε < (1 / 3 : ℝ) →
    ∃ K0 : ℕ, 1 ≤ K0 ∧
    ∃ constant : ℝ, 0 < constant ∧
      ∀ δ γ : ℝ, 0 < δ → δ < 1 → 0 < γ →
      ∀ K : ℕ, K0 ≤ K → γ ≤ δ ^ K →
        ∃ threshold : ℕ, 2 ≤ threshold ∧
        ∀ (B : CFP.IntegerBox ℓ)
          (A : Finset (LatticePoint ℓ)),
          threshold ≤ A.card → A ⊆ B.carrier →
          (B.carrier.card : ℝ) ≤ Real.rpow (A.card : ℝ) β →
          IsBoxNonaveraging A →
          Real.rpow (A.card : ℝ) (-(1 / 3 : ℝ)) ≤ γ →
          ∃ selector : BoundedCFPSelector C,
          ∃ hnorm : selector.Eligible (normalizeSet B A),
            Nonempty (IrreducibleReplacementResult selector B A hnorm
              ε δ γ K constant)

end

end Erdos186.PZ.Reduction
