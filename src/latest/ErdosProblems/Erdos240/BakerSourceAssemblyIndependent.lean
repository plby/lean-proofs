/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerInduction
import ErdosProblems.Erdos240.BakerAdmissibleParameters
import ErdosProblems.Erdos240.BakerInitialMatrixHeight
import ErdosProblems.Erdos240.BakerLemma2Concrete
import ErdosProblems.Erdos240.BakerSourceHeightAbsorptionCore
import ErdosProblems.Erdos240.BakerTerminalInstantiation
import ErdosProblems.Erdos240.RationalPrimeBaker
import ErdosProblems.Erdos240.ShiftedZeroCount

/-!
# Independent assembly of the rational-logarithm Baker argument

This file contains a logical assembly skeleton which is independent of the
numerical estimates in van der Poorten--Loxton.  It makes the remaining
construction obligation explicit rather than postulating the desired
logarithmic lower bound.  It does **not** certify that the current auxiliary
formulas in the surrounding scaffolding are faithful to the paper; those
definitions must be audited and corrected before constructing the certificate
predicate below.

An `ExtrapolationChain` is the source Lemma 6 state machine.  Its state may
change at every level: in the actual proof radical coefficient extraction
replaces the coefficient family by a nonzero residue fibre.  Its four step
fields are precisely the construction boundaries of `BakerInduction.vdpl_lemma6`:
integral extrapolation, interpolation, the Liouville alternative, and radical
descent.  In particular this module does not assert the false literal identity
that the same coefficient vector at level `J` becomes the vector at level
`J+1` merely by scaling the argument.

A `ZeroCountEndpoint` records only the explicit algebraic identification
required at the maximal level.  The already checked shifted-polynomial zero
count forces its nonzero coefficient vector to be zero.  Thus a complete
certificate is contradictory.

The preferred construction target is `HasNormalizedConcreteSourceChains`.
It retains the unabsorbed source height exponent, fixes the state and
functions to the audited concrete definitions, and exposes the exact
Lemmas 3--6 and terminal-equation fields still to be built.  The older generic
certificate interface is retained below only as a compatibility bridge.
-/

open scoped BigOperators Polynomial

noncomputable section

namespace Erdos240.BakerSourceAssemblyIndependent

open Erdos240
open Erdos240.RationalPrimeBaker
open Erdos240.BakerInduction
open Erdos240.BakerSourceState
open Erdos240.BakerFinalZeroCount
open Erdos240.BakerInitialMatrixHeight
open Erdos240.BakerTerminalInstantiation
open Erdos240.BakerSourceHeightAbsorption
open Polynomial

universe u

attribute [local instance] Matrix.seminormedAddCommGroup

/-- The source's state-changing integral/rational extrapolation data.

`State J` contains the coefficient family at level `J`; `Good J x` records
its nontriviality and common height bound.  The first three step fields are
the exact hypotheses used by the checked Lemma 5 transition.  `descend`
performs the genuinely state-changing radical residue extraction. -/
structure ExtrapolationChain {ι : Type u} [Fintype ι] [Nonempty ι]
    (P : VDPLParameters ι) where
  State : ℕ → Type u
  Good : ∀ J, State J → Prop
  F : ∀ J, State J → ℂ → VDPLMultiIndex P.rank → ℂ
  G : ∀ J, State J → ℂ → VDPLMultiIndex P.rank → ℂ
  lower : ∀ J, State J → ℕ → VDPLMultiIndex P.rank → ℝ
  base : State 0
  baseGood : Good 0 base
  baseVanishes : IntegralSeedAtLevel P (G 0 base) 0
  integralStep : ∀ J (x : State J), P.LevelOK J → Good J x →
    IntegralSeedAtLevel P (G J x) J →
    IntegralExtrapolatedAtLevel P (G J x) J
  upperStep : ∀ J (x : State J), P.LevelOK J → Good J x →
    IntegralExtrapolatedAtLevel P (G J x) J →
    RationalInterpolationUpperAtLevel P (F J x) (lower J x) J
  lowerStep : ∀ J (x : State J), P.LevelOK J → Good J x →
    IntegralExtrapolatedAtLevel P (G J x) J →
    RationalLiouvilleAlternativeAtLevel P (F J x) (G J x)
      (lower J x) J
  descend : ∀ J (x : State J), P.LevelOK (J + 1) → Good J x →
    RationalExtrapolatedAtLevel P (G J x) J →
    ∃ y : State (J + 1), Good (J + 1) y ∧
      CoprimeDescentAtLevel P (G (J + 1) y) J
  completeCoprime : ∀ J (x : State (J + 1)), P.LevelOK (J + 1) →
    Good (J + 1) x → CoprimeCompletionAtLevel P (G (J + 1) x) J

namespace ExtrapolationChain

variable {ι : Type u} [Fintype ι] [Nonempty ι]
  {P : VDPLParameters ι} (chain : ExtrapolationChain P)

/-- The checked source Lemma 6 induction produces a good, vanishing state at
every admissible level. -/
theorem vanishesAtLevel (J : ℕ) (hJ : P.LevelOK J) :
    ∃ x : chain.State J, chain.Good J x ∧
      IntegralSeedAtLevel P (chain.G J x) J := by
  exact vdpl_lemma6 P chain.State chain.Good chain.F chain.G chain.lower
    chain.base chain.baseGood chain.baseVanishes chain.integralStep
    chain.upperStep chain.lowerStep chain.descend chain.completeCoprime J hJ

/-- A canonical terminal state selected from the checked induction.  This
lets the zero-count endpoint be tied to the coefficient family actually
produced by radical descent, without pretending those coefficients are
unchanged across levels. -/
noncomputable def stateAtLevel (J : ℕ) (hJ : P.LevelOK J) : chain.State J :=
  Classical.choose (chain.vanishesAtLevel J hJ)

theorem stateAtLevel_good (J : ℕ) (hJ : P.LevelOK J) :
    chain.Good J (chain.stateAtLevel J hJ) :=
  (Classical.choose_spec (chain.vanishesAtLevel J hJ)).1

theorem stateAtLevel_seed (J : ℕ) (hJ : P.LevelOK J) :
    IntegralSeedAtLevel P
      (chain.G J (chain.stateAtLevel J hJ)) J :=
  (Classical.choose_spec (chain.vanishesAtLevel J hJ)).2

end ExtrapolationChain

/-! ## Exact concrete-state assembly -/

/-- The concrete source Lemma-6 data after the coefficient construction has
produced an initial `LevelState`.

Unlike `ExtrapolationChain`, this structure fixes every state and function to
the audited source definitions.  A `LevelState` itself carries nontriviality,
the uniform coefficient-height bound, and the genuine active old and last
side lengths after residue descent.  The terminal identification with source
equation (13) is no longer a field: `ConcreteSourceChain.false` invokes the
checked `false_of_terminal_source` endpoint directly. -/
structure ConcreteSourceChain {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ) where
  last_ne_zero : bLast ≠ 0
  lower : ∀ J, LevelState P J → ℕ → VDPLMultiIndex P.rank → ℝ
  base : LevelState P 0
  baseVanishes : IntegralSeedAtLevel P (g base b bLast) 0
  integralStep : ∀ J (state : LevelState P J), P.LevelOK J →
    IntegralSeedAtLevel P (g state b bLast) J →
    IntegralExtrapolatedAtLevel P (g state b bLast) J
  upperStep : ∀ J (state : LevelState P J), P.LevelOK J →
    IntegralExtrapolatedAtLevel P (g state b bLast) J →
    RationalInterpolationUpperAtLevel P (f state b bLast)
      (lower J state) J
  lowerStep : ∀ J (state : LevelState P J), P.LevelOK J →
    IntegralExtrapolatedAtLevel P (g state b bLast) J →
    RationalLiouvilleAlternativeAtLevel P (f state b bLast)
      (g state b bLast) (lower J state) J
  descend : ∀ J (state : LevelState P J), P.LevelOK (J + 1) →
    RationalExtrapolatedAtLevel P (g state b bLast) J →
    ∃ next : LevelState P (J + 1),
      CoprimeDescentAtLevel P (g next b bLast) J
  completeCoprime : ∀ J (state : LevelState P (J + 1)),
    P.LevelOK (J + 1) → CoprimeCompletionAtLevel P (g state b bLast) J

/-- The source argument after the level-zero Siegel-lemma state has been
constructed.  Keeping this continuation separate records the precise output
still required from Lemmas 3--6, without making any field depend on a chosen
level-zero coefficient vector.  The terminal contradiction is already a
checked consequence of the last integral seed. -/
structure ConcreteSourceContinuation {oldRank : ℕ} [Nonempty (Fin oldRank)]
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ) where
  last_ne_zero : bLast ≠ 0
  lower : ∀ J, LevelState P J → ℕ → VDPLMultiIndex P.rank → ℝ
  integralStep : ∀ J (state : LevelState P J), P.LevelOK J →
    IntegralSeedAtLevel P (g state b bLast) J →
    IntegralExtrapolatedAtLevel P (g state b bLast) J
  upperStep : ∀ J (state : LevelState P J), P.LevelOK J →
    IntegralExtrapolatedAtLevel P (g state b bLast) J →
    RationalInterpolationUpperAtLevel P (f state b bLast)
      (lower J state) J
  lowerStep : ∀ J (state : LevelState P J), P.LevelOK J →
    IntegralExtrapolatedAtLevel P (g state b bLast) J →
    RationalLiouvilleAlternativeAtLevel P (f state b bLast)
      (g state b bLast) (lower J state) J
  descend : ∀ J (state : LevelState P J), P.LevelOK (J + 1) →
    RationalExtrapolatedAtLevel P (g state b bLast) J →
    ∃ next : LevelState P (J + 1),
      CoprimeDescentAtLevel P (g next b bLast) J
  completeCoprime : ∀ J (state : LevelState P (J + 1)),
    P.LevelOK (J + 1) → CoprimeCompletionAtLevel P (g state b bLast) J

namespace ConcreteSourceContinuation

variable {oldRank : ℕ} [Nonempty (Fin oldRank)]
  {P : VDPLParameters (Fin oldRank)} {b : Fin oldRank → ℤ} {bLast : ℤ}

/-- Attach the concrete level-zero state delivered by Lemma 2 to the
source continuation. -/
def withBase (data : ConcreteSourceContinuation P b bLast)
    (base : LevelState P 0)
    (baseVanishes : IntegralSeedAtLevel P (g base b bLast) 0) :
    ConcreteSourceChain P b bLast where
  last_ne_zero := data.last_ne_zero
  lower := data.lower
  base := base
  baseVanishes := baseVanishes
  integralStep := data.integralStep
  upperStep := data.upperStep
  lowerStep := data.lowerStep
  descend := data.descend
  completeCoprime := data.completeCoprime

end ConcreteSourceContinuation

namespace ConcreteSourceChain

variable {oldRank : ℕ} [Nonempty (Fin oldRank)]
  {P : VDPLParameters (Fin oldRank)} {b : Fin oldRank → ℤ} {bLast : ℤ}

/-- Forget only the concrete names, retaining the exact state-changing
induction data consumed by `BakerInduction.vdpl_lemma6`. -/
def toExtrapolationChain (data : ConcreteSourceChain P b bLast) :
    ExtrapolationChain P where
  State := LevelState P
  Good := fun _ _ ↦ True
  F := fun _ state ↦ f state b bLast
  G := fun _ state ↦ g state b bLast
  lower := data.lower
  base := data.base
  baseGood := trivial
  baseVanishes := data.baseVanishes
  integralStep := fun J state hJ _ hseed ↦
    data.integralStep J state hJ hseed
  upperStep := fun J state hJ _ hint ↦
    data.upperStep J state hJ hint
  lowerStep := fun J state hJ _ hint ↦
    data.lowerStep J state hJ hint
  descend := fun J state hnext _ hrat ↦ by
    obtain ⟨next, hseed⟩ := data.descend J state hnext hrat
    exact ⟨next, trivial, hseed⟩
  completeCoprime := fun J state hJ _ ↦
    data.completeCoprime J state hJ

/-- Exact end-to-end contradiction from a concrete Lemma-6 chain.  The
terminal level is the minimal source level above the varying-prime side; it
is still strictly admissible because `q < k^epsilon`. -/
theorem false (data : ConcreteSourceChain P b bLast) : False := by
  obtain ⟨J, hJpos, hterminal, hJ⟩ := P.exists_terminal_level_pos
  obtain ⟨state, _hgood, hseed⟩ :=
    data.toExtrapolationChain.vanishesAtLevel J hJ
  exact false_of_terminal_source state b bLast data.last_ne_zero hJpos
    hterminal hseed

/-- Assemble Lemma 2 with all later source steps.  The two displayed
inequalities are exactly the remaining numerical inputs of the checked
level-zero coefficient constructor.  The continuation must construct the
concrete Lemma-6 steps; the checked terminal endpoint is then automatic for
the state returned there. -/
theorem false_of_initialEstimates
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hreq : Erdos240.BakerLemma2Concrete.initialDimensionRequirement P ∈
      P.kRequirements)
    (hunknown :
      (Fintype.card (Erdos240.BakerAuxiliary.LambdaBox
        (Erdos240.BakerLemma2Concrete.initialBoxShape P)) : ℝ) ≤
        Real.exp ((1 / 6 : ℝ) * P.h * P.k * P.Omega *
          Real.log P.OmegaOld))
    (hmatrix :
      ‖(Erdos240.BakerLemma2Concrete.initialIntegralConstraintModel P b bLast
          (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ)).matrix‖ ≤
        Real.exp ((1 / 6 : ℝ) * P.h * P.k * P.Omega *
          Real.log P.OmegaOld))
    (build : ∀ state : LevelState P 0,
      IntegralSeedAtLevel P (g state b bLast) 0 →
        ConcreteSourceChain P b bLast) : False := by
  obtain ⟨state, hvanish⟩ :=
    Erdos240.BakerLemma2Concrete.exists_initial_levelState_vanishes
      P b bLast hreq hunknown hmatrix
  have hseed : IntegralSeedAtLevel P (g state b bLast) 0 := by
    simpa only [IntegralSeedAtLevel,
      Erdos240.BakerLemma2Concrete.initialRadius_eq,
      Erdos240.BakerLemma2Concrete.initialBudget_eq] using hvanish
  exact (build state hseed).false

/-- Version in which both level-zero counting estimates come directly from
the two explicit admissibility-ledger entries.  Only the literal integral
matrix-height estimate and the later source steps remain as inputs. -/
theorem false_of_initialRequirements
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hdimension : Erdos240.BakerLemma2Concrete.initialDimensionRequirement P ∈
      P.kRequirements)
    (hunknown : Erdos240.BakerLemma2Concrete.initialUnknownRequirement P ∈
      P.kRequirements)
    (hmatrix :
      ‖(Erdos240.BakerLemma2Concrete.initialIntegralConstraintModel P b bLast
          (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ)).matrix‖ ≤
        Real.exp ((1 / 6 : ℝ) * P.h * P.k * P.Omega *
          Real.log P.OmegaOld))
    (build : ∀ state : LevelState P 0,
      IntegralSeedAtLevel P (g state b bLast) 0 →
        ConcreteSourceChain P b bLast) : False := by
  apply false_of_initialEstimates P b bLast hdimension
  · exact Erdos240.BakerLemma2Concrete.initial_unknownCount_le_exp_heightScale
      P hunknown
  · exact hmatrix
  · exact build

/-- Source-faithful level-zero wrapper around the raw Siegel endpoint.  The
matrix is allowed the printed `exp (2H)` height; the factor-eight dimension
margin and the column-count ledger are used internally to recover the final
`exp (H/3)` coefficient-height bound carried by `LevelState`. -/
theorem exists_initial_levelState_vanishes_sourceHeight
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hdimension : Erdos240.BakerLemma2Concrete.initialDimensionRequirement P ∈
      P.kRequirements)
    (hunknown : Erdos240.BakerLemma2Concrete.initialUnknownRequirement P ∈
      P.kRequirements)
    (hmatrix :
      ‖(Erdos240.BakerLemma2Concrete.initialIntegralConstraintModel P b bLast
          (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ)).matrix‖ ≤
        Real.exp (2 * ((P.h : ℝ) * P.k * P.Omega *
          Real.log P.OmegaOld))) :
    ∃ state : LevelState P 0,
      VanishesOn (g state b bLast) 1
        (Erdos240.BakerLemma2Concrete.initialRadius P)
        (Erdos240.BakerLemma2Concrete.initialBudget P) := by
  obtain ⟨c, hc, hequations, hheight⟩ :=
    Erdos240.BakerLemma2Concrete.exists_initial_auxiliary_coefficients_sourceHeight
      P b bLast (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ)
      hdimension hunknown hmatrix
  have hpointwise : ∀ lambda, |(c lambda : ℝ)| ≤ P.coeffHeight := by
    intro lambda
    have hcomponent := (norm_le_pi_norm c lambda).trans hheight
    simpa only [Int.norm_eq_abs, Int.cast_abs, Int.cast_natCast] using
      hcomponent
  let state : LevelState P 0 :=
    LevelState.ofCoefficients c hc hpointwise
  refine ⟨state, ?_⟩
  apply levelZero_vanishes_of_auxiliaryEquations P state b bLast
  simpa only [state, LevelState.ofCoefficients] using hequations

/-- Source-faithful Lemma-2-to-continuation assembly using the raw-Siegel
matrix height `exp (2H)`. -/
theorem false_of_initialSourceHeightRequirements
    (P : VDPLParameters (Fin oldRank))
    (b : Fin oldRank → ℤ) (bLast : ℤ)
    (hdimension : Erdos240.BakerLemma2Concrete.initialDimensionRequirement P ∈
      P.kRequirements)
    (hunknown : Erdos240.BakerLemma2Concrete.initialUnknownRequirement P ∈
      P.kRequirements)
    (hmatrix :
      ‖(Erdos240.BakerLemma2Concrete.initialIntegralConstraintModel P b bLast
          (fun r ↦ (P.old r : ℤ)) (P.newPrime : ℤ)).matrix‖ ≤
        Real.exp (2 * ((P.h : ℝ) * P.k * P.Omega *
          Real.log P.OmegaOld)))
    (continuation : ConcreteSourceContinuation P b bLast) : False := by
  obtain ⟨state, hvanish⟩ :=
    exists_initial_levelState_vanishes_sourceHeight P b bLast hdimension
      hunknown hmatrix
  have hseed : IntegralSeedAtLevel P (g state b bLast) 0 := by
    simpa only [IntegralSeedAtLevel,
      Erdos240.BakerLemma2Concrete.initialRadius_eq,
      Erdos240.BakerLemma2Concrete.initialBudget_eq] using hvanish
  exact (continuation.withBase state hseed).false

end ConcreteSourceChain

/-- The exact algebraic endpoint needed for the final zero-count argument.

Each Hasse derivative of the shifted-polynomial combination is identified
with a value of the last-level auxiliary function.  The terminal level is
admissible for Lemma 6 and explicitly lies beyond `LlastZeroScale`, so the
last exponential side has become zero.  The node and derivative bounds put
the identified value inside `vanishesAtLevel`. -/
structure ZeroCountEndpoint {ι : Type u} [Fintype ι] [Nonempty ι]
    {P : VDPLParameters ι} (chain : ExtrapolationChain P)
    (κ : Type u) [Fintype κ] where
  level : ℕ
  levelOK : P.LevelOK level
  lastSideScale_lt_qpow :
    P.LlastZeroScale < ((P.q ^ level : ℕ) : ℝ)
  polynomial : ℂ[X]
  degree : ℕ
  split : ℕ
  degree_pos : 0 < degree
  polynomial_degree : polynomial.natDegree = degree
  split_le : split ≤ degree
  coefficient : Fin (split + 1) ⊕ Fin (degree - split) → ℂ
  coefficient_ne_zero : coefficient ≠ 0
  node : κ → ℕ
  node_injective : Function.Injective node
  node_pos : ∀ i, 0 < node i
  node_le_radius : ∀ i, node i ≤ P.R level
  multiplicity : κ → ℕ
  count : degree < ∑ i, multiplicity i
  derivativeIndex : ∀ i, Fin (multiplicity i) → VDPLMultiIndex P.rank
  derivativeWeight : ∀ i k,
    VDPLMultiIndex.weight (derivativeIndex i k) ≤ P.Slevel level
  identify : ∀ i (k : ℕ) (hk : k < multiplicity i),
    (hasseDeriv k
        (shiftedPolynomialCombination polynomial degree split coefficient)).eval
          (node i : ℂ) =
      chain.G level (chain.stateAtLevel level levelOK) (node i : ℂ)
        (derivativeIndex i ⟨k, hk⟩)

namespace ZeroCountEndpoint

variable {ι : Type u} [Fintype ι] [Nonempty ι]
  {P : VDPLParameters ι} {chain : ExtrapolationChain P}
  {κ : Type u} [Fintype κ]

/-- A completed source endpoint is impossible: final vanishing and the
checked Lemma 7 zero count contradict the nonzero auxiliary coefficients. -/
theorem false (endpoint : ZeroCountEndpoint chain κ) : False := by
  have hnode : Function.Injective (fun i : κ ↦ (endpoint.node i : ℂ)) := by
    intro i j hij
    apply endpoint.node_injective
    have hijReal := congrArg Complex.re hij
    simp at hijReal
    exact_mod_cast hijReal
  have hzero : ∀ i k, k < endpoint.multiplicity i →
      (hasseDeriv k
        (shiftedPolynomialCombination endpoint.polynomial endpoint.degree
          endpoint.split endpoint.coefficient)).eval
            (endpoint.node i : ℂ) = 0 := by
    intro i k hk
    rw [endpoint.identify i k hk]
    have hv := chain.stateAtLevel_seed endpoint.level endpoint.levelOK
      (endpoint.node i) (endpoint.node_pos i) (endpoint.node_le_radius i)
      (endpoint.derivativeIndex i ⟨k, hk⟩)
      (endpoint.derivativeWeight i ⟨k, hk⟩)
    simpa only [Nat.cast_one, div_one] using hv
  have hcoeff : endpoint.coefficient = 0 :=
    shiftedPolynomialCombination_eq_zero_coefficients_of_hasseDeriv
      endpoint.polynomial endpoint.degree_pos endpoint.polynomial_degree
      endpoint.split_le (fun i ↦ (endpoint.node i : ℂ)) endpoint.multiplicity
      hnode endpoint.coefficient endpoint.count hzero
  exact endpoint.coefficient_ne_zero hcoeff

end ZeroCountEndpoint

/-- A complete source certificate packages an extrapolation chain and its
maximal-level zero-count endpoint.  This is an ordinary proposition. -/
def VDPLContradictionCertificate {ι : Type u} [Fintype ι] [Nonempty ι]
    (P : VDPLParameters ι) : Prop :=
  ∃ (chain : ExtrapolationChain P) (κ : Type u) (_inst : Fintype κ),
    Nonempty (@ZeroCountEndpoint ι _ _ P chain κ _inst)

/-- Every complete source certificate gives an actual contradiction. -/
theorem VDPLContradictionCertificate.false
    {ι : Type u} [Fintype ι] [Nonempty ι] {P : VDPLParameters ι}
    (certificate : VDPLContradictionCertificate P) : False := by
  rcases certificate with ⟨chain, κ, inst, ⟨endpoint⟩⟩
  let : Fintype κ := inst
  exact endpoint.false

/-- The raw rational-prime data before installing the source's finite lower
bound ledger for `k`. -/
private def rawSourceParameters {ι : Type u} [Fintype ι]
    (old : ι → ℕ) (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old)
    (newPrime : ℕ) (newPrimePrime : newPrime.Prime)
    (newFresh : ∀ i, old i ≠ newPrime)
    (N : ℕ) (Nlarge : Real.exp 2 ≤ (N : ℝ)) : VDPLParameters ι where
  old := old
  old_prime := oldPrime
  old_injective := oldInjective
  newPrime := newPrime
  new_prime := newPrimePrime
  new_fresh := newFresh
  Bsrc := N
  Bsrc_lower := Nlarge
  kRequirements := ∅

/-- The first fixed rank-only requirement beyond source equation (1): the
cube bound for the Lemma 2 row/column dimension count. -/
def sourceInitialDimensionRequirement {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) : ℝ :=
  (2048 * (16 * P.rank : ℝ) ^ P.rank) ^ (3 : ℕ)

/-- Rank-only ledger entry absorbing the level-zero column count into one
sixth of the source coefficient-height exponent. -/
def sourceInitialUnknownRequirement {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) : ℝ :=
  144 * (P.rank + 2 : ℝ) ^ (2 : ℕ)

private def sourceExtraRequirements {ι : Type u} [Fintype ι]
    (P : VDPLParameters ι) : Finset ℝ :=
  {sourceInitialDimensionRequirement P, sourceInitialUnknownRequirement P}

/-- Package the concrete rational-prime input with all three requirements
from source equation (1) and the two fixed Lemma 2 dimension/column-count
requirements installed before any derived parameter is formed.  Every extra
entry is rank-only, hence the chosen `k` is uniform in the varying prime,
coefficients, cutoff, and prime values. -/
def sourceParameters {ι : Type u} [Fintype ι]
    (old : ι → ℕ) (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old)
    (newPrime : ℕ) (newPrimePrime : newPrime.Prime)
    (newFresh : ∀ i, old i ≠ newPrime)
    (N : ℕ) (Nlarge : Real.exp 2 ≤ (N : ℝ)) : VDPLParameters ι :=
  let P := rawSourceParameters old oldPrime oldInjective newPrime newPrimePrime
    newFresh N Nlarge
  P.withSourceRequirements (sourceExtraRequirements P)

/-- The chosen source parameter `k` depends only on the cardinality of the
old index type.  In particular it is independent of every old prime value,
the varying prime, and the coefficient cutoff. -/
theorem sourceParameters_k_eq {ι : Type u} [Fintype ι]
    (old₁ : ι → ℕ) (oldPrime₁ : ∀ i, (old₁ i).Prime)
    (oldInjective₁ : Function.Injective old₁)
    (newPrime₁ : ℕ) (newPrimePrime₁ : newPrime₁.Prime)
    (newFresh₁ : ∀ i, old₁ i ≠ newPrime₁)
    (N₁ : ℕ) (Nlarge₁ : Real.exp 2 ≤ (N₁ : ℝ))
    (old₂ : ι → ℕ) (oldPrime₂ : ∀ i, (old₂ i).Prime)
    (oldInjective₂ : Function.Injective old₂)
    (newPrime₂ : ℕ) (newPrimePrime₂ : newPrime₂.Prime)
    (newFresh₂ : ∀ i, old₂ i ≠ newPrime₂)
    (N₂ : ℕ) (Nlarge₂ : Real.exp 2 ≤ (N₂ : ℝ)) :
    (sourceParameters old₁ oldPrime₁ oldInjective₁ newPrime₁ newPrimePrime₁
        newFresh₁ N₁ Nlarge₁).k =
      (sourceParameters old₂ oldPrime₂ oldInjective₂ newPrime₂ newPrimePrime₂
        newFresh₂ N₂ Nlarge₂).k := by
  rfl

/-- The source constant `C = k^(1+mu)` is uniform for the same reason. -/
theorem sourceParameters_C_eq {ι : Type u} [Fintype ι]
    (old₁ : ι → ℕ) (oldPrime₁ : ∀ i, (old₁ i).Prime)
    (oldInjective₁ : Function.Injective old₁)
    (newPrime₁ : ℕ) (newPrimePrime₁ : newPrime₁.Prime)
    (newFresh₁ : ∀ i, old₁ i ≠ newPrime₁)
    (N₁ : ℕ) (Nlarge₁ : Real.exp 2 ≤ (N₁ : ℝ))
    (old₂ : ι → ℕ) (oldPrime₂ : ∀ i, (old₂ i).Prime)
    (oldInjective₂ : Function.Injective old₂)
    (newPrime₂ : ℕ) (newPrimePrime₂ : newPrime₂.Prime)
    (newFresh₂ : ∀ i, old₂ i ≠ newPrime₂)
    (N₂ : ℕ) (Nlarge₂ : Real.exp 2 ≤ (N₂ : ℝ)) :
    (sourceParameters old₁ oldPrime₁ oldInjective₁ newPrime₁ newPrimePrime₁
        newFresh₁ N₁ Nlarge₁).C =
      (sourceParameters old₂ oldPrime₂ oldInjective₂ newPrime₂ newPrimePrime₂
        newFresh₂ N₂ Nlarge₂).C := by
  unfold VDPLParameters.C
  rw [sourceParameters_k_eq old₁ oldPrime₁ oldInjective₁ newPrime₁
    newPrimePrime₁ newFresh₁ N₁ Nlarge₁ old₂ oldPrime₂ oldInjective₂
    newPrime₂ newPrimePrime₂ newFresh₂ N₂ Nlarge₂]
  rfl

/-- The normalized source constant can be chosen before the varying prime
and coefficient cutoff.  We select one harmless reference prime beyond the
finite old family and one reference cutoff above `exp 2`; the preceding
rank-only invariance theorem then identifies its `C` with every actual
source parameter. -/
theorem exists_uniform_sourceConstant {ι : Type u} [Fintype ι]
    (old : ι → ℕ) (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (newPrime : ℕ) (newPrimePrime : newPrime.Prime)
        (newFresh : ∀ i, old i ≠ newPrime)
        (N : ℕ) (Nlarge : Real.exp 2 ≤ (N : ℝ)),
        (sourceParameters old oldPrime oldInjective newPrime newPrimePrime
          newFresh N Nlarge).C = C₀ := by
  classical
  let oldMax : ℕ := Finset.univ.sup old
  obtain ⟨referencePrime, hreferencePrime, referencePrime_prime⟩ :=
    Nat.exists_infinite_primes (oldMax + 1)
  have referencePrime_fresh : ∀ i, old i ≠ referencePrime := by
    intro i
    have holdMax : old i ≤ oldMax := by
      exact Finset.le_sup (f := old) (Finset.mem_univ i)
    have holdLt : old i < referencePrime := by omega
    exact ne_of_lt holdLt
  let referenceBound : ℕ := ⌈Real.exp 2⌉₊
  have referenceBound_large : Real.exp 2 ≤ (referenceBound : ℝ) := by
    exact Nat.le_ceil (Real.exp 2)
  let referenceParameters := sourceParameters old oldPrime oldInjective
    referencePrime referencePrime_prime referencePrime_fresh referenceBound
      referenceBound_large
  refine ⟨referenceParameters.C, referenceParameters.C_pos, ?_⟩
  intro newPrime newPrimePrime newFresh N Nlarge
  exact sourceParameters_C_eq old oldPrime oldInjective newPrime newPrimePrime
    newFresh N Nlarge old oldPrime oldInjective referencePrime
      referencePrime_prime referencePrime_fresh referenceBound
        referenceBound_large

/-- The parameter delivered to the source construction contains its fixed
rank-only Lemma 2 dimension requirement. -/
theorem sourceInitialDimensionRequirement_mem_sourceParameters
    {ι : Type u} [Fintype ι]
    (old : ι → ℕ) (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old)
    (newPrime : ℕ) (newPrimePrime : newPrime.Prime)
    (newFresh : ∀ i, old i ≠ newPrime)
    (N : ℕ) (Nlarge : Real.exp 2 ≤ (N : ℝ)) :
    sourceInitialDimensionRequirement
        (sourceParameters old oldPrime oldInjective newPrime newPrimePrime
          newFresh N Nlarge) ∈
      (sourceParameters old oldPrime oldInjective newPrime newPrimePrime
        newFresh N Nlarge).kRequirements := by
  let P := rawSourceParameters old oldPrime oldInjective newPrime newPrimePrime
    newFresh N Nlarge
  change sourceInitialDimensionRequirement
      (P.withSourceRequirements (sourceExtraRequirements P)) ∈
    (P.withSourceRequirements (sourceExtraRequirements P)).kRequirements
  apply P.mem_withSourceRequirements_of_mem
  simp only [sourceExtraRequirements, Finset.mem_insert, Finset.mem_singleton]
  left
  unfold sourceInitialDimensionRequirement
  rw [P.withSourceRequirements_rank]

/-- The parameter delivered to the source construction also contains the
fixed rank-only level-zero column-count requirement. -/
theorem sourceInitialUnknownRequirement_mem_sourceParameters
    {ι : Type u} [Fintype ι]
    (old : ι → ℕ) (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old)
    (newPrime : ℕ) (newPrimePrime : newPrime.Prime)
    (newFresh : ∀ i, old i ≠ newPrime)
    (N : ℕ) (Nlarge : Real.exp 2 ≤ (N : ℝ)) :
    sourceInitialUnknownRequirement
        (sourceParameters old oldPrime oldInjective newPrime newPrimePrime
          newFresh N Nlarge) ∈
      (sourceParameters old oldPrime oldInjective newPrime newPrimePrime
        newFresh N Nlarge).kRequirements := by
  let P := rawSourceParameters old oldPrime oldInjective newPrime newPrimePrime
    newFresh N Nlarge
  change sourceInitialUnknownRequirement
      (P.withSourceRequirements (sourceExtraRequirements P)) ∈
    (P.withSourceRequirements (sourceExtraRequirements P)).kRequirements
  apply P.mem_withSourceRequirements_of_mem
  simp only [sourceExtraRequirements, Finset.mem_insert, Finset.mem_singleton]
  right
  unfold sourceInitialUnknownRequirement
  rw [P.withSourceRequirements_rank]

/-- Fin-indexed specialization in the literal name used by the concrete
Lemma 2 dimension theorem. -/
theorem initialDimensionRequirement_mem_sourceParameters
    {oldRank : ℕ}
    (old : Fin oldRank → ℕ) (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old)
    (newPrime : ℕ) (newPrimePrime : newPrime.Prime)
    (newFresh : ∀ i, old i ≠ newPrime)
    (N : ℕ) (Nlarge : Real.exp 2 ≤ (N : ℝ)) :
    Erdos240.BakerLemma2Concrete.initialDimensionRequirement
        (sourceParameters old oldPrime oldInjective newPrime newPrimePrime
          newFresh N Nlarge) ∈
      (sourceParameters old oldPrime oldInjective newPrime newPrimePrime
        newFresh N Nlarge).kRequirements := by
  simpa [sourceInitialDimensionRequirement,
    Erdos240.BakerLemma2Concrete.initialDimensionRequirement,
    Erdos240.BakerLemma2Concrete.initialDimensionConstant] using
      sourceInitialDimensionRequirement_mem_sourceParameters old oldPrime
        oldInjective newPrime newPrimePrime newFresh N Nlarge

/-- Fin-indexed specialization in the literal name used by the concrete
Lemma 2 column-count theorem. -/
theorem initialUnknownRequirement_mem_sourceParameters
    {oldRank : ℕ}
    (old : Fin oldRank → ℕ) (oldPrime : ∀ i, (old i).Prime)
    (oldInjective : Function.Injective old)
    (newPrime : ℕ) (newPrimePrime : newPrime.Prime)
    (newFresh : ∀ i, old i ≠ newPrime)
    (N : ℕ) (Nlarge : Real.exp 2 ≤ (N : ℝ)) :
    Erdos240.BakerLemma2Concrete.initialUnknownRequirement
        (sourceParameters old oldPrime oldInjective newPrime newPrimePrime
          newFresh N Nlarge) ∈
      (sourceParameters old oldPrime oldInjective newPrime newPrimePrime
        newFresh N Nlarge).kRequirements := by
  simpa [sourceInitialUnknownRequirement,
    Erdos240.BakerLemma2Concrete.initialUnknownRequirement] using
      sourceInitialUnknownRequirement_mem_sourceParameters old oldPrime
        oldInjective newPrime newPrimePrime newFresh N Nlarge

/-- A nonempty finite type has a nonempty canonical `Fin` enumeration. -/
theorem finCardNonempty (ι : Type u) [Fintype ι] [Nonempty ι] :
    Nonempty (Fin (Fintype.card ι)) :=
  ⟨⟨0, Fintype.card_pos⟩⟩

/-- Exact source-shaped construction target using the audited concrete state
model.  An arbitrary finite old family is reindexed by `Fintype.equivFin`,
because the polynomial-coordinate development uses explicit `Fin` indices.
The strict-smallness hypothesis is deliberately kept in the original
project-facing indexing; hence no dependence or statement is lost in this
interface. -/
def HasConcreteSourceChains : Prop :=
  ∀ (ι : Type u) [Fintype ι] [Nonempty ι] (old : ι → ℕ),
    (oldPrime : ∀ i, (old i).Prime) →
    (oldInjective : Function.Injective old) →
    letI : Nonempty (Fin (Fintype.card ι)) := finCardNonempty ι
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃p : ℕ⦄ (c : ι → ℤ) (d : ℤ) (N : ℕ)
        (hp : p.Prime) (hpFresh : ∀ i, old i ≠ p)
        (hN : Real.exp 2 ≤ (N : ℝ))
        (_hc : ∀ i, (c i).natAbs ≤ N) (_hd : d.natAbs ≤ N)
        (_hdne : d ≠ 0) (_hform : indexedRationalLogForm old p c d ≠ 0),
        |indexedRationalLogForm old p c d| <
            Real.exp (-C * Real.log (p : ℝ) * Real.log (N : ℝ)) →
          Nonempty (ConcreteSourceChain
            (sourceParameters
              (fun j : Fin (Fintype.card ι) ↦
                old ((Fintype.equivFin ι).symm j))
              (fun j ↦ oldPrime ((Fintype.equivFin ι).symm j))
              (oldInjective.comp (Fintype.equivFin ι).symm.injective)
              p hp (fun j ↦ hpFresh ((Fintype.equivFin ι).symm j)) N hN)
            (fun j ↦ c ((Fintype.equivFin ι).symm j)) d)

/-- The faithful unabsorbed source target.  Its exponent displays separately
the fixed old-height factors and the varying last height.  This prevents the
analytic construction from hiding a constant which depends on the varying
prime or on the coefficient cutoff. -/
def HasNormalizedConcreteSourceChains : Prop :=
  ∀ (ι : Type u) [Fintype ι] [Nonempty ι] (old : ι → ℕ),
    (oldPrime : ∀ i, (old i).Prime) →
    (oldInjective : Function.Injective old) →
    letI : Nonempty (Fin (Fintype.card ι)) := finCardNonempty ι
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ ⦃p : ℕ⦄ (c : ι → ℤ) (d : ℤ) (N : ℕ)
        (hp : p.Prime) (hpFresh : ∀ i, old i ≠ p)
        (hN : Real.exp 2 ≤ (N : ℝ))
        (_hc : ∀ i, (c i).natAbs ≤ N) (_hd : d.natAbs ≤ N)
        (_hdne : d ≠ 0) (_hform : indexedRationalLogForm old p c d ≠ 0),
        let P := sourceParameters old oldPrime oldInjective p hp hpFresh N hN
        |indexedRationalLogForm old p c d| <
            Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
              Real.log P.newHeight * Real.log (N : ℝ))) →
          Nonempty (ConcreteSourceChain
            (sourceParameters
              (fun j : Fin (Fintype.card ι) ↦
                old ((Fintype.equivFin ι).symm j))
              (fun j ↦ oldPrime ((Fintype.equivFin ι).symm j))
              (oldInjective.comp (Fintype.equivFin ι).symm.injective)
              p hp (fun j ↦ hpFresh ((Fintype.equivFin ι).symm j)) N hN)
            (fun j ↦ c ((Fintype.equivFin ι).symm j)) d)

/-- A componentwise version of `HasNormalizedConcreteSourceChains` exposing
the later source continuation.  This is the preferred integration boundary
for the concrete Lemma-3--6 modules: the rank-only counting estimates are
entries of `sourceParameters`, while `BakerInitialMatrixHeight` discharges the
source-faithful level-zero matrix estimate from the coefficient bounds. -/
def HasNormalizedConcreteSourceComponents : Prop :=
  ∀ (ι : Type u) [Fintype ι] [Nonempty ι] (old : ι → ℕ),
    (oldPrime : ∀ i, (old i).Prime) →
    (oldInjective : Function.Injective old) →
    letI : Nonempty (Fin (Fintype.card ι)) := finCardNonempty ι
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ ⦃p : ℕ⦄ (c : ι → ℤ) (d : ℤ) (N : ℕ)
        (hp : p.Prime) (hpFresh : ∀ i, old i ≠ p)
        (hN : Real.exp 2 ≤ (N : ℝ))
        (_hc : ∀ i, (c i).natAbs ≤ N) (_hd : d.natAbs ≤ N)
        (_hdne : d ≠ 0) (_hform : indexedRationalLogForm old p c d ≠ 0),
        let P := sourceParameters old oldPrime oldInjective p hp hpFresh N hN
        |indexedRationalLogForm old p c d| <
            Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
              Real.log P.newHeight * Real.log (N : ℝ))) →
          let oldFin := fun j : Fin (Fintype.card ι) ↦
            old ((Fintype.equivFin ι).symm j)
          let oldPrimeFin : ∀ j, (oldFin j).Prime := fun j ↦
            oldPrime ((Fintype.equivFin ι).symm j)
          let oldInjectiveFin : Function.Injective oldFin :=
            oldInjective.comp (Fintype.equivFin ι).symm.injective
          let freshFin : ∀ j, oldFin j ≠ p := fun j ↦
            hpFresh ((Fintype.equivFin ι).symm j)
          let Pfin := sourceParameters oldFin oldPrimeFin oldInjectiveFin p hp
            freshFin N hN
          let bfin := fun j : Fin (Fintype.card ι) ↦
            c ((Fintype.equivFin ι).symm j)
          Nonempty (ConcreteSourceContinuation Pfin bfin d)

/-- Assemble the componentwise normalized source construction.  The proof
uses the two checked rank-only ledger entries to invoke concrete Lemma 2,
then attaches its nonzero bounded coefficient state to the supplied
Lemma-3--6 continuation. -/
theorem normalizedConcreteSourceChains_of_components
    (hsource : HasNormalizedConcreteSourceComponents.{u}) :
    HasNormalizedConcreteSourceChains.{u} := by
  intro ι _ _ old oldPrime oldInjective
  obtain ⟨C₀, hC₀, hcomponents⟩ :=
    hsource ι old oldPrime oldInjective
  refine ⟨C₀, hC₀, ?_⟩
  intro p c d N hp hpFresh hN hc hd hdne hform
  dsimp only
  intro hsmall
  let : Nonempty (Fin (Fintype.card ι)) := finCardNonempty ι
  let oldFin := fun j : Fin (Fintype.card ι) ↦
    old ((Fintype.equivFin ι).symm j)
  let oldPrimeFin : ∀ j, (oldFin j).Prime := fun j ↦
    oldPrime ((Fintype.equivFin ι).symm j)
  let oldInjectiveFin : Function.Injective oldFin :=
    oldInjective.comp (Fintype.equivFin ι).symm.injective
  let freshFin : ∀ j, oldFin j ≠ p := fun j ↦
    hpFresh ((Fintype.equivFin ι).symm j)
  let Pfin := sourceParameters oldFin oldPrimeFin oldInjectiveFin p hp
    freshFin N hN
  let bfin := fun j : Fin (Fintype.card ι) ↦
    c ((Fintype.equivFin ι).symm j)
  obtain ⟨hcontinue⟩ :=
    hcomponents c d N hp hpFresh hN hc hd hdne hform hsmall
  have hdimension :
      Erdos240.BakerLemma2Concrete.initialDimensionRequirement Pfin ∈
        Pfin.kRequirements := by
    exact initialDimensionRequirement_mem_sourceParameters oldFin oldPrimeFin
      oldInjectiveFin p hp freshFin N hN
  have hunknownRequirement :
      Erdos240.BakerLemma2Concrete.initialUnknownRequirement Pfin ∈
        Pfin.kRequirements := by
    exact initialUnknownRequirement_mem_sourceParameters oldFin oldPrimeFin
      oldInjectiveFin p hp freshFin N hN
  have hbfin : ∀ r, (bfin r).natAbs ≤ Pfin.Bsrc := by
    intro r
    simpa only [bfin, Pfin, sourceParameters, rawSourceParameters,
      VDPLParameters.withSourceRequirements_Bsrc] using
        hc ((Fintype.equivFin ι).symm r)
  have hdPfin : d.natAbs ≤ Pfin.Bsrc := by
    simpa only [Pfin, sourceParameters, rawSourceParameters,
      VDPLParameters.withSourceRequirements_Bsrc] using hd
  obtain ⟨state, hvanish⟩ :=
    exists_initial_levelState_vanishes_sourceHeight_of_bounds Pfin bfin d
      hbfin hdPfin hdimension hunknownRequirement
  have hseed : IntegralSeedAtLevel Pfin (g state bfin d) 0 := by
    simpa only [IntegralSeedAtLevel,
      Erdos240.BakerLemma2Concrete.initialRadius_eq,
      Erdos240.BakerLemma2Concrete.initialBudget_eq] using hvanish
  exact ⟨hcontinue.withBase state hseed⟩

/-- Fixed-family height absorption for the concrete chain constructor.  The
new constant depends only on the old family, never on `p`, the coefficients,
or `N`. -/
theorem concreteSourceChains_of_normalized
    (hsource : HasNormalizedConcreteSourceChains.{u}) :
    HasConcreteSourceChains.{u} := by
  intro ι _ _ old oldPrime oldInjective
  obtain ⟨C₀, hC₀, hconstruct⟩ := hsource ι old oldPrime oldInjective
  let C : ℝ := C₀ * oldFamilySourceMultiplier old
  have hC : 0 < C := mul_pos hC₀ (oldFamilySourceMultiplier_pos old)
  refine ⟨C, hC, ?_⟩
  intro p c d N hp hpFresh hN hc hd hdne hform hsmall
  let P := sourceParameters old oldPrime oldInjective p hp hpFresh N hN
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg ((show (1 : ℝ) ≤ Real.exp 2 by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by norm_num)).trans hN)
  have hPold : P.old = old := by rfl
  have hPnewPrime : P.newPrime = p := by rfl
  have hsourceLe :
      C₀ * P.OmegaOld * Real.log P.OmegaOld * Real.log P.newHeight *
          Real.log (N : ℝ) ≤
        C * Real.log (p : ℝ) * Real.log (N : ℝ) := by
    dsimp only [C]
    rw [← hPold, ← hPnewPrime]
    exact sourceExponent_le_absorbedExponent P hC₀.le hlogN
  have hexp :
      Real.exp (-C * Real.log (p : ℝ) * Real.log (N : ℝ)) ≤
        Real.exp (-(C₀ * P.OmegaOld * Real.log P.OmegaOld *
          Real.log P.newHeight * Real.log (N : ℝ))) := by
    apply Real.exp_le_exp.mpr
    linarith
  apply hconstruct c d N hp hpFresh hN hc hd hdne hform
  exact hsmall.trans_le hexp

/-- A concrete source-chain constructor immediately gives the exact
strict-smallness contradiction consumed by the rational-prime assembly. -/
theorem smallFormContradiction_of_concreteSourceChains
    (hsource : HasConcreteSourceChains.{u}) :
    HasNonemptyVDPLSmallFormContradiction.{u} := by
  intro ι _ _ old oldPrime oldInjective
  obtain ⟨C, hC, hconstruct⟩ := hsource ι old oldPrime oldInjective
  refine ⟨C, hC, ?_⟩
  intro p c d N hp hpFresh hN hc hd hdne hform hsmall
  let : Nonempty (Fin (Fintype.card ι)) :=
    ⟨⟨0, Fintype.card_pos⟩⟩
  obtain ⟨data⟩ := hconstruct c d N hp hpFresh hN hc hd hdne hform hsmall
  exact data.false

/-- Complete uniform rational-prime logarithm lower bound from the concrete
source-chain construction target. -/
theorem uniformBounds_of_concreteSourceChains
    (hsource : HasConcreteSourceChains.{u}) :
    HasUniformRationalPrimeLogBounds.{u} :=
  uniform_bounds_of_vdplSmallFormContradiction
    (smallFormContradiction_of_concreteSourceChains hsource)

/-- Complete project-facing uniform bound from the faithful unabsorbed
concrete source-chain construction. -/
theorem uniformBounds_of_normalizedConcreteSourceChains
    (hsource : HasNormalizedConcreteSourceChains.{u}) :
    HasUniformRationalPrimeLogBounds.{u} :=
  uniformBounds_of_concreteSourceChains
    (concreteSourceChains_of_normalized hsource)

/-- Legacy generic construction interface for the source argument.

Whenever the proposed integral-cutoff lower bound fails, the eventual explicit
auxiliary construction must produce an `ExtrapolationChain` and a
`ZeroCountEndpoint`.  All quantifiers and uniformity requirements of the
eventual theorem are visible here: `C` depends only on the fixed old prime
family, while the certificate must be constructed uniformly in the fresh
prime, coefficients, and cutoff.

This definition is only a logical compatibility interface.  In particular it does not
validate any existing formula for the Delta shift, exponential monomial,
height floor, or final side length.  The unconditional development must first
correct those formulas and then prove that this predicate holds; no result
below assumes it except by an explicit theorem argument. -/
def HasIntegralCutoffSourceCertificates : Prop :=
  ∀ (ι : Type u) [Fintype ι] [Nonempty ι] (old : ι → ℕ),
    (oldPrime : ∀ i, (old i).Prime) →
    (oldInjective : Function.Injective old) →
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃p : ℕ⦄ (c : ι → ℤ) (d : ℤ) (N : ℕ)
        (hp : p.Prime) (hpFresh : ∀ i, old i ≠ p)
        (hN : Real.exp 2 ≤ (N : ℝ))
        (_hc : ∀ i, (c i).natAbs ≤ N) (_hd : d.natAbs ≤ N)
        (_hdne : d ≠ 0) (_hform : indexedRationalLogForm old p c d ≠ 0),
        |indexedRationalLogForm old p c d| <
            Real.exp (-C * Real.log (p : ℝ) * Real.log (N : ℝ)) →
          VDPLContradictionCertificate
            (sourceParameters old oldPrime oldInjective p hp hpFresh N hN)

/-- A constructed contradictory certificate is exactly the strict-smallness
contradiction expected by the main-independent rational-prime assembly. -/
theorem smallFormContradiction_of_sourceCertificates
    (hsource : HasIntegralCutoffSourceCertificates.{u}) :
    HasNonemptyVDPLSmallFormContradiction.{u} := by
  intro ι _ _ old oldPrime oldInjective
  obtain ⟨C, hC, hconstruct⟩ := hsource ι old oldPrime oldInjective
  refine ⟨C, hC, ?_⟩
  intro p c d N hp hpFresh hN hc hd hdne hform hsmall
  exact (hconstruct c d N hp hpFresh hN hc hd hdne hform hsmall).false

/-- The source-certificate construction implies the integral-cutoff Baker
bound for every nonempty old family. -/
theorem integralCutoffBounds_nonempty_of_sourceCertificates
    (hsource : HasIntegralCutoffSourceCertificates.{u})
    (ι : Type u) [Fintype ι] [Nonempty ι] (old : ι → ℕ)
    (oldPrime : ∀ i, (old i).Prime) (oldInjective : Function.Injective old) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ⦃p : ℕ⦄ (c : ι → ℤ) (d : ℤ) (N : ℕ),
        p.Prime → (∀ i, old i ≠ p) → Real.exp 2 ≤ (N : ℝ) →
        (∀ i, (c i).natAbs ≤ N) → d.natAbs ≤ N → d ≠ 0 →
        indexedRationalLogForm old p c d ≠ 0 →
        Real.exp (-C * Real.log (p : ℝ) * Real.log (N : ℝ)) ≤
          |indexedRationalLogForm old p c d| := by
  obtain ⟨C, hC, hconstruct⟩ := hsource ι old oldPrime oldInjective
  refine ⟨C, hC, ?_⟩
  intro p c d N hp hpFresh hN hc hd hdne hform
  by_contra hnot
  have hsmall : |indexedRationalLogForm old p c d| <
      Real.exp (-C * Real.log (p : ℝ) * Real.log (N : ℝ)) :=
    lt_of_not_ge hnot
  exact (hconstruct c d N hp hpFresh hN hc hd hdne hform hsmall).false

/-- Full integral-cutoff source bound.  Empty old families are elementary;
nonempty families are exactly the content of the source certificate theorem. -/
theorem integralCutoffBounds_of_sourceCertificates
    (hsource : HasIntegralCutoffSourceCertificates.{u}) :
    HasIntegralCutoffRationalPrimeLogBounds.{u} := by
  apply integralCutoff_bounds_of_nonempty
  intro ι _ _ old oldPrime oldInjective
  exact integralCutoffBounds_nonempty_of_sourceCertificates
    hsource ι old oldPrime oldInjective

/-- The complete checked logical bridge from source certificates to the
uniform real-cutoff family estimate used by Erdős 240. -/
theorem uniformBounds_of_sourceCertificates
    (hsource : HasIntegralCutoffSourceCertificates.{u}) :
    HasUniformRationalPrimeLogBounds.{u} :=
  uniform_rational_prime_log_lower_bound_of_integralCutoff
    (integralCutoffBounds_of_sourceCertificates hsource)

#print axioms Erdos240.BakerSourceAssemblyIndependent.ExtrapolationChain.vanishesAtLevel
#print axioms Erdos240.BakerSourceAssemblyIndependent.ConcreteSourceChain.false
#print axioms Erdos240.BakerSourceAssemblyIndependent.ConcreteSourceChain.false_of_initialEstimates
#print axioms Erdos240.BakerSourceAssemblyIndependent.ConcreteSourceChain.false_of_initialRequirements
#print axioms Erdos240.BakerSourceAssemblyIndependent.ZeroCountEndpoint.false
#print axioms Erdos240.BakerSourceAssemblyIndependent.smallFormContradiction_of_concreteSourceChains
#print axioms Erdos240.BakerSourceAssemblyIndependent.uniformBounds_of_concreteSourceChains
#print axioms Erdos240.BakerSourceAssemblyIndependent.normalizedConcreteSourceChains_of_components
#print axioms Erdos240.BakerSourceAssemblyIndependent.concreteSourceChains_of_normalized
#print axioms Erdos240.BakerSourceAssemblyIndependent.uniformBounds_of_normalizedConcreteSourceChains
#print axioms Erdos240.BakerSourceAssemblyIndependent.smallFormContradiction_of_sourceCertificates
#print axioms Erdos240.BakerSourceAssemblyIndependent.integralCutoffBounds_of_sourceCertificates
#print axioms Erdos240.BakerSourceAssemblyIndependent.uniformBounds_of_sourceCertificates

end Erdos240.BakerSourceAssemblyIndependent
