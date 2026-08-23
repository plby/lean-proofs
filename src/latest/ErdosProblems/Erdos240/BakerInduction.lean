/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos240.BakerIntegralExtrapolation
import ErdosProblems.Erdos240.BakerRationalExtrapolation

/-!
# The finite-level induction in van der Poorten--Loxton Lemma 6

This file isolates the logical induction on pp. 50--52 of van der
Poorten--Loxton.  Its five inputs are deliberately visible in the statement:

* the initial auxiliary object and its level-zero vanishing;
* the integral extrapolation of Lemma 4;
* the interpolation upper bound and Liouville alternative used by Lemma 5;
* the radical-monomial coefficient extraction, which gives successor zeros
  at the nodes coprime to `q`;
* the following coprime-node Hermite/Liouville completion, which fills the
  nodes divisible by `q` and restores the full integral seed.

The type `State J` is the eventual level-`J` coefficient box.  The predicate
`Good J x` is where the caller records nontriviality and the common
coefficient-height bound.  Thus this abstract induction does not postulate
those facts silently: a final source theorem must construct `baseGood` and
prove that `descend` preserves `Good` using the exact radical-monomial basis.

The radii and derivative budgets below are not abstract variables.  Lemma 4
retains its full terminal rectangle at iteration `3 * (rank + 1)`; Lemma 5
restricts that rectangle to radius `R (J+1)` and budget `Sstep J`; radical
descent preserves this budget on the coprime nodes; and the p. 52 completion
returns the next full budget `Slevel (J+1)`.
-/

open scoped BigOperators

noncomputable section

namespace Erdos240.BakerInduction

open Erdos240
open Erdos240.BakerRationalExtrapolation

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Vanishing available on entry to induction level `J`. -/
def IntegralSeedAtLevel (P : VDPLParameters ι)
    (G : ℂ → VDPLMultiIndex P.rank → ℂ) (J : ℕ) : Prop :=
  VanishesOn G 1 (P.R J) (P.Slevel J)

/-- The exact output of the radical-monomial extraction on p. 51 of
van der Poorten--Loxton.  At this intermediate point one only knows the
successor-level equations at nodes prime to `q`.

This is deliberately weaker than `IntegralSeedAtLevel`: the source next
uses Hermite interpolation on the coprime nodes, together with the Lemma 3
upper estimate and the Liouville lower alternative, to fill the nodes
divisible by `q`. -/
def CoprimeIntegralSeedAtLevel (P : VDPLParameters ι)
    (G : ℂ → VDPLMultiIndex P.rank → ℂ) (J : ℕ) : Prop :=
  ∀ l, 1 ≤ l → l ≤ P.R J → l.Coprime P.q →
    ∀ m, VDPLMultiIndex.weight m ≤ P.Slevel J →
      G (l : ℂ) m = 0

/-- The exact, predecessor-indexed output of equation (12).  It deliberately
retains the larger Lemma 5 budget `Sstep J`; p. 52 spends one quarter of this
budget on extra Hermite derivatives and only then restricts the base
multiindex to the successor budget `Slevel (J+1)`. -/
def CoprimeDescentAtLevel (P : VDPLParameters ι)
    (G : ℂ → VDPLMultiIndex P.rank → ℂ) (J : ℕ) : Prop :=
  ∀ l, 1 ≤ l → l ≤ P.R (J + 1) → l.Coprime P.q →
    ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
      G (l : ℂ) m = 0

/-- The second half of the source's successor step: coprime-node Hermite
interpolation and the Liouville alternative turn the full `Sstep J`
coprime descent output into the all-node successor seed. -/
def CoprimeCompletionAtLevel (P : VDPLParameters ι)
    (G : ℂ → VDPLMultiIndex P.rank → ℂ) (J : ℕ) : Prop :=
  CoprimeDescentAtLevel P G J → IntegralSeedAtLevel P G (J + 1)

/-- A full integral seed restricts to the coprime nodes. -/
theorem IntegralSeedAtLevel.coprime
    {P : VDPLParameters ι} {G : ℂ → VDPLMultiIndex P.rank → ℂ}
    {J : ℕ} (h : IntegralSeedAtLevel P G J) :
    CoprimeIntegralSeedAtLevel P G J := by
  intro l hl hlR _hcop m hm
  simpa using h l hl hlR m hm

/-- Restrict the full predecessor budget retained by equation (12) to the
successor budget.  This is only a bookkeeping projection: the p. 52
completion uses the stronger `CoprimeDescentAtLevel` hypothesis itself. -/
theorem CoprimeDescentAtLevel.coprimeSeed
    {P : VDPLParameters ι} {G : ℂ → VDPLMultiIndex P.rank → ℂ}
    {J : ℕ} (h : CoprimeDescentAtLevel P G J) :
    CoprimeIntegralSeedAtLevel P G (J + 1) := by
  intro l hl hlR hcop m hm
  exact h l hl hlR hcop m (hm.trans (P.Slevel_succ_le_Sstep J))

/-- Exact terminal output of source Lemma 4 at outer level `J`.

The source iterates integral Hermite extrapolation through
`3 * (rank + 1)` stages.  Lemma 5 uses this full rectangle: its radius is
`floor(16 q^J h k^(1/2))`, and its derivative budget is the terminal
`lemmaFourBudget`.  Restricting prematurely to `R (J+1), Sstep J` loses the
node radius and jet slack used in equation (10). -/
def IntegralExtrapolatedAtLevel (P : VDPLParameters ι)
    (G : ℂ → VDPLMultiIndex P.rank → ℂ) (J : ℕ) : Prop :=
  VanishesOn G 1
    (P.lemmaFourRadius J (3 * (P.rank + 1)))
    (P.lemmaFourBudget J (3 * (P.rank + 1)))

/-- Exact rational-grid output of source Lemma 5 at level `J`. -/
def RationalExtrapolatedAtLevel (P : VDPLParameters ι)
    (G : ℂ → VDPLMultiIndex P.rank → ℂ) (J : ℕ) : Prop :=
  VanishesOn G P.q (P.R (J + 1)) (P.Sstep J)

/-- The strict interpolation estimate required in the nondivisible branch
of Lemma 5.  Every range and budget occurring in the source step is explicit
in this predicate. -/
def RationalInterpolationUpperAtLevel (P : VDPLParameters ι)
    (F : ℂ → VDPLMultiIndex P.rank → ℂ)
    (lower : ℕ → VDPLMultiIndex P.rank → ℝ) (J : ℕ) : Prop :=
  ∀ l, 1 ≤ l → l ≤ P.R (J + 1) → ¬ P.q ∣ l →
    ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
      ‖F ((l : ℂ) / (P.q : ℂ)) m‖ < lower l m

/-- The Liouville alternative required in Lemma 5.  The zero branch concerns
the algebraic auxiliary function `G`; the lower-bound branch concerns the
nearby entire function `F`. -/
def RationalLiouvilleAlternativeAtLevel (P : VDPLParameters ι)
    (F G : ℂ → VDPLMultiIndex P.rank → ℂ)
    (lower : ℕ → VDPLMultiIndex P.rank → ℝ) (J : ℕ) : Prop :=
  ∀ l, 1 ≤ l → l ≤ P.R (J + 1) →
    ∀ m, VDPLMultiIndex.weight m ≤ P.Sstep J →
      G ((l : ℂ) / (P.q : ℂ)) m = 0 ∨
        lower l m ≤ ‖F ((l : ℂ) / (P.q : ℂ)) m‖

/-- The three numerical transitions used by the `J → J+1` induction.
The first is the exact radius recursion, the second is the derivative-budget
restriction in Lemma 5, and the third is downward closure of the admissible
level inequality. -/
theorem numeric_transition (P : VDPLParameters ι) (J : ℕ) :
    P.R (J + 1) = P.q * P.R J ∧
      P.Slevel (J + 1) ≤ P.Sstep J ∧
      (P.LevelOK (J + 1) → P.LevelOK J) := by
  exact ⟨P.R_succ J, P.Slevel_succ_le_Sstep J,
    fun h ↦ VDPLParameters.LevelOK.mono P h (Nat.le_succ J)⟩

/-- The terminal Lemma 4 radius contains the full numerator range needed by
Lemma 5.  This is the source comparison
`q ≤ k^ε ≤ k^(1/2)` written through the already checked first-step
radius bound and monotonicity of the later radius scale. -/
theorem R_succ_le_terminalLemmaFourRadius
    (P : VDPLParameters ι) (J : ℕ) :
    P.R (J + 1) ≤ P.lemmaFourRadius J (3 * (P.rank + 1)) := by
  refine (P.R_succ_le_lemmaFourRadius_one J).trans ?_
  unfold VDPLParameters.lemmaFourRadius
  apply Nat.floor_mono
  unfold VDPLParameters.lemmaFourRadiusScale
  have hindex : (1 : ℕ) ≤ 3 * (P.rank + 1) := by omega
  have hindexReal : (1 : ℝ) ≤ (3 * (P.rank + 1) : ℕ) := by
    exact_mod_cast hindex
  have hexponent :
      P.epsilon * (1 : ℝ) ≤
        P.epsilon * ((3 * (P.rank + 1) : ℕ) : ℝ) := by
    exact mul_le_mul_of_nonneg_left hindexReal P.epsilon_pos.le
  have hrpow := Real.rpow_le_rpow_of_exponent_le P.one_le_k hexponent
  exact mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_one] using hrpow)
    (by positivity)

/-- Restrict the full terminal Lemma 4 rectangle to the integral rectangle
used in the divisible-numerator branch of Lemma 5. -/
theorem IntegralExtrapolatedAtLevel.forLemma5
    {P : VDPLParameters ι} {G : ℂ → VDPLMultiIndex P.rank → ℂ}
    {J : ℕ} (hJ : P.LevelOK J)
    (h : IntegralExtrapolatedAtLevel P G J) :
    VanishesOn G 1 (P.R (J + 1)) (P.Sstep J) := by
  exact h.mono (R_succ_le_terminalLemmaFourRadius P J)
    (P.Sstep_le_terminalBudget hJ)

/-- Checked Lemma 5 transition in the notation used by Lemma 6.

The integral vanishing is the output of Lemma 4.  The two quantitative
hypotheses are exactly the strict interpolation upper bound and the
Liouville alternative; no estimate is bundled into an undischarged step
assumption. -/
theorem rational_extrapolation_at_level
    (P : VDPLParameters ι) (J : ℕ)
    {F G : ℂ → VDPLMultiIndex P.rank → ℂ}
    (lower : ℕ → VDPLMultiIndex P.rank → ℝ)
    (hJ : P.LevelOK J)
    (hint : IntegralExtrapolatedAtLevel P G J)
    (hupper : RationalInterpolationUpperAtLevel P F lower J)
    (hlower : RationalLiouvilleAlternativeAtLevel P F G lower J) :
    RationalExtrapolatedAtLevel P G J := by
  exact vdpl_lemma5 P J lower (hint.forLemma5 hJ) hupper hlower

/-- One complete logical `J → J+1` step after Lemma 4, radical coefficient
extraction, and the coprime-node completion have been instantiated.

The conclusion of `descend` is only the coprime part of the next level's
integral seed.  This is the exact output of expanding coefficients by their
residues modulo `q` and applying linear independence of the radical monomials.
The separate `completeCoprime` hypothesis is the subsequent interpolation
and Liouville argument at nodes divisible by `q`. -/
theorem vdpl_lemma6_step
    (P : VDPLParameters ι) (J : ℕ)
    {F G : ℂ → VDPLMultiIndex P.rank → ℂ}
    (lower : ℕ → VDPLMultiIndex P.rank → ℝ)
    (hJ : P.LevelOK J)
    (hint : IntegralExtrapolatedAtLevel P G J)
    (hupper : RationalInterpolationUpperAtLevel P F lower J)
    (hlower : RationalLiouvilleAlternativeAtLevel P F G lower J)
    {Next : Type*} (GoodNext : Next → Prop)
    (Gnext : Next → ℂ → VDPLMultiIndex P.rank → ℂ)
    (descend : RationalExtrapolatedAtLevel P G J →
      ∃ y : Next, GoodNext y ∧
        CoprimeDescentAtLevel P (Gnext y) J)
    (completeCoprime : ∀ y, GoodNext y →
      CoprimeCompletionAtLevel P (Gnext y) J) :
    ∃ y : Next, GoodNext y ∧ IntegralSeedAtLevel P (Gnext y) (J + 1) := by
  obtain ⟨y, hyGood, hyCoprime⟩ :=
    descend (rational_extrapolation_at_level P J lower hJ hint hupper hlower)
  exact ⟨y, hyGood, completeCoprime y hyGood hyCoprime⟩

/-- Abstract but assumption-transparent form of source Lemma 6.

`State J` packages the level-`J` coefficient family, while `Good J x`
packages its nonzero coefficient and common height bound.  A concrete Baker
theorem must instantiate all five displayed boundaries:

1. `baseGood` and `baseVanishes` from the auxiliary construction (Lemma 2);
2. `integralStep` from the quantitative integral extrapolation (Lemma 4);
3. `upperStep` and `lowerStep` from interpolation and Liouville (Lemmas 3, 5);
4. `descend` from the exact radical-monomial basis and coefficient extraction;
5. `completeCoprime` from the source's coprime-node Hermite interpolation and
   Liouville completion at nodes divisible by `q`.

The theorem itself then performs the complete finite induction and calls the
checked Lemma 5 transition at every successor level. -/
theorem vdpl_lemma6
    (P : VDPLParameters ι)
    (State : ℕ → Type*)
    (Good : ∀ J, State J → Prop)
    (F G : ∀ J, State J → ℂ → VDPLMultiIndex P.rank → ℂ)
    (lower : ∀ J, State J → ℕ → VDPLMultiIndex P.rank → ℝ)
    (base : State 0)
    (baseGood : Good 0 base)
    (baseVanishes : IntegralSeedAtLevel P (G 0 base) 0)
    (integralStep : ∀ J (x : State J), P.LevelOK J → Good J x →
      IntegralSeedAtLevel P (G J x) J →
      IntegralExtrapolatedAtLevel P (G J x) J)
    (upperStep : ∀ J (x : State J), P.LevelOK J → Good J x →
      IntegralExtrapolatedAtLevel P (G J x) J →
      RationalInterpolationUpperAtLevel P (F J x) (lower J x) J)
    (lowerStep : ∀ J (x : State J), P.LevelOK J → Good J x →
      IntegralExtrapolatedAtLevel P (G J x) J →
      RationalLiouvilleAlternativeAtLevel P (F J x) (G J x)
        (lower J x) J)
    (descend : ∀ J (x : State J), P.LevelOK (J + 1) → Good J x →
      RationalExtrapolatedAtLevel P (G J x) J →
      ∃ y : State (J + 1), Good (J + 1) y ∧
        CoprimeDescentAtLevel P (G (J + 1) y) J)
    (completeCoprime : ∀ J (x : State (J + 1)), P.LevelOK (J + 1) →
      Good (J + 1) x → CoprimeCompletionAtLevel P (G (J + 1) x) J) :
    ∀ J, P.LevelOK J →
      ∃ x : State J, Good J x ∧ IntegralSeedAtLevel P (G J x) J := by
  intro J
  induction J with
  | zero =>
      intro _hlevel
      exact ⟨base, baseGood, baseVanishes⟩
  | succ J ih =>
      intro hnext
      have hcurrent : P.LevelOK J :=
        VDPLParameters.LevelOK.mono P hnext (Nat.le_succ J)
      obtain ⟨x, hxGood, hxVanishes⟩ := ih hcurrent
      have hint : IntegralExtrapolatedAtLevel P (G J x) J :=
        integralStep J x hcurrent hxGood hxVanishes
      have hupper : RationalInterpolationUpperAtLevel P (F J x) (lower J x) J :=
        upperStep J x hcurrent hxGood hint
      have hlower : RationalLiouvilleAlternativeAtLevel P (F J x) (G J x)
          (lower J x) J :=
        lowerStep J x hcurrent hxGood hint
      have hrat : RationalExtrapolatedAtLevel P (G J x) J :=
        rational_extrapolation_at_level P J (lower J x) hcurrent
          hint hupper hlower
      obtain ⟨y, hyGood, hyCoprime⟩ := descend J x hnext hxGood hrat
      exact ⟨y, hyGood, completeCoprime J y hnext hyGood hyCoprime⟩

/-- Simultaneous finite-range form: one admissible terminal level yields a
good auxiliary object at every earlier level. -/
theorem vdpl_lemma6_up_to
    (P : VDPLParameters ι)
    (State : ℕ → Type*)
    (Good : ∀ J, State J → Prop)
    (F G : ∀ J, State J → ℂ → VDPLMultiIndex P.rank → ℂ)
    (lower : ∀ J, State J → ℕ → VDPLMultiIndex P.rank → ℝ)
    (base : State 0)
    (baseGood : Good 0 base)
    (baseVanishes : IntegralSeedAtLevel P (G 0 base) 0)
    (integralStep : ∀ J (x : State J), P.LevelOK J → Good J x →
      IntegralSeedAtLevel P (G J x) J →
      IntegralExtrapolatedAtLevel P (G J x) J)
    (upperStep : ∀ J (x : State J), P.LevelOK J → Good J x →
      IntegralExtrapolatedAtLevel P (G J x) J →
      RationalInterpolationUpperAtLevel P (F J x) (lower J x) J)
    (lowerStep : ∀ J (x : State J), P.LevelOK J → Good J x →
      IntegralExtrapolatedAtLevel P (G J x) J →
      RationalLiouvilleAlternativeAtLevel P (F J x) (G J x)
        (lower J x) J)
    (descend : ∀ J (x : State J), P.LevelOK (J + 1) → Good J x →
      RationalExtrapolatedAtLevel P (G J x) J →
      ∃ y : State (J + 1), Good (J + 1) y ∧
        CoprimeDescentAtLevel P (G (J + 1) y) J)
    (completeCoprime : ∀ J (x : State (J + 1)), P.LevelOK (J + 1) →
      Good (J + 1) x → CoprimeCompletionAtLevel P (G (J + 1) x) J)
    {N : ℕ} (hN : P.LevelOK N) :
    ∀ J, J ≤ N →
      ∃ x : State J, Good J x ∧ IntegralSeedAtLevel P (G J x) J := by
  intro J hJN
  exact vdpl_lemma6 P State Good F G lower base baseGood baseVanishes
    integralStep upperStep lowerStep descend completeCoprime J
      (VDPLParameters.LevelOK.mono P hN hJN)

end Erdos240.BakerInduction

#print axioms Erdos240.BakerInduction.numeric_transition
#print axioms Erdos240.BakerInduction.rational_extrapolation_at_level
#print axioms Erdos240.BakerInduction.vdpl_lemma6
