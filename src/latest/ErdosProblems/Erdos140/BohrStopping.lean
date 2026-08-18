import ErdosProblems.Erdos140.BohrBasic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Maximal regular-Bohr restriction chains

This file contains the finite stopping argument used by the balanced
restriction step of the Kelley--Meka proof.  Unlike the numerical state in
`DensityIteration.lean`, every node below contains an actual subset of an
actual, scale-regular finite Bohr carrier.

The analytic density-increment lemma is represented by the predicate
`ProducesIncrement`: whenever a proposed stopping inequality is bad, it
produces another regular restriction with controlled density, rank, and
cardinality.  The main theorem proves that this process stops, and returns
all three accumulated bounds.  The final specialization records explicitly
that an eleventh-power loss at each of at most `L + 1` stages has total
twelfth-power cost.
-/

open Finset
open scoped NNReal

namespace Erdos140.BohrStopping

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- One node of the regular-Bohr restriction iteration.

The ambient finite set is `(bohr.dilate outer).carrier`; `inner` is the shell
width at which this carrier is certified to be coarsely regular. -/
structure RegularRestriction (G : Type*) [AddCommGroup G] [Fintype G]
    [DecidableEq G] where
  bohr : BohrData G
  outer : ℝ≥0
  inner : ℝ≥0
  regular : 0 < inner ∧ inner ≤ outer ∧
    (bohr.dilate (outer + inner)).carrier.card ≤
      2 * (bohr.dilate (outer - inner)).carrier.card
  set : Finset G
  nonempty : set.Nonempty
  subset_carrier : set ⊆ (bohr.dilate outer).carrier

namespace RegularRestriction

/-- The finite regular Bohr carrier at a restriction node. -/
def ambient (s : RegularRestriction G) : Finset G :=
  (s.bohr.dilate s.outer).carrier

/-- The relative density of the restricted set in its Bohr carrier. -/
def density (s : RegularRestriction G) : ℝ :=
  (s.set.card : ℝ) / s.ambient.card

/-- Rank of the ambient Bohr datum.  Dilation does not change this rank. -/
def rank (s : RegularRestriction G) : ℕ := s.bohr.rank

/-- Cardinality of the ambient regular Bohr carrier. -/
def card (s : RegularRestriction G) : ℕ := s.ambient.card

lemma ambient_nonempty (s : RegularRestriction G) : s.ambient.Nonempty :=
  (s.bohr.dilate s.outer).carrier_nonempty

lemma card_pos (s : RegularRestriction G) : 0 < s.card :=
  s.ambient_nonempty.card_pos

lemma density_pos (s : RegularRestriction G) : 0 < s.density := by
  exact div_pos (by exact_mod_cast s.nonempty.card_pos)
    (by exact_mod_cast s.ambient_nonempty.card_pos)

lemma density_nonneg (s : RegularRestriction G) : 0 ≤ s.density :=
  s.density_pos.le

lemma density_le_one (s : RegularRestriction G) : s.density ≤ 1 := by
  rw [density, div_le_one (by exact_mod_cast s.ambient_nonempty.card_pos)]
  exact_mod_cast Finset.card_le_card s.subset_carrier

end RegularRestriction

/-- A controlled density-increment move between actual regular Bohr
restrictions.  The size inequality is deliberately stated after casting to
`ℝ`, because its natural loss factor is exponential. -/
def IsControlledIncrement (q : ℝ) (rankCost : ℕ) (sizeCost : ℝ)
    (s t : RegularRestriction G) : Prop :=
  q * s.density ≤ t.density ∧
    t.rank ≤ s.rank + rankCost ∧
    Real.exp (-sizeCost) * (s.card : ℝ) ≤ (t.card : ℝ)

/-- A chain with exactly `n` controlled restriction moves. -/
inductive ControlledChain (q : ℝ) (rankCost : ℕ) (sizeCost : ℝ) :
    ℕ → RegularRestriction G → RegularRestriction G → Prop
  | nil (s : RegularRestriction G) : ControlledChain q rankCost sizeCost 0 s s
  | cons {n : ℕ} {s t u : RegularRestriction G}
      (hst : IsControlledIncrement q rankCost sizeCost s t)
      (htu : ControlledChain q rankCost sizeCost n t u) :
      ControlledChain q rankCost sizeCost (n + 1) s u

namespace ControlledChain

/-- Density multiplies along a controlled chain. -/
theorem density_bound {q : ℝ} {rankCost : ℕ} {sizeCost : ℝ}
    (hq : 0 ≤ q) {n : ℕ} {s t : RegularRestriction G}
    (h : ControlledChain q rankCost sizeCost n s t) :
    q ^ n * s.density ≤ t.density := by
  induction h with
  | nil s => simp
  | @cons n s t u hst htu ih =>
      have hqpow : 0 ≤ q ^ n := pow_nonneg hq n
      calc
        q ^ (n + 1) * s.density = q ^ n * (q * s.density) := by
          rw [pow_succ]
          ring
        _ ≤ q ^ n * t.density :=
          mul_le_mul_of_nonneg_left hst.1 hqpow
        _ ≤ u.density := ih

/-- Rank costs add along a controlled chain. -/
theorem rank_bound {q : ℝ} {rankCost : ℕ} {sizeCost : ℝ}
    {n : ℕ} {s t : RegularRestriction G}
    (h : ControlledChain q rankCost sizeCost n s t) :
    t.rank ≤ s.rank + n * rankCost := by
  induction h with
  | nil s => simp
  | @cons n s t u hst htu ih =>
      calc
        u.rank ≤ t.rank + n * rankCost := ih
        _ ≤ (s.rank + rankCost) + n * rankCost :=
          Nat.add_le_add_right hst.2.1 (n * rankCost)
        _ = s.rank + (n + 1) * rankCost := by
          simp only [Nat.add_mul, one_mul]
          omega

/-- Exponential cardinality losses multiply along a controlled chain. -/
theorem card_bound {q : ℝ} {rankCost : ℕ} {sizeCost : ℝ}
    {n : ℕ} {s t : RegularRestriction G}
    (h : ControlledChain q rankCost sizeCost n s t) :
    Real.exp (-(n : ℝ) * sizeCost) * (s.card : ℝ) ≤ (t.card : ℝ) := by
  induction h with
  | nil s => simp
  | @cons n s t u hst htu ih =>
      have hexp_nonneg : 0 ≤ Real.exp (-(n : ℝ) * sizeCost) :=
        (Real.exp_pos _).le
      calc
        Real.exp (-((n + 1 : ℕ) : ℝ) * sizeCost) * (s.card : ℝ) =
            Real.exp (-(n : ℝ) * sizeCost) *
              (Real.exp (-sizeCost) * (s.card : ℝ)) := by
          rw [show -((n + 1 : ℕ) : ℝ) * sizeCost =
              (-(n : ℝ) * sizeCost) + (-sizeCost) by
            push_cast
            ring,
            Real.exp_add]
          ring
        _ ≤ Real.exp (-(n : ℝ) * sizeCost) * (t.card : ℝ) :=
          mul_le_mul_of_nonneg_left hst.2.2 hexp_nonneg
        _ ≤ (u.card : ℝ) := ih

end ControlledChain

/-- The exact interface supplied by a density-increment proposition: every
node at which `Bad` holds admits another controlled regular restriction. -/
def ProducesIncrement (Bad : RegularRestriction G → Prop)
    (q : ℝ) (rankCost : ℕ) (sizeCost : ℝ) : Prop :=
  ∀ s : RegularRestriction G, Bad s →
    ∃ t : RegularRestriction G,
      IsControlledIncrement q rankCost sizeCost s t

/-- Finite count-or-increment recursion on actual Bohr restrictions.

The growth hypothesis says that `fuel` consecutive increments would force
density above one.  Therefore a terminal node occurs after at most `fuel`
moves. -/
theorem exists_terminal_chain
    {Terminal : RegularRestriction G → Prop}
    {q : ℝ} {rankCost : ℕ} {sizeCost : ℝ}
    (hq : 0 ≤ q)
    (hstep : ∀ s : RegularRestriction G,
      Terminal s ∨ ∃ t, IsControlledIncrement q rankCost sizeCost s t)
    (fuel : ℕ) (s : RegularRestriction G)
    (hgrowth : 1 < q ^ fuel * s.density) :
    ∃ n ≤ fuel, ∃ t : RegularRestriction G,
      ControlledChain q rankCost sizeCost n s t ∧ Terminal t := by
  induction fuel generalizing s with
  | zero =>
      have hs := s.density_le_one
      simp only [pow_zero, one_mul] at hgrowth
      exact (not_lt_of_ge hs hgrowth).elim
  | succ fuel ih =>
      rcases hstep s with hterminal | ⟨t, hst⟩
      · exact ⟨0, by omega, s, ControlledChain.nil s, hterminal⟩
      · have hqpow : 0 ≤ q ^ fuel := pow_nonneg hq fuel
        have hgrowth' : 1 < q ^ fuel * t.density := by
          calc
            1 < q ^ (fuel + 1) * s.density := by simpa using hgrowth
            _ = q ^ fuel * (q * s.density) := by
              rw [pow_succ]
              ring
            _ ≤ q ^ fuel * t.density :=
              mul_le_mul_of_nonneg_left hst.1 hqpow
        obtain ⟨n, hn, u, hchain, hu⟩ := ih t hgrowth'
        exact ⟨n + 1, by omega, u, ControlledChain.cons hst hchain, hu⟩

/-- An unconditional maximal controlled chain: terminal means precisely that
no further controlled regular restriction exists. -/
theorem exists_maximal_chain
    {q : ℝ} {rankCost : ℕ} {sizeCost : ℝ}
    (hq : 0 ≤ q) (fuel : ℕ) (s : RegularRestriction G)
    (hgrowth : 1 < q ^ fuel * s.density) :
    ∃ n ≤ fuel, ∃ t : RegularRestriction G,
      ControlledChain q rankCost sizeCost n s t ∧
      ¬ ∃ u : RegularRestriction G,
        IsControlledIncrement q rankCost sizeCost t u := by
  apply exists_terminal_chain (q := q) (rankCost := rankCost)
    (sizeCost := sizeCost) hq (fuel := fuel) (s := s) _ hgrowth
  intro t
  classical
  exact em (∃ u : RegularRestriction G,
    IsControlledIncrement q rankCost sizeCost t u) |>.symm

/-- A maximal chain stops every bad alternative that is known to produce a
controlled increment.  The conclusion also exposes the accumulated density,
rank, and cardinality estimates. -/
theorem exists_stopping_chain
    {Bad : RegularRestriction G → Prop}
    {q : ℝ} {rankCost : ℕ} {sizeCost : ℝ}
    (hq : 0 ≤ q)
    (hbad : ProducesIncrement Bad q rankCost sizeCost)
    (fuel : ℕ) (s : RegularRestriction G)
    (hgrowth : 1 < q ^ fuel * s.density) :
    ∃ n ≤ fuel, ∃ t : RegularRestriction G,
      ControlledChain q rankCost sizeCost n s t ∧
      ¬ Bad t ∧
      q ^ n * s.density ≤ t.density ∧
      t.rank ≤ s.rank + n * rankCost ∧
      Real.exp (-(n : ℝ) * sizeCost) * (s.card : ℝ) ≤ (t.card : ℝ) := by
  obtain ⟨n, hn, t, hchain, hmax⟩ :=
    exists_maximal_chain hq fuel s hgrowth
  refine ⟨n, hn, t, hchain, ?_,
    hchain.density_bound hq, hchain.rank_bound, hchain.card_bound⟩
  intro hBad
  exact hmax (hbad t hBad)

/-- The per-stage loss used in the quantitative iteration. -/
def eleventhPowerStepCost (K : ℝ) (L : ℕ) : ℝ :=
  K * ((L + 1 : ℕ) : ℝ) ^ 11

/-- The accumulated size loss after `L + 1` stages. -/
def twelfthPowerSizeCost (K : ℝ) (L : ℕ) : ℝ :=
  K * ((L + 1 : ℕ) : ℝ) ^ 12

/-- Twelfth-power loss when `m` increment steps are allowed for each dyadic
density unit. -/
def twelfthPowerSizeCostWithMultiplier (K : ℝ) (m L : ℕ) : ℝ :=
  (m : ℝ) * K * ((L + 1 : ℕ) : ℝ) ^ 12

/-- The dyadic scale condition on the initial relative density. -/
def OnDyadicScale (L : ℕ) (density : ℝ) : Prop :=
  1 / (2 : ℝ) ^ L ≤ density

private lemma dyadic_growth {L : ℕ} {s : RegularRestriction G}
    (hscale : OnDyadicScale L s.density) :
    1 < (2 : ℝ) ^ (L + 1) * s.density := by
  have hp : 0 < (2 : ℝ) ^ L := pow_pos (by norm_num) _
  have hfactor : 0 ≤ (2 : ℝ) ^ (L + 1) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hscale hfactor
  have heq : (2 : ℝ) ^ (L + 1) * (1 / (2 : ℝ) ^ L) = 2 := by
    rw [pow_succ]
    field_simp
  calc
    1 < (2 : ℝ) := by norm_num
    _ = (2 : ℝ) ^ (L + 1) * (1 / (2 : ℝ) ^ L) := heq.symm
    _ ≤ (2 : ℝ) ^ (L + 1) * s.density := hmul

private lemma accumulated_size_le_twelfth {K : ℝ} {L n : ℕ}
    (hK : 0 ≤ K) (hn : n ≤ L + 1) :
    (n : ℝ) * eleventhPowerStepCost K L ≤ twelfthPowerSizeCost K L := by
  have hnR : (n : ℝ) ≤ (L + 1 : ℕ) := by exact_mod_cast hn
  have hstep : 0 ≤ eleventhPowerStepCost K L := by
    exact mul_nonneg hK (pow_nonneg (by positivity) _)
  calc
    (n : ℝ) * eleventhPowerStepCost K L ≤
        ((L + 1 : ℕ) : ℝ) * eleventhPowerStepCost K L :=
      mul_le_mul_of_nonneg_right hnR hstep
    _ = twelfthPowerSizeCost K L := by
      simp only [eleventhPowerStepCost, twelfthPowerSizeCost]
      ring

private lemma fixed_factor_growth {q : ℝ} {m L : ℕ}
    {s : RegularRestriction G} (hq : 0 ≤ q) (hqm : (2 : ℝ) ≤ q ^ m)
    (hscale : OnDyadicScale L s.density) :
    1 < q ^ (m * (L + 1)) * s.density := by
  have hpow : (2 : ℝ) ^ (L + 1) ≤ (q ^ m) ^ (L + 1) :=
    pow_le_pow_left₀ (by positivity) hqm (L + 1)
  have hpow' : (2 : ℝ) ^ (L + 1) ≤ q ^ (m * (L + 1)) := by
    simpa [pow_mul] using hpow
  have hmul := mul_le_mul hpow' hscale
    (by positivity : 0 ≤ 1 / (2 : ℝ) ^ L)
    (pow_nonneg hq (m * (L + 1)))
  have heq : (2 : ℝ) ^ (L + 1) * (1 / (2 : ℝ) ^ L) = 2 := by
    rw [pow_succ]
    field_simp
  calc
    1 < (2 : ℝ) := by norm_num
    _ = (2 : ℝ) ^ (L + 1) * (1 / (2 : ℝ) ^ L) := heq.symm
    _ ≤ q ^ (m * (L + 1)) * s.density := hmul

private lemma accumulated_size_le_twelfth_withMultiplier
    {K : ℝ} {m L n : ℕ} (hK : 0 ≤ K) (hn : n ≤ m * (L + 1)) :
    (n : ℝ) * eleventhPowerStepCost K L ≤
      twelfthPowerSizeCostWithMultiplier K m L := by
  have hnR : (n : ℝ) ≤ (m * (L + 1) : ℕ) := by exact_mod_cast hn
  have hstep : 0 ≤ eleventhPowerStepCost K L := by
    exact mul_nonneg hK (pow_nonneg (by positivity) _)
  calc
    (n : ℝ) * eleventhPowerStepCost K L ≤
        ((m * (L + 1) : ℕ) : ℝ) * eleventhPowerStepCost K L :=
      mul_le_mul_of_nonneg_right hnR hstep
    _ = twelfthPowerSizeCostWithMultiplier K m L := by
      simp only [eleventhPowerStepCost, twelfthPowerSizeCostWithMultiplier]
      push_cast
      ring

/-- **Regular-Bohr stopping with twelfth-power cost.**

Suppose the initial relative density is at least `2⁻ᴸ`.  If every bad node
produces a density-doubling restriction, with rank cost `rankCost` and
logarithmic size cost at most `K(L+1)^11`, then after at most `L+1` actual
regular-Bohr restrictions the bad alternative fails.  The final ambient
carrier has size at least

`exp (-K(L+1)^12) * |ambient_initial|`.

No numerical state is synthesized in this theorem: the returned `t` contains
the final Bohr datum, regularity proof, subset, and containment proof. -/
theorem exists_stopping_restriction_twelfth
    {Bad : RegularRestriction G → Prop}
    {K : ℝ} {L rankCost : ℕ}
    (hK : 0 ≤ K)
    (hbad : ProducesIncrement Bad 2 rankCost
      (eleventhPowerStepCost K L))
    (s : RegularRestriction G)
    (hscale : OnDyadicScale L s.density) :
    ∃ n ≤ L + 1, ∃ t : RegularRestriction G,
      ControlledChain 2 rankCost (eleventhPowerStepCost K L) n s t ∧
      ¬ Bad t ∧
      (2 : ℝ) ^ n * s.density ≤ t.density ∧
      t.rank ≤ s.rank + (L + 1) * rankCost ∧
      Real.exp (-(twelfthPowerSizeCost K L)) * (s.card : ℝ) ≤
        (t.card : ℝ) := by
  obtain ⟨n, hn, t, hchain, hnotBad, hdensity, hrank, hcard⟩ :=
    exists_stopping_chain (q := (2 : ℝ)) (rankCost := rankCost)
      (sizeCost := eleventhPowerStepCost K L) (by norm_num) hbad
      (L + 1) s (dyadic_growth hscale)
  refine ⟨n, hn, t, hchain, hnotBad, hdensity, ?_, ?_⟩
  · exact hrank.trans (Nat.add_le_add_left (Nat.mul_le_mul_right rankCost hn) s.rank)
  · have hcost := accumulated_size_le_twelfth hK hn
    have hexp :
        Real.exp (-(twelfthPowerSizeCost K L)) ≤
          Real.exp (-(n : ℝ) * eleventhPowerStepCost K L) :=
      Real.exp_le_exp.mpr (by
        nlinarith only [hcost])
    exact (mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg s.card)).trans hcard

/-- **Fixed-factor regular-Bohr stopping.**

This is the form used when the analytic density increment is by a fixed
factor `q > 1` rather than by two.  An integer `m` with `2 ≤ q^m` lets `m`
increment steps pay for one dyadic density unit.  Thus the chain has length
at most `m(L+1)`, its rank grows by at most that many copies of `rankCost`,
and its total size loss is `m * K * (L+1)^12`. -/
theorem exists_stopping_restriction_fixedFactor
    {Bad : RegularRestriction G → Prop}
    {q K : ℝ} {m L rankCost : ℕ}
    (hq : 0 ≤ q) (hqm : (2 : ℝ) ≤ q ^ m) (hK : 0 ≤ K)
    (hbad : ProducesIncrement Bad q rankCost
      (eleventhPowerStepCost K L))
    (s : RegularRestriction G) (hscale : OnDyadicScale L s.density) :
    ∃ n ≤ m * (L + 1), ∃ t : RegularRestriction G,
      ControlledChain q rankCost (eleventhPowerStepCost K L) n s t ∧
      ¬ Bad t ∧
      q ^ n * s.density ≤ t.density ∧
      t.rank ≤ s.rank + (m * (L + 1)) * rankCost ∧
      Real.exp (-(twelfthPowerSizeCostWithMultiplier K m L)) *
          (s.card : ℝ) ≤ (t.card : ℝ) := by
  obtain ⟨n, hn, t, hchain, hnotBad, hdensity, hrank, hcard⟩ :=
    exists_stopping_chain (q := q) (rankCost := rankCost)
      (sizeCost := eleventhPowerStepCost K L) hq hbad
      (m * (L + 1)) s (fixed_factor_growth hq hqm hscale)
  refine ⟨n, hn, t, hchain, hnotBad, hdensity, ?_, ?_⟩
  · exact hrank.trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right rankCost hn) s.rank)
  · have hcost := accumulated_size_le_twelfth_withMultiplier hK hn
    have hexp :
        Real.exp (-(twelfthPowerSizeCostWithMultiplier K m L)) ≤
          Real.exp (-(n : ℝ) * eleventhPowerStepCost K L) :=
      Real.exp_le_exp.mpr (by nlinarith only [hcost])
    exact (mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg s.card)).trans hcard

#print axioms RegularRestriction.density_le_one
#print axioms ControlledChain.card_bound
#print axioms exists_maximal_chain
#print axioms exists_stopping_restriction_twelfth
#print axioms exists_stopping_restriction_fixedFactor

end

end Erdos140.BohrStopping
