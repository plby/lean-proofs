/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import Mathlib

/-!
# Erdős 730: positive lower density implies the upstream infinitude target

This module contains only the general density-to-infinitude bridge.  It does
not assume or claim the analytic positive-density estimate for the explicit
four-linear-form family.
-/

open Filter
open scoped Topology

namespace Erdos730.FullDensity

/-- Number of parameters in `[1, X]` satisfying `good`. -/
def parameterCount (good : ℕ → Prop) [DecidablePred good] (X : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter good).card

/-- The exact positive-density surface claimed by the supplied proof, with a
generic parameter predicate. -/
def HasCandidatePositiveDensity (good : ℕ → Prop) [DecidablePred good] : Prop :=
  (107 : ℝ) / 2500 <
    liminf (fun X : ℕ => (parameterCount good X : ℝ) / X) atTop

/-- A positive lower density at the candidate's explicit constant forces
infinitely many good parameters. -/
theorem parameterSet_infinite_of_candidatePositiveDensity
    (good : ℕ → Prop) [DecidablePred good]
    (h : HasCandidatePositiveDensity good) :
    Set.Infinite {x : ℕ | good x} := by
  intro hfinite
  let C : ℕ := hfinite.toFinset.card
  have hcount (X : ℕ) : parameterCount good X ≤ C := by
    simp only [parameterCount, C]
    exact Finset.card_le_card (by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_Icc] at hx
      simpa using hx.2)
  have hbounded : IsBoundedUnder (· ≥ ·) atTop
      (fun X : ℕ => (parameterCount good X : ℝ) / X) := by
    change ∃ b : ℝ, ∀ᶠ X : ℕ in atTop,
      b ≤ (parameterCount good X : ℝ) / X
    refine ⟨0, Eventually.of_forall (fun X : ℕ => ?_)⟩
    exact div_nonneg (by positivity : (0 : ℝ) ≤ parameterCount good X)
      (by positivity : (0 : ℝ) ≤ X)
  have hevent : ∀ᶠ X : ℕ in atTop,
      (107 : ℝ) / 2500 < (parameterCount good X : ℝ) / X :=
    eventually_lt_of_lt_liminf h hbounded
  have hlarge : ∀ᶠ X : ℕ in atTop, C * 2500 < 107 * X := by
    exact eventually_atTop.2 ⟨C * 2500 + 1, fun X hX => by omega⟩
  obtain ⟨X, hratio, hCX, hX⟩ :=
    (hevent.and (hlarge.and (eventually_gt_atTop 0))).exists
  have hcast : (parameterCount good X : ℝ) ≤ C := by
    exact_mod_cast hcount X
  have hden : (0 : ℝ) < X := by
    exact_mod_cast hX
  have hupper : (parameterCount good X : ℝ) / X ≤ C / X :=
    div_le_div_of_nonneg_right hcast hden.le
  have hsmall : (C : ℝ) / X < (107 : ℝ) / 2500 := by
    rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 2500)]
    exact_mod_cast hCX
  linarith

/-- If an injective explicit family maps every good parameter into a target
set, the candidate positive-density estimate proves that target infinite. -/
theorem target_infinite_of_candidatePositiveDensity
    (good : ℕ → Prop) [DecidablePred good]
    {α : Type*} (family : ℕ → α) (target : Set α)
    (h : HasCandidatePositiveDensity good)
    (hinj : Function.Injective family)
    (hmaps : ∀ x, good x → family x ∈ target) :
    target.Infinite := by
  have hgood : Set.Infinite {x : ℕ | good x} :=
    parameterSet_infinite_of_candidatePositiveDensity good h
  have himage : Set.Infinite (family '' {x : ℕ | good x}) :=
    hgood.image hinj.injOn
  exact himage.mono (by
    rintro y ⟨x, hx, rfl⟩
    exact hmaps x hx)

#print axioms parameterSet_infinite_of_candidatePositiveDensity
#print axioms target_infinite_of_candidatePositiveDensity

end Erdos730.FullDensity
