/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset

namespace Erdos297

noncomputable def selectionProbability (lam x : ℝ) : ℝ :=
  if x = 0 then 0 else 1 / (1 + Real.exp (lam / x))

noncomputable def momentKernel (lam x : ℝ) : ℝ :=
  if x = 0 then 0 else selectionProbability lam x / x

noncomputable def moment (lam : ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, momentKernel lam x

def IsCriticalParameter (lam : ℝ) : Prop :=
  0 < lam ∧ moment lam = 1

def IsUniqueCriticalParameter (lam : ℝ) : Prop :=
  IsCriticalParameter lam ∧ ∀ μ, IsCriticalParameter μ → μ = lam

def denominators (N : ℕ) : Finset ℕ := Icc 1 N

end Erdos297

namespace UnitFractions

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

end UnitFractions

namespace Erdos297

def representations (N : ℕ) : Finset (Finset ℕ) :=
  (denominators N).powerset.filter fun A ↦ UnitFractions.rec_sum A = 1

def count (N : ℕ) : ℕ := (representations N).card

noncomputable def logGrowth (N : ℕ) : ℝ := Real.log (count N : ℝ) / N

noncomputable def freeEnergyKernel (lam x : ℝ) : ℝ :=
  if x = 0 then 0 else Real.log (1 + Real.exp (-lam / x))

noncomputable def gamma (lam : ℝ) : ℝ :=
  lam + ∫ x in Set.Icc (0 : ℝ) 1, freeEnergyKernel lam x

theorem erdos_297 :
    ∃ lam : ℝ, Erdos297.IsUniqueCriticalParameter lam ∧
      Filter.Tendsto Erdos297.logGrowth Filter.atTop (nhds (Erdos297.gamma lam)) := by
  sorry

end Erdos297
