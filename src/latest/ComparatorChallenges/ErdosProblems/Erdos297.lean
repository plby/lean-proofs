import Mathlib

open Filter Finset
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Erdos297

def selectionProbability (lam x : ℝ) : ℝ :=
  if x = 0 then 0 else 1 / (1 + Real.exp (lam / x))

end Erdos297

namespace Erdos297

def momentKernel (lam x : ℝ) : ℝ :=
  if x = 0 then 0 else selectionProbability lam x / x

end Erdos297

namespace Erdos297

def moment (lam : ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, momentKernel lam x

end Erdos297

namespace Erdos297

def IsCriticalParameter (lam : ℝ) : Prop :=
  0 < lam ∧ moment lam = 1

end Erdos297

namespace Erdos297

def IsUniqueCriticalParameter (lam : ℝ) : Prop :=
  IsCriticalParameter lam ∧ ∀ μ, IsCriticalParameter μ → μ = lam

end Erdos297

namespace Erdos297

def denominators (N : ℕ) : Finset ℕ := Icc 1 N

end Erdos297

namespace UnitFractions

def rec_sum (A : Finset ℕ) : ℚ := A.sum fun n ↦ (1 : ℚ) / n

end UnitFractions

namespace Erdos297

def representations (N : ℕ) : Finset (Finset ℕ) :=
  (denominators N).powerset.filter fun A ↦ UnitFractions.rec_sum A = 1

end Erdos297

namespace Erdos297

def count (N : ℕ) : ℕ := (representations N).card

end Erdos297

namespace Erdos297

def logGrowth (N : ℕ) : ℝ := Real.log (count N : ℝ) / N

end Erdos297

namespace Erdos297

def freeEnergyKernel (lam x : ℝ) : ℝ :=
  if x = 0 then 0 else Real.log (1 + Real.exp (-lam / x))

end Erdos297

namespace Erdos297

def gamma (lam : ℝ) : ℝ :=
  lam + ∫ x in Set.Icc (0 : ℝ) 1, freeEnergyKernel lam x

end Erdos297

namespace Erdos297

def NaturalLogResolution : Prop :=
  ∃ lam : ℝ, IsUniqueCriticalParameter lam ∧
    Tendsto logGrowth atTop (𝓝 (gamma lam))

end Erdos297

namespace Erdos297

theorem erdos_297 : NaturalLogResolution := by
  sorry

end Erdos297

end
