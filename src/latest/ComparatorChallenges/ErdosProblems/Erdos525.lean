import Mathlib

open scoped Topology
open Asymptotics Filter

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos525

noncomputable def uniformProbability {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / Fintype.card Ω

end Erdos525

namespace Erdos525

abbrev SignVector (N : ℕ) := Fin (N + 1) → Bool

end Erdos525

namespace Erdos525

def sign (b : Bool) : ℝ := if b then 1 else -1

end Erdos525

namespace Erdos525

def littlewoodEval {N : ℕ} (ε : SignVector N) (z : ℂ) : ℂ :=
  ∑ j, (sign (ε j) : ℂ) * z ^ (j : ℕ)

end Erdos525

namespace Erdos525

def unitCircle : Set ℂ := Metric.sphere 0 1

end Erdos525

namespace Erdos525

def modulusRange {N : ℕ} (ε : SignVector N) : Set ℝ :=
  (fun z : ℂ ↦ ‖littlewoodEval ε z‖) '' unitCircle

end Erdos525

namespace Erdos525

noncomputable def minModulus {N : ℕ} (ε : SignVector N) : ℝ :=
  sInf (modulusRange ε)

end Erdos525

namespace Erdos525

noncomputable def minimumTail (N : ℕ) (τ : ℝ) : ℝ :=
  uniformProbability (fun ε : SignVector N ↦ τ / Real.sqrt N < minModulus ε)

end Erdos525

namespace Erdos525

noncomputable def rate : ℝ := Real.sqrt (Real.pi / 12)

end Erdos525

namespace Erdos525

noncomputable def exceptionalFamily (N : ℕ) : Finset (SignVector N) :=
  Finset.univ.filter fun ε ↦ 1 ≤ minModulus ε

end Erdos525

namespace Erdos525

def HasSmallValue {N : ℕ} (ε : SignVector N) : Prop :=
  ∃ z : ℂ, ‖z‖ = 1 ∧ ‖littlewoodEval ε z‖ < 1

end Erdos525

namespace Erdos525

theorem erdos_525_resolution :
    (∀ τ : ℝ, 0 < τ →
      Tendsto (fun N : ℕ ↦ minimumTail N τ) atTop
        (𝓝 (Real.exp (-rate * τ)))) ∧
    IsLittleO atTop
      (fun N : ℕ ↦ ((exceptionalFamily N).card : ℝ))
      (fun N : ℕ ↦ (2 : ℝ) ^ N) ∧
    Tendsto
      (fun N : ℕ ↦
        uniformProbability (fun ε : SignVector N ↦ HasSmallValue ε))
      atTop (𝓝 1) := by
  sorry

end Erdos525

end
