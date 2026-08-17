import Mathlib

open scoped BigOperators Pointwise Combinatorics.Additive
open Finset
open Filter Topology Asymptotics Real

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos1180

def AdmissibleDenom (ε : ℝ) (p n : ℕ) : Prop :=
  0 < n ∧ (n : ℝ) ≤ (p : ℝ) ^ ε ∧ Nat.Coprime n p

end Erdos1180

namespace Erdos1180

def Represents (ε : ℝ) (p : ℕ) (a : ZMod p) (xs : List ℕ) : Prop :=
  (∀ n ∈ xs, AdmissibleDenom ε p n) ∧
    (List.map (fun n : ℕ ↦ ((n : ZMod p)⁻¹)) xs).sum = a

end Erdos1180

namespace Erdos1180

def Erdos1180Claim : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℕ, ∀ p : ℕ, p.Prime → ∀ a : ZMod p,
    ∃ xs : List ℕ, xs.length ≤ C ∧ Represents ε p a xs

end Erdos1180

namespace Erdos1180

theorem erdos_1180 : Erdos1180Claim := by
  sorry

end Erdos1180

end
