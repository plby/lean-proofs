import ErdosProblems.Erdos73.CyclicAntipodalInvolution
import Mathlib.Tactic.Group

/-! The local permutation algebra of switching one pair of opposite corners per face. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {D : Type*}

def faceSwitch (τ : Equiv.Perm D) (chosen : D → Bool) (x : D) : D :=
  if chosen x then τ x else x

theorem faceSwitch_involutive (τ : Equiv.Perm D) (chosen : D → Bool)
    (hτ : Function.Involutive τ) (hchosen : ∀ x, chosen (τ x) = chosen x) :
    Function.Involutive (faceSwitch τ chosen) := by
  intro x
  cases hx : chosen x
  · simp only [faceSwitch, hx, Bool.false_eq_true, if_false]
  · simp only [faceSwitch, hx, ite_true, hchosen]
    exact hτ x

def faceSwitchPerm (τ : Equiv.Perm D) (chosen : D → Bool)
    (hτ : Function.Involutive τ) (hchosen : ∀ x, chosen (τ x) = chosen x) : Equiv.Perm D where
  toFun := faceSwitch τ chosen
  invFun := faceSwitch τ chosen
  left_inv := faceSwitch_involutive τ chosen hτ hchosen
  right_inv := faceSwitch_involutive τ chosen hτ hchosen

theorem faceSwitch_factor (α τ : Equiv.Perm D) (chosen : D → Bool)
    (hα : Function.Involutive α) (hτ : Function.Involutive τ)
    (hcomm : Function.Commute α τ) (hchosen : ∀ x, chosen (τ x) = chosen x)
    (hflip : ∀ x, chosen (α x) = !(chosen x)) :
    τ = faceSwitchPerm τ chosen hτ hchosen * α * faceSwitchPerm τ chosen hτ hchosen * α := by
  ext x
  change τ x = faceSwitch τ chosen (α (faceSwitch τ chosen (α x)))
  have hcx : α (τ (α x)) = τ x := by rw [hcomm, hα]
  cases hx : chosen x
  · have hax : chosen (α x) = true := by rw [hflip, hx]; rfl
    simp only [faceSwitch, hax, ite_true, hcx, hchosen, hx, Bool.false_eq_true, if_false]
  · have hax : chosen (α x) = false := by rw [hflip, hx]; rfl
    simp only [faceSwitch, hax, Bool.false_eq_true, if_false, hα x, hx, ite_true]

theorem commute_after_involutive_switch {Γ : Type*} [Group Γ]
    (α σ T : Γ) (hT : T * T = 1)
    (hface : σ⁻¹ * α * σ * α = T * α * T * α) : Commute α (σ * T) := by
  have hh : α * σ = σ * T * α * T := by
    have hh' : σ⁻¹ * α * σ = T * α * T := mul_right_cancel hface
    calc
      α * σ = σ * (σ⁻¹ * α * σ) := by group
      _ = σ * (T * α * T) := by rw [hh']
      _ = σ * T * α * T := by group
  change α * (σ * T) = (σ * T) * α
  calc
    α * (σ * T) = (α * σ) * T := (mul_assoc _ _ _).symm
    _ = (σ * T * α * T) * T := by rw [hh]
    _ = σ * T * α := by rw [mul_assoc, hT, mul_one]

theorem faceSwitch_commutes_with_edge_pairing (α σ τ : Equiv.Perm D) (chosen : D → Bool)
    (hα : Function.Involutive α) (hτ : Function.Involutive τ)
    (hcomm : Function.Commute α τ) (hchosen : ∀ x, chosen (τ x) = chosen x)
    (hflip : ∀ x, chosen (α x) = !(chosen x))
    (hface : σ⁻¹ * α * σ * α = τ) :
    Commute α (σ * faceSwitchPerm τ chosen hτ hchosen) := by
  apply commute_after_involutive_switch
  · ext x
    exact faceSwitch_involutive τ chosen hτ hchosen x
  · exact hface.trans (faceSwitch_factor α τ chosen hα hτ hcomm hchosen hflip)

end
end Erdos73
