import Mathlib
import Mathlib.Combinatorics.Additive.Energy

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Pointwise Combinatorics.Additive

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

private def energyNegRightEquiv :
    ((G × G) × (G × G)) ≃ ((G × G) × (G × G)) where
  toFun p := (p.1, (-p.2.2, -p.2.1))
  invFun p := (p.1, (-p.2.2, -p.2.1))
  left_inv p := by rcases p with ⟨⟨a,b⟩,⟨c,d⟩⟩; simp
  right_inv p := by rcases p with ⟨⟨a,b⟩,⟨c,d⟩⟩; simp

/-- Negating the second set does not change additive energy. -/
theorem addEnergy_neg_right (A : Finset G) :
    A.addEnergy (-A) = A.addEnergy A := by
  unfold Finset.addEnergy
  apply Finset.card_equiv (energyNegRightEquiv (G := G))
  rintro ⟨⟨a₁,a₂⟩,⟨c₁,c₂⟩⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_neg']
  constructor
  · rintro ⟨⟨haa, hc₁, hc₂⟩, heq⟩
    refine ⟨⟨haa, hc₂, hc₁⟩, ?_⟩
    calc
      a₁ + -c₂ = (a₁ + c₁) + (-c₁ + -c₂) := by abel
      _ = (a₂ + c₂) + (-c₁ + -c₂) := congrArg (fun z => z + (-c₁ + -c₂)) heq
      _ = a₂ + -c₁ := by abel
  · rintro ⟨⟨haa, hc₂, hc₁⟩, heq⟩
    refine ⟨⟨haa, hc₁, hc₂⟩, ?_⟩
    calc
      a₁ + c₁ = (a₁ + -c₂) + (c₂ + c₁) := by abel
      _ = (a₂ + -c₁) + (c₂ + c₁) := congrArg (fun z => z + (c₂ + c₁)) heq
      _ = a₂ + c₂ := by abel

end Erdos336
