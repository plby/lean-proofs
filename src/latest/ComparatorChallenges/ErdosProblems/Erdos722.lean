import Mathlib

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos722

def IsAdmissible (n k r : ℕ) : Prop :=
  ∀ i < r, Nat.choose (k - i) (r - i) ∣ Nat.choose (n - i) (r - i)

end Erdos722

namespace Erdos722

structure SeparatedReserveFocusingFamily (n k r : ℕ)
    (reserve host : Finset (Finset (Fin n))) where
  block : Finset (Fin n) → Finset (Fin n)
  block_card : ∀ e ∈ reserve, (block e).card = k
  root_subset : ∀ e ∈ reserve, e ⊆ block e
  spill_subset : ∀ e ∈ reserve,
    (block e).powersetCard r \ {e} ⊆ host
  reserve_unique : ∀ e ∈ reserve, ∀ g ∈ reserve,
    g ⊆ block e → g = e
  spill_pairwise : ∀ e ∈ reserve, ∀ e' ∈ reserve, e ≠ e' →
    Disjoint ((block e).powersetCard r \ {e})
      ((block e').powersetCard r \ {e'})

end Erdos722

namespace Erdos722

noncomputable def SeparatedReserveFocusingFamily.blocks
    {n k r : ℕ} {reserve host : Finset (Finset (Fin n))}
    (F : SeparatedReserveFocusingFamily n k r reserve host) :
    Finset (Finset (Fin n)) := by
  classical
  exact reserve.image F.block

end Erdos722

namespace Erdos722

def IsSteinerSystem (n k r : ℕ) (blocks : Finset (Finset (Fin n))) : Prop :=
  (∀ B ∈ blocks, B.card = k) ∧
    ∀ A ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      (blocks.filter fun B ↦ A ⊆ B).card = 1

end Erdos722

namespace Erdos722

def Resolution : Prop :=
  ∀ k r : ℕ, 0 < r → r < k →
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → IsAdmissible n k r →
      ∃ blocks : Finset (Finset (Fin n)), IsSteinerSystem n k r blocks

end Erdos722

namespace Erdos722

theorem erdos_722 : Resolution := by
  sorry

end Erdos722

end
