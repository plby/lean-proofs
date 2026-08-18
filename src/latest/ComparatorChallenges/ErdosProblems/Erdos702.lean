import Mathlib

open Finset
open Asymptotics Filter
open scoped BigOperators
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos702

def IsUniform {n : ℕ} (k : ℕ) (𝓕 : Finset (Finset (Fin n))) : Prop :=
  ∀ A ∈ 𝓕, A.card = k

end Erdos702

namespace Erdos702

def HasSingletonIntersection {n : ℕ} (𝓕 : Finset (Finset (Fin n))) : Prop :=
  ∃ A ∈ 𝓕, ∃ B ∈ 𝓕, (A ∩ B).card = 1

end Erdos702

namespace Erdos702

def AllNStatement : Prop :=
  ∀ (n k : ℕ) (𝓕 : Finset (Finset (Fin n))),
    4 ≤ k →
    IsUniform k 𝓕 →
    Nat.choose (n - 2) (k - 2) < 𝓕.card →
    HasSingletonIntersection 𝓕

end Erdos702

namespace Erdos702

def twoStarBound (n k : ℕ) : ℕ := Nat.choose (n - 2) (k - 2)

end Erdos702

namespace Erdos702

def EventualStatement : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
    ∀ 𝓕 : Finset (Finset (Fin n)),
      IsUniform k 𝓕 →
      twoStarBound n k < 𝓕.card →
      HasSingletonIntersection 𝓕

end Erdos702

namespace Erdos702

theorem erdos_702_all_n_false : ¬ AllNStatement := by
  sorry

end Erdos702

namespace Erdos702

theorem erdos_702_eventually : EventualStatement := by
  sorry

end Erdos702

end
