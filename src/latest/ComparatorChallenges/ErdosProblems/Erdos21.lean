import Mathlib

open Finset Filter
open Equiv

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos21

def IsUniform {α : Type*} [DecidableEq α]
    (n : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, A.card = n

end Erdos21

namespace Erdos21

def IsIntersecting {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty

end Erdos21

namespace Erdos21

def AvoidsAllSmallSets {α : Type*} [DecidableEq α]
    (n : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ S : Finset α, S.card ≤ n - 1 → ∃ A ∈ F, Disjoint S A

end Erdos21

namespace Erdos21

def IsErdosLovaszFamily {α : Type*} [DecidableEq α]
    (n : ℕ) (F : Finset (Finset α)) : Prop :=
  IsUniform n F ∧ IsIntersecting F ∧ AvoidsAllSmallSets n F

end Erdos21

namespace Erdos21

noncomputable def erdosLovaszF (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ F : Finset (Finset ℕ), IsErdosLovaszFamily n F ∧ F.card = m}

end Erdos21

namespace Erdos21

def Erdos21Question : Prop :=
  ∃ C N : ℕ, ∀ n : ℕ, N ≤ n → erdosLovaszF n ≤ C * n

end Erdos21

namespace Erdos21

theorem erdos_21 : Erdos21Question := by
  sorry

end Erdos21

end
