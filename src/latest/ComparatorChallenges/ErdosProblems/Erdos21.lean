/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset Filter
open Equiv

noncomputable section


namespace Erdos21

open scoped Classical in
def IsUniform {α : Type*} [DecidableEq α]
    (n : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, A.card = n

end Erdos21

namespace Erdos21

open scoped Classical in
def IsIntersecting {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, (A ∩ B).Nonempty

end Erdos21

namespace Erdos21

open scoped Classical in
def AvoidsAllSmallSets {α : Type*} [DecidableEq α]
    (n : ℕ) (F : Finset (Finset α)) : Prop :=
  ∀ S : Finset α, S.card ≤ n - 1 → ∃ A ∈ F, Disjoint S A

end Erdos21

namespace Erdos21

open scoped Classical in
def IsErdosLovaszFamily {α : Type*} [DecidableEq α]
    (n : ℕ) (F : Finset (Finset α)) : Prop :=
  IsUniform n F ∧ IsIntersecting F ∧ AvoidsAllSmallSets n F

end Erdos21

namespace Erdos21

open scoped Classical in
noncomputable def erdosLovaszF (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ F : Finset (Finset ℕ), IsErdosLovaszFamily n F ∧ F.card = m}

end Erdos21

namespace Erdos21

open scoped Classical in
def Erdos21Question : Prop :=
  ∃ C N : ℕ, ∀ n : ℕ, N ≤ n → erdosLovaszF n ≤ C * n

end Erdos21

namespace Erdos21

open scoped Classical in
theorem erdos_21 : Erdos21Question := by
  sorry

end Erdos21

end
