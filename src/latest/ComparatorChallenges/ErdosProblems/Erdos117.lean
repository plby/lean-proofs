import Mathlib

universe u u_2 u_3

open Filter Asymptotics
open scoped Topology

namespace Erdos117

def NoncommutingBound (G : Type u_2) [Group G] (n : ℕ) : Prop :=
  ∀ s : Finset G, (s : Set G).Pairwise (fun x y => ¬ Commute x y) → s.card ≤ n

def AbelianCover (G : Type u_2) [Group G] (ι : Type u_3) (A : ι → Subgroup G) : Prop :=
  (∀ i, IsMulCommutative (A i)) ∧ ∀ x : G, ∃ i, x ∈ A i

def HasAbelianCover (G : Type u_2) [Group G] (k : ℕ) : Prop :=
  ∃ A : Fin k → Subgroup G, AbelianCover G (Fin k) A

def UniversalAbelianCoverBound (n k : ℕ) : Prop :=
  ∀ (G : Type u) [Group G], NoncommutingBound G n → HasAbelianCover G k

noncomputable def h (n : ℕ) : ℕ∞ :=
  ⨅ k : {k : ℕ // UniversalAbelianCoverBound.{u} n k}, (k.1 : ℕ∞)

theorem erdos_117 :
    (∀ n : ℕ, h.{u} n < ⊤) ∧
    (∀ n : ℕ, 1 ≤ n → (2 ^ ((n - 1) / 2) : ℕ∞) ≤ h.{u} n) ∧
    ((fun n : ℕ => Real.log (h.{u} n).toNat / Real.log 2 - (n : ℝ) / 2) =O[atTop]
      (fun n : ℕ => Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3)) ∧
    Tendsto (fun n : ℕ => ((h.{u} n).toNat : ℝ) ^ (1 / (n : ℝ))) atTop
      (𝓝 (Real.sqrt 2)) := by
  sorry

end Erdos117
