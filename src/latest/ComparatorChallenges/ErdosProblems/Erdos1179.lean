/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos1179

variable {G : Type*} [AddCommGroup G] [Fintype G]

def subsetSum (S : Finset G) : G := ∑ x ∈ S, x

noncomputable def setRepCount (A : Finset G) (g : G) : ℕ := by
  classical
  exact (A.powerset.filter fun S ↦ subsetSum S = g).card

def SetBalanced (ε : ℝ) (A : Finset G) : Prop :=
  ∀ g : G,
    |(setRepCount A g : ℝ) - (2 : ℝ) ^ A.card / Fintype.card G| ≤
      ε * ((2 : ℝ) ^ A.card / Fintype.card G)

def hallLength (q t n : ℕ) : ℕ := q + 8 * t + n * (2 * t)

def hallQ (N : ℕ) : ℕ := Nat.log 2 N

def hallM (N : ℕ) : ℕ := Nat.clog 2 (hallQ N)

noncomputable def hallBlock (N : ℕ) : ℕ :=
  ⌈(4 : ℝ) * hallQ N / hallM N⌉₊

def hallRounds (N : ℕ) : ℕ := Nat.sqrt (hallM N) + 1

noncomputable def erdos1179Size (N : ℕ) : ℕ :=
  hallLength (hallQ N) (hallBlock N) (hallRounds N)

noncomputable def uniformProbability {Ω : Type*} [Fintype Ω]
    (P : Ω → Prop) : ℝ :=
  (Nat.card {ω // P ω} : ℝ) / Fintype.card Ω

abbrev KSubsets (G : Type*) [Fintype G] (k : ℕ) :=
  {A : Finset G // A.card = k}

noncomputable def subsetSuccessProbability (ε : ℝ) (k : ℕ) : ℝ :=
  uniformProbability (fun A : KSubsets G k ↦ SetBalanced ε A.1)

theorem erdos_1179 :
    (∀ (G : Type u) [AddCommGroup G] [Fintype G] (ε : ℝ),
      0 < ε → ε < 1 → ∀ A : Finset G,
        SetBalanced ε A → Fintype.card G ≤ 2 ^ A.card) ∧
    Tendsto (fun N : ℕ ↦
      (erdos1179Size N : ℝ) / Real.logb 2 N) atTop (nhds 1) ∧
    ∀ (ε : ℝ), 0 < ε → ε < 1 →
      ∀ (G : ℕ → Type u) [∀ i, AddCommGroup (G i)] [∀ i, Fintype (G i)],
        Tendsto (fun i ↦ Fintype.card (G i)) atTop atTop →
        Tendsto (fun i ↦ subsetSuccessProbability (G := G i) ε
          (erdos1179Size (Fintype.card (G i)))) atTop (nhds 1) := by
  sorry

end Erdos1179
