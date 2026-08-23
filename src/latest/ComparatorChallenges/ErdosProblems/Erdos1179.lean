import Mathlib

open Filter
open scoped BigOperators Topology

noncomputable section


namespace Erdos1179

variable {G : Type*} [AddCommGroup G] [Fintype G]

open scoped Classical in
def subsetSum (S : Finset G) : G := ∑ x ∈ S, x

end Erdos1179

namespace Erdos1179

variable {G : Type*} [AddCommGroup G] [Fintype G]

open scoped Classical in
noncomputable def setRepCount (A : Finset G) (g : G) : ℕ := by
  classical
  exact (A.powerset.filter fun S ↦ subsetSum S = g).card

end Erdos1179

namespace Erdos1179

variable {G : Type*} [AddCommGroup G] [Fintype G]

open scoped Classical in
def SetBalanced (ε : ℝ) (A : Finset G) : Prop :=
  ∀ g : G,
    |(setRepCount A g : ℝ) - (2 : ℝ) ^ A.card / Fintype.card G| ≤
      ε * ((2 : ℝ) ^ A.card / Fintype.card G)

end Erdos1179

namespace Erdos1179

open scoped Classical in
def hallLength (q t n : ℕ) : ℕ := q + 8 * t + n * (2 * t)

end Erdos1179

namespace Erdos1179

open scoped Classical in
def hallQ (N : ℕ) : ℕ := Nat.log 2 N

end Erdos1179

namespace Erdos1179

open scoped Classical in
def hallM (N : ℕ) : ℕ := Nat.clog 2 (hallQ N)

end Erdos1179

namespace Erdos1179

open scoped Classical in
noncomputable def hallBlock (N : ℕ) : ℕ :=
  ⌈(4 : ℝ) * hallQ N / hallM N⌉₊

end Erdos1179

namespace Erdos1179

open scoped Classical in
def hallRounds (N : ℕ) : ℕ := Nat.sqrt (hallM N) + 1

end Erdos1179

namespace Erdos1179

open scoped Classical in
noncomputable def erdos1179Size (N : ℕ) : ℕ :=
  hallLength (hallQ N) (hallBlock N) (hallRounds N)

end Erdos1179

namespace Erdos1179

variable {G : Type*} [AddCommGroup G] [Fintype G]

open scoped Classical in
noncomputable def uniformProbability {Ω : Type*} [Fintype Ω]
    (P : Ω → Prop) : ℝ :=
  (Nat.card {ω // P ω} : ℝ) / Fintype.card Ω

end Erdos1179

namespace Erdos1179

variable {G : Type*} [AddCommGroup G] [Fintype G]

open scoped Classical in
abbrev KSubsets (G : Type*) [Fintype G] (k : ℕ) :=
  {A : Finset G // A.card = k}

end Erdos1179

namespace Erdos1179

variable {G : Type*} [AddCommGroup G] [Fintype G]

open scoped Classical in
noncomputable def subsetSuccessProbability (ε : ℝ) (k : ℕ) : ℝ :=
  uniformProbability (fun A : KSubsets G k ↦ SetBalanced ε A.1)

end Erdos1179

namespace Erdos1179

open scoped Classical in
theorem erdos1179 :
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

end
