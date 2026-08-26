import Mathlib

namespace Erdos327

/-- The positive interval `{1, ..., N}`. -/
def upto (N : ℕ) : Finset ℕ := Finset.Icc 1 N

@[simp] theorem mem_upto {N n : ℕ} :
    n ∈ upto N ↔ 1 ≤ n ∧ n ≤ N := by
  simp [upto]

/-- Two distinct integers conflict for the first part of Erdős Problem 327. -/
def ConflictOne (a b : ℕ) : Prop :=
  a + b ∣ a * b

/-- The corresponding conflict for the `2ab` variant. -/
def ConflictTwo (a b : ℕ) : Prop :=
  a + b ∣ 2 * a * b

/-- The cancelled odd-even conflict relation used by the mixed-coordinate
parametrization: `a` is the odd endpoint and `2b` the even endpoint. -/
def MixedConflict (a b : ℕ) : Prop :=
  a + 2 * b ∣ a * b

/-- A finite set has no first-variant conflict between distinct members. -/
def OneAdmissible (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ ConflictOne a b

/-- A finite set has no second-variant conflict between distinct members. -/
def TwoAdmissible (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ ConflictTwo a b

/-- The asymptotic conclusion answering the first question of Erdős Problem 327. -/
def Erdos327Conclusion : Prop :=
  ∃ ε : ℝ, 0 < ε ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ A : Finset ℕ,
        A ⊆ upto N ∧
        OneAdmissible A ∧
        (1 / 2 + ε) * (N : ℝ) ≤ (A.card : ℝ)

/-- The positive-density conclusion for the second (`2ab`) question in
Erdős Problem 327. -/
def Erdos327SecondConclusion : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ A : Finset ℕ,
        A ⊆ upto N ∧
        TwoAdmissible A ∧
        c * (N : ℝ) ≤ (A.card : ℝ)

/-- Both asymptotic conclusions in Erdős Problem 327. -/
def Erdos327FullConclusion : Prop :=
  Erdos327Conclusion ∧ Erdos327SecondConclusion

/-- The even-endpoint form proved by the construction in the paper. -/
def EvenEndpointConclusion : Prop :=
  ∃ η : ℝ, 0 < η ∧
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∃ A : Finset ℕ,
        A ⊆ upto (2 * N) ∧
        OneAdmissible A ∧
        (1 + η) * (N : ℝ) ≤ (A.card : ℝ)

end Erdos327
