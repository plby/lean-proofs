import Mathlib

namespace Erdos38

open scoped Pointwise
open Finset Real Filter

attribute [local instance] Classical.propDecidable

noncomputable section

def countIn (A : Set ℕ) (N : ℕ) : ℕ :=
  #{a ∈ Ioc 0 N | a ∈ A}

def hSumset : ℕ → Set ℕ → Set ℕ
  | 0, _ => {0}
  | h + 1, B => hSumset h B + B

def IsAdditiveBasis (B : Set ℕ) : Prop :=
  ∃ h : ℕ, ∀ᶠ n in Filter.atTop, n ∈ hSumset h B

def translateSet (A : Set ℕ) (b : ℕ) : Set ℕ := (· + b) '' A

def unionTranslateCount (A : Set ℕ) (b : ℕ) (N : ℕ) : ℕ :=
  countIn (A ∪ translateSet A b) N
end

section CountIn

end CountIn

section SchnirelmannProps

end SchnirelmannProps

section ErdosF

end ErdosF

noncomputable section

end

noncomputable section

end

noncomputable section

end

noncomputable section

end

noncomputable section

end

noncomputable section

end

noncomputable section

end

end Erdos38

attribute [local instance] Classical.propDecidable

open scoped BigOperators Pointwise
open Finset Real Filter

namespace Erdos38

theorem erdos_problem_38 :
    ∃ (B : Set ℕ) (f : ℝ → ℝ),
      ¬IsAdditiveBasis B ∧
        (∀ α : ℝ, 0 < α → α < 1 → 0 < f α) ∧
          ∀ (A : Set ℕ),
            0 < schnirelmannDensity A →
            schnirelmannDensity A < 1 →
            ∀ (N : ℕ), 0 < N → ∃ b ∈ B,
              (schnirelmannDensity A + f (schnirelmannDensity A)) * ↑N ≤
                (unionTranslateCount A b N : ℝ) := by
  sorry

end Erdos38
