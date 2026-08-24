import Mathlib

open scoped BigOperators

namespace Erdos360

abbrev BelowTarget (n : ℕ) := {x : ℕ // x ∈ Finset.Ico 1 n}

def Monochromatic {n r : ℕ} (c : BelowTarget n → Fin r)
    (A : Finset (BelowTarget n)) : Prop :=
  ∀ ⦃x⦄, x ∈ A → ∀ ⦃y⦄, y ∈ A → c x = c y

def AvoidsTarget (n r : ℕ) (c : BelowTarget n → Fin r) : Prop :=
  ∀ A : Finset (BelowTarget n), Monochromatic c A →
    A.sum (fun x ↦ x.1) ≠ n

def Colorable (n r : ℕ) : Prop :=
  ∃ c : BelowTarget n → Fin r, AvoidsTarget n r c

lemma exists_colorable {n : ℕ} (hn : 0 < n) : ∃ r, Colorable n r := by
  sorry

noncomputable def f (n : ℕ) : ℕ := by
  classical
  exact if hn : n = 0 then 0 else Nat.find (exists_colorable (Nat.pos_of_ne_zero hn))

noncomputable def resolutionScale (n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) (1 / 3 : ℝ) *
      ((n : ℝ) / (Nat.totient n : ℝ)) /
    (Real.rpow (Real.log n) (1 / 3 : ℝ) *
      Real.rpow (Real.log (Real.log n)) (2 / 3 : ℝ))

theorem erdos_360 :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        c * resolutionScale n ≤ (f n : ℝ) ∧
          (f n : ℝ) ≤ C * resolutionScale n := by
  sorry

end Erdos360
