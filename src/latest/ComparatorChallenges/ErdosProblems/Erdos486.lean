import Mathlib

namespace Erdos486

/-- Positive integers avoiding each residue set once its modulus is smaller. -/
def survivors (A : Set ℕ) (X : (n : A) → Set (ZMod (n : ℕ))) : Set ℕ :=
  {m | 0 < m ∧ ∀ n : A, (n : ℕ) < m → (m : ZMod (n : ℕ)) ∉ X n}

/-- The harmonic sum over members strictly below a real cutoff. -/
noncomputable def logSum (B : Set ℕ) (x : ℝ) : ℝ := by
  classical
  exact ∑ m ∈ Finset.range ⌈x⌉₊,
    if m ∈ B ∧ (m : ℝ) < x then (m : ℝ)⁻¹ else 0

noncomputable def logAverage (B : Set ℕ) (x : ℝ) : ℝ :=
  logSum B x / Real.log x

/-- One fixed infinite system has distinct lower and upper logarithmic densities. -/
theorem erdos_486_quantitative :
    ∃ (A : Set ℕ), A.Infinite ∧ 0 ∉ A ∧
      ∃ X : (n : A) → Set (ZMod (n : ℕ)),
        (¬ ∃ d : ℝ, Filter.Tendsto (logAverage (survivors A X)) Filter.atTop (nhds d)) ∧
        Filter.liminf (logAverage (survivors A X)) Filter.atTop ≤ (177 : ℝ) / 200 ∧
        (49 : ℝ) / 50 ≤ Filter.limsup (logAverage (survivors A X)) Filter.atTop := by
  sorry

/-- Arbitrary delayed congruence systems need not have logarithmic density. -/
theorem not_erdos_486 :
    ¬ ∀ (A : Set ℕ) (X : (n : A) → Set (ZMod (n : ℕ))), 0 ∉ A →
      ∃ d : ℝ, Filter.Tendsto (logAverage (survivors A X)) Filter.atTop (nhds d) := by
  sorry

end Erdos486
