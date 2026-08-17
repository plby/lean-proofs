/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Basic
import ErdosProblems.Erdos896.Scale

/-!
# Final assembly lemmas for Erdős Problem 896

This file isolates the elementary last step of the resolution. The analytic
inputs may be supplied as eventual upper and lower estimates with positive
lower constant; these estimates assemble directly into an `IsTheta` theorem.
It also records the finite bridge from any admissible constructed pair to the
maximum in the statement of the problem.
-/

namespace Erdos896

open Filter Asymptotics

/-! ## From a constructed pair to the finite maximum -/

/-- A lower bound proved for one admissible pair is a lower bound for `maxF`. -/
theorem le_maxF_of_le_F {N K : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ box N) (hB : B ⊆ box N) (hK : K ≤ F A B) :
    K ≤ maxF N :=
  hK.trans (F_le_maxF hA hB)

/-- Existential form of `le_maxF_of_le_F`, convenient for a construction
whose two sets are returned together with their quantitative lower bound. -/
theorem le_maxF_of_exists_pair {N K : ℕ}
    (h : ∃ A B : Finset ℕ,
      A ⊆ box N ∧ B ⊆ box N ∧ K ≤ F A B) :
    K ≤ maxF N := by
  rcases h with ⟨A, B, hA, hB, hK⟩
  exact le_maxF_of_le_F hA hB hK

/-- Real-valued form of the same bridge, avoiding a rounding step in analytic
lower bounds. -/
theorem real_le_maxF_of_exists_pair {N : ℕ} {x : ℝ}
    (h : ∃ A B : Finset ℕ,
      A ⊆ box N ∧ B ⊆ box N ∧ x ≤ (F A B : ℝ)) :
    x ≤ (maxF N : ℝ) := by
  rcases h with ⟨A, B, hA, hB, hx⟩
  exact hx.trans (Nat.cast_le.mpr (F_le_maxF hA hB))

/-! ## Generic asymptotic assembly -/

/-- Nonnegative real functions satisfying matching eventual constant bounds
are of the same asymptotic order. The lower constant must be positive so that
the lower estimate can be inverted for the reverse big-O relation. -/
theorem isTheta_of_eventually_const_mul_le
    {index : Type*} {l : Filter index} {f g : index → ℝ}
    {cLower cUpper : ℝ}
    (hcLower : 0 < cLower)
    (hf : ∀ᶠ i in l, 0 ≤ f i)
    (hg : ∀ᶠ i in l, 0 ≤ g i)
    (hlower : ∀ᶠ i in l, cLower * g i ≤ f i)
    (hupper : ∀ᶠ i in l, f i ≤ cUpper * g i) :
    f =Θ[l] g := by
  constructor
  · apply IsBigO.of_bound cUpper
    filter_upwards [hf, hg, hupper] with i hfi hgi hi
    simpa only [Real.norm_eq_abs, abs_of_nonneg hfi, abs_of_nonneg hgi] using hi
  · apply IsBigO.of_bound cLower⁻¹
    filter_upwards [hf, hg, hlower] with i hfi hgi hi
    simp only [Real.norm_eq_abs, abs_of_nonneg hgi, abs_of_nonneg hfi]
    rw [inv_mul_eq_div]
    exact (le_div_iff₀' hcLower).2 hi

/-- The final asymptotic conclusion follows from explicit eventual lower and
upper estimates at the Ford scale. -/
theorem maxF_isTheta_scale896_of_eventually_bounds
    {cLower cUpper : ℝ}
    (hcLower : 0 < cLower)
    (hlower : ∀ᶠ N : ℕ in atTop,
      cLower * scale896 N ≤ (maxF N : ℝ))
    (hupper : ∀ᶠ N : ℕ in atTop,
      (maxF N : ℝ) ≤ cUpper * scale896 N) :
    (fun N : ℕ ↦ (maxF N : ℝ)) =Θ[atTop] scale896 := by
  exact isTheta_of_eventually_const_mul_le hcLower
    (Filter.Eventually.of_forall fun _ ↦ Nat.cast_nonneg _)
    (eventually_scale896_pos.mono fun _ hN ↦ hN.le) hlower hupper

end Erdos896
