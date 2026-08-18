/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterOrbitNumerics

/-!
# A second-moment lower bound for a positive set
-/

open Set Function MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos984

noncomputable section

/-- Elementary second-moment inequality, in a form avoiding square roots:
if a real function has positive mean `m` and second moment at most
`C*m²`, then its positive set has measure at least `1/C`. -/
lemma one_div_le_measureReal_posSet_of_secondMoment
    {X : Type*} [MeasurableSpace X] {mu : Measure X} [IsFiniteMeasure mu]
    (S : X → ℝ) (hSmeas : Measurable S) (hSint : Integrable S mu)
    (hSsq : Integrable (fun x ↦ S x ^ 2) mu)
    (m C : ℝ) (hm : 0 < m) (hC : 0 < C)
    (hmean : ∫ x, S x ∂mu = m)
    (hsecond : ∫ x, S x ^ 2 ∂mu ≤ C * m ^ 2) :
    1 / C ≤ mu.real {x | 0 < S x} := by
  let P : Set X := {x | 0 < S x}
  have hP : MeasurableSet P := by
    exact measurableSet_lt measurable_const hSmeas
  have hden : 0 < 2 * C * m := by positivity
  have hind : Integrable (P.indicator S) mu := hSint.indicator hP
  have hconst : Integrable (P.indicator (fun _ : X ↦ C * m / 2)) mu :=
    (integrable_const (C * m / 2)).indicator hP
  have hright : Integrable (fun x ↦
      S x ^ 2 / (2 * C * m) + P.indicator (fun _ : X ↦ C * m / 2) x) mu :=
    (hSsq.div_const _).add hconst
  have htoIndicator : ∀ x, S x ≤ P.indicator S x := by
    intro x
    by_cases hx : x ∈ P
    · simp [hx]
    · rw [Set.indicator_of_notMem hx]
      exact le_of_not_gt hx
  have hyoung : ∀ x, P.indicator S x ≤
      S x ^ 2 / (2 * C * m) +
        P.indicator (fun _ : X ↦ C * m / 2) x := by
    intro x
    by_cases hx : x ∈ P
    · simp only [Set.indicator_of_mem hx]
      have heq : S x ^ 2 / (2 * C * m) + C * m / 2 =
          (S x ^ 2 + (C * m) ^ 2) / (2 * C * m) := by
        field_simp
      rw [heq, le_div_iff₀ hden]
      nlinarith [sq_nonneg (S x - C * m)]
    · simp only [Set.indicator_of_notMem hx]
      exact div_nonneg (sq_nonneg _) hden.le |>.trans (le_add_of_nonneg_right le_rfl)
  have hfirst :
      (∫ x, S x ^ 2 ∂mu) / (2 * C * m) ≤ m / 2 := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hmain : m ≤ m / 2 + mu.real P * (C * m / 2) := by
    calc
      m = ∫ x, S x ∂mu := hmean.symm
      _ ≤ ∫ x, P.indicator S x ∂mu :=
        integral_mono hSint hind htoIndicator
      _ ≤ ∫ x,
          (S x ^ 2 / (2 * C * m) +
            P.indicator (fun _ : X ↦ C * m / 2) x) ∂mu :=
        integral_mono hind hright hyoung
      _ = (∫ x, S x ^ 2 ∂mu) / (2 * C * m) +
          mu.real P * (C * m / 2) := by
        rw [integral_add (hSsq.div_const _) hconst, integral_div,
          integral_indicator_const _ hP]
        simp [smul_eq_mul]
      _ ≤ m / 2 + mu.real P * (C * m / 2) :=
        add_le_add hfirst le_rfl
  rw [div_le_iff₀ hC]
  nlinarith

end

end Erdos984
