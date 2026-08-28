import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBlowupH1Charts
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLaurent

/-!
# Actual additive splitting on the blowup chart overlap

In the second chart the reciprocal Laurent part is evaluated at `(s*t,t)`.
This polynomial substitution extends holomorphically across the exceptional
coordinate. Thus the actual blowup transition, rather than an untwisted
product transition, is used in the splitting equation.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupH1

def reverseBase (q : ℂ × ℂ) : ℂ × ℂ := (q.1 * q.2, q.2)

theorem reverseBase_analytic : AnalyticOnNhd ℂ reverseBase univ := by
  intro q _
  exact (analyticAt_fst.mul analyticAt_snd).prod analyticAt_snd

theorem reverseBase_cross (q : ℂ × ℂ) (hq : q.2 ≠ 0) :
    reverseBase (cross q) = (q.1, q.2⁻¹) := by
  apply Prod.ext
  · change q.1 * q.2 * q.2⁻¹ = q.1
    rw [mul_assoc, mul_inv_cancel₀ hq, mul_one]
  · rfl

/-- A holomorphic function on the actual overlap is a difference of
entire chart functions, with the literal blowup coordinate change. -/
theorem exists_holomorphic_overlap_split {h : ℂ × ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h {q | q.2 ≠ 0}) :
    ∃ a : Bool → ℂ × ℂ → ℂ, (∀ b, AnalyticOnNhd ℂ (a b) univ) ∧
      ∀ q, q.2 ≠ 0 → a false q - a true (cross q) = h q := by
  obtain ⟨p, m, hp, hm, _, heq⟩ := Laurent.exists_entire_parametric_splitting hh
  let a : Bool → ℂ × ℂ → ℂ := fun b q => if b then -m (reverseBase q) else p q
  refine ⟨a, ?_, ?_⟩
  · intro b q _
    cases b
    · exact hp q (mem_univ _)
    · exact ((hm (reverseBase q) (mem_univ _)).comp
        (reverseBase_analytic q (mem_univ _))).neg
  · intro q hq
    change p q - -m (reverseBase (cross q)) = h q
    rw [reverseBase_cross q hq, sub_neg_eq_add]
    exact (heq q.1 q.2 hq).symm

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.BlowupH1
