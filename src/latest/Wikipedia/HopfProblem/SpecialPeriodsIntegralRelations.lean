import Wikipedia.HopfProblem.SpecialPeriodsLinearIndependence

/-!
# Universal integral relations among the actual periods

The coefficient computation in Lemma 9.3 is applied to the genuine
constructed functions. The only integral relation valid everywhere is
the multiple of `u ∧ w + 6 γ ∧ δ`, in the displayed six-coordinate order.
This file proves the analytic-function relation, not an assumed
identification of these coefficients with Néron--Severi classes.
-/

noncomputable section

open UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- Coordinates are `γu, γw, γδ, uw, uδ, wδ`, as in Section 9.1. -/
def periodRelationEta : Fin 6 → ℤ := ![0, 0, 6, 1, 0, 0]

/-- The actual holomorphic period-relation function `P_E`. -/
def specialPeriodRelation (E : Fin 6 → ℤ) (z : ℍ) : ℂ :=
  (E 0 : ℂ) - (E 1 : ℂ) * specialTau z - (E 2 : ℂ) * specialMu z +
    6 * (E 3 : ℂ) * specialMu z + (E 4 : ℂ) * specialBeta z +
    (E 5 : ℂ) * (6 * specialMu z ^ 2 - specialTau z * specialBeta z)

theorem specialPeriodRelation_holomorphic (E : Fin 6 → ℤ) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (specialPeriodRelation E) := by
  have hτ := specialTau_holomorphic
  have hμ := specialMu_holomorphic
  have hβ := specialBeta_holomorphic
  exact (((((contMDiff_const.sub (contMDiff_const.mul hτ)).sub
    (contMDiff_const.mul hμ)).add (contMDiff_const.mul hμ)).add
    (contMDiff_const.mul hβ)).add
    (contMDiff_const.mul ((contMDiff_const.mul (hμ.pow 2)).sub (hτ.mul hβ))))

theorem specialPeriodRelation_eq_combination (E : Fin 6 → ℤ) (z : ℍ) :
    specialPeriodRelation E z =
      (E 0 : ℂ) + (-(E 1 : ℂ)) * specialTau z +
      (6 * (E 3 : ℂ) - (E 2 : ℂ)) * specialMu z + (E 4 : ℂ) * specialBeta z +
      (E 5 : ℂ) * (6 * specialMu z ^ 2 - specialTau z * specialBeta z) := by
  unfold specialPeriodRelation
  ring

/-- The integer coefficient form of the universal-relation calculation. -/
theorem specialPeriodRelation_identically_zero_coefficients (E : Fin 6 → ℤ)
    (h : ∀ z : ℍ, specialPeriodRelation E z = 0) :
    E 0 = 0 ∧ E 1 = 0 ∧ E 2 = 6 * E 3 ∧ E 4 = 0 ∧ E 5 = 0 := by
  have hrel : ∀ z : ℍ, (E 0 : ℂ) + (-(E 1 : ℂ)) * specialTau z +
      (6 * (E 3 : ℂ) - (E 2 : ℂ)) * specialMu z + (E 4 : ℂ) * specialBeta z +
      (E 5 : ℂ) * (6 * specialMu z ^ 2 - specialTau z * specialBeta z) = 0 := by
    intro z
    rw [← specialPeriodRelation_eq_combination]
    exact h z
  obtain ⟨h0, h1, h2, h4, h5⟩ := specialPeriodFunctions_relation
    (E 0) (-(E 1 : ℂ)) (6 * (E 3 : ℂ) - (E 2 : ℂ)) (E 4) (E 5) hrel
  have e0 : E 0 = 0 := by exact_mod_cast h0
  have e1 : E 1 = 0 := by exact_mod_cast neg_eq_zero.mp h1
  have e2' : 6 * E 3 - E 2 = 0 := by exact_mod_cast h2
  have e4 : E 4 = 0 := by exact_mod_cast h4
  have e5 : E 5 = 0 := by exact_mod_cast h5
  exact ⟨e0, e1, by omega, e4, e5⟩

/-- Exactly the integer multiples of the specified coefficient vector
give an identically zero period-relation function. -/
theorem specialPeriodRelation_identically_zero_iff (E : Fin 6 → ℤ) :
    (∀ z : ℍ, specialPeriodRelation E z = 0) ↔
      ∃ n : ℤ, E = n • periodRelationEta := by
  constructor
  · intro h
    obtain ⟨h0, h1, h2, h4, h5⟩ := specialPeriodRelation_identically_zero_coefficients E h
    refine ⟨E 3, ?_⟩
    funext i
    fin_cases i <;>
      simp [Pi.smul_apply, periodRelationEta, h0, h1, h2, h4, h5, mul_comm]
  · rintro ⟨n, rfl⟩ z
    simp [specialPeriodRelation, Pi.smul_apply, periodRelationEta]
    ring

theorem specialPeriodRelation_eta (z : ℍ) : specialPeriodRelation periodRelationEta z = 0 :=
  (specialPeriodRelation_identically_zero_iff periodRelationEta).mpr ⟨1, by simp⟩ z

/-- Every other integer coefficient vector has an actual point at
which its holomorphic period relation does not vanish. -/
theorem specialPeriodRelation_exists_ne_zero (E : Fin 6 → ℤ)
    (hE : ¬ ∃ n : ℤ, E = n • periodRelationEta) :
    ∃ z : ℍ, specialPeriodRelation E z ≠ 0 := by
  by_contra h
  push Not at h
  exact hE ((specialPeriodRelation_identically_zero_iff E).mp h)

end Wikipedia.HopfProblem.SpecialPeriods
