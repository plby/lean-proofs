import Wikipedia.HopfProblem.SpecialPeriodsExistence
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Linear independence of the actual special period functions

Lemma 9.3 follows directly from the two actual transformation laws at
the cusp and the order-four point. Finite differences eliminate the
coefficients; no genericity or independence premise is imposed on the
constructed periods.
-/

noncomputable section

open UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods

open Triangle

theorem specialTau_ne_zero (z : ℍ) : specialTau z ≠ 0 := by
  intro h
  have hp := specialTau_im_pos z
  rw [h, Complex.zero_im] at hp
  exact (lt_irrefl 0) hp

/-- The scalar cusp equations, including the two affine terms. -/
theorem specialPeriods_cusp_scalars (z : ℍ) :
    specialTau (triangleGeometricRepresentation triangleCuspGenerator z) = specialTau z - 1 ∧
    specialMu (triangleGeometricRepresentation triangleCuspGenerator z) = specialMu z ∧
    specialBeta (triangleGeometricRepresentation triangleCuspGenerator z) = specialBeta z + 1 := by
  have h := congrArg Subtype.val (specialPeriodMap_cusp z)
  refine ⟨congrArg PeriodPoint.τ h, ?_, congrArg PeriodPoint.β h⟩
  simpa only [specialMu, PeriodDomain.step₀, PeriodPoint.step₀] using
    congrArg PeriodPoint.μ h

private theorem relation_cusp_difference (a b c d e : ℂ)
    (h : ∀ z : ℍ, a + b * specialTau z + c * specialMu z + d * specialBeta z +
      e * (6 * specialMu z ^ 2 - specialTau z * specialBeta z) = 0) (z : ℍ) :
    -b + d + e * (specialBeta z - specialTau z + 1) = 0 := by
  have hz := h z
  have hg := h (triangleGeometricRepresentation triangleCuspGenerator z)
  obtain ⟨hτ, hμ, hβ⟩ := specialPeriods_cusp_scalars z
  rw [hτ, hμ, hβ] at hg
  linear_combination hg - hz

private theorem relation_last_coefficient_zero (b d e : ℂ)
    (h : ∀ z : ℍ, -b + d + e * (specialBeta z - specialTau z + 1) = 0) : e = 0 := by
  have hz := h centerTwo
  have hg := h (triangleGeometricRepresentation triangleCuspGenerator centerTwo)
  obtain ⟨hτ, _, hβ⟩ := specialPeriods_cusp_scalars centerTwo
  rw [hτ, hβ] at hg
  linear_combination (hg - hz) / 2

private theorem reduced_relation_second (a b c : ℂ)
    (h : ∀ z : ℍ, a + b * (specialTau z + specialBeta z) + c * specialMu z = 0)
    (z : ℍ) :
    6 * b * specialMu z ^ 2 + c * (specialTau z - 1) * specialMu z +
      b * (specialTau z ^ 2 + 3 * specialTau z + 1) - c * specialTau z = 0 := by
  have hg := h (generatorTwoSL • z)
  obtain ⟨hτ, hμ, hβ⟩ := specialPeriods_generator₂ z
  rw [hτ, hμ, hβ] at hg
  have hg' : a * specialTau z +
      b * (-1 + (specialBeta z - 3) * specialTau z - 6 * specialMu z ^ 2) +
      c * (specialTau z + specialMu z) = 0 := by
    calc
      _ = specialTau z * (a + b * (-1 / specialTau z +
          (specialBeta z - 3 - 6 * specialMu z ^ 2 / specialTau z)) +
          c * (1 + specialMu z / specialTau z)) := by
        field_simp [specialTau_ne_zero z]
        ring
      _ = 0 := by rw [hg, mul_zero]
  linear_combination specialTau z * h z - hg'

private theorem reduced_relation_translation (b c : ℂ)
    (h : ∀ z : ℍ, 6 * b * specialMu z ^ 2 + c * (specialTau z - 1) * specialMu z +
      b * (specialTau z ^ 2 + 3 * specialTau z + 1) - c * specialTau z = 0) (z : ℍ) :
    c * specialMu z + 2 * b * (specialTau z + 1) - c = 0 := by
  have hz := h z
  have hg := h (triangleGeometricRepresentation triangleCuspGenerator z)
  obtain ⟨hτ, hμ, _⟩ := specialPeriods_cusp_scalars z
  rw [hτ, hμ] at hg
  linear_combination hz - hg

private theorem reduced_relation_middle_coefficients_zero (b c : ℂ)
    (h : ∀ z : ℍ, c * specialMu z + 2 * b * (specialTau z + 1) - c = 0) :
    b = 0 ∧ c = 0 := by
  have hz := h centerTwo
  have hg := h (triangleGeometricRepresentation triangleCuspGenerator centerTwo)
  obtain ⟨hτ, hμ, _⟩ := specialPeriods_cusp_scalars centerTwo
  rw [hτ, hμ] at hg
  have hb : b = 0 := by linear_combination (hz - hg) / 2
  have hcμ : ∀ z : ℍ, c * specialMu z = c := by
    intro z
    have hh := h z
    rw [hb] at hh
    linear_combination hh
  have hsecond := hcμ (generatorTwoSL • centerTwo)
  rw [(specialPeriods_generator₂ centerTwo).2.1] at hsecond
  have hzero : c * specialMu centerTwo = 0 := by
    calc
      _ = specialTau centerTwo *
          (c * (1 + specialMu centerTwo / specialTau centerTwo) - c) := by
        field_simp [specialTau_ne_zero centerTwo]
        ring
      _ = 0 := by rw [hsecond, sub_self, mul_zero]
  exact ⟨hb, (hcμ centerTwo).symm.trans hzero⟩

/-- The coefficient form of Lemma 9.3 for the actual constructed periods. -/
theorem specialPeriodFunctions_relation (a b c d e : ℂ)
    (h : ∀ z : ℍ, a + b * specialTau z + c * specialMu z + d * specialBeta z +
      e * (6 * specialMu z ^ 2 - specialTau z * specialBeta z) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by
  have hdiff := relation_cusp_difference a b c d e h
  have he := relation_last_coefficient_zero b d e hdiff
  have hdb : d = b := by
    have hz := hdiff centerTwo
    rw [he] at hz
    linear_combination hz
  have hred : ∀ z : ℍ, a + b * (specialTau z + specialBeta z) + c * specialMu z = 0 := by
    intro z
    have hz := h z
    rw [he, hdb] at hz
    linear_combination hz
  have hquad := reduced_relation_second a b c hred
  have htrans := reduced_relation_translation b c hquad
  obtain ⟨hb, hc⟩ := reduced_relation_middle_coefficients_zero b c htrans
  have ha : a = 0 := by simpa only [hb, hc, zero_mul, add_zero] using hred centerTwo
  exact ⟨ha, hb, hc, hdb.trans hb, he⟩

/-- The five actual holomorphic functions appearing in the period relation. -/
def specialPeriodFunctions : Fin 5 → (ℍ → ℂ) :=
  ![fun _ => 1, specialTau, specialMu, specialBeta,
    fun z => 6 * specialMu z ^ 2 - specialTau z * specialBeta z]

/-- The genuine linear-independence statement in the function space. -/
theorem specialPeriodFunctions_linearIndependent :
    LinearIndependent ℂ specialPeriodFunctions := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hrel : ∀ z : ℍ, g 0 + g 1 * specialTau z + g 2 * specialMu z +
      g 3 * specialBeta z +
      g 4 * (6 * specialMu z ^ 2 - specialTau z * specialBeta z) = 0 := by
    intro z
    have hz := congrFun hg z
    simpa [specialPeriodFunctions, Fin.sum_univ_succ, add_assoc] using hz
  obtain ⟨h0, h1, h2, h3, h4⟩ :=
    specialPeriodFunctions_relation (g 0) (g 1) (g 2) (g 3) (g 4) hrel
  fin_cases i <;> assumption

end Wikipedia.HopfProblem.SpecialPeriods
