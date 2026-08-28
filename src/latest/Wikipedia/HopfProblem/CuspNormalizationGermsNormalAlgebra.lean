import Wikipedia.HopfProblem.CuspNormalizationGermsNormalBound
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Analytic quotient extension and integral closure

This file isolates the algebraic passage from extension of bounded actual
analytic quotients to integral closedness of the actual analytic-germ ring.
The extension theorem is supplied by the analytic argument in the final
normality module; integrality itself supplies the required local bound.
-/

noncomputable section

open Set Filter Topology
open scoped nonZeroDivisors

namespace Wikipedia.HopfProblem.CuspNormalization.Germs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {a : E} {f g q : E → ℂ}

/-- An actual analytic quotient extension represents the same element of
the fraction field of analytic germs. -/
theorem fraction_eq_algebraMap_of_eventuallyEq_mul
    (hf : AnalyticAt ℂ f a) (hg : AnalyticAt ℂ g a) (hq : AnalyticAt ℂ q a)
    (hgerm : ofAnalytic g hg ≠ 0)
    (he : f =ᶠ[𝓝 a] (fun z => g z * q z)) :
    algebraMap (AnalyticGerm a) (FractionRing (AnalyticGerm a)) (ofAnalytic f hf) /
        algebraMap (AnalyticGerm a) (FractionRing (AnalyticGerm a)) (ofAnalytic g hg) =
      algebraMap (AnalyticGerm a) (FractionRing (AnalyticGerm a)) (ofAnalytic q hq) := by
  have hmul : ofAnalytic f hf = ofAnalytic g hg * ofAnalytic q hq := by
    exact (ofAnalytic_eq_iff f (g * q) hf (hg.mul hq)).mpr he
  have hgmap :
      algebraMap (AnalyticGerm a) (FractionRing (AnalyticGerm a)) (ofAnalytic g hg) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hgerm
  rw [hmul, map_mul, mul_comm, mul_div_cancel_right₀ _ hgmap]

/-- Algebraic assembly of normality from extension of locally bounded
actual analytic quotients. No bound on an integral element is assumed:
the monic relation proves that bound. -/
theorem isIntegrallyClosed_of_analytic_quotient_extension
    (hext : ∀ (f g : E → ℂ), AnalyticAt ℂ f a → AnalyticAt ℂ g a →
      (¬ g =ᶠ[𝓝 a] 0) → ∀ M : ℝ,
      (∀ᶠ z in 𝓝 a, g z ≠ 0 → ‖f z / g z‖ ≤ M) →
      ∃ q : E → ℂ, AnalyticAt ℂ q a ∧ f =ᶠ[𝓝 a] (fun z => g z * q z)) :
    IsIntegrallyClosed (AnalyticGerm a) := by
  refine (isIntegrallyClosed_iff (FractionRing (AnalyticGerm a))).mpr ?_
  intro x hx
  obtain ⟨φ, ψ, hψ, rfl⟩ := IsFractionRing.div_surjective (AnalyticGerm a) x
  obtain ⟨f, hf, rfl⟩ := exists_representative φ
  obtain ⟨g, hg, rfl⟩ := exists_representative ψ
  have hgerm : ofAnalytic g hg ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hψ
  obtain ⟨M, _, hM⟩ :=
    exists_pos_eventually_norm_div_le_off_zero_of_isIntegral hf hg hgerm hx
  obtain ⟨q, hq, he⟩ := hext f g hf hg
    (fun hzero => hgerm ((ofAnalytic_eq_zero_iff g hg).mpr hzero)) M hM
  exact ⟨ofAnalytic q hq, (fraction_eq_algebraMap_of_eventuallyEq_mul hf hg hq hgerm he).symm⟩

end Wikipedia.HopfProblem.CuspNormalization.Germs
