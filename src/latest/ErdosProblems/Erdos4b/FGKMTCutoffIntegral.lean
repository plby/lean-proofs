/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCutoffAverage
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.BigOperators.Fin

/-!
# The genuine cube integral and its coordinate recurrence

The main term is an ordinary Lebesgue integral on the unit cube. Its
recurrence is obtained from a measure-preserving coordinate equivalence
and Fubini's theorem, with integrability proved from the bounded cutoff.
-/

namespace Erdos4b.FGKMT

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

def unitIntervalMeasure : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsFiniteMeasure unitIntervalMeasure := by
  unfold unitIntervalMeasure
  infer_instance

theorem unitIntervalMeasure_integral (f : ℝ → ℝ) :
    (∫ t, f t ∂unitIntervalMeasure) = ∫ t in (0 : ℝ)..1, f t := by
  rw [unitIntervalMeasure, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

def cutoffCubeIntegral (G Φ : ℝ → ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  ∫ t : Fin j → ℝ, (∏ i, G (t i)) * Φ (u + ∑ i, t i)
    ∂Measure.pi (fun _ : Fin j => unitIntervalMeasure)

theorem cutoffCubeIntegral_eq_cube (G Φ : ℝ → ℝ) (j : ℕ) (u : ℝ) :
    cutoffCubeIntegral G Φ j u =
      ∫ t in Set.pi Set.univ (fun _ : Fin j => Set.Icc (0 : ℝ) 1),
        (∏ i, G (t i)) * Φ (u + ∑ i, t i) := by
  unfold cutoffCubeIntegral unitIntervalMeasure
  rw [← Measure.restrict_pi_pi]
  rfl

theorem cutoffCubeIntegral_zero (G Φ : ℝ → ℝ) (u : ℝ) :
    cutoffCubeIntegral G Φ 0 u = Φ u := by
  simp [cutoffCubeIntegral, measureReal_def]

theorem cutoffCubeIntegral_one (G : ℝ → ℝ) (j : ℕ) (u : ℝ) :
    cutoffCubeIntegral G (fun _ => 1) j u = (∫ t in (0 : ℝ)..1, G t) ^ j := by
  simp only [cutoffCubeIntegral, mul_one]
  rw [integral_fintype_prod_eq_pow]
  simp only [Fintype.card_fin, unitIntervalMeasure_integral]

theorem cutoffCubeIntegrand_integrable {G Φ : ℝ → ℝ} {K : ℝ}
    (hG : Continuous G) (hΦ : BoundedCutoff Φ K) (j : ℕ) (u : ℝ) :
    Integrable (fun t : Fin j → ℝ => (∏ i, G (t i)) * Φ (u + ∑ i, t i))
      (Measure.pi (fun _ : Fin j => unitIntervalMeasure)) := by
  have hGi : Integrable G unitIntervalMeasure := hG.integrableOn_Icc
  have hprod := Integrable.fintype_prod (fun _ : Fin j => hGi)
  have hcont : Continuous (fun t : Fin j → ℝ => Φ (u + ∑ i, t i)) := by
    apply hΦ.smooth.continuous.comp
    fun_prop
  apply hprod.mul_bdd hcont.aestronglyMeasurable
  exact Eventually.of_forall (fun t => by
    simpa only [Real.norm_eq_abs] using hΦ.value_bound (u + ∑ i, t i))

theorem cutoffCubeIntegral_succ {G Φ : ℝ → ℝ} {K : ℝ}
    (hG : Continuous G) (hΦ : BoundedCutoff Φ K) (j : ℕ) (u : ℝ) :
    cutoffCubeIntegral G Φ (j + 1) u = cutoffCubeIntegral G (cutoffAverage G Φ) j u := by
  let f := fun t : Fin (j + 1) → ℝ => (∏ i, G (t i)) * Φ (u + ∑ i, t i)
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (j + 1) => ℝ) 0).symm
  have he := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (j + 1) => unitIntervalMeasure) 0).symm
  have hf : Integrable f (Measure.pi (fun _ : Fin (j + 1) => unitIntervalMeasure)) :=
    cutoffCubeIntegrand_integrable hG hΦ (j + 1) u
  have hcomp : Integrable (fun z => f (e z))
      (unitIntervalMeasure.prod (Measure.pi (fun _ : Fin j => unitIntervalMeasure))) :=
    (he.integrable_comp_emb e.measurableEmbedding).2 hf
  change (∫ t, f t ∂Measure.pi (fun _ : Fin (j + 1) => unitIntervalMeasure)) = _
  rw [← he.integral_comp' f, integral_prod_symm _ hcomp]
  unfold cutoffCubeIntegral
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  calc
    _ = ∫ x, (∏ i : Fin j, G (t i)) * (G x * Φ ((u + ∑ i, t i) + x))
        ∂unitIntervalMeasure := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only [f, e]
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Fin.prod_univ_succ, Fin.sum_univ_succ,
        Equiv.coe_fn_mk, Fin.cons_succ, Fin.cons_zero, Fin.zero_succAbove, cast_eq]
      have harg : u + (x + ∑ i, t i) = (u + ∑ i, t i) + x := by ring
      rw [harg]
      ring
    _ = _ := integral_const_mul _ _

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.cutoffCubeIntegral_succ
