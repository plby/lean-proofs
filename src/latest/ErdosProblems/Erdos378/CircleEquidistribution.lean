/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# A Weyl criterion on the unit additive circle

This file packages the exact compactness/density argument used in the
Granville--Ramaré proof.  A family of probability measures on `ℝ / ℤ`
converges to Haar measure as soon as every nonzero Fourier coefficient tends
to zero.
-/

open Filter MeasureTheory
open scoped Topology ComplexConjugate

namespace Erdos378
namespace CircleEquidistribution

noncomputable section

abbrev UnitCircle := AddCircle (1 : ℝ)

/-- Normalized Haar measure on `ℝ / ℤ`, bundled as a probability measure. -/
def unitHaar : ProbabilityMeasure UnitCircle :=
  ⟨AddCircle.haarAddCircle, inferInstance⟩

lemma integral_fourier_unitHaar (h : ℤ) :
    ∫ z : UnitCircle, fourier h z ∂AddCircle.haarAddCircle =
      if h = 0 then 1 else 0 := by
  by_cases hh : h = 0
  · subst h
    simp [fourier]
  · simp only [hh, if_false]
    exact integral_eq_zero_of_add_right_eq_neg
      (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hh (by norm_num))

/-- Weyl's criterion for probability measures on the unit additive circle. -/
theorem tendsto_unitHaar_of_fourier
    {I : Type*} {F : Filter I} (mu : I → ProbabilityMeasure UnitCircle)
    (hmode : ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun i ↦
        ∫ z : UnitCircle, fourier h z ∂(mu i : Measure UnitCircle))
        F (nhds 0)) :
    Tendsto mu F (nhds unitHaar) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ]
  intro f
  let H : Measure UnitCircle := AddCircle.haarAddCircle
  have hfourier (h : ℤ) :
      Tendsto (fun i ↦
        ∫ z : UnitCircle, fourier h z ∂(mu i : Measure UnitCircle)) F
        (nhds (∫ z : UnitCircle, fourier h z ∂H)) := by
    by_cases hh : h = 0
    · subst h
      simpa [fourier, H] using
        (tendsto_const_nhds :
          Tendsto (fun _ : I ↦ (1 : ℂ)) F (nhds 1))
    · rw [show (∫ z : UnitCircle, fourier h z ∂H) = 0 by
          simpa [H, hh] using integral_fourier_unitHaar h]
      exact hmode h hh
  have hspan (g : C(UnitCircle, ℂ))
      (hg : g ∈ Submodule.span ℂ (Set.range fourier)) :
      Tendsto (fun i ↦ ∫ z : UnitCircle, g z ∂(mu i : Measure UnitCircle)) F
        (nhds (∫ z : UnitCircle, g z ∂H)) := by
    induction hg using Submodule.span_induction with
    | mem g hg =>
        rcases hg with ⟨h, rfl⟩
        exact hfourier h
    | zero =>
        simpa using
          (tendsto_const_nhds : Tendsto (fun _ : I ↦ (0 : ℂ)) F (nhds 0))
    | add g q _ _ hg hq =>
        have hgi (i : I) : Integrable g (mu i : Measure UnitCircle) :=
          (BoundedContinuousFunction.mkOfCompact g).integrable _
        have hqi (i : I) : Integrable q (mu i : Measure UnitCircle) :=
          (BoundedContinuousFunction.mkOfCompact q).integrable _
        have hgH : Integrable g H :=
          (BoundedContinuousFunction.mkOfCompact g).integrable _
        have hqH : Integrable q H :=
          (BoundedContinuousFunction.mkOfCompact q).integrable _
        simpa only [ContinuousMap.add_apply,
          integral_add (hgi _) (hqi _), integral_add hgH hqH] using hg.add hq
    | smul c g _ hg =>
        simpa only [ContinuousMap.smul_apply, Pi.smul_apply, integral_smul]
          using hg.const_smul c
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hfcl : f.toContinuousMap ∈
      closure (↑(Submodule.span ℂ
        (Set.range (fourier (T := (1 : ℝ))))) :
          Set C(UnitCircle, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    exact Submodule.mem_top
  obtain ⟨g, hgspan, hfg⟩ :=
    (Metric.mem_closure_iff.mp hfcl) (ε / 3) (by linarith)
  have hg := hspan g hgspan
  rw [Metric.tendsto_nhds] at hg
  filter_upwards [hg (ε / 3) (by linarith)] with i hi
  have hleft :
      ‖∫ z : UnitCircle, f z ∂(mu i : Measure UnitCircle) -
          ∫ z : UnitCircle, g z ∂(mu i : Measure UnitCircle)‖ < ε / 3 := by
    have hfint : Integrable (fun z : UnitCircle ↦ f z)
        (mu i : Measure UnitCircle) := f.integrable _
    have hgint : Integrable (fun z : UnitCircle ↦ g z)
        (mu i : Measure UnitCircle) :=
      (BoundedContinuousFunction.mkOfCompact g).integrable _
    rw [← integral_sub hfint hgint]
    calc
      _ ≤ ‖f.toContinuousMap - g‖ *
          (mu i : Measure UnitCircle).real Set.univ :=
        norm_integral_le_of_norm_le_const (.of_forall fun z ↦
          ContinuousMap.norm_coe_le_norm (f.toContinuousMap - g) z)
      _ = dist f.toContinuousMap g := by
        rw [probReal_univ, mul_one, dist_eq_norm]
      _ < ε / 3 := hfg
  have hright :
      ‖∫ z : UnitCircle, g z ∂H - ∫ z : UnitCircle, f z ∂H‖ <
        ε / 3 := by
    have hgint : Integrable (fun z : UnitCircle ↦ g z) H :=
      (BoundedContinuousFunction.mkOfCompact g).integrable H
    have hfint : Integrable (fun z : UnitCircle ↦ f z) H := f.integrable H
    rw [← integral_sub hgint hfint]
    calc
      _ ≤ ‖g - f.toContinuousMap‖ * H.real Set.univ :=
        norm_integral_le_of_norm_le_const (.of_forall fun z ↦
          ContinuousMap.norm_coe_le_norm (g - f.toContinuousMap) z)
      _ = dist f.toContinuousMap g := by
        rw [probReal_univ, mul_one, dist_eq_norm]
        exact norm_sub_rev _ _
      _ < ε / 3 := hfg
  change dist (∫ (x : UnitCircle), f x ∂↑(mu i))
      (∫ (x : UnitCircle), f x ∂↑unitHaar) < ε
  change dist (∫ (x : UnitCircle), f x ∂↑(mu i))
      (∫ (x : UnitCircle), f x ∂H) < ε
  rw [dist_eq_norm] at hi ⊢
  calc
    _ ≤
        ‖∫ z : UnitCircle, f z ∂(mu i : Measure UnitCircle) -
            ∫ z : UnitCircle, g z ∂(mu i : Measure UnitCircle)‖ +
        ‖∫ z : UnitCircle, g z ∂(mu i : Measure UnitCircle) -
            ∫ z : UnitCircle, g z ∂H‖ +
        ‖∫ z : UnitCircle, g z ∂H - ∫ z : UnitCircle, f z ∂H‖ := by
      calc
        _ = ‖(∫ z : UnitCircle, f z ∂(mu i : Measure UnitCircle) -
                ∫ z : UnitCircle, g z ∂(mu i : Measure UnitCircle)) +
              ((∫ z : UnitCircle, g z ∂(mu i : Measure UnitCircle) -
                  ∫ z : UnitCircle, g z ∂H) +
                (∫ z : UnitCircle, g z ∂H -
                  ∫ z : UnitCircle, f z ∂H))‖ := by
            congr 1 <;> ring
        _ ≤
            ‖∫ z : UnitCircle, f z ∂(mu i : Measure UnitCircle) -
                ∫ z : UnitCircle, g z ∂(mu i : Measure UnitCircle)‖ +
              ‖(∫ z : UnitCircle, g z ∂(mu i : Measure UnitCircle) -
                  ∫ z : UnitCircle, g z ∂H) +
                (∫ z : UnitCircle, g z ∂H -
                  ∫ z : UnitCircle, f z ∂H)‖ := norm_add_le _ _
        _ ≤
            ‖∫ z : UnitCircle, f z ∂(mu i : Measure UnitCircle) -
                ∫ z : UnitCircle, g z ∂(mu i : Measure UnitCircle)‖ +
              (‖∫ z : UnitCircle, g z ∂(mu i : Measure UnitCircle) -
                  ∫ z : UnitCircle, g z ∂H‖ +
                ‖∫ z : UnitCircle, g z ∂H -
                  ∫ z : UnitCircle, f z ∂H‖) := by
            gcongr
            exact norm_add_le _ _
        _ = _ := by ring
    _ < ε := by linarith

end

end CircleEquidistribution
end Erdos378
