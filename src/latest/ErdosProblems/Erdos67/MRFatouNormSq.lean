import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# A Fatou lemma for complex square norms

This file packages the precise lower-semicontinuity statement used when a
finite Perron integral converges pointwise to a short sum.  Keeping it
separate makes the continuous Perron-limit passage independent of the
number-theoretic definitions.
-/

open MeasureTheory Filter Topology

noncomputable section

/-- If complex functions converge almost everywhere and their squared norms
have a uniform integral bound, then the squared norm of the limit has the
same bound. -/
theorem integral_normSq_le_of_ae_tendsto_of_uniform
    {F : ℕ → ℝ → ℂ} {G : ℝ → ℂ} {s : Set ℝ} {E : ℝ}
    (hF : ∀ n, IntegrableOn (fun x ↦ Complex.normSq (F n x)) s)
    (hG : IntegrableOn (fun x ↦ Complex.normSq (G x)) s)
    (hlim : ∀ᵐ x ∂(volume.restrict s),
      Tendsto (fun n ↦ F n x) atTop (nhds (G x)))
    (hE : 0 ≤ E)
    (hbound : ∀ n, ∫ x in s, Complex.normSq (F n x) ≤ E) :
    (∫ x in s, Complex.normSq (G x)) ≤ E := by
  let f : ℕ → ℝ → ENNReal := fun n x ↦ ENNReal.ofReal (Complex.normSq (F n x))
  let g : ℝ → ENNReal := fun x ↦ ENNReal.ofReal (Complex.normSq (G x))
  have hfmeas : ∀ n, AEMeasurable (f n) (volume.restrict s) := by
    intro n
    exact (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hglim : ∀ᵐ x ∂(volume.restrict s),
      Tendsto (fun n ↦ f n x) atTop (nhds (g x)) := by
    filter_upwards [hlim] with x hx
    exact ((ENNReal.continuous_ofReal.comp Complex.continuous_normSq).tendsto _).comp hx
  have hfatou := MeasureTheory.lintegral_liminf_le' (u := atTop) hfmeas
  rw [show (∫⁻ x, liminf (fun n ↦ f n x) atTop ∂volume.restrict s) =
      ∫⁻ x, g x ∂volume.restrict s by
        apply lintegral_congr_ae
        filter_upwards [hglim] with x hx
        exact hx.liminf_eq] at hfatou
  have hfi (n : ℕ) : ∫⁻ x, f n x ∂volume.restrict s =
      ENNReal.ofReal (∫ x in s, Complex.normSq (F n x)) := by
    symm
    exact ofReal_integral_eq_lintegral_ofReal (hF n)
      (ae_of_all _ fun x ↦ Complex.normSq_nonneg _)
  have hgi : ∫⁻ x, g x ∂volume.restrict s =
      ENNReal.ofReal (∫ x in s, Complex.normSq (G x)) := by
    symm
    exact ofReal_integral_eq_lintegral_ofReal hG
      (ae_of_all _ fun x ↦ Complex.normSq_nonneg _)
  rw [hgi] at hfatou
  have hliminf : liminf (fun n ↦ ∫⁻ x, f n x ∂volume.restrict s) atTop ≤
      ENNReal.ofReal E := by
    apply liminf_le_of_frequently_le'
    exact .of_forall fun n ↦ by
      rw [hfi n]
      exact ENNReal.ofReal_le_ofReal (hbound n)
  have hof := hfatou.trans hliminf
  exact (ENNReal.ofReal_le_ofReal_iff hE).mp hof
