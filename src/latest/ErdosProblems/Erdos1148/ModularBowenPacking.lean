import ErdosProblems.Erdos1148.ModularHaarBowenBall
import ErdosProblems.Erdos1148.FiniteMeasurePacking

/-! # Packing modular Bowen balls gives coherent covers with a volume bound -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure
open scoped MatrixGroups ENNReal

lemma modularForwardHaarBall_overlap_center {η S : ℝ} (hη : 0 ≤ η) (hηone : η ≤ 1)
    (hS : 0 ≤ S) (g h : SL(2, ℝ))
    (hoverlap : ¬ Disjoint (modularForwardHaarBall η S g) (modularForwardHaarBall η S h)) :
    modularMk g ∈ modularForwardHaarBall (4 * η) S h := by
  obtain ⟨z, ⟨u, hu, huz⟩, ⟨v, hv, hvz⟩⟩ := Set.not_disjoint_iff.mp hoverlap
  obtain ⟨γ, hγ⟩ := (modularMk_eq_iff (g * u) (h * v)).mp (huz.trans hvz.symm)
  have hsmall : v * u⁻¹ ∈ forwardHaarTube (4 * η) S := by
    apply forwardHaarTube_mono _ (forwardHaarTube_mul hη hη hS hv (forwardHaarTube_inv hS hu))
    nlinarith [mul_nonneg hη (sub_nonneg.mpr hηone)]
  refine ⟨v * u⁻¹, hsmall, ?_⟩
  change modularMk (h * (v * u⁻¹)) = modularMk g
  have hframe : h * (v * u⁻¹) = (γ : SL(2, ℝ)) * g := by
    calc
      _ = (h * v) * u⁻¹ := by group
      _ = ((γ : SL(2, ℝ)) * (g * u)) * u⁻¹ := by rw [hγ]
      _ = _ := by group
  rw [hframe, modularMk_integral_mul]

theorem exists_modularBowen_cover_of_ball_mass {η S c : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 32) (hS : 0 ≤ S) (hc : 0 < c)
    (A W : Set ModularOrbitSpace)
    (hmass : ∀ g : SL(2, ℝ), modularMk g ∈ A →
      ENNReal.ofReal (c * Real.exp (-S)) ≤
        normalizedModularHaarMeasure (modularForwardHaarBall η S g))
    (hcontain : ∀ g : SL(2, ℝ), modularMk g ∈ A → modularForwardHaarBall η S g ⊆ W) :
    ∃ (N : ℕ) (B : Fin N → Set SL(2, ℝ)),
      (N : ℝ) ≤ (normalizedModularHaarMeasure.real W / c) * Real.exp S ∧
      A ⊆ ⋃ i, modularMk '' B i ∧ (∀ i, IsCompact (B i)) ∧
      ∀ i, LiftForwardClose (16 * η) S (B i) := by
  classical
  have hcS : 0 < c * Real.exp (-S) := mul_pos hc (Real.exp_pos _)
  have hreal : ∀ g : SL(2, ℝ), modularMk g ∈ A → c * Real.exp (-S) ≤
      normalizedModularHaarMeasure.real (modularForwardHaarBall η S g) := by
    intro g hg
    have h := ENNReal.toReal_mono (measure_ne_top _ _) (hmass g hg)
    simpa only [ENNReal.toReal_ofReal hcS.le, Measure.real] using h
  obtain ⟨F, hF, _, hcard, hcover⟩ := exists_finite_measure_packing normalizedModularHaarMeasure
    (modularMk ⁻¹' A) (modularForwardHaarBall η S) W hcS
    (fun g _ => (isCompact_modularForwardHaarBall hη.le (by linarith) hS g).measurableSet)
    hreal hcontain
  let e := F.equivFin
  let B : Fin F.card → Set SL(2, ℝ) := fun i =>
    (fun u : SL(2, ℝ) => (e.symm i).val * u) '' forwardHaarTube (4 * η) S
  have hbound : (F.card : ℝ) ≤ (normalizedModularHaarMeasure.real W / c) * Real.exp S := by
    apply ((le_div_iff₀ hcS).mpr hcard).trans_eq
    rw [Real.exp_neg]
    field_simp [hc.ne', Real.exp_ne_zero]
  refine ⟨F.card, B, hbound, ?_, ?_, ?_⟩
  · intro x hx
    have hxout : modularMk x.out ∈ A := by simpa only [modularMk, Quotient.out_eq] using hx
    obtain ⟨g, hg, hoverlap⟩ := hcover x.out hxout
    have hmem := modularForwardHaarBall_overlap_center hη.le (by linarith) hS x.out g hoverlap
    have hmem' : x ∈ modularMk '' ((fun u : SL(2, ℝ) => g * u) '' forwardHaarTube (4 * η) S) := by
      simpa only [modularForwardHaarBall_eq, modularMk, Quotient.out_eq] using hmem
    refine Set.mem_iUnion.mpr ⟨e ⟨g, hg⟩, ?_⟩
    simpa only [B, Equiv.symm_apply_apply] using hmem'
  · intro i
    exact (isCompact_forwardHaarTube (by positivity) (by linarith) hS).image
      (continuous_const.mul continuous_id)
  · intro i
    have h := (forwardHaarTube_liftForwardClose (show 0 ≤ 4 * η by positivity)
      (show 4 * η ≤ 1 by linarith) hS).left_mul (e.symm i).val
    simpa only [B, show 4 * (4 * η) = 16 * η by ring] using h

end Erdos1148.DukeArithmetic
