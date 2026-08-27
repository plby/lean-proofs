import Arxiv.Arxiv2411_18291.IndependentTrials

/-! # Exposing some permutation colours and using the remaining independent colours -/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Arxiv2411_18291.RandomPermutation

variable {I J T V : Type*} [Fintype V] [DecidableEq V]
variable [MeasurableSpace (Equiv.Perm V)] [MeasurableSingletonClass (Equiv.Perm V)]

theorem probability_map_restrict (e : J ↪ I) :
    (probability I V).map (fun σ j => σ (e j)) = probability J V :=
  Measure.map_infinitePi_infinitePi_of_inj e.injective

theorem probability_map_trials {L : ℕ} (e : Fin L × J ↪ I) :
    (probability I V).map (fun σ j i => σ (e (j, i))) =
      IndependentTrials.probability (probability J V) L := by
  calc
    _ = ((probability I V).map (fun σ p => σ (e p))).map
        (MeasurableEquiv.curry (Fin L) J (Equiv.Perm V)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by
      rw [probability_map_restrict]
      exact Measure.infinitePi_map_curry
        (fun (_ : Fin L) (_ : J) => (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure)

theorem probability_trial_event [Finite J] {L : ℕ} (e : Fin L × J ↪ I)
    (B : Set (Fin L → Sample J V)) :
    (probability I V).real {σ | (fun j i => σ (e (j, i))) ∈ B} =
      (IndependentTrials.probability (probability J V) L).real B := by
  change ((probability I V) ((fun σ j i => σ (e (j, i))) ⁻¹' B)).toReal = _
  rw [← Measure.map_apply (by fun_prop) (Set.toFinite B).measurableSet,
    probability_map_trials]
  rfl

theorem probability_map_split [Finite J] [Finite T] (e : J ⊕ T ↪ I) :
    (probability I V).map (fun σ =>
      ((fun j => σ (e (.inl j))), (fun t => σ (e (.inr t))))) =
        (probability J V).prod (probability T V) := by
  let := Fintype.ofFinite J
  let := Fintype.ofFinite T
  let split := MeasurableEquiv.sumPiEquivProdPi (fun _ : J ⊕ T => Equiv.Perm V)
  calc
    _ = ((probability I V).map (fun σ j => σ (e j))).map split := by
      rw [Measure.map_map split.measurable (by fun_prop)]
      rfl
    _ = _ := by
      rw [probability_map_restrict]
      simpa only [probability, Measure.infinitePi_eq_pi] using
        (measurePreserving_sumPiEquivProdPi
          (fun _ : J ⊕ T => (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure)).map_eq

theorem probability_real_uncurry [Finite J] (L : ℕ)
    (B : Set (Sample (Fin L × J) V)) :
    (probability (Fin L × J) V).real B =
      (IndependentTrials.probability (probability J V) L).real
        {ω | (fun p => ω p.1 p.2) ∈ B} := by
  have hmap := Measure.infinitePi_map_curry_symm
    (fun (_ : Fin L) (_ : J) => (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure)
  change (probability (Fin L × J) V).real B =
    (IndependentTrials.probability (probability J V) L).real
      ((MeasurableEquiv.curry (Fin L) J (Equiv.Perm V)).symm ⁻¹' B)
  simp only [measureReal_def]
  rw [← Measure.map_apply
    (MeasurableEquiv.curry (Fin L) J (Equiv.Perm V)).symm.measurable
      (Set.toFinite B).measurableSet]
  exact congrArg (fun μ => μ.real B) hmap.symm

theorem probability_sections_le [Finite J] [Finite T] (e : J ⊕ T ↪ I)
    (B : Set (Sample J V × Sample T V)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hB : ∀ σ, (probability T V).real {τ | (σ, τ) ∈ B} ≤ δ) :
    (probability I V).real
      {σ | ((fun j => σ (e (.inl j))), (fun t => σ (e (.inr t)))) ∈ B} ≤ δ := by
  have hmeas : MeasurableSet B := (Set.toFinite B).measurableSet
  have hprod : ((probability J V).prod (probability T V)) B ≤ ENNReal.ofReal δ := by
    rw [Measure.prod_apply hmeas]
    calc
      _ ≤ ∫⁻ _ : Sample J V, ENNReal.ofReal δ ∂probability J V := by
        apply lintegral_mono
        intro σ
        exact (ENNReal.le_ofReal_iff_toReal_le (by finiteness) hδ).mpr (hB σ)
      _ = _ := by simp only [lintegral_const, measure_univ, mul_one]
  have hreal : ((probability J V).prod (probability T V)).real B ≤ δ := by
    exact (ENNReal.toReal_mono (by finiteness) hprod).trans_eq (ENNReal.toReal_ofReal hδ)
  change ((probability I V) ((fun σ =>
    ((fun j => σ (e (.inl j))), (fun t => σ (e (.inr t))))) ⁻¹' B)).toReal ≤ δ
  rw [← Measure.map_apply (by fun_prop) hmeas, probability_map_split e]
  exact hreal

end Arxiv2411_18291.RandomPermutation
