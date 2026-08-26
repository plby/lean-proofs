import ErdosProblems.Erdos67.StationaryEntropy
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Finite-coordinate laws of probability measures

This connects the finite probability-vector entropy estimates with the limiting
stationary probability measure. All finite expectations are identified with
their measure-theoretic integrals.
-/

open scoped BigOperators
open Finset MeasureTheory

namespace Erdos67.FiniteEntropy

variable {A B Ω : Type*} [Fintype A] [Fintype B]

/-- Convert a finite probability mass function to a real probability vector. -/
noncomputable def ofPMF (p : PMF A) : FinProb A :=
  ⟨fun a ↦ (p a).toReal, by
    constructor
    · intro a
      exact ENNReal.toReal_nonneg
    · rw [← ENNReal.toReal_sum (fun a _ ↦ p.apply_ne_top a)]
      have hp : (∑ a, p a) = 1 := by simpa only [tsum_fintype] using p.tsum_coe
      rw [hp, ENNReal.toReal_one]⟩

theorem ofPMF_apply (p : PMF A) (a : A) : ofPMF p a = (p a).toReal := rfl

theorem ofPMF_map (p : PMF A) (f : A → B) :
    ofPMF (p.map f) = stdSimplex.map f (ofPMF p) := by
  classical
  apply Subtype.ext
  funext b
  change ofPMF (p.map f) b = stdSimplex.map f (ofPMF p) b
  rw [ofPMF_apply, PMF.map_apply, tsum_fintype, stdSimplex.map_coe]
  simp only [FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases hab : f a = b
    · subst b
      simp only [if_true, ofPMF_apply]
    · simp only [hab, Ne.symm hab, if_false, ENNReal.toReal_zero]
  · intro a _
    split_ifs
    · exact p.apply_ne_top a
    · exact ENNReal.zero_ne_top

theorem ofPMF_toPMF (p : FinProb A) : ofPMF (toPMF p) = p := by
  apply Subtype.ext
  funext a
  change (ENNReal.ofReal (p a)).toReal = p a
  exact ENNReal.toReal_ofReal (prob_nonneg p a)

theorem map_equiv_apply (p : FinProb A) (e : A ≃ B) (a : A) :
    stdSimplex.map e p (e a) = p a := by
  classical
  simp only [stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    simp only [show e b ≠ e a from fun h ↦ hba (e.injective h), if_false]
  · simp

theorem eq_uniformVector_of_constant [Nonempty A] (p : FinProb A)
    (h : ∀ a b, p a = p b) : p = uniformVector := by
  apply Subtype.ext
  funext a
  change p a = (Fintype.card A : ℝ)⁻¹
  have hsum : (Fintype.card A : ℝ) * p a = 1 := by
    have hs := stdSimplex.sum_eq_one p
    have hconst : ∀ b, p b = p a := fun b ↦ h b a
    simpa only [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hs
  have hc : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  calc
    p a = ((Fintype.card A : ℝ) * p a) / Fintype.card A := by field_simp
    _ = (Fintype.card A : ℝ)⁻¹ := by rw [hsum, one_div]

variable [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSingletonClass A]
variable [MeasurableSpace B] [MeasurableSingletonClass B]

/-- The real finite law of a measurable finite-valued random variable. -/
noncomputable def measureLaw (Q : ProbabilityMeasure Ω) (X : Ω → A) (hX : Measurable X) :
    FinProb A :=
  ofPMF (Q.map hX.aemeasurable : Measure A).toPMF

theorem measureLaw_apply (Q : ProbabilityMeasure Ω) (X : Ω → A) (hX : Measurable X) (a : A) :
    measureLaw Q X hX a = ((Q : Measure Ω) (X ⁻¹' {a})).toReal := by
  change ((Q.map hX.aemeasurable : Measure A) {a}).toReal = _
  rw [Q.map_apply' hX.aemeasurable (measurableSet_singleton a)]

theorem measureLaw_expectation (Q : ProbabilityMeasure Ω) (X : Ω → A)
    (hX : Measurable X) (F : A → ℝ) :
    (∑ a, measureLaw Q X hX a * F a) = ∫ ω, F (X ω) ∂(Q : Measure Ω) := by
  change (∑ a, ((Q.map hX.aemeasurable : Measure A).toPMF a).toReal • F a) = _
  rw [← PMF.integral_eq_sum, Measure.toPMF_toMeasure]
  change (∫ a, F a ∂Measure.map X (Q : Measure Ω)) = _
  exact integral_map hX.aemeasurable (measurable_of_countable F).aestronglyMeasurable

theorem measureLaw_map (Q : ProbabilityMeasure Ω) (X : Ω → A)
    (hX : Measurable X) (g : A → B) (hg : Measurable g) :
    measureLaw Q (g ∘ X) (hg.comp hX) = stdSimplex.map g (measureLaw Q X hX) := by
  unfold measureLaw
  rw [← ofPMF_map]
  congr 1
  apply (PMF.toMeasure_inj).mp
  rw [Measure.toPMF_toMeasure, ← PMF.toMeasure_map g _ hg, Measure.toPMF_toMeasure]
  change Measure.map (g ∘ X) (Q : Measure Ω) =
    Measure.map g (Measure.map X (Q : Measure Ω))
  exact (Measure.map_map hg hX).symm

theorem fstMarginal_measureLaw (Q : ProbabilityMeasure Ω) (X : Ω → A)
    (Y : Ω → B) (hX : Measurable X) (hY : Measurable Y) :
    fstMarginal (measureLaw Q (fun ω ↦ (X ω, Y ω)) (hX.prodMk hY)) =
      measureLaw Q X hX := by
  exact (measureLaw_map Q (fun ω ↦ (X ω, Y ω)) (hX.prodMk hY)
    Prod.fst measurable_fst).symm

theorem sndMarginal_measureLaw (Q : ProbabilityMeasure Ω) (X : Ω → A)
    (Y : Ω → B) (hX : Measurable X) (hY : Measurable Y) :
    sndMarginal (measureLaw Q (fun ω ↦ (X ω, Y ω)) (hX.prodMk hY)) =
      measureLaw Q Y hY := by
  exact (measureLaw_map Q (fun ω ↦ (X ω, Y ω)) (hX.prodMk hY)
    Prod.snd measurable_snd).symm

theorem measureLaw_comp_preserving (Q : ProbabilityMeasure Ω) (T : Ω → Ω)
    (hT : Measurable T) (hpres : Measure.map T (Q : Measure Ω) = (Q : Measure Ω))
    (X : Ω → A) (hX : Measurable X) :
    measureLaw Q (X ∘ T) (hX.comp hT) = measureLaw Q X hX := by
  apply Subtype.ext
  funext a
  change measureLaw Q (X ∘ T) (hX.comp hT) a = measureLaw Q X hX a
  rw [measureLaw_apply, measureLaw_apply]
  congr 1
  calc
    (Q : Measure Ω) ((X ∘ T) ⁻¹' {a}) = (Measure.map T (Q : Measure Ω)) (X ⁻¹' {a}) :=
      (Measure.map_apply hT (hX (measurableSet_singleton a))).symm
    _ = (Q : Measure Ω) (X ⁻¹' {a}) := by rw [hpres]

end Erdos67.FiniteEntropy
