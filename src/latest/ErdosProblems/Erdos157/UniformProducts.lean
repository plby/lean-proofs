import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Tactic
import ErdosProblems.Erdos157.FiniteDensity

/-! Uniform finite-coordinate cylinders and the countable avoidance principle. -/

namespace Erdos157.Elementary
namespace UniformProducts

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {I : Type*} [DecidableEq I] (X : I → Type*)
    [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

noncomputable def coordinateMeasure (i : I) : Measure (X i) := uniformOn Set.univ

instance coordinateMeasure_isProbability (i : I) : IsProbabilityMeasure (coordinateMeasure X i) := by
  unfold coordinateMeasure
  infer_instance

noncomputable def productMeasure : Measure (∀ i, X i) := Measure.infinitePi (coordinateMeasure X)

instance productMeasure_isProbability : IsProbabilityMeasure (productMeasure X) := by
  unfold productMeasure
  infer_instance

theorem finite_pi_uniform [Fintype I] :
    Measure.pi (coordinateMeasure X) = uniformOn (Set.univ : Set (∀ i, X i)) := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.pi_singleton]
  simp only [coordinateMeasure, uniformOn_univ, Measure.count_singleton, one_div,
    Fintype.card_pi, Nat.cast_prod]
  rw [ENNReal.prod_inv_distrib (by
    intro i _ j _ _
    exact Or.inr (ENNReal.natCast_ne_top _))]

theorem cylinder_measure (s : Finset I) (B : Finset (∀ i : s, X i)) :
    productMeasure X {x | s.restrict x ∈ B} =
      (B.card : ℝ≥0∞) / Fintype.card (∀ i : s, X i) := by
  have hm : MeasurableSet (B : Set (∀ i : s, X i)) := B.measurableSet
  change productMeasure X (s.restrict ⁻¹' (B : Set (∀ i : s, X i))) = _
  rw [← Measure.map_apply (Finset.measurable_restrict s) hm]
  change (Measure.infinitePi (coordinateMeasure X)).map s.restrict _ = _
  rw [Measure.infinitePi_map_restrict]
  change (Measure.pi (coordinateMeasure (fun i : s => X i))) (B : Set (∀ i : s, X i)) = _
  rw [finite_pi_uniform, uniformOn_univ, Measure.count_apply_finset]

theorem cylinder_measure_real (s : Finset I) (B : Finset (∀ i : s, X i)) :
    (productMeasure X).real {x | s.restrict x ∈ B} =
      (B.card : ℝ) / Fintype.card (∀ i : s, X i) := by
  rw [measureReal_def, cylinder_measure]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]

theorem cylinder_density (s : Finset I) (p : (∀ i : s, X i) → Prop) :
    (productMeasure X).real {x | p (s.restrict x)} = finiteDensity p := by
  classical
  let B := Finset.univ.filter p
  have he : {x | p (s.restrict x)} = {x | s.restrict x ∈ B} := by ext x; simp [B]
  rw [he, cylinder_measure_real, ← finiteDensity_finset B]
  exact finiteDensity_congr (fun x => by simp [B])

theorem prefix_density (Y : ℕ → Type*) [∀ i, Fintype (Y i)] [∀ i, Nonempty (Y i)]
    [∀ i, MeasurableSpace (Y i)] [∀ i, MeasurableSingletonClass (Y i)]
    (k : ℕ) (p : (∀ i : Fin k, Y i) → Prop) :
    (productMeasure Y).real {x | p (fun i => x i)} = finiteDensity p := by
  classical
  let e : (∀ i : (Finset.range k), Y i) ≃ (∀ i : Fin k, Y i) :=
    { toFun := fun a i => a ⟨i.1, Finset.mem_range.mpr i.2⟩
      invFun := fun a i => a ⟨i.1, Finset.mem_range.mp i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := cylinder_density Y (Finset.range k) (fun x => p (e x))
  rw [finiteDensity_equiv e p] at hc
  exact hc

theorem coordinate_density (i : I) (p : X i → Prop) :
    (productMeasure X).real {x | p (x i)} = finiteDensity p := by
  classical
  let B : Finset (X i) := Finset.univ.filter p
  have he : {x : ∀ j, X j | p (x i)} = (fun x => x i) ⁻¹' (B : Set (X i)) := by ext x; simp [B]
  have hm : productMeasure X {x | p (x i)} = (B.card : ℝ≥0∞) / Fintype.card (X i) := by
    rw [he, ← Measure.map_apply (measurable_pi_apply i) B.measurableSet]
    change ((Measure.infinitePi (coordinateMeasure X)).map (fun x => x i)) _ = _
    rw [Measure.infinitePi_map_eval, coordinateMeasure, uniformOn_univ, Measure.count_apply_finset]
  rw [measureReal_def, hm, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ← finiteDensity_finset B]
  exact finiteDensity_congr (fun x => by simp [B])

end UniformProducts

open MeasureTheory
open scoped ENNReal

/-- A countable union of events whose total upper bound is less than one
cannot cover a probability space. No independence is needed for this step. -/
theorem exists_avoiding_events {Ω J : Type*} [MeasurableSpace Ω] [Countable J]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (bad : J → Set Ω) (ε : J → ℝ)
    (hε : ∀ j, 0 ≤ ε j) (hsum : Summable ε) (htotal : ∑' j, ε j < 1)
    (hbad : ∀ j, μ.real (bad j) ≤ ε j) : ∃ x, ∀ j, x ∉ bad j := by
  classical
  have hb (j : J) : μ (bad j) ≤ ENNReal.ofReal (ε j) :=
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) (hε j)).mpr (hbad j)
  have hbound : μ (⋃ j, bad j) < 1 := by
    calc
      _ ≤ ∑' j, μ (bad j) := measure_iUnion_le bad
      _ ≤ ∑' j, ENNReal.ofReal (ε j) := ENNReal.tsum_le_tsum hb
      _ = ENNReal.ofReal (∑' j, ε j) := (ENNReal.ofReal_tsum_of_nonneg hε hsum).symm
      _ < 1 := by
        simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr htotal
  by_contra h
  have hu : (⋃ j, bad j) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_contra hx
    apply h
    refine ⟨x, ?_⟩
    simpa only [not_exists] using hx
  rw [hu, measure_univ] at hbound
  exact lt_irrefl _ hbound

/-- Summable eventual failure bounds leave a realization with only finitely many
failures. The initial events need no quantitative bound. -/
theorem exists_eventually_avoiding_events {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (bad : ℕ → Set Ω) (ε : ℕ → ℝ)
    (hsum : Summable ε)
    (hbad : ∀ᶠ n in Filter.atTop, μ.real (bad n) ≤ ε n) :
    ∃ x, ∀ᶠ n in Filter.atTop, x ∉ bad n := by
  have hs : Summable (fun n => μ.real (bad n)) :=
    hsum.of_norm_bounded_eventually_nat (hbad.mono (fun n hn => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg : 0 ≤ μ.real (bad n))] using hn))
  have he (n : ℕ) : μ (bad n) = ENNReal.ofReal (μ.real (bad n)) := by
    exact (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
  have ht : (∑' n, μ (bad n)) ≠ ⊤ := by
    simp_rw [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => measureReal_nonneg) hs]
    exact ENNReal.ofReal_ne_top
  exact (ae_eventually_notMem ht).exists

end Erdos157.Elementary
