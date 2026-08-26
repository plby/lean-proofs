/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.Wiener

namespace Erdos254

open Filter MeasureTheory Set
open scoped BigOperators Topology ENNReal

/-- A countable set can be exhausted by a finite set up to arbitrarily small
mass, for a finite measure. -/
lemma exists_finite_small_tail {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (μ : Measure X) [IsFiniteMeasure μ]
    {S : Set X} (hS : S.Countable) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : Finset X, (F : Set X) ⊆ S ∧ μ.real (S \ (F : Set X)) < ε := by
  classical
  let : Countable S := hS.to_subtype
  cases isEmpty_or_nonempty S with
  | inl hempty =>
      have hSE : S = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact isEmptyElim (⟨x, hx⟩ : S)
      exact ⟨∅, by simp, by simpa [hSE] using hε⟩
  | inr hnonempty =>
      obtain ⟨e, he⟩ := exists_surjective_nat S
      let F : ℕ → Finset X := fun N ↦ (Finset.range N).image (fun n ↦ (e n : X))
      have hFS (N : ℕ) : (F N : Set X) ⊆ S := by
        intro x hx
        obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hx
        exact (e n).property
      have hmono : Monotone F := fun i j hij ↦
        Finset.image_subset_image (Finset.range_mono hij)
      have hanti : Antitone (fun N ↦ S \ (F N : Set X)) := by
        intro i j hij x hx
        exact ⟨hx.1, fun hxi ↦ hx.2 (hmono hij hxi)⟩
      have hinter : (⋂ N, S \ (F N : Set X)) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hxS := (Set.mem_iInter.mp hx 0).1
        obtain ⟨n, hn⟩ := he ⟨x, hxS⟩
        apply (Set.mem_iInter.mp hx (n + 1)).2
        apply Finset.mem_image.mpr
        exact ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self _), congrArg Subtype.val hn⟩
      have ht := tendsto_measure_iInter_atTop (μ := μ)
        (fun N ↦ (hS.measurableSet.diff (F N).measurableSet).nullMeasurableSet)
        hanti ⟨0, measure_ne_top _ _⟩
      have ht' : Tendsto (fun N ↦ μ.real (S \ (F N : Set X))) atTop (𝓝 0) := by
        have ht0 : Tendsto (fun N ↦ μ (S \ (F N : Set X))) atTop (𝓝 0) := by
          simpa only [Function.comp_def, hinter, measure_empty] using ht
        simpa only [Measure.real, ENNReal.toReal_zero, Function.comp_def] using
          (ENNReal.continuousAt_toReal (show (0 : ℝ≥0∞) ≠ ⊤ by simp)).tendsto.comp ht0
      obtain ⟨N, hN⟩ := (ht'.eventually_lt_const hε).exists
      exact ⟨F N, hFS N, hN⟩

def circleAtoms (μ : Measure Circle) : Set Circle := {z | μ {z} ≠ 0}

lemma circleAtoms_countable (μ : Measure Circle) [IsFiniteMeasure μ] :
    (circleAtoms μ).Countable := by
  simpa [circleAtoms, pos_iff_ne_zero] using
    (Measure.countable_meas_level_set_pos (μ := μ) measurable_id)

noncomputable def circleAtomicPart (μ : Measure Circle) : Measure Circle :=
  μ.restrict (circleAtoms μ)

noncomputable def circleContinuousPart (μ : Measure Circle) : Measure Circle :=
  μ.restrict (circleAtoms μ)ᶜ

instance circleAtomicPart_finite (μ : Measure Circle) [IsFiniteMeasure μ] :
    IsFiniteMeasure (circleAtomicPart μ) := by unfold circleAtomicPart; infer_instance

instance circleContinuousPart_finite (μ : Measure Circle) [IsFiniteMeasure μ] :
    IsFiniteMeasure (circleContinuousPart μ) := by unfold circleContinuousPart; infer_instance

instance circleContinuousPart_nullSingleton (μ : Measure Circle) :
    NullSingletonClass (circleContinuousPart μ) := by
  constructor
  intro z
  rw [circleContinuousPart, Measure.restrict_apply (measurableSet_singleton z)]
  by_cases hz : z ∈ circleAtoms μ
  · have h : ({z} : Set Circle) ∩ (circleAtoms μ)ᶜ = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_singleton_iff, mem_compl_iff, mem_empty_iff_false, iff_false]
      rintro ⟨rfl, hx⟩
      exact hx hz
    rw [h, measure_empty]
  · apply measure_mono_null inter_subset_left
    simpa only [circleAtoms, mem_ofPred_eq, not_not] using hz

lemma circle_atomic_add_continuous (μ : Measure Circle) [IsFiniteMeasure μ] :
    circleAtomicPart μ + circleContinuousPart μ = μ :=
  Measure.restrict_add_restrict_compl (circleAtoms_countable μ).measurableSet

lemma circleCoeff_add (μ ν : Measure Circle) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (n : ℕ) :
    circleCoeff (μ + ν) n = circleCoeff μ n + circleCoeff ν n := by
  apply integral_add_measure
  all_goals
    exact (circleCoordinate.continuous.pow n).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma norm_circleCoeff_restrict_le (μ : Measure Circle) [IsFiniteMeasure μ]
    (S : Set Circle) (n : ℕ) : ‖circleCoeff (μ.restrict S) n‖ ≤ μ.real S := by
  calc
    _ ≤ ∫ z, ‖(z : ℂ) ^ n‖ ∂μ.restrict S := norm_integral_le_integral_norm _
    _ = μ.real S := by simp [norm_pow, Circle.norm_coe, Measure.real]

lemma circleCoeff_finset (μ : Measure Circle) [IsFiniteMeasure μ]
    (F : Finset Circle) (n : ℕ) :
    circleCoeff (μ.restrict (F : Set Circle)) n =
      ∑ z ∈ F, (μ.real {z} : ℂ) * (z : ℂ) ^ n := by
  have hint : IntegrableOn (fun z : Circle ↦ (z : ℂ) ^ n) (F : Set Circle) μ :=
    (circleCoordinate.continuous.pow n).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ z in (F : Set Circle), (z : ℂ) ^ n ∂μ := rfl
    _ = ∑ z ∈ F, μ.real {z} • (z : ℂ) ^ n := setIntegral_finset F hint
    _ = _ := Finset.sum_congr rfl fun z _ ↦ RCLike.real_smul_eq_coe_mul _ _

lemma norm_atomic_sub_finite_le (μ : Measure Circle) [IsFiniteMeasure μ]
    (F : Finset Circle) (hF : (F : Set Circle) ⊆ circleAtoms μ) (n : ℕ) :
    ‖circleCoeff (circleAtomicPart μ) n - circleCoeff (μ.restrict (F : Set Circle)) n‖ ≤
      μ.real (circleAtoms μ \ (F : Set Circle)) := by
  have hsplit : circleAtomicPart μ = μ.restrict (F : Set Circle) +
      μ.restrict (circleAtoms μ \ (F : Set Circle)) := by
    rw [← Measure.restrict_union' disjoint_sdiff_self_right F.measurableSet]
    apply congrArg μ.restrict
    ext z
    constructor
    · intro hz
      by_cases h : z ∈ F
      · exact Or.inl h
      · exact Or.inr ⟨hz, h⟩
    · rintro (h | h)
      · exact hF h
      · exact h.1
  rw [hsplit, circleCoeff_add, add_sub_cancel_left]
  exact norm_circleCoeff_restrict_le μ _ n

end Erdos254
