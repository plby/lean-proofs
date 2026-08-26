import ErdosProblems.Erdos1002.FactorialEventExpansion
import ErdosProblems.Erdos1002.MultivariatePoissonFactorial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Mixed factorial measures as labeled distinct tuples

This is the multivariate form of the factorial-event expansion.  Distinctness
within each label is encoded by an embedding.  If the labeled event sets are
pairwise disjoint, the file also proves that the resulting tuple is globally
distinct, so no cross-label diagonal is hidden in the notation.
-/

open MeasureTheory Set Finset
open scoped BigOperators

namespace Erdos1002

noncomputable section

open MultivariateFactorialMomentMethod

local instance mixedFactorialEventExpansionPropDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

variable {Ω I ι : Type*} [DecidableEq I] [Fintype ι]

/-- Simultaneous event selected by a labeled family of internally distinct
tuples. -/
def mixedTupleEvent {s : Finset I} {k : ι → ℕ}
    (E : ι → I → Set Ω) (F : ∀ i, Fin (k i) ↪ s) : Set Ω :=
  ⋂ i, tupleEvent (E i) (F i)

omit [DecidableEq I] in
theorem measurableSet_mixedTupleEvent [MeasurableSpace Ω]
    {s : Finset I} {k : ι → ℕ} {E : ι → I → Set Ω}
    (hE : ∀ (i : ι) (q : I), q ∈ s → MeasurableSet (E i q))
    (F : ∀ i, Fin (k i) ↪ s) :
    MeasurableSet (mixedTupleEvent E F) := by
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_tupleEvent (fun q hq ↦ hE i q hq) (F i)

theorem mixedDescFactorial_finiteEventCount_eq_sum_indicators
    (s : Finset I) (E : ι → I → Set Ω) (ω : Ω) (k : ι → ℕ) :
    mixedDescFactorial k (fun i ↦ finiteEventCount s (E i) ω) =
      ∑ F : ∀ i, Fin (k i) ↪ (s : Finset I),
        (mixedTupleEvent E F).indicator (fun _ ↦ (1 : ℝ)) ω := by
  classical
  unfold mixedDescFactorial
  simp_rw [cast_finiteEventCount_descFactorial_eq_sum_indicators]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro F _hF
  by_cases h : ∀ i, ω ∈ tupleEvent (E i) (F i)
  · have hmixed : ω ∈ mixedTupleEvent E F := by
      exact Set.mem_iInter.mpr h
    simp only [Set.indicator_of_mem hmixed]
    apply Finset.prod_eq_one
    intro i _hi
    exact Set.indicator_of_mem (h i) _
  · have hmixed : ω ∉ mixedTupleEvent E F := by
      simpa only [mixedTupleEvent, Set.mem_iInter] using! h
    obtain ⟨i, hi⟩ := not_forall.mp h
    rw [Set.indicator_of_notMem hmixed]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Set.indicator_of_notMem hi _

theorem integral_mixedDescFactorial_finiteEventCount
    [MeasurableSpace Ω] (s : Finset I) (E : ι → I → Set Ω)
    (k : ι → ℕ) (mu : Measure Ω) [IsFiniteMeasure mu]
    (hE : ∀ (i : ι) (q : I), q ∈ s → MeasurableSet (E i q)) :
    ∫ ω, mixedDescFactorial k (fun i ↦ finiteEventCount s (E i) ω) ∂mu =
      ∑ F : ∀ i, Fin (k i) ↪ (s : Finset I),
        mu.real (mixedTupleEvent E F) := by
  simp_rw [mixedDescFactorial_finiteEventCount_eq_sum_indicators]
  rw [MeasureTheory.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro F _hF
    exact MeasureTheory.integral_indicator_one
      (measurableSet_mixedTupleEvent hE F)
  · intro F _hF
    exact (integrable_const (1 : ℝ)).indicator
      (measurableSet_mixedTupleEvent hE F)

omit [DecidableEq I] [Fintype ι] in
/-- Pairwise disjoint labels force distinctness across labels, while each
`F i` already enforces distinctness within its own label. -/
theorem mixedTuple_globally_injective_of_pairwise_disjoint
    {s : Finset I} {k : ι → ℕ} (E : ι → I → Set Ω)
    (hdisj : ∀ i j, i ≠ j → ∀ q, Disjoint (E i q) (E j q))
    (ω : Ω) (F : ∀ i, Fin (k i) ↪ s)
    (hω : ω ∈ mixedTupleEvent E F) :
    Function.Injective
      (fun z : Σ i, Fin (k i) ↦ ((F z.1 z.2 : s) : I)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ hz
  have hall : ∀ i j, ω ∈ E i (F i j) := by
    intro i' j'
    have hi : ω ∈ tupleEvent (E i') (F i') := Set.mem_iInter.mp hω i'
    exact Set.mem_iInter.mp hi j'
  by_cases hii : i = j
  · subst j
    have hab : a = b := by
      apply (F i).injective
      apply Subtype.ext
      exact hz
    subst b
    rfl
  · exfalso
    have hleft : ω ∈ E i (F i a) := hall i a
    have hright0 : ω ∈ E j (F j b) := hall j b
    have hq : ((F i a : s) : I) = ((F j b : s) : I) := hz
    have hright : ω ∈ E j (F i a) := by
      simpa only [hq] using! hright0
    exact Set.disjoint_left.mp (hdisj i j hii (F i a)) hleft hright

/-- Mixed factorial moment of the actual marked count vector, expanded into
Lebesgue measures of labeled tuple events. -/
theorem mixedFactorialMoment_markedCount_eq_sum_tupleMeasures
    (N P : ℕ) (B : ι → Set (ℝ × ℝ × ℝ))
    (hB : ∀ i, MeasurableSet (B i)) (k : ι → ℕ) :
    ∫ α, mixedDescFactorial k
        (fun i ↦ markedResonanceCount N P (B i) α) ∂uniform01Measure =
      ∑ F : ∀ i, Fin (k i) ↪ (Finset.Icc 1 P : Finset ℕ),
        uniform01Measure.real
          (mixedTupleEvent (fun i ↦ markedDenominatorEvent N (B i)) F) := by
  have h := integral_mixedDescFactorial_finiteEventCount
    (Finset.Icc 1 P) (fun i ↦ markedDenominatorEvent N (B i))
    k uniform01Measure
    (fun i q _hq ↦ measurableSet_markedDenominatorEvent N (hB i) q)
  simpa only [← markedResonanceCount_eq_finiteEventCount] using! h

end

end Erdos1002
