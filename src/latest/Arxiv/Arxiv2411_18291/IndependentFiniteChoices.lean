import Arxiv.Arxiv2411_18291.UniformFiniteFibers
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Independent uniform choices from finite sets

The choices may have different finite types. A coordinate event has its
uniform marginal law, and weighting its indicator by the coordinate's
cardinality gives expectation equal to the number of successful choices.
-/

open Finset MeasureTheory ProbabilityTheory

noncomputable section

namespace Arxiv2411_18291.RandomFiniteChoice

variable {I : Type*}

abbrev Sample (A : I → Type*) := ∀ i, A i

def probability (A : I → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSingletonClass (A i)] : Measure (Sample A) :=
  Measure.infinitePi fun i => (PMF.uniformOfFintype (A i)).toMeasure

variable {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
variable [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSingletonClass (A i)]

instance : IsProbabilityMeasure (probability A) := by
  unfold probability
  infer_instance

theorem coordinate_law (i : I) :
    (probability A).map (fun ω => ω i) = (PMF.uniformOfFintype (A i)).toMeasure :=
  Measure.infinitePi_map_eval (fun i => (PMF.uniformOfFintype (A i)).toMeasure) i

omit [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] in
theorem coordinate_event_measurable (i : I) (s : Finset (A i)) :
    MeasurableSet {ω : Sample A | ω i ∈ s} :=
  (measurable_pi_apply i) s.measurableSet

theorem probability_coordinate (i : I) (s : Set (A i)) :
    probability A ((fun ω : Sample A => ω i) ⁻¹' s) =
      (PMF.uniformOfFintype (A i)).toMeasure s := by
  rw [← Measure.map_apply (measurable_pi_apply i) (Set.toFinite s).measurableSet, coordinate_law]

theorem probabilityReal_coordinate_finset (i : I) (s : Finset (A i)) :
    (probability A).real {ω | ω i ∈ s} = s.card / (Fintype.card (A i) : ℝ) := by
  classical
  change (probability A ((fun ω : Sample A => ω i) ⁻¹' (s : Set (A i)))).toReal = _
  rw [probability_coordinate]
  have hf (x : A i) : univ.filter (fun y => y = x) = {x} := by ext y; simp
  exact uniform_equal_fibers_probability (id : A i → A i) (Classical.choice inferInstance)
    (by intro x; simp only [id_eq, hf, card_singleton]) s

theorem independent (f : ∀ i, A i → ℝ) :
    iIndepFun (fun i (ω : Sample A) => f i (ω i)) (probability A) :=
  iIndepFun_infinitePi (X := f) (fun i => measurable_of_countable (f i))

def weightedMember (i : I) (s : Finset (A i)) : Sample A → ℝ :=
  {ω : Sample A | ω i ∈ s}.indicator fun _ => Fintype.card (A i)

omit [∀ i, Nonempty (A i)] [∀ i, MeasurableSpace (A i)]
    [∀ i, MeasurableSingletonClass (A i)] in
theorem weightedMember_bounds (i : I) (s : Finset (A i)) (ω : Sample A) :
    0 ≤ weightedMember i s ω ∧ weightedMember i s ω ≤ Fintype.card (A i) := by
  classical
  simp only [weightedMember, Set.indicator]
  split_ifs <;> simp only [le_refl, Nat.cast_nonneg, and_self]

omit [∀ i, Nonempty (A i)] in
theorem weightedMember_measurable (i : I) (s : Finset (A i)) :
    Measurable (weightedMember i s) :=
  measurable_const.indicator (coordinate_event_measurable i s)

theorem weightedMember_integrable (i : I) (s : Finset (A i)) :
    Integrable (weightedMember i s) (probability A) :=
  (integrable_const _).indicator (coordinate_event_measurable i s)

theorem weightedMember_mean (i : I) (s : Finset (A i)) :
    (∫ ω, weightedMember i s ω ∂probability A) = s.card := by
  rw [weightedMember, integral_indicator_const _ (coordinate_event_measurable i s),
    smul_eq_mul, probabilityReal_coordinate_finset]
  exact div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero : Fintype.card (A i) ≠ 0))

theorem weightedMember_independent (s : ∀ i, Finset (A i)) :
    iIndepFun (fun i => weightedMember i (s i)) (probability A) := by
  classical
  have heq : (fun i => weightedMember i (s i)) =
      (fun i (ω : Sample A) => if ω i ∈ s i then (Fintype.card (A i) : ℝ) else 0) := by
    funext i ω
    simp only [weightedMember, Set.indicator, Set.mem_ofPred_eq]
  rw [heq]
  exact independent (fun i x => if x ∈ s i then (Fintype.card (A i) : ℝ) else 0)

end Arxiv2411_18291.RandomFiniteChoice
