import Arxiv.Arxiv2411_18291.IndependentPermutationEvents
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# First and second moments of coloured candidate counts

Every candidate imposes constraints on the same finite set of independent
colours. The first moment is a sum of products of marginal probabilities;
the second moment is a sum of products of joint probabilities in each colour.
All variables are actual measurable, integrable indicator sums.
-/

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291.RandomPermutation

variable {I V C : Type*}

def present (s : Finset I) (A : I → Set (Equiv.Perm V)) : Sample I V → ℝ :=
  (allConstraints s A).indicator fun _ => 1

theorem present_bounds (s : Finset I) (A : I → Set (Equiv.Perm V)) (ω : Sample I V) :
    0 ≤ present s A ω ∧ present s A ω ≤ 1 := by
  classical
  simp only [present, Set.indicator]
  split_ifs <;> norm_num

theorem present_mul (s : Finset I) (A B : I → Set (Equiv.Perm V)) (ω : Sample I V) :
    present s A ω * present s B ω = present s (fun i => A i ∩ B i) ω := by
  classical
  by_cases hA : ω ∈ allConstraints s A <;> by_cases hB : ω ∈ allConstraints s B <;>
    simp [present, ← allConstraints_inter, hA, hB]

def eventCount (s : Finset I) (T : Finset C) (A : C → I → Set (Equiv.Perm V)) : Sample I V → ℝ :=
  fun ω => ∑ x ∈ T, present s (A x) ω

theorem eventCount_bounds (s : Finset I) (T : Finset C) (A : C → I → Set (Equiv.Perm V))
    (ω : Sample I V) : 0 ≤ eventCount s T A ω ∧ eventCount s T A ω ≤ T.card := by
  constructor
  · exact sum_nonneg (fun x _ => (present_bounds s (A x) ω).1)
  · calc
      _ ≤ ∑ _x ∈ T, (1 : ℝ) := sum_le_sum (fun x _ => (present_bounds s (A x) ω).2)
      _ = _ := by simp

theorem eventCount_sq (s : Finset I) (T : Finset C) (A : C → I → Set (Equiv.Perm V))
    (ω : Sample I V) :
    eventCount s T A ω ^ 2 = ∑ x ∈ T, ∑ y ∈ T, present s (fun i => A x i ∩ A y i) ω := by
  simp only [eventCount, pow_two, sum_mul, mul_sum, present_mul]
  exact sum_comm

variable [Fintype V] [DecidableEq V]
variable [MeasurableSpace (Equiv.Perm V)] [MeasurableSingletonClass (Equiv.Perm V)]

omit [Fintype V] [DecidableEq V] in
theorem present_measurable [Finite V] (s : Finset I) (A : I → Set (Equiv.Perm V)) :
    Measurable (present s A) :=
  measurable_const.indicator (allConstraints_measurable s A)

omit [Fintype V] [DecidableEq V] in
theorem eventCount_measurable [Finite V] (s : Finset I) (T : Finset C)
    (A : C → I → Set (Equiv.Perm V)) : Measurable (eventCount s T A) :=
  Finset.measurable_fun_sum T (fun x _ => present_measurable s (A x))

theorem present_integrable (s : Finset I) (A : I → Set (Equiv.Perm V)) :
    Integrable (present s A) (probability I V) :=
  (integrable_const 1).indicator (allConstraints_measurable s A)

theorem present_mean (s : Finset I) (A : I → Set (Equiv.Perm V)) :
    (∫ ω, present s A ω ∂probability I V) =
      ∏ i ∈ s, (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real (A i) := by
  change (∫ ω, (allConstraints s A).indicator (1 : Sample I V → ℝ) ω ∂probability I V) = _
  rw [integral_indicator_one (allConstraints_measurable s A), probabilityReal_allConstraints]

theorem eventCount_integrable (s : Finset I) (T : Finset C)
    (A : C → I → Set (Equiv.Perm V)) : Integrable (eventCount s T A) (probability I V) :=
  integrable_finsetSum T (fun x _ => present_integrable s (A x))

theorem eventCount_sq_integrable (s : Finset I) (T : Finset C)
    (A : C → I → Set (Equiv.Perm V)) :
    Integrable (fun ω => eventCount s T A ω ^ 2) (probability I V) := by
  simp_rw [eventCount_sq]
  exact integrable_finsetSum T (fun x _ => integrable_finsetSum T
    (fun y _ => present_integrable s (fun i => A x i ∩ A y i)))

theorem eventCount_mean (s : Finset I) (T : Finset C) (A : C → I → Set (Equiv.Perm V)) :
    (∫ ω, eventCount s T A ω ∂probability I V) =
      ∑ x ∈ T, ∏ i ∈ s, (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real (A x i) := by
  unfold eventCount
  rw [integral_finsetSum T (fun x _ => present_integrable s (A x))]
  simp only [present_mean]

theorem eventCount_second_moment (s : Finset I) (T : Finset C)
    (A : C → I → Set (Equiv.Perm V)) :
    (∫ ω, eventCount s T A ω ^ 2 ∂probability I V) =
      ∑ x ∈ T, ∑ y ∈ T,
        ∏ i ∈ s, (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real (A x i ∩ A y i) := by
  simp_rw [eventCount_sq]
  rw [integral_finsetSum T (fun x _ => integrable_finsetSum T
    (fun y _ => present_integrable s (fun i => A x i ∩ A y i)))]
  apply sum_congr rfl
  intro x _
  rw [integral_finsetSum T (fun y _ => present_integrable s (fun i => A x i ∩ A y i))]
  simp only [present_mean]

end Arxiv2411_18291.RandomPermutation
