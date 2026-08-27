import Arxiv.Arxiv2411_18291.PermutationPairProbability
import Mathlib.Probability.Independence.InfinitePi

/-!
# Independent random vertex permutations

The product measure supplies independent colours. For a finite set of
colours, simultaneous constraints have probability equal to the product of
their one-permutation probabilities. Constraints from different candidate
embeddings are not assumed independent.
-/

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section

namespace Arxiv2411_18291.RandomPermutation

variable {I V : Type*} [Fintype V] [DecidableEq V]
variable [MeasurableSpace (Equiv.Perm V)] [MeasurableSingletonClass (Equiv.Perm V)]

abbrev Sample (I V : Type*) := I → Equiv.Perm V

def probability (I V : Type*) [Fintype V] [DecidableEq V]
    [MeasurableSpace (Equiv.Perm V)] [MeasurableSingletonClass (Equiv.Perm V)] :
    Measure (Sample I V) :=
  Measure.infinitePi fun _ => (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure

instance : IsProbabilityMeasure (probability I V) := by
  unfold probability
  infer_instance

def allConstraints (s : Finset I) (A : I → Set (Equiv.Perm V)) : Set (Sample I V) :=
  {ω | ∀ i ∈ s, ω i ∈ A i}

omit [Fintype V] [DecidableEq V] [MeasurableSpace (Equiv.Perm V)]
    [MeasurableSingletonClass (Equiv.Perm V)] in
theorem allConstraints_eq_iInter (s : Finset I) (A : I → Set (Equiv.Perm V)) :
    allConstraints s A = ⋂ i ∈ s, (fun ω : Sample I V => ω i) ⁻¹' A i := by
  ext ω
  simp only [allConstraints, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]

omit [Fintype V] [DecidableEq V] in
theorem allConstraints_measurable [Finite V] (s : Finset I) (A : I → Set (Equiv.Perm V)) :
    MeasurableSet (allConstraints s A) := by
  rw [allConstraints_eq_iInter]
  exact MeasurableSet.biInter s.countable_toSet (fun i _ =>
    (measurable_pi_apply i) (Set.toFinite (A i)).measurableSet)

theorem coordinate_law (i : I) :
    (probability I V).map (fun ω => ω i) = (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure :=
  Measure.infinitePi_map_eval (fun _ => (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure) i

theorem probability_coordinate (i : I) (A : Set (Equiv.Perm V)) :
    probability I V ((fun ω : Sample I V => ω i) ⁻¹' A) =
      (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure A := by
  rw [← Measure.map_apply (measurable_pi_apply i) (Set.toFinite A).measurableSet, coordinate_law]

theorem probability_allConstraints (s : Finset I) (A : I → Set (Equiv.Perm V)) :
    probability I V (allConstraints s A) =
      ∏ i ∈ s, (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure (A i) := by
  have hInd : iIndepFun (fun i (ω : Sample I V) => ω i) (probability I V) :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  rw [allConstraints_eq_iInter,
    hInd.measure_inter_preimage_eq_mul s (fun i _ => (Set.toFinite (A i)).measurableSet)]
  simp only [probability_coordinate]

theorem probabilityReal_allConstraints (s : Finset I) (A : I → Set (Equiv.Perm V)) :
    (probability I V).real (allConstraints s A) =
      ∏ i ∈ s, (PMF.uniformOfFintype (Equiv.Perm V)).toMeasure.real (A i) := by
  simp only [measureReal_def, probability_allConstraints, ENNReal.toReal_prod]

omit [Fintype V] [DecidableEq V] [MeasurableSpace (Equiv.Perm V)]
    [MeasurableSingletonClass (Equiv.Perm V)] in
theorem allConstraints_inter (s : Finset I) (A B : I → Set (Equiv.Perm V)) :
    allConstraints s A ∩ allConstraints s B = allConstraints s (fun i => A i ∩ B i) := by
  ext ω
  simp only [allConstraints, Set.mem_inter_iff, Set.mem_ofPred_eq, forall_and]

end Arxiv2411_18291.RandomPermutation
