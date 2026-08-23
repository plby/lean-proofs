import ErdosProblems.Erdos1166.Erdos1166HLOZActualStopped
import ErdosProblems.Erdos1166.Erdos1166HLOZConditionalPairRuns

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal ProbabilityTheory

namespace Erdos1166.HLOZActualStopped

open HLOZDecomposition
open HLOZReconstruction

theorem actualStoppedVector_atoms_disjoint {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (E : Finset (Fin (q + 1) → ℕ))
    {v w : Fin (q + 1) → ℕ}
    (hv : v ∈ actualAdmissibleStoppedVectors m k labels E)
    (hw : w ∈ actualAdmissibleStoppedVectors m k labels E)
    (hvw : v ≠ w) :
    Disjoint
      (stoppedPrefixAtom (reconstructedStoppedPrefix labels v))
      (stoppedPrefixAtom (reconstructedStoppedPrefix labels w)) := by
  classical
  have hvstop : IsFirstKStoppedPrefix m k
      (reconstructedStoppedPrefix labels v) :=
    (Finset.mem_filter.mp hv).2
  have hwstop : IsFirstKStoppedPrefix m k
      (reconstructedStoppedPrefix labels w) :=
    (Finset.mem_filter.mp hw).2
  apply stoppedPrefixAtom_pairwiseDisjoint_on_firstK m k hvstop hwstop
  exact fun hp ↦ hvw (reconstructedStoppedPrefix_injective labels hnondist hp)

theorem measurableSet_actualStoppedVectorEvent {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (E : Finset (Fin (q + 1) → ℕ)) :
    MeasurableSet (actualStoppedVectorEvent m k labels E) := by
  unfold actualStoppedVectorEvent
  measurability

noncomputable def actualStoppedVector {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (E : Finset (Fin (q + 1) → ℕ))
    (ω : ℕ → Direction) : Fin (q + 1) → ℕ := by
  classical
  exact if h : ω ∈ actualStoppedVectorEvent m k labels E then
      Classical.choose (by
        simpa only [actualStoppedVectorEvent, Set.mem_iUnion] using h)
    else 0

theorem actualStoppedVector_spec {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (E : Finset (Fin (q + 1) → ℕ))
    {ω : ℕ → Direction}
    (hω : ω ∈ actualStoppedVectorEvent m k labels E) :
    actualStoppedVector m k labels E ω ∈
        actualAdmissibleStoppedVectors m k labels E ∧
      ω ∈ stoppedPrefixAtom
        (reconstructedStoppedPrefix labels
          (actualStoppedVector m k labels E ω)) := by
  classical
  rw [actualStoppedVector, dif_pos hω]
  rcases Classical.choose_spec (by
      simpa only [actualStoppedVectorEvent, Set.mem_iUnion] using hω) with
    ⟨hmem, hatom⟩
  exact ⟨hmem, hatom⟩

theorem actualStoppedVector_eq_of_mem_atom {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (E : Finset (Fin (q + 1) → ℕ))
    {v : Fin (q + 1) → ℕ}
    (hv : v ∈ actualAdmissibleStoppedVectors m k labels E)
    {ω : ℕ → Direction}
    (hωv : ω ∈ stoppedPrefixAtom (reconstructedStoppedPrefix labels v)) :
    actualStoppedVector m k labels E ω = v := by
  classical
  have hωE : ω ∈ actualStoppedVectorEvent m k labels E := by
    unfold actualStoppedVectorEvent
    exact Set.mem_iUnion_of_mem v (Set.mem_iUnion_of_mem hv hωv)
  have hspec := actualStoppedVector_spec m k labels E hωE
  by_contra hne
  exact Set.disjoint_left.mp
    (actualStoppedVector_atoms_disjoint m k labels hnondist E
      hspec.1 hv hne) hspec.2 hωv

theorem actualStoppedVector_fiber_inter_event {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (E : Finset (Fin (q + 1) → ℕ))
    (v : Fin (q + 1) → ℕ) :
    actualStoppedVectorEvent m k labels E ∩
        {ω | actualStoppedVector m k labels E ω = v} =
      if v ∈ actualAdmissibleStoppedVectors m k labels E then
        stoppedPrefixAtom (reconstructedStoppedPrefix labels v)
      else ∅ := by
  classical
  by_cases hv : v ∈ actualAdmissibleStoppedVectors m k labels E
  · rw [if_pos hv]
    ext ω
    constructor
    · rintro ⟨hωE, hωv⟩
      have hspec := actualStoppedVector_spec m k labels E hωE
      rw [hωv] at hspec
      exact hspec.2
    · intro hω
      exact ⟨by
        unfold actualStoppedVectorEvent
        exact Set.mem_iUnion_of_mem v (Set.mem_iUnion_of_mem hv hω),
        actualStoppedVector_eq_of_mem_atom m k labels hnondist E hv hω⟩
  · rw [if_neg hv]
    ext ω
    constructor
    · rintro ⟨hωE, hωv⟩
      exact False.elim
        (hv (hωv ▸ (actualStoppedVector_spec m k labels E hωE).1))
    · intro h
      exact False.elim h

theorem measurable_actualStoppedVector {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (E : Finset (Fin (q + 1) → ℕ)) :
    Measurable (actualStoppedVector m k labels E) := by
  classical
  apply measurable_to_countable'
  intro v
  let A := actualAdmissibleStoppedVectors m k labels E
  let B := actualStoppedVectorEvent m k labels E
  let C := stoppedPrefixAtom (reconstructedStoppedPrefix labels v)
  have hB : MeasurableSet B := measurableSet_actualStoppedVectorEvent m k labels E
  have hC : MeasurableSet C := measurableSet_stoppedPrefixAtom _
  by_cases hv : v ∈ A
  · by_cases hv0 : v = 0
    · have heq : {ω | actualStoppedVector m k labels E ω = v} =
          C ∪ Bᶜ := by
        ext ω
        by_cases hωB : ω ∈ B
        · constructor
          · intro hωv
            left
            have hspec := actualStoppedVector_spec m k labels E hωB
            rw [hωv] at hspec
            exact hspec.2
          · intro h
            rcases h with hωC | hωBc
            · exact actualStoppedVector_eq_of_mem_atom
                m k labels hnondist E hv hωC
            · exact False.elim (hωBc hωB)
        · simp only [Set.mem_union, Set.mem_compl_iff, hωB,
            not_false_eq_true, or_true, iff_true]
          have hωB' : ω ∉ actualStoppedVectorEvent m k labels E := hωB
          simp [actualStoppedVector, hωB', hv0]
      change MeasurableSet {ω | actualStoppedVector m k labels E ω = v}
      rw [heq]
      exact hC.union hB.compl
    · have heq : {ω | actualStoppedVector m k labels E ω = v} = C := by
        ext ω
        by_cases hωB : ω ∈ B
        · constructor
          · intro hωv
            have hspec := actualStoppedVector_spec m k labels E hωB
            rw [hωv] at hspec
            exact hspec.2
          · intro hωC
            exact actualStoppedVector_eq_of_mem_atom
              m k labels hnondist E hv hωC
        · constructor
          · intro hωv
            have hωB' : ω ∉ actualStoppedVectorEvent m k labels E := hωB
            simp [actualStoppedVector, hωB'] at hωv
            exact False.elim (hv0 hωv.symm)
          · intro hωC
            have hωB' : ω ∈ B := by
              unfold B actualStoppedVectorEvent
              exact Set.mem_iUnion_of_mem v
                (Set.mem_iUnion_of_mem hv hωC)
            exact False.elim (hωB hωB')
      change MeasurableSet {ω | actualStoppedVector m k labels E ω = v}
      rw [heq]
      exact hC
  · by_cases hv0 : v = 0
    · have heq : {ω | actualStoppedVector m k labels E ω = v} = Bᶜ := by
        ext ω
        by_cases hωB : ω ∈ B
        · constructor
          · intro hωv
            have hspec := actualStoppedVector_spec m k labels E hωB
            rw [hωv] at hspec
            exact False.elim (hv hspec.1)
          · intro hωBc
            exact False.elim (hωBc hωB)
        · simp only [Set.mem_compl_iff, hωB, not_false_eq_true, iff_true]
          have hωB' : ω ∉ actualStoppedVectorEvent m k labels E := hωB
          simp [actualStoppedVector, hωB', hv0]
      change MeasurableSet {ω | actualStoppedVector m k labels E ω = v}
      rw [heq]
      exact hB.compl
    · have heq : {ω | actualStoppedVector m k labels E ω = v} = ∅ := by
        ext ω
        constructor
        · intro hωv
          by_cases hωB : ω ∈ B
          · have hspec := actualStoppedVector_spec m k labels E hωB
            rw [hωv] at hspec
            exact False.elim (hv hspec.1)
          · have hωB' : ω ∉ actualStoppedVectorEvent m k labels E := hωB
            simp [actualStoppedVector, hωB'] at hωv
            exact False.elim (hv0 hωv.symm)
        · intro h
          exact False.elim h
      change MeasurableSet {ω | actualStoppedVector m k labels E ω = v}
      rw [heq]
      exact MeasurableSet.empty

theorem runVectorMeasure_singleton_eq_stoppedGeometricWeight {q : ℕ}
    (v : Fin (q + 1) → ℕ) :
    HLOZUrn.runVectorMeasure (q + 1) {v} = stoppedGeometricWeight v := by
  rw [Erdos1166.runVectorMeasure_singleton_ennreal]
  unfold stoppedGeometricWeight
  apply Finset.prod_congr rfl
  intro i _
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_pow,
    ENNReal.toReal_mul, ENNReal.toReal_inv]
  norm_num [pow_succ, one_div, inv_pow]
  have hpow : (1 / 16 : ℝ) ^ v i = (16 ^ v i : ℝ)⁻¹ := by
    rw [one_div, inv_pow]
  rw [hpow]
  field_simp

theorem runVectorMeasure_finset_eq_sum_stoppedGeometricWeight {q : ℕ}
    (A : Finset (Fin (q + 1) → ℕ)) :
    HLOZUrn.runVectorMeasure (q + 1) (A : Set (Fin (q + 1) → ℕ)) =
      ∑ v ∈ A, stoppedGeometricWeight v := by
  have hset : (A : Set (Fin (q + 1) → ℕ)) =
      ⋃ v ∈ A, ({v} : Set (Fin (q + 1) → ℕ)) := by
    ext v
    simp
  rw [hset]
  have hd : (A : Set (Fin (q + 1) → ℕ)).PairwiseDisjoint
      (fun v ↦ ({v} : Set (Fin (q + 1) → ℕ))) := by
    intro v _ w _ hvw
    change Disjoint ({v} : Set (Fin (q + 1) → ℕ)) {w}
    rw [Set.disjoint_left]
    intro x hxv hxw
    exact hvw ((Set.mem_singleton_iff.mp hxv).symm.trans
      (Set.mem_singleton_iff.mp hxw))
  rw [measure_biUnion_finset hd (fun _ _ ↦ measurableSet_singleton _)]
  apply Finset.sum_congr rfl
  intro v _
  exact runVectorMeasure_singleton_eq_stoppedGeometricWeight v

theorem runVectorMeasure_cond_finset_singleton {q : ℕ}
    (A : Finset (Fin (q + 1) → ℕ))
    (v : Fin (q + 1) → ℕ) (hv : v ∈ A) :
    (HLOZUrn.runVectorMeasure (q + 1))[|(A : Set (Fin (q + 1) → ℕ))]
        {v} =
      stoppedGeometricWeight v /
        ∑ w ∈ A, stoppedGeometricWeight w := by
  rw [cond_apply A.measurableSet]
  have hinter : (A : Set (Fin (q + 1) → ℕ)) ∩ {v} = {v} := by
    ext w
    simp [hv]
  rw [hinter, runVectorMeasure_finset_eq_sum_stoppedGeometricWeight,
    runVectorMeasure_singleton_eq_stoppedGeometricWeight]
  rw [div_eq_mul_inv]
  exact mul_comm _ _

theorem actualStoppedVector_conditional_singleton {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (E : Finset (Fin (q + 1) → ℕ))
    (v : Fin (q + 1) → ℕ) :
    incrementLaw[|actualStoppedVectorEvent m k labels E]
        {ω | actualStoppedVector m k labels E ω = v} =
      (HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissibleStoppedVectors m k labels E :
          Set (Fin (q + 1) → ℕ))] {v} := by
  classical
  let A := actualAdmissibleStoppedVectors m k labels E
  let B := actualStoppedVectorEvent m k labels E
  rw [cond_apply (measurableSet_actualStoppedVectorEvent m k labels E)]
  rw [actualStoppedVector_fiber_inter_event m k labels hnondist E v]
  by_cases hv : v ∈ A
  · rw [if_pos hv]
    rw [mul_comm]
    change incrementLaw
        (stoppedPrefixAtom (reconstructedStoppedPrefix labels v)) /
          incrementLaw B = _
    rw [reconstructedStoppedPrefix_conditional_geometric
      m k labels hnondist E v hv]
    exact (runVectorMeasure_cond_finset_singleton A v hv).symm
  · rw [if_neg hv, measure_empty, mul_zero]
    rw [cond_apply A.measurableSet]
    have hinter : (A : Set (Fin (q + 1) → ℕ)) ∩ {v} = ∅ := by
      ext w
      simp [hv]
    rw [hinter, measure_empty, mul_zero]

/-- Measure-level actual stopped law.  The decoder is evaluated under the
finite union of genuine stopping-prefix atoms, and its law is the iid
geometric run-vector measure filtered by exactly the vectors that pass the
same stopping-time test. -/
theorem actualStoppedVector_hasLaw_filtered {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (E : Finset (Fin (q + 1) → ℕ)) :
    HasLaw (actualStoppedVector m k labels E)
      (HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissibleStoppedVectors m k labels E :
          Set (Fin (q + 1) → ℕ))]
      incrementLaw[|actualStoppedVectorEvent m k labels E] := by
  constructor
  · exact (measurable_actualStoppedVector m k labels hnondist E).aemeasurable
  · apply Measure.ext_of_singleton
    intro v
    rw [Measure.map_apply
      (measurable_actualStoppedVector m k labels hnondist E)
      (measurableSet_singleton v)]
    exact actualStoppedVector_conditional_singleton
      m k labels hnondist E v

end Erdos1166.HLOZActualStopped
