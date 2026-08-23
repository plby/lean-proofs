import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedRunBridge
import ErdosProblems.Erdos1166.Erdos1166HLOZPrimedStopped
import ErdosProblems.Erdos1166.Erdos1166HLOZActualStoppedLaw

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

namespace Erdos1166.HLOZIncompleteStoppedBlocks

open HLOZDecomposition HLOZReconstruction HLOZActualStopped HLOZPrimedStopped

/-! ### The q+1 external bases, including the unfinished last run -/

def stoppedExternalBasesFrom : Site → List IncrementPair → List Site
  | a, [] => [a]
  | a, p :: labels =>
      a :: stoppedExternalBasesFrom (pairEndpoint a p) labels

@[simp] theorem stoppedExternalBasesFrom_length
    (a : Site) (labels : List IncrementPair) :
    (stoppedExternalBasesFrom a labels).length = labels.length + 1 := by
  induction labels generalizing a with
  | nil => rfl
  | cons p labels ih =>
      simp only [stoppedExternalBasesFrom, List.length_cons, ih]

def stoppedExternalBaseAt {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (i : Fin (q + 1)) : Site :=
  (stoppedExternalBasesFrom a (List.ofFn labels)).get
    (Fin.cast (by simp [stoppedExternalBasesFrom_length]) i)

def stoppedExternalBaseSet {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) : Finset Site :=
  (stoppedExternalBasesFrom a (List.ofFn labels)).toFinset

abbrev StoppedExternalBase {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) :=
  {x : Site // x ∈ stoppedExternalBaseSet a labels}

abbrev StoppedExternalIndex {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (b : StoppedExternalBase a labels) :=
  {i : Fin (q + 1) // stoppedExternalBaseAt a labels i = b.1}

theorem stoppedExternalBaseAt_mem {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (i : Fin (q + 1)) :
    stoppedExternalBaseAt a labels i ∈ stoppedExternalBaseSet a labels := by
  unfold stoppedExternalBaseSet stoppedExternalBaseAt
  rw [List.mem_toFinset]
  exact List.get_mem _ _

noncomputable def stoppedPaperBlockVector {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) :
    ∀ b : StoppedExternalBase a labels,
      StoppedExternalIndex a labels b → ℕ :=
  fun _ i => v i.1

/-! ### Generic finite pullback of bounded block constraints -/

noncomputable def stoppedBlockConstraints {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (threshold : StoppedExternalBase a labels → ℕ) :
    ∀ b : StoppedExternalBase a labels,
      Finset (StoppedExternalIndex a labels b → ℕ) :=
  fun b => HLOZConditionalProduct.natSumBelow (threshold b)

noncomputable def stoppedVectorConstraint {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (m : ℕ)
    (threshold : StoppedExternalBase a labels → ℕ) :
    Finset (Fin (q + 1) → ℕ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin (q + 1) => Finset.range m).filter
    fun v => stoppedPaperBlockVector a labels v ∈
      HLOZConditionalProduct.blockEvent
        (stoppedBlockConstraints a labels threshold)

theorem stoppedPaperBlockVector_coordinate_le_sum {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ)
    (i : Fin (q + 1)) :
    v i ≤ ∑ j : StoppedExternalIndex a labels
        ⟨stoppedExternalBaseAt a labels i,
          stoppedExternalBaseAt_mem a labels i⟩,
      stoppedPaperBlockVector a labels v
        ⟨stoppedExternalBaseAt a labels i,
          stoppedExternalBaseAt_mem a labels i⟩ j := by
  classical
  let b : StoppedExternalBase a labels :=
    ⟨stoppedExternalBaseAt a labels i,
      stoppedExternalBaseAt_mem a labels i⟩
  let j : StoppedExternalIndex a labels b := ⟨i, rfl⟩
  have hj : j ∈ (Finset.univ : Finset (StoppedExternalIndex a labels b)) :=
    Finset.mem_univ j
  have hle := Finset.single_le_sum
    (f := fun z : StoppedExternalIndex a labels b =>
      stoppedPaperBlockVector a labels v b z)
    (fun _ _ => Nat.zero_le _) hj
  simpa [b, j, stoppedPaperBlockVector] using hle

theorem mem_stoppedVectorConstraint_iff {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (m : ℕ)
    (threshold : StoppedExternalBase a labels → ℕ)
    (hthreshold : ∀ b, threshold b ≤ m)
    (v : Fin (q + 1) → ℕ) :
    v ∈ stoppedVectorConstraint a labels m threshold ↔
      stoppedPaperBlockVector a labels v ∈
        HLOZConditionalProduct.blockEvent
          (stoppedBlockConstraints a labels threshold) := by
  classical
  rw [stoppedVectorConstraint, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro hblock
    refine ⟨Fintype.mem_piFinset.mpr ?_, hblock⟩
    intro i
    rw [Finset.mem_range]
    let b : StoppedExternalBase a labels :=
      ⟨stoppedExternalBaseAt a labels i,
        stoppedExternalBaseAt_mem a labels i⟩
    have hb := hblock b
    rw [stoppedBlockConstraints,
      HLOZConditionalProduct.mem_natSumBelow_iff] at hb
    have hle := stoppedPaperBlockVector_coordinate_le_sum a labels v i
    have hle' : v i ≤ ∑ j : StoppedExternalIndex a labels b,
        stoppedPaperBlockVector a labels v b j := by
      simpa [b] using hle
    have htm := hthreshold b
    change v i < m
    omega

theorem mem_stoppedBlockConstraints_iff {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (threshold : StoppedExternalBase a labels → ℕ)
    (v : Fin (q + 1) → ℕ) :
    stoppedPaperBlockVector a labels v ∈
        HLOZConditionalProduct.blockEvent
          (stoppedBlockConstraints a labels threshold) ↔
      ∀ b, (∑ i, stoppedPaperBlockVector a labels v b i) < threshold b := by
  constructor
  · intro h b
    exact (HLOZConditionalProduct.mem_natSumBelow_iff _ _).mp (h b)
  · intro h b
    exact (HLOZConditionalProduct.mem_natSumBelow_iff _ _).mpr (h b)

/-! ### A reusable decoder for the three parity cases not covered upstream -/

noncomputable def finiteAtomDecoder {Ω V : Type*} [Inhabited V]
    (A : Finset V) (atom : V → Set Ω) (ω : Ω) : V := by
  classical
  exact if h : ∃ v ∈ A, ω ∈ atom v then Classical.choose h else default

def finiteAtomEvent {Ω V : Type*}
    (A : Finset V) (atom : V → Set Ω) : Set Ω :=
  ⋃ v ∈ A, atom v

theorem finiteAtomDecoder_spec {Ω V : Type*} [Inhabited V]
    (A : Finset V) (atom : V → Set Ω) {ω : Ω}
    (hω : ω ∈ finiteAtomEvent A atom) :
    finiteAtomDecoder A atom ω ∈ A ∧
      ω ∈ atom (finiteAtomDecoder A atom ω) := by
  classical
  have hex : ∃ v ∈ A, ω ∈ atom v := by
    rw [finiteAtomEvent] at hω
    rcases Set.mem_iUnion.mp hω with ⟨v, hω⟩
    rcases Set.mem_iUnion.mp hω with ⟨hv, hω⟩
    exact ⟨v, hv, hω⟩
  rw [finiteAtomDecoder, dif_pos hex]
  exact Classical.choose_spec hex

theorem finiteAtomDecoder_eq_of_mem_atom {Ω V : Type*} [Inhabited V]
    (A : Finset V) (atom : V → Set Ω)
    (hdisjoint : ∀ {v w}, v ∈ A → w ∈ A → v ≠ w →
      Disjoint (atom v) (atom w))
    {v : V} (hv : v ∈ A) {ω : Ω} (hωv : ω ∈ atom v) :
    finiteAtomDecoder A atom ω = v := by
  classical
  have hωE : ω ∈ finiteAtomEvent A atom := by
    unfold finiteAtomEvent
    exact Set.mem_iUnion_of_mem v (Set.mem_iUnion_of_mem hv hωv)
  have hspec := finiteAtomDecoder_spec A atom hωE
  by_contra hne
  exact Set.disjoint_left.mp
    (hdisjoint hspec.1 hv hne) hspec.2 hωv

theorem finiteAtomDecoder_fiber_inter_event {Ω V : Type*} [Inhabited V]
    [DecidableEq V]
    (A : Finset V) (atom : V → Set Ω)
    (hdisjoint : ∀ {v w}, v ∈ A → w ∈ A → v ≠ w →
      Disjoint (atom v) (atom w)) (v : V) :
    finiteAtomEvent A atom ∩ {ω | finiteAtomDecoder A atom ω = v} =
      if v ∈ A then atom v else ∅ := by
  classical
  by_cases hv : v ∈ A
  · rw [if_pos hv]
    ext ω
    constructor
    · rintro ⟨hωE, hωv⟩
      have hspec := finiteAtomDecoder_spec A atom hωE
      rw [hωv] at hspec
      exact hspec.2
    · intro hω
      exact ⟨by
        unfold finiteAtomEvent
        exact Set.mem_iUnion_of_mem v (Set.mem_iUnion_of_mem hv hω),
        finiteAtomDecoder_eq_of_mem_atom A atom hdisjoint hv hω⟩
  · rw [if_neg hv]
    ext ω
    constructor
    · rintro ⟨hωE, hωv⟩
      exact False.elim
        (hv (hωv ▸ (finiteAtomDecoder_spec A atom hωE).1))
    · intro h
      exact False.elim h

theorem measurableSet_finiteAtomEvent {Ω V : Type*}
    [MeasurableSpace Ω] [Countable V]
    (A : Finset V) (atom : V → Set Ω)
    (hmeas : ∀ v ∈ A, MeasurableSet (atom v)) :
    MeasurableSet (finiteAtomEvent A atom) := by
  unfold finiteAtomEvent
  measurability

theorem measurable_finiteAtomDecoder {Ω V : Type*} [Inhabited V]
    [MeasurableSpace Ω] [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable V] (A : Finset V) (atom : V → Set Ω)
    (hdisjoint : ∀ {v w}, v ∈ A → w ∈ A → v ≠ w →
      Disjoint (atom v) (atom w))
    (hmeas : ∀ v ∈ A, MeasurableSet (atom v)) :
    Measurable (finiteAtomDecoder A atom) := by
  classical
  apply measurable_to_countable'
  intro v
  let B := finiteAtomEvent A atom
  have hB : MeasurableSet B := measurableSet_finiteAtomEvent A atom hmeas
  by_cases hv : v ∈ A
  · by_cases hv0 : v = default
    · have heq : {ω | finiteAtomDecoder A atom ω = v} = atom v ∪ Bᶜ := by
        ext ω
        by_cases hωB : ω ∈ B
        · constructor
          · intro hωv
            left
            have hspec := finiteAtomDecoder_spec A atom hωB
            rw [hωv] at hspec
            exact hspec.2
          · intro h
            rcases h with hωatom | hωBc
            · exact finiteAtomDecoder_eq_of_mem_atom
                A atom hdisjoint hv hωatom
            · exact False.elim (hωBc hωB)
        · simp only [Set.mem_union, Set.mem_compl_iff, hωB,
            not_false_eq_true, or_true, iff_true]
          have hex : ¬ ∃ w ∈ A, ω ∈ atom w := by
            rintro ⟨w, hwA, hωw⟩
            apply hωB
            unfold B finiteAtomEvent
            exact Set.mem_iUnion_of_mem w
              (Set.mem_iUnion_of_mem hwA hωw)
          have hdec : finiteAtomDecoder A atom ω = default := by
            rw [finiteAtomDecoder, dif_neg hex]
          exact hdec.trans hv0.symm
      change MeasurableSet {ω | finiteAtomDecoder A atom ω = v}
      rw [heq]
      exact (hmeas v hv).union hB.compl
    · have heq : {ω | finiteAtomDecoder A atom ω = v} = atom v := by
        ext ω
        by_cases hωB : ω ∈ B
        · constructor
          · intro hωv
            have hspec := finiteAtomDecoder_spec A atom hωB
            rw [hωv] at hspec
            exact hspec.2
          · exact finiteAtomDecoder_eq_of_mem_atom A atom hdisjoint hv
        · constructor
          · intro hωv
            have hex : ¬ ∃ w ∈ A, ω ∈ atom w := by
              rintro ⟨w, hwA, hωw⟩
              apply hωB
              unfold B finiteAtomEvent
              exact Set.mem_iUnion_of_mem w
                (Set.mem_iUnion_of_mem hwA hωw)
            have hdec : finiteAtomDecoder A atom ω = default := by
              rw [finiteAtomDecoder, dif_neg hex]
            change finiteAtomDecoder A atom ω = v at hωv
            rw [hdec] at hωv
            exact False.elim (hv0 hωv.symm)
          · intro hωatom
            have hωB' : ω ∈ B := by
              unfold B finiteAtomEvent
              exact Set.mem_iUnion_of_mem v
                (Set.mem_iUnion_of_mem hv hωatom)
            exact False.elim (hωB hωB')
      change MeasurableSet {ω | finiteAtomDecoder A atom ω = v}
      rw [heq]
      exact hmeas v hv
  · by_cases hv0 : v = default
    · have heq : {ω | finiteAtomDecoder A atom ω = v} = Bᶜ := by
        ext ω
        by_cases hωB : ω ∈ B
        · constructor
          · intro hωv
            have hspec := finiteAtomDecoder_spec A atom hωB
            rw [hωv] at hspec
            exact False.elim (hv hspec.1)
          · intro hωBc
            exact False.elim (hωBc hωB)
        · simp only [Set.mem_compl_iff, hωB, not_false_eq_true, iff_true]
          have hex : ¬ ∃ w ∈ A, ω ∈ atom w := by
            rintro ⟨w, hwA, hωw⟩
            apply hωB
            unfold B finiteAtomEvent
            exact Set.mem_iUnion_of_mem w
              (Set.mem_iUnion_of_mem hwA hωw)
          have hdec : finiteAtomDecoder A atom ω = default := by
            rw [finiteAtomDecoder, dif_neg hex]
          exact hdec.trans hv0.symm
      change MeasurableSet {ω | finiteAtomDecoder A atom ω = v}
      rw [heq]
      exact hB.compl
    · have heq : {ω | finiteAtomDecoder A atom ω = v} = ∅ := by
        ext ω
        constructor
        · intro hωv
          by_cases hωB : ω ∈ B
          · have hspec := finiteAtomDecoder_spec A atom hωB
            rw [hωv] at hspec
            exact False.elim (hv hspec.1)
          · have hex : ¬ ∃ w ∈ A, ω ∈ atom w := by
              rintro ⟨w, hwA, hωw⟩
              apply hωB
              unfold B finiteAtomEvent
              exact Set.mem_iUnion_of_mem w
                (Set.mem_iUnion_of_mem hwA hωw)
            have hdec : finiteAtomDecoder A atom ω = default := by
              rw [finiteAtomDecoder, dif_neg hex]
            change finiteAtomDecoder A atom ω = v at hωv
            rw [hdec] at hωv
            exact False.elim (hv0 hωv.symm)
        · intro h
          exact False.elim h
      change MeasurableSet {ω | finiteAtomDecoder A atom ω = v}
      rw [heq]
      exact MeasurableSet.empty

theorem finiteAtomDecoder_conditional_singleton_geometric {q : ℕ}
    (A : Finset (Fin (q + 1) → ℕ))
    (atom : (Fin (q + 1) → ℕ) → Set (ℕ → Direction))
    (hdisjoint : ∀ {v w}, v ∈ A → w ∈ A → v ≠ w →
      Disjoint (atom v) (atom w))
    (hmeas : ∀ v ∈ A, MeasurableSet (atom v))
    (hratio : ∀ v ∈ A,
      incrementLaw (atom v) / incrementLaw (finiteAtomEvent A atom) =
        stoppedGeometricWeight v /
          ∑ w ∈ A, stoppedGeometricWeight w)
    (v : Fin (q + 1) → ℕ) :
    incrementLaw[|finiteAtomEvent A atom]
        {ω | finiteAtomDecoder A atom ω = v} =
      (HLOZUrn.runVectorMeasure (q + 1))[|
        (A : Set (Fin (q + 1) → ℕ))] {v} := by
  classical
  rw [cond_apply (measurableSet_finiteAtomEvent A atom hmeas)]
  rw [finiteAtomDecoder_fiber_inter_event A atom hdisjoint v]
  by_cases hv : v ∈ A
  · rw [if_pos hv, mul_comm]
    change incrementLaw (atom v) /
      incrementLaw (finiteAtomEvent A atom) = _
    rw [hratio v hv]
    exact (runVectorMeasure_cond_finset_singleton A v hv).symm
  · rw [if_neg hv, measure_empty, mul_zero]
    rw [cond_apply A.measurableSet]
    have hinter : (A : Set (Fin (q + 1) → ℕ)) ∩ {v} = ∅ := by
      ext w
      simp [hv]
    rw [hinter, measure_empty, mul_zero]

theorem finiteAtomDecoder_hasLaw_geometric {q : ℕ}
    (A : Finset (Fin (q + 1) → ℕ))
    (atom : (Fin (q + 1) → ℕ) → Set (ℕ → Direction))
    (hdisjoint : ∀ {v w}, v ∈ A → w ∈ A → v ≠ w →
      Disjoint (atom v) (atom w))
    (hmeas : ∀ v ∈ A, MeasurableSet (atom v))
    (hratio : ∀ v ∈ A,
      incrementLaw (atom v) / incrementLaw (finiteAtomEvent A atom) =
        stoppedGeometricWeight v /
          ∑ w ∈ A, stoppedGeometricWeight w) :
    HasLaw (finiteAtomDecoder A atom)
      (HLOZUrn.runVectorMeasure (q + 1))[|
        (A : Set (Fin (q + 1) → ℕ))]
      incrementLaw[|finiteAtomEvent A atom] := by
  constructor
  · exact (measurable_finiteAtomDecoder A atom hdisjoint hmeas).aemeasurable
  · apply Measure.ext_of_singleton
    intro v
    rw [Measure.map_apply
      (measurable_finiteAtomDecoder A atom hdisjoint hmeas)
      (measurableSet_singleton v)]
    exact finiteAtomDecoder_conditional_singleton_geometric
      A atom hdisjoint hmeas hratio v

theorem finiteAtomEvent_incrementLaw_ne_zero
    {V : Type*} (A : Finset V) (atom : V → Set (ℕ → Direction))
    {v : V} (hv : v ∈ A) (hpos : incrementLaw (atom v) ≠ 0) :
    incrementLaw (finiteAtomEvent A atom) ≠ 0 := by
  intro hzero
  apply hpos
  apply bot_unique
  have hsubset : atom v ⊆ finiteAtomEvent A atom := by
    intro ω hω
    unfold finiteAtomEvent
    exact Set.mem_iUnion_of_mem v (Set.mem_iUnion_of_mem hv hω)
  simpa [hzero] using measure_mono (μ := incrementLaw) hsubset

theorem runVectorMeasure_finset_ne_zero_of_nonempty {q : ℕ}
    (A : Finset (Fin (q + 1) → ℕ)) (hA : A.Nonempty) :
    HLOZUrn.runVectorMeasure (q + 1)
      (A : Set (Fin (q + 1) → ℕ)) ≠ 0 := by
  rcases hA with ⟨v, hv⟩
  intro hzero
  have hsubset : ({v} : Set (Fin (q + 1) → ℕ)) ⊆ A := by
    simpa [Set.singleton_subset_iff]
  have hle := measure_mono
    (μ := HLOZUrn.runVectorMeasure (q + 1)) hsubset
  rw [hzero] at hle
  have hsingleton : HLOZUrn.runVectorMeasure (q + 1) {v} = 0 :=
    bot_unique hle
  rw [runVectorMeasure_singleton_eq_stoppedGeometricWeight] at hsingleton
  have hweight : stoppedGeometricWeight v ≠ 0 := by
    unfold stoppedGeometricWeight
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  exact hweight hsingleton

theorem stoppedPrefixAtoms_disjoint_of_firstKPrefixAt
    {V : Type*} (m k : ℕ) (A : Finset V)
    (p : V → StoppedPrefix)
    (hstop : ∀ v ∈ A, IsFirstKPrefixAt m k ((p v).1 - 1) (p v).2)
    (hlen : ∀ v w, (p v).1 - 1 = (p w).1 - 1 → (p v).1 = (p w).1)
    (hinj : Function.Injective p)
    {v w : V} (hv : v ∈ A) (hw : w ∈ A) (hvw : v ≠ w) :
    Disjoint (stoppedPrefixAtom (p v)) (stoppedPrefixAtom (p w)) := by
  classical
  rw [Set.disjoint_left]
  intro ω hωv hωw
  have hTv := prefixAtom_subset_firstKSitesReachLevel_fiber_at
    (T := (p v).1 - 1) (n := (p v).1) (by omega) (hstop v hv) hωv
  have hTw := prefixAtom_subset_firstKSitesReachLevel_fiber_at
    (T := (p w).1 - 1) (n := (p w).1) (by omega) (hstop w hw) hωw
  have hT : (p v).1 - 1 = (p w).1 - 1 :=
    WithTop.coe_eq_coe.mp (hTv.symm.trans hTw)
  have hpw : p v = p w := by
    cases hpv : p v with
    | mk nv wv =>
      cases hpw : p w with
      | mk nw ww =>
        have hn : nv = nw := by
          simpa only [hpv, hpw] using hlen v w hT
        subst nw
        simp only [hpv, hpw] at hωv hωw ⊢
        have hww : wv = ww :=
          (Set.mem_singleton_iff.mp hωv).symm.trans
            (Set.mem_singleton_iff.mp hωw)
        subst ww
        rfl
  exact hvw (hinj hpw)

/-! ### Four concrete stopped external profiles -/

def zeroStoppedVector (q : ℕ) : Fin (q + 1) → ℕ := 0

noncomputable def unprimedEvenReference {q : ℕ}
    (labels : Fin q → IncrementPair) : ℕ → Direction :=
  extendPrefix
    (reconstructedStoppedPrefix labels (zeroStoppedVector q)).2

noncomputable def unprimedOddReference {q : ℕ}
    (labels : Fin q → IncrementPair) (terminal : IncrementPair) :
    ℕ → Direction :=
  extendPrefix
    (reconstructedOddStoppedPrefix labels (zeroStoppedVector q) terminal).2

noncomputable def primedOddReference {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair) : ℕ → Direction :=
  extendPrefix
    (reconstructedPrimedStoppedPrefix first labels (zeroStoppedVector q)).2

noncomputable def primedEvenReference {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) : ℕ → Direction :=
  extendPrefix
    (reconstructedPrimedTerminalStoppedPrefix first labels
      (zeroStoppedVector q) terminal).2

noncomputable def unprimedEvenPairMax {q : ℕ}
    (labels : Fin q → IncrementPair) (x : Site) : ℕ :=
  paperExternalPairMaxAt
    (simpleRandomWalk (unprimedEvenReference labels)) (2 * q) x

noncomputable def unprimedOddPairMax {q : ℕ}
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (x : Site) : ℕ :=
  paperExternalPairMaxAt
    (simpleRandomWalk (unprimedOddReference labels terminal))
    ((reconstructedOddStoppedPrefix labels (zeroStoppedVector q) terminal).1 - 1) x

noncomputable def primedExternalPairMaxAt
    (s : ℕ → Site) (T : ℕ) (x : Site) : ℕ :=
  max (primedExternalLocalTime s T x)
    (primedExternalLocalTime s T (x + paperE1))

noncomputable def primedOddPairMax {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair) (x : Site) : ℕ :=
  primedExternalPairMaxAt
    (simpleRandomWalk (primedOddReference first labels)) (2 * q + 1) x

noncomputable def primedEvenPairMax {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) (x : Site) : ℕ :=
  primedExternalPairMaxAt
    (simpleRandomWalk (primedEvenReference first labels terminal))
    ((reconstructedPrimedTerminalStoppedPrefix first labels
      (zeroStoppedVector q) terminal).1 - 1) x

noncomputable def unprimedEvenStoppedConstraint {q : ℕ}
    (labels : Fin q → IncrementPair) (m : ℕ) :
    Finset (Fin (q + 1) → ℕ) :=
  stoppedVectorConstraint (0, 0) labels m fun b =>
    m - unprimedEvenPairMax labels b.1

noncomputable def unprimedOddStoppedConstraint {q : ℕ}
    (labels : Fin q → IncrementPair) (terminal : IncrementPair) (m : ℕ) :
    Finset (Fin (q + 1) → ℕ) :=
  stoppedVectorConstraint (0, 0) labels m fun b =>
    m - unprimedOddPairMax labels terminal b.1

noncomputable def primedOddStoppedConstraint {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair) (m : ℕ) :
    Finset (Fin (q + 1) → ℕ) :=
  stoppedVectorConstraint (directionStep first) labels m fun b =>
    m - primedOddPairMax first labels b.1

noncomputable def primedEvenStoppedConstraint {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) (m : ℕ) :
    Finset (Fin (q + 1) → ℕ) :=
  stoppedVectorConstraint (directionStep first) labels m fun b =>
    m - primedEvenPairMax first labels terminal b.1

theorem mem_unprimedEvenStoppedConstraint_iff {q : ℕ}
    (labels : Fin q → IncrementPair) (m : ℕ)
    (v : Fin (q + 1) → ℕ) :
    v ∈ unprimedEvenStoppedConstraint labels m ↔
      ∀ b : StoppedExternalBase (0, 0) labels,
        (∑ i, stoppedPaperBlockVector (0, 0) labels v b i) +
          unprimedEvenPairMax labels b.1 < m := by
  rw [unprimedEvenStoppedConstraint,
    mem_stoppedVectorConstraint_iff]
  · rw [mem_stoppedBlockConstraints_iff]
    constructor <;> intro h b
    · have := h b
      omega
    · have := h b
      omega
  · intro b
    exact Nat.sub_le _ _

theorem mem_unprimedOddStoppedConstraint_iff {q : ℕ}
    (labels : Fin q → IncrementPair) (terminal : IncrementPair) (m : ℕ)
    (v : Fin (q + 1) → ℕ) :
    v ∈ unprimedOddStoppedConstraint labels terminal m ↔
      ∀ b : StoppedExternalBase (0, 0) labels,
        (∑ i, stoppedPaperBlockVector (0, 0) labels v b i) +
          unprimedOddPairMax labels terminal b.1 < m := by
  rw [unprimedOddStoppedConstraint,
    mem_stoppedVectorConstraint_iff]
  · rw [mem_stoppedBlockConstraints_iff]
    constructor <;> intro h b
    · have := h b
      omega
    · have := h b
      omega
  · intro b
    exact Nat.sub_le _ _

theorem mem_primedOddStoppedConstraint_iff {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair) (m : ℕ)
    (v : Fin (q + 1) → ℕ) :
    v ∈ primedOddStoppedConstraint first labels m ↔
      ∀ b : StoppedExternalBase (directionStep first) labels,
        (∑ i, stoppedPaperBlockVector (directionStep first)
          labels v b i) +
          primedOddPairMax first labels b.1 < m := by
  rw [primedOddStoppedConstraint,
    mem_stoppedVectorConstraint_iff]
  · rw [mem_stoppedBlockConstraints_iff]
    constructor <;> intro h b
    · have := h b
      omega
    · have := h b
      omega
  · intro b
    exact Nat.sub_le _ _

theorem mem_primedEvenStoppedConstraint_iff {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) (m : ℕ)
    (v : Fin (q + 1) → ℕ) :
    v ∈ primedEvenStoppedConstraint first labels terminal m ↔
      ∀ b : StoppedExternalBase (directionStep first) labels,
        (∑ i, stoppedPaperBlockVector (directionStep first)
          labels v b i) +
          primedEvenPairMax first labels terminal b.1 < m := by
  rw [primedEvenStoppedConstraint,
    mem_stoppedVectorConstraint_iff]
  · rw [mem_stoppedBlockConstraints_iff]
    constructor <;> intro h b
    · have := h b
      omega
    · have := h b
      omega
  · intro b
    exact Nat.sub_le _ _

theorem mem_unprimedEvenStoppedConstraint_iff_paperBlockEvent {q : ℕ}
    (labels : Fin q → IncrementPair) (m : ℕ)
    (v : Fin (q + 1) → ℕ) :
    v ∈ unprimedEvenStoppedConstraint labels m ↔
      stoppedPaperBlockVector (0, 0) labels v ∈
        HLOZConditionalProduct.blockEvent
          (paperBlockConstraints
            (ι := StoppedExternalIndex (0, 0) labels)
            (simpleRandomWalk (unprimedEvenReference labels))
            (2 * q) m (fun b : StoppedExternalBase (0, 0) labels ↦ b.1)) := by
  rw [mem_unprimedEvenStoppedConstraint_iff,
    mem_blockEvent_paperBlockConstraints_iff]
  rfl

theorem mem_unprimedOddStoppedConstraint_iff_paperBlockEvent {q : ℕ}
    (labels : Fin q → IncrementPair) (terminal : IncrementPair) (m : ℕ)
    (v : Fin (q + 1) → ℕ) :
    v ∈ unprimedOddStoppedConstraint labels terminal m ↔
      stoppedPaperBlockVector (0, 0) labels v ∈
        HLOZConditionalProduct.blockEvent
          (paperBlockConstraints
            (ι := StoppedExternalIndex (0, 0) labels)
            (simpleRandomWalk (unprimedOddReference labels terminal))
            ((reconstructedOddStoppedPrefix labels
              (zeroStoppedVector q) terminal).1 - 1)
            m (fun b : StoppedExternalBase (0, 0) labels ↦ b.1)) := by
  rw [mem_unprimedOddStoppedConstraint_iff,
    mem_blockEvent_paperBlockConstraints_iff]
  rfl

noncomputable def primedPaperBlockConstraints
    {β : Type*} [Fintype β] {ι : β → Type*}
    [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)]
    (s : ℕ → Site) (T m : ℕ) (site : β → Site) :
    ∀ b, Finset (ι b → ℕ) :=
  fun b ↦ HLOZConditionalProduct.natSumBelow
    (m - primedExternalPairMaxAt s T (site b))

theorem mem_blockEvent_primedPaperBlockConstraints_iff
    {β : Type*} [Fintype β] {ι : β → Type*}
    [∀ b, Fintype (ι b)] [∀ b, DecidableEq (ι b)]
    (s : ℕ → Site) (T m : ℕ) (site : β → Site)
    (ρ : ∀ b, ι b → ℕ) :
    ρ ∈ HLOZConditionalProduct.blockEvent
        (primedPaperBlockConstraints (ι := ι) s T m site) ↔
      ∀ b, (∑ i, ρ b i) + primedExternalPairMaxAt s T (site b) < m := by
  constructor
  · intro h b
    have hb := h b
    rw [primedPaperBlockConstraints,
      HLOZConditionalProduct.mem_natSumBelow_iff] at hb
    omega
  · intro h b
    rw [primedPaperBlockConstraints,
      HLOZConditionalProduct.mem_natSumBelow_iff]
    have hb := h b
    omega

theorem mem_primedOddStoppedConstraint_iff_primedPaperBlockEvent {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair) (m : ℕ)
    (v : Fin (q + 1) → ℕ) :
    v ∈ primedOddStoppedConstraint first labels m ↔
      stoppedPaperBlockVector (directionStep first) labels v ∈
        HLOZConditionalProduct.blockEvent
          (primedPaperBlockConstraints
            (ι := StoppedExternalIndex (directionStep first) labels)
            (simpleRandomWalk (primedOddReference first labels))
            (2 * q + 1) m
            (fun b : StoppedExternalBase (directionStep first) labels ↦ b.1)) := by
  rw [mem_primedOddStoppedConstraint_iff,
    mem_blockEvent_primedPaperBlockConstraints_iff]
  rfl

theorem mem_primedEvenStoppedConstraint_iff_primedPaperBlockEvent {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) (m : ℕ)
    (v : Fin (q + 1) → ℕ) :
    v ∈ primedEvenStoppedConstraint first labels terminal m ↔
      stoppedPaperBlockVector (directionStep first) labels v ∈
        HLOZConditionalProduct.blockEvent
          (primedPaperBlockConstraints
            (ι := StoppedExternalIndex (directionStep first) labels)
            (simpleRandomWalk (primedEvenReference first labels terminal))
            ((reconstructedPrimedTerminalStoppedPrefix first labels
              (zeroStoppedVector q) terminal).1 - 1)
            m (fun b : StoppedExternalBase
              (directionStep first) labels ↦ b.1)) := by
  rw [mem_primedEvenStoppedConstraint_iff,
    mem_blockEvent_primedPaperBlockConstraints_iff]
  rfl

/-! ### Filtered q+1 laws with the concrete paper-profile finsets -/

theorem actualStoppedVector_hasLaw_unprimedEvenPaperConstraint {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair) :
    HasLaw
      (actualStoppedVector m k labels
        (unprimedEvenStoppedConstraint labels m))
      (HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissibleStoppedVectors m k labels
          (unprimedEvenStoppedConstraint labels m) :
            Set (Fin (q + 1) → ℕ))]
      incrementLaw[|actualStoppedVectorEvent m k labels
        (unprimedEvenStoppedConstraint labels m)] :=
  actualStoppedVector_hasLaw_filtered m k labels hnondist _

noncomputable def actualOddStoppedVector {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) (E : Finset (Fin (q + 1) → ℕ)) :
    (ℕ → Direction) → (Fin (q + 1) → ℕ) :=
  finiteAtomDecoder
    (actualAdmissibleOddStoppedVectors m k labels terminal E)
    (fun v ↦ stoppedPrefixAtom
      (reconstructedOddStoppedPrefix labels v terminal))

theorem actualOddStoppedVector_hasLaw_filtered {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair) (E : Finset (Fin (q + 1) → ℕ)) :
    HasLaw (actualOddStoppedVector m k labels terminal E)
      (HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissibleOddStoppedVectors m k labels terminal E :
          Set (Fin (q + 1) → ℕ))]
      incrementLaw[|actualOddStoppedVectorEvent m k labels terminal E] := by
  classical
  let A := actualAdmissibleOddStoppedVectors m k labels terminal E
  let atom := fun v : Fin (q + 1) → ℕ ↦
    stoppedPrefixAtom (reconstructedOddStoppedPrefix labels v terminal)
  change HasLaw (finiteAtomDecoder A atom)
    (HLOZUrn.runVectorMeasure (q + 1))[|(A : Set _)]
    incrementLaw[|finiteAtomEvent A atom]
  apply finiteAtomDecoder_hasLaw_geometric
  · intro v w hv hw hvw
    apply stoppedPrefixAtoms_disjoint_of_firstKPrefixAt
      m k A (fun z ↦ reconstructedOddStoppedPrefix labels z terminal)
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · intro z z' hlen
      rw [reconstructedOddStoppedPrefix_length,
        reconstructedOddStoppedPrefix_length] at hlen ⊢
      omega
    · exact reconstructedOddStoppedPrefix_injective labels hnondist terminal
    · exact hv
    · exact hw
    · exact hvw
  · intro v _
    exact measurableSet_stoppedPrefixAtom _
  · intro v hv
    simpa [A, atom, finiteAtomEvent, actualOddStoppedVectorEvent] using
      reconstructedOddStoppedPrefix_conditional_geometric
        m k labels hnondist terminal E v hv

theorem actualOddStoppedVector_hasLaw_unprimedOddPaperConstraint {q : ℕ}
    (m k : ℕ) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair) :
    HasLaw
      (actualOddStoppedVector m k labels terminal
        (unprimedOddStoppedConstraint labels terminal m))
      (HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissibleOddStoppedVectors m k labels terminal
          (unprimedOddStoppedConstraint labels terminal m) :
            Set (Fin (q + 1) → ℕ))]
      incrementLaw[|actualOddStoppedVectorEvent m k labels terminal
        (unprimedOddStoppedConstraint labels terminal m)] :=
  actualOddStoppedVector_hasLaw_filtered m k labels hnondist terminal _

noncomputable def actualPrimedStoppedVector {q : ℕ}
    (m k : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (E : Finset (Fin (q + 1) → ℕ)) :
    (ℕ → Direction) → (Fin (q + 1) → ℕ) :=
  finiteAtomDecoder
    (actualAdmissiblePrimedStoppedVectors m k first labels E)
    (fun v ↦ stoppedPrefixAtom
      (reconstructedPrimedStoppedPrefix first labels v))

theorem actualPrimedStoppedVector_hasLaw_filtered {q : ℕ}
    (m k : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (E : Finset (Fin (q + 1) → ℕ)) :
    HasLaw (actualPrimedStoppedVector m k first labels E)
      (HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissiblePrimedStoppedVectors m k first labels E :
          Set (Fin (q + 1) → ℕ))]
      incrementLaw[|actualPrimedStoppedVectorEvent m k first labels E] := by
  classical
  let A := actualAdmissiblePrimedStoppedVectors m k first labels E
  let atom := fun v : Fin (q + 1) → ℕ ↦
    stoppedPrefixAtom (reconstructedPrimedStoppedPrefix first labels v)
  change HasLaw (finiteAtomDecoder A atom)
    (HLOZUrn.runVectorMeasure (q + 1))[|(A : Set _)]
    incrementLaw[|finiteAtomEvent A atom]
  apply finiteAtomDecoder_hasLaw_geometric
  · intro v w hv hw hvw
    apply stoppedPrefixAtom_pairwiseDisjoint_on_firstK m k
    · exact (Finset.mem_filter.mp hv).2
    · exact (Finset.mem_filter.mp hw).2
    · exact fun hp ↦ hvw
        (reconstructedPrimedStoppedPrefix_injective
          first labels hnondist hp)
  · intro v _
    exact measurableSet_stoppedPrefixAtom _
  · intro v hv
    simpa [A, atom, finiteAtomEvent, actualPrimedStoppedVectorEvent] using
      reconstructedPrimedStoppedPrefix_conditional_geometric
        m k first labels hnondist E v

theorem actualPrimedStoppedVector_hasLaw_primedOddPaperConstraint {q : ℕ}
    (m k : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair) :
    HasLaw
      (actualPrimedStoppedVector m k first labels
        (primedOddStoppedConstraint first labels m))
      (HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissiblePrimedStoppedVectors m k first labels
          (primedOddStoppedConstraint first labels m) :
            Set (Fin (q + 1) → ℕ))]
      incrementLaw[|actualPrimedStoppedVectorEvent m k first labels
        (primedOddStoppedConstraint first labels m)] :=
  actualPrimedStoppedVector_hasLaw_filtered m k first labels hnondist _

noncomputable def actualPrimedTerminalVector {q : ℕ}
    (m k : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) (E : Finset (Fin (q + 1) → ℕ)) :
    (ℕ → Direction) → (Fin (q + 1) → ℕ) :=
  finiteAtomDecoder
    (actualAdmissiblePrimedTerminalVectors m k first labels terminal E)
    (fun v ↦ stoppedPrefixAtom
      (reconstructedPrimedTerminalStoppedPrefix first labels v terminal))

theorem actualPrimedTerminalVector_hasLaw_filtered {q : ℕ}
    (m k : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair) (E : Finset (Fin (q + 1) → ℕ)) :
    HasLaw (actualPrimedTerminalVector m k first labels terminal E)
      (HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissiblePrimedTerminalVectors m k first labels terminal E :
          Set (Fin (q + 1) → ℕ))]
      incrementLaw[|actualPrimedTerminalVectorEvent
        m k first labels terminal E] := by
  classical
  let A := actualAdmissiblePrimedTerminalVectors
    m k first labels terminal E
  let atom := fun v : Fin (q + 1) → ℕ ↦ stoppedPrefixAtom
    (reconstructedPrimedTerminalStoppedPrefix first labels v terminal)
  change HasLaw (finiteAtomDecoder A atom)
    (HLOZUrn.runVectorMeasure (q + 1))[|(A : Set _)]
    incrementLaw[|finiteAtomEvent A atom]
  apply finiteAtomDecoder_hasLaw_geometric
  · intro v w hv hw hvw
    apply stoppedPrefixAtoms_disjoint_of_firstKPrefixAt
      m k A (fun z ↦
        reconstructedPrimedTerminalStoppedPrefix first labels z terminal)
    · intro z hz
      exact (Finset.mem_filter.mp hz).2
    · intro z z' hlen
      rw [reconstructedPrimedTerminalStoppedPrefix_length,
        reconstructedPrimedTerminalStoppedPrefix_length] at hlen ⊢
      omega
    · exact reconstructedPrimedTerminalStoppedPrefix_injective
        first labels hnondist terminal
    · exact hv
    · exact hw
    · exact hvw
  · intro v _
    exact measurableSet_stoppedPrefixAtom _
  · intro v hv
    simpa [A, atom, finiteAtomEvent, actualPrimedTerminalVectorEvent] using
      reconstructedPrimedTerminal_conditional_geometric
        m k first labels hnondist terminal E v

theorem actualPrimedTerminalVector_hasLaw_primedEvenPaperConstraint {q : ℕ}
    (m k : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair) :
    HasLaw
      (actualPrimedTerminalVector m k first labels terminal
        (primedEvenStoppedConstraint first labels terminal m))
      (HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissiblePrimedTerminalVectors m k first labels terminal
          (primedEvenStoppedConstraint first labels terminal m) :
            Set (Fin (q + 1) → ℕ))]
      incrementLaw[|actualPrimedTerminalVectorEvent m k first labels terminal
        (primedEvenStoppedConstraint first labels terminal m)] :=
  actualPrimedTerminalVector_hasLaw_filtered
    m k first labels hnondist terminal _

end Erdos1166.HLOZIncompleteStoppedBlocks
