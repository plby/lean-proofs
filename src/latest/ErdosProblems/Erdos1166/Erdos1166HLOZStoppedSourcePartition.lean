import ErdosProblems.Erdos1166.Erdos1166HLOZMixedCreationBlocks

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal ProbabilityTheory

namespace Erdos1166.HLOZStoppedSourcePartition

open HLOZDecomposition HLOZReconstruction HLOZActualStopped
  HLOZPrimedStopped HLOZIncompleteStoppedBlocks HLOZMixedCreationBlocks

def stoppedSourceCondition (m k : ℕ) (C : Finset Site) :
    Set (ℕ → Direction) :=
  {ω | simpleRandomWalk ω ∈ hlozThresholdTimeEventK m k ∧
    levelCreationSitesUpTo (simpleRandomWalk ω) m k = C}

noncomputable def prefixSourceCondition
    (m k : ℕ) (C : Finset Site) (p : StoppedPrefix) : Prop :=
  let s := simpleRandomWalk (extendPrefix p.2)
  s ∈ hlozThresholdTimeEventK m k ∧ levelCreationSitesUpTo s m k = C

/-- At a genuine `T_m^k` prefix, the literal source condition is exactly
the mixed (4.7)/(4.8) horizontal-domino condition: equality on dominoes
meeting the fixed creation set and strict inequality on disjoint dominoes. -/
theorem prefixSourceCondition_iff_mixedX1
    (m k : ℕ) (C : Finset Site) (p : StoppedPrefix)
    (T : ℕ) (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hfirst : firstKSitesReachLevel m k
      (simpleRandomWalk (extendPrefix p.2)) = T) :
    prefixSourceCondition m k C p ↔
      MixedX1DominoCondition
        (simpleRandomWalk (extendPrefix p.2)) T m C := by
  exact sourceCondition_at_first_iff_mixedX1
    (simpleRandomWalk (extendPrefix p.2)) m k T C hm hk hfree hfirst

theorem firstKSitesReachLevel_eq_of_prefix_eq
    {s t : ℕ → Site} {m k T : ℕ}
    (hst : ∀ j, j ≤ T → s j = t j)
    (hs : firstKSitesReachLevel m k s = T) :
    firstKSitesReachLevel m k t = T :=
  firstKSitesReachLevel_congr_prefix_of_eq hst hs

theorem levelCreationSitesUpTo_eq_of_prefix_eq
    {s t : ℕ → Site} {m k T : ℕ}
    (hst : ∀ j, j ≤ T → s j = t j)
    (hs : firstKSitesReachLevel m k s = T) :
    levelCreationSitesUpTo s m k = levelCreationSitesUpTo t m k := by
  classical
  unfold levelCreationSitesUpTo
  apply Finset.image_congr
  intro i hi
  have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
  have hTi : firstKSitesReachLevel m i s ≤ (T : WithTop ℕ) := by
    have hmono := firstKSitesReachLevel_mono_k s m hik
    simpa only [hs] using hmono
  have hfinite : firstKSitesReachLevel m i s ≠ ⊤ := by
    intro htop
    rw [htop] at hTi
    exact (not_le_of_gt (WithTop.coe_lt_top T)) hTi
  let Ti := (firstKSitesReachLevel m i s).untopA
  have hTiCoe : (Ti : WithTop ℕ) = firstKSitesReachLevel m i s := by
    dsimp only [Ti]
    rw [WithTop.untopA_eq_untop hfinite]
    exact WithTop.coe_untop _ hfinite
  have hTiNat : Ti ≤ T := by
    exact WithTop.coe_le_coe.mp (hTiCoe.trans_le hTi)
  have htime : firstKSitesReachLevel m i t = Ti := by
    apply firstKSitesReachLevel_congr_prefix_of_eq
      (s := s) (t := t)
    · intro j hj
      exact hst j (hj.trans hTiNat)
    · exact hTiCoe.symm
  unfold levelCreationSite
  rw [htime]
  change s Ti = t Ti
  exact hst Ti hTiNat

theorem stoppedSourceCondition_constant_on_prefix
    (m k T : ℕ) (C : Finset Site) (p : StoppedPrefix)
    (hTp : T ≤ p.1)
    (hfirst : firstKSitesReachLevel m k
      (simpleRandomWalk (extendPrefix p.2)) = T)
    {ω : ℕ → Direction} (hω : ω ∈ stoppedPrefixAtom p) :
    ω ∈ stoppedSourceCondition m k C ↔
      prefixSourceCondition m k C p := by
  let s := simpleRandomWalk (extendPrefix p.2)
  let t := simpleRandomWalk ω
  have hpath : ∀ j, j ≤ T → s j = t j := by
    intro j hj
    change simpleRandomWalk (extendPrefix p.2) j = simpleRandomWalk ω j
    exact (simpleRandomWalk_congr_extendPrefix p.2 ω hω j
      (hj.trans hTp)).symm
  have htfirst : firstKSitesReachLevel m k t = T :=
    firstKSitesReachLevel_eq_of_prefix_eq hpath hfirst
  have hM : s ∈ hlozThresholdTimeEventK m k ↔
      t ∈ hlozThresholdTimeEventK m k := by
    let F := hlozMThresholdFiberPathEvent m k T
    have hF := mem_iff_of_measurableSet_canonicalFiltration T
      (measurableSet_hlozMThresholdFiberPathEvent m k T) hpath
    change (s ∈ hlozThresholdTimeEventK m k ∧
        firstKSitesReachLevel m k s = (T : WithTop ℕ)) ↔
      (t ∈ hlozThresholdTimeEventK m k ∧
        firstKSitesReachLevel m k t = (T : WithTop ℕ)) at hF
    rw [hfirst, htfirst] at hF
    simpa using hF
  have hC : levelCreationSitesUpTo s m k =
      levelCreationSitesUpTo t m k :=
    levelCreationSitesUpTo_eq_of_prefix_eq hpath hfirst
  change (t ∈ hlozThresholdTimeEventK m k ∧
      levelCreationSitesUpTo t m k = C) ↔
    (s ∈ hlozThresholdTimeEventK m k ∧
      levelCreationSitesUpTo s m k = C)
  rw [← hM, ← hC]

theorem finiteAtomEvent_inter_condition_eq_filter
    {V Ω : Type*} [DecidableEq V]
    (A : Finset V) (atom : V → Set Ω) (Q : Set Ω) (P : V → Prop)
    [DecidablePred P]
    (hconstant : ∀ v ∈ A, ∀ ω ∈ atom v, (ω ∈ Q ↔ P v)) :
    finiteAtomEvent A atom ∩ Q =
      finiteAtomEvent (A.filter P) atom := by
  ext ω
  simp only [finiteAtomEvent, Set.mem_inter_iff, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨v, hv⟩, hQ⟩
    rcases hv with ⟨hvA, hωv⟩
    refine ⟨v, Finset.mem_filter.mpr ⟨hvA, ?_⟩, hωv⟩
    exact (hconstant v hvA ω hωv).mp hQ
  · rintro ⟨v, hv, hωv⟩
    rcases Finset.mem_filter.mp hv with ⟨hvA, hPv⟩
    exact ⟨⟨v, hvA, hωv⟩, (hconstant v hvA ω hωv).mpr hPv⟩

noncomputable def sourceFilterForPrefixes {V : Type*} [DecidableEq V]
    (m k : ℕ) (C : Finset Site) (p : V → StoppedPrefix)
    (E : Finset V) : Finset V := by
  classical
  exact E.filter fun v ↦ prefixSourceCondition m k C (p v)

theorem actualStoppedVectorEvent_inter_sourceCondition {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (E : Finset (Fin (q + 1) → ℕ)) :
    actualStoppedVectorEvent m k labels E ∩ stoppedSourceCondition m k C =
      actualStoppedVectorEvent m k labels
        (sourceFilterForPrefixes m k C
          (reconstructedStoppedPrefix labels) E) := by
  classical
  let p := reconstructedStoppedPrefix labels
  let A := actualAdmissibleStoppedVectors m k labels E
  let P := fun v : Fin (q + 1) → ℕ ↦
    prefixSourceCondition m k C (p v)
  let atom := fun v : Fin (q + 1) → ℕ ↦ stoppedPrefixAtom (p v)
  have hA : actualAdmissibleStoppedVectors m k labels
      (sourceFilterForPrefixes m k C p E) = A.filter P := by
    ext v
    simp only [actualAdmissibleStoppedVectors, sourceFilterForPrefixes,
      Finset.mem_filter, A, P]
    tauto
  change finiteAtomEvent A atom ∩ stoppedSourceCondition m k C =
    finiteAtomEvent
      (actualAdmissibleStoppedVectors m k labels
        (sourceFilterForPrefixes m k C p E)) atom
  rw [hA]
  apply finiteAtomEvent_inter_condition_eq_filter
  intro v hv ω hω
  have hfirst : firstKSitesReachLevel m k
      (simpleRandomWalk (extendPrefix (p v).2)) = (p v).1 :=
    (Finset.mem_filter.mp hv).2
  exact stoppedSourceCondition_constant_on_prefix
    m k (p v).1 C (p v) le_rfl hfirst hω

theorem actualOddStoppedVectorEvent_inter_sourceCondition {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) (E : Finset (Fin (q + 1) → ℕ)) :
    actualOddStoppedVectorEvent m k labels terminal E ∩
        stoppedSourceCondition m k C =
      actualOddStoppedVectorEvent m k labels terminal
        (sourceFilterForPrefixes m k C
          (fun v ↦ reconstructedOddStoppedPrefix labels v terminal) E) := by
  classical
  let p := fun v : Fin (q + 1) → ℕ ↦
    reconstructedOddStoppedPrefix labels v terminal
  let A := actualAdmissibleOddStoppedVectors m k labels terminal E
  let P := fun v : Fin (q + 1) → ℕ ↦
    prefixSourceCondition m k C (p v)
  let atom := fun v : Fin (q + 1) → ℕ ↦ stoppedPrefixAtom (p v)
  have hA : actualAdmissibleOddStoppedVectors m k labels terminal
      (sourceFilterForPrefixes m k C p E) = A.filter P := by
    ext v
    simp only [actualAdmissibleOddStoppedVectors, sourceFilterForPrefixes,
      Finset.mem_filter, A, P]
    tauto
  change finiteAtomEvent A atom ∩ stoppedSourceCondition m k C =
    finiteAtomEvent
      (actualAdmissibleOddStoppedVectors m k labels terminal
        (sourceFilterForPrefixes m k C p E)) atom
  rw [hA]
  apply finiteAtomEvent_inter_condition_eq_filter
  intro v hv ω hω
  have hfirst : firstKSitesReachLevel m k
      (simpleRandomWalk (extendPrefix (p v).2)) = (p v).1 - 1 :=
    (Finset.mem_filter.mp hv).2
  exact stoppedSourceCondition_constant_on_prefix
    m k ((p v).1 - 1) C (p v) (by omega) hfirst hω

theorem actualPrimedStoppedVectorEvent_inter_sourceCondition {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (E : Finset (Fin (q + 1) → ℕ)) :
    actualPrimedStoppedVectorEvent m k first labels E ∩
        stoppedSourceCondition m k C =
      actualPrimedStoppedVectorEvent m k first labels
        (sourceFilterForPrefixes m k C
          (reconstructedPrimedStoppedPrefix first labels) E) := by
  classical
  let p := reconstructedPrimedStoppedPrefix first labels
  let A := actualAdmissiblePrimedStoppedVectors m k first labels E
  let P := fun v : Fin (q + 1) → ℕ ↦
    prefixSourceCondition m k C (p v)
  let atom := fun v : Fin (q + 1) → ℕ ↦ stoppedPrefixAtom (p v)
  have hA : actualAdmissiblePrimedStoppedVectors m k first labels
      (sourceFilterForPrefixes m k C p E) = A.filter P := by
    ext v
    simp only [actualAdmissiblePrimedStoppedVectors, sourceFilterForPrefixes,
      Finset.mem_filter, A, P]
    tauto
  change finiteAtomEvent A atom ∩ stoppedSourceCondition m k C =
    finiteAtomEvent
      (actualAdmissiblePrimedStoppedVectors m k first labels
        (sourceFilterForPrefixes m k C p E)) atom
  rw [hA]
  apply finiteAtomEvent_inter_condition_eq_filter
  intro v hv ω hω
  have hfirst : firstKSitesReachLevel m k
      (simpleRandomWalk (extendPrefix (p v).2)) = (p v).1 :=
    (Finset.mem_filter.mp hv).2
  exact stoppedSourceCondition_constant_on_prefix
    m k (p v).1 C (p v) le_rfl hfirst hω

theorem actualPrimedTerminalVectorEvent_inter_sourceCondition {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (E : Finset (Fin (q + 1) → ℕ)) :
    actualPrimedTerminalVectorEvent m k first labels terminal E ∩
        stoppedSourceCondition m k C =
      actualPrimedTerminalVectorEvent m k first labels terminal
        (sourceFilterForPrefixes m k C
          (fun v ↦ reconstructedPrimedTerminalStoppedPrefix
            first labels v terminal) E) := by
  classical
  let p := fun v : Fin (q + 1) → ℕ ↦
    reconstructedPrimedTerminalStoppedPrefix first labels v terminal
  let A := actualAdmissiblePrimedTerminalVectors
    m k first labels terminal E
  let P := fun v : Fin (q + 1) → ℕ ↦
    prefixSourceCondition m k C (p v)
  let atom := fun v : Fin (q + 1) → ℕ ↦ stoppedPrefixAtom (p v)
  have hA : actualAdmissiblePrimedTerminalVectors m k first labels terminal
      (sourceFilterForPrefixes m k C p E) = A.filter P := by
    ext v
    simp only [actualAdmissiblePrimedTerminalVectors, sourceFilterForPrefixes,
      Finset.mem_filter, A, P]
    tauto
  change finiteAtomEvent A atom ∩ stoppedSourceCondition m k C =
    finiteAtomEvent
      (actualAdmissiblePrimedTerminalVectors m k first labels terminal
        (sourceFilterForPrefixes m k C p E)) atom
  rw [hA]
  apply finiteAtomEvent_inter_condition_eq_filter
  intro v hv ω hω
  have hfirst : firstKSitesReachLevel m k
      (simpleRandomWalk (extendPrefix (p v).2)) = (p v).1 - 1 :=
    (Finset.mem_filter.mp hv).2
  exact stoppedSourceCondition_constant_on_prefix
    m k ((p v).1 - 1) C (p v) (by omega) hfirst hω
/-! The mixed source finsets.  Unlike the superseded all-below filter,
these use (4.7) on every horizontal domino meeting the fixed creation set
and (4.8) only on disjoint dominoes. -/

noncomputable def stoppedRunVectorBox (q m : ℕ) :
    Finset (Fin (q + 1) → ℕ) :=
  Fintype.piFinset fun _ : Fin (q + 1) ↦ Finset.range (m + 1)

noncomputable def mixedPrefixConstraint {V : Type*} [DecidableEq V]
    (m : ℕ) (C : Finset Site) (T : V → ℕ)
    (p : V → StoppedPrefix) (E : Finset V) : Finset V := by
  classical
  exact E.filter fun v ↦
    MixedX1DominoCondition
      (simpleRandomWalk (extendPrefix (p v).2)) (T v) m C

noncomputable def unprimedEvenSourceConstraint {q : ℕ}
    (m _k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair) :=
  mixedPrefixConstraint m C
    (fun v ↦ (reconstructedStoppedPrefix labels v).1)
    (reconstructedStoppedPrefix labels) (stoppedRunVectorBox q m)

noncomputable def unprimedOddSourceConstraint {q : ℕ}
    (m _k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) :=
  mixedPrefixConstraint m C
    (fun v ↦ (reconstructedOddStoppedPrefix labels v terminal).1 - 1)
    (fun v ↦ reconstructedOddStoppedPrefix labels v terminal)
    (stoppedRunVectorBox q m)

noncomputable def primedOddSourceConstraint {q : ℕ}
    (m _k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) :=
  mixedPrefixConstraint m C
    (fun v ↦ (reconstructedPrimedStoppedPrefix first labels v).1)
    (reconstructedPrimedStoppedPrefix first labels)
    (stoppedRunVectorBox q m)

noncomputable def primedEvenSourceConstraint {q : ℕ}
    (m _k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair) :=
  mixedPrefixConstraint m C
    (fun v ↦
      (reconstructedPrimedTerminalStoppedPrefix
        first labels v terminal).1 - 1)
    (fun v ↦ reconstructedPrimedTerminalStoppedPrefix
      first labels v terminal)
    (stoppedRunVectorBox q m)

theorem unprimedEven_source_partition {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) :
    actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
        stoppedSourceCondition m k C =
      actualStoppedVectorEvent m k labels
        (unprimedEvenSourceConstraint m k C labels) := by
  rw [actualStoppedVectorEvent_inter_sourceCondition]
  have hA : actualAdmissibleStoppedVectors m k labels
      (sourceFilterForPrefixes m k C
        (reconstructedStoppedPrefix labels) (stoppedRunVectorBox q m)) =
      actualAdmissibleStoppedVectors m k labels
        (unprimedEvenSourceConstraint m k C labels) := by
    ext v
    simp only [actualAdmissibleStoppedVectors, sourceFilterForPrefixes,
      unprimedEvenSourceConstraint, mixedPrefixConstraint,
      Finset.mem_filter]
    constructor
    · rintro ⟨⟨hv, hsource⟩, hfirst⟩
      exact ⟨⟨hv, (prefixSourceCondition_iff_mixedX1
        m k C (reconstructedStoppedPrefix labels v)
        (reconstructedStoppedPrefix labels v).1 hm hk hfree hfirst).mp
          hsource⟩, hfirst⟩
    · rintro ⟨⟨hv, hmixed⟩, hfirst⟩
      exact ⟨⟨hv, (prefixSourceCondition_iff_mixedX1
        m k C (reconstructedStoppedPrefix labels v)
        (reconstructedStoppedPrefix labels v).1 hm hk hfree hfirst).mpr
          hmixed⟩, hfirst⟩
  unfold actualStoppedVectorEvent
  rw [hA]

theorem unprimedOdd_source_partition {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) :
    actualOddStoppedVectorEvent m k labels terminal
          (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C =
      actualOddStoppedVectorEvent m k labels terminal
        (unprimedOddSourceConstraint m k C labels terminal) := by
  rw [actualOddStoppedVectorEvent_inter_sourceCondition]
  have hA : actualAdmissibleOddStoppedVectors m k labels terminal
      (sourceFilterForPrefixes m k C
        (fun v ↦ reconstructedOddStoppedPrefix labels v terminal)
        (stoppedRunVectorBox q m)) =
      actualAdmissibleOddStoppedVectors m k labels terminal
        (unprimedOddSourceConstraint m k C labels terminal) := by
    ext v
    simp only [actualAdmissibleOddStoppedVectors, sourceFilterForPrefixes,
      unprimedOddSourceConstraint, mixedPrefixConstraint, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hv, hsource⟩, hfirst⟩
      exact ⟨⟨hv, (prefixSourceCondition_iff_mixedX1
        m k C (reconstructedOddStoppedPrefix labels v terminal)
        ((reconstructedOddStoppedPrefix labels v terminal).1 - 1)
        hm hk hfree hfirst).mp hsource⟩, hfirst⟩
    · rintro ⟨⟨hv, hmixed⟩, hfirst⟩
      exact ⟨⟨hv, (prefixSourceCondition_iff_mixedX1
        m k C (reconstructedOddStoppedPrefix labels v terminal)
        ((reconstructedOddStoppedPrefix labels v terminal).1 - 1)
        hm hk hfree hfirst).mpr hmixed⟩, hfirst⟩
  unfold actualOddStoppedVectorEvent
  rw [hA]

theorem primedOdd_source_partition {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) :
    actualPrimedStoppedVectorEvent m k first labels
          (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C =
      actualPrimedStoppedVectorEvent m k first labels
        (primedOddSourceConstraint m k C first labels) := by
  rw [actualPrimedStoppedVectorEvent_inter_sourceCondition]
  have hA : actualAdmissiblePrimedStoppedVectors m k first labels
      (sourceFilterForPrefixes m k C
        (reconstructedPrimedStoppedPrefix first labels)
        (stoppedRunVectorBox q m)) =
      actualAdmissiblePrimedStoppedVectors m k first labels
        (primedOddSourceConstraint m k C first labels) := by
    ext v
    simp only [actualAdmissiblePrimedStoppedVectors, sourceFilterForPrefixes,
      primedOddSourceConstraint, mixedPrefixConstraint, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hv, hsource⟩, hfirst⟩
      exact ⟨⟨hv, (prefixSourceCondition_iff_mixedX1
        m k C (reconstructedPrimedStoppedPrefix first labels v)
        (reconstructedPrimedStoppedPrefix first labels v).1
        hm hk hfree hfirst).mp hsource⟩, hfirst⟩
    · rintro ⟨⟨hv, hmixed⟩, hfirst⟩
      exact ⟨⟨hv, (prefixSourceCondition_iff_mixedX1
        m k C (reconstructedPrimedStoppedPrefix first labels v)
        (reconstructedPrimedStoppedPrefix first labels v).1
        hm hk hfree hfirst).mpr hmixed⟩, hfirst⟩
  unfold actualPrimedStoppedVectorEvent
  rw [hA]

theorem primedEven_source_partition {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair) (terminal : IncrementPair)
    (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) :
    actualPrimedTerminalVectorEvent m k first labels terminal
          (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C =
      actualPrimedTerminalVectorEvent m k first labels terminal
        (primedEvenSourceConstraint m k C first labels terminal) := by
  rw [actualPrimedTerminalVectorEvent_inter_sourceCondition]
  have hA : actualAdmissiblePrimedTerminalVectors m k first labels terminal
      (sourceFilterForPrefixes m k C
        (fun v ↦ reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal) (stoppedRunVectorBox q m)) =
      actualAdmissiblePrimedTerminalVectors m k first labels terminal
        (primedEvenSourceConstraint m k C first labels terminal) := by
    ext v
    simp only [actualAdmissiblePrimedTerminalVectors, sourceFilterForPrefixes,
      primedEvenSourceConstraint, mixedPrefixConstraint, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hv, hsource⟩, hfirst⟩
      exact ⟨⟨hv, (prefixSourceCondition_iff_mixedX1
        m k C (reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal)
        ((reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal).1 - 1)
        hm hk hfree hfirst).mp hsource⟩, hfirst⟩
    · rintro ⟨⟨hv, hmixed⟩, hfirst⟩
      exact ⟨⟨hv, (prefixSourceCondition_iff_mixedX1
        m k C (reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal)
        ((reconstructedPrimedTerminalStoppedPrefix
          first labels v terminal).1 - 1)
        hm hk hfree hfirst).mpr hmixed⟩, hfirst⟩
  unfold actualPrimedTerminalVectorEvent
  rw [hA]

theorem unprimedEven_source_hasLaw {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) :
    HasLaw
      (actualStoppedVector m k labels
        (unprimedEvenSourceConstraint m k C labels))
      (HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissibleStoppedVectors m k labels
          (unprimedEvenSourceConstraint m k C labels) : Set _)]
      incrementLaw[|
        actualStoppedVectorEvent m k labels (stoppedRunVectorBox q m) ∩
          stoppedSourceCondition m k C] := by
  rw [unprimedEven_source_partition m k C labels hm hk hfree]
  exact actualStoppedVector_hasLaw_filtered m k labels hnondist _

theorem unprimedOdd_source_hasLaw {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) :
    HasLaw
      (actualOddStoppedVector m k labels terminal
        (unprimedOddSourceConstraint m k C labels terminal))
      (HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissibleOddStoppedVectors m k labels terminal
          (unprimedOddSourceConstraint m k C labels terminal) : Set _)]
      incrementLaw[|
        actualOddStoppedVectorEvent m k labels terminal
            (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C] := by
  rw [unprimedOdd_source_partition m k C labels terminal hm hk hfree]
  exact actualOddStoppedVector_hasLaw_filtered
    m k labels hnondist terminal _

theorem primedOdd_source_hasLaw {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) :
    HasLaw
      (actualPrimedStoppedVector m k first labels
        (primedOddSourceConstraint m k C first labels))
      (HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissiblePrimedStoppedVectors m k first labels
          (primedOddSourceConstraint m k C first labels) : Set _)]
      incrementLaw[|
        actualPrimedStoppedVectorEvent m k first labels
            (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C] := by
  rw [primedOdd_source_partition m k C first labels hm hk hfree]
  exact actualPrimedStoppedVector_hasLaw_filtered
    m k first labels hnondist _

theorem primedEven_source_hasLaw {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair) (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) :
    HasLaw
      (actualPrimedTerminalVector m k first labels terminal
        (primedEvenSourceConstraint m k C first labels terminal))
      (HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissiblePrimedTerminalVectors m k first labels terminal
          (primedEvenSourceConstraint m k C first labels terminal) : Set _)]
      incrementLaw[|
        actualPrimedTerminalVectorEvent m k first labels terminal
            (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C] := by
  rw [primedEven_source_partition m k C first labels terminal hm hk hfree]
  exact actualPrimedTerminalVector_hasLaw_filtered
    m k first labels hnondist terminal _

end Erdos1166.HLOZStoppedSourcePartition
