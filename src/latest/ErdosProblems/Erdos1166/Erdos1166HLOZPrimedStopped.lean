import ErdosProblems.Erdos1166.Erdos1166HLOZActualStopped
import ErdosProblems.Erdos1166.Erdos1166HLOZProp45SourceMirrors

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

namespace Erdos1166.HLOZPrimedStopped

open HLOZDecomposition HLOZActualStopped
open HLOZReconstruction
open HLOZUrn HLOZProp45SourceClock HLOZProp45SourceInterval
open HLOZProp45SourceMirrors

/-! ### The concrete one-step-shifted deletion -/

/-- A completed lazy excursion for the primed deletion.  Its endpoint is
odd, so its two increments are `(ω (2r+1), ω (2r+2))`. -/
def IsPrimedLazyEnd (s : ℕ → Site) (j : ℕ) : Prop :=
  3 ≤ j ∧ Odd j ∧
    s (j - 2) = s (j - 1) + paperE1 ∧ s j = s (j - 2)

noncomputable local instance primedLazyEndDecidable
    (s : ℕ → Site) (j : ℕ) : Decidable (IsPrimedLazyEnd s j) :=
  Classical.propDecidable _

noncomputable def primedLazyEndsThrough
    (s : ℕ → Site) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 3 n).filter (IsPrimedLazyEnd s)

noncomputable def primedCompletedRemovedTimes
    (s : ℕ → Site) (n : ℕ) : Finset ℕ :=
  (primedLazyEndsThrough s n).biUnion fun j ↦ {j - 1, j}

noncomputable def primedPartialRemovedTimes
    (s : ℕ → Site) (n : ℕ) : Finset ℕ :=
  if IsPrimedLazyEnd s (n + 1) then {n} else ∅

noncomputable def primedRemovedTimes
    (s : ℕ → Site) (n : ℕ) : Finset ℕ :=
  primedCompletedRemovedTimes s n ∪ primedPartialRemovedTimes s n

noncomputable def primedRetainedTimes
    (s : ℕ → Site) (n : ℕ) : Finset ℕ :=
  Finset.range (n + 1) \ primedRemovedTimes s n

noncomputable def primedLazyLocalTime
    (s : ℕ → Site) (n : ℕ) (x : Site) : ℕ :=
  ((primedRemovedTimes s n).filter fun j ↦ s j = x).card

noncomputable def primedExternalLocalTime
    (s : ℕ → Site) (n : ℕ) (x : Site) : ℕ :=
  ((primedRetainedTimes s n).filter fun j ↦ s j = x).card

noncomputable def primedExternalClock
    (s : ℕ → Site) (n : ℕ) : ℕ :=
  n - 2 * (primedLazyEndsThrough s n).card -
    if IsPrimedLazyEnd s (n + 1) then 1 else 0

theorem primedRemovedTimes_subset_range (s : ℕ → Site) (n : ℕ) :
    primedRemovedTimes s n ⊆ Finset.range (n + 1) := by
  intro j hj
  rw [primedRemovedTimes, Finset.mem_union] at hj
  rcases hj with hj | hj
  · rcases Finset.mem_biUnion.mp hj with ⟨k, hk, hjk⟩
    have hkn : k ≤ n :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hjk
    simp only [Finset.mem_range]
    rcases hjk with rfl | rfl <;> omega
  · simp only [primedPartialRemovedTimes] at hj
    split at hj
    · simp only [Finset.mem_singleton] at hj
      subst j
      simp
    · simp at hj

/-- Exact primed analogue of HLOZ (2.14). -/
theorem localTime_eq_primedExternal_add_primedLazy
    (s : ℕ → Site) (n : ℕ) (x : Site) :
    localTime s n x =
      primedExternalLocalTime s n x + primedLazyLocalTime s n x := by
  let all := (Finset.range (n + 1)).filter fun j ↦ s j = x
  let lazy := (primedRemovedTimes s n).filter fun j ↦ s j = x
  have hlazy : lazy ⊆ all := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨primedRemovedTimes_subset_range s n hj.1, hj.2⟩
  have hcard := Finset.card_sdiff_add_card_eq_card hlazy
  have hdiff : all \ lazy =
      (primedRetainedTimes s n).filter fun j ↦ s j = x := by
    ext j
    simp only [all, lazy, primedRetainedTimes, Finset.mem_sdiff,
      Finset.mem_filter, Finset.mem_range, and_assoc]
    tauto
  simpa [localTime, primedExternalLocalTime, primedLazyLocalTime,
    all, lazy, hdiff] using hcard.symm

/-! ### Primed inverse clock and holding coordinates -/

def primedExcursionEndSet (s : ℕ → Site) (q : ℕ) : Set ℕ :=
  {j | IsPrimedLazyEnd s j ∧ primedExternalClock s (j - 2) = q}

noncomputable def primedHoldingTime (s : ℕ → Site) (q : ℕ) : ℕ∞ :=
  (primedExcursionEndSet s q).encard

noncomputable def primedHoldingNat (s : ℕ → Site) (q : ℕ) : ℕ :=
  (primedHoldingTime s q).toNat

noncomputable def primedExternalInverseMinus
    (s : ℕ → Site) (q : ℕ) : ℕ := by
  classical
  exact if h : ∃ n, primedExternalClock s n = q then Nat.find h else 0

theorem primedExternalInverseMinus_spec {s : ℕ → Site} {q : ℕ}
    (h : ∃ n, primedExternalClock s n = q) :
    primedExternalClock s (primedExternalInverseMinus s q) = q := by
  rw [primedExternalInverseMinus, dif_pos h]
  exact Nat.find_spec h

theorem primedExternalInverseMinus_minimal {s : ℕ → Site} {q n : ℕ}
    (hn : primedExternalClock s n = q) :
    primedExternalInverseMinus s q ≤ n := by
  have h : ∃ j, primedExternalClock s j = q := ⟨n, hn⟩
  rw [primedExternalInverseMinus, dif_pos h]
  exact Nat.find_min' h hn

noncomputable def primedExternalStateAt
    (s : ℕ → Site) (q : ℕ) : Site :=
  s (primedExternalInverseMinus s q)

noncomputable def primedExternalVisitIndexList
    (s : ℕ → Site) (q : ℕ) (x : Site) : List ℕ :=
  (List.range (q + 1)).filter fun r ↦ primedExternalStateAt s r = x

noncomputable def primedInverseClockProfile
    (s : ℕ → Site) (q : ℕ) (x : Site) : ℕ :=
  (primedExternalVisitIndexList s q x).length

noncomputable def primedInverseClockHoldingPrefix
    (s : ℕ → Site) (q cut : ℕ) (x : Site) : ℕ :=
  (((primedExternalVisitIndexList s q x).take cut).map
    (primedHoldingNat s)).sum

/-- The source's abstract primed clock instantiated by the actual
one-step-shifted deletion. -/
noncomputable def concretePrimedShiftedDeletionClock
    (m k q : ℕ) : PrimedShiftedDeletionClock m k where
  stoppedExternal s x :=
    primedExternalLocalTime s (favoriteCreationHorizon m k s) x
  stoppedLazy s x :=
    primedLazyLocalTime s (favoriteCreationHorizon m k s) x
  inverseProfile s x := primedInverseClockProfile s q x
  inverseHoldingPrefix s cut x :=
    primedInverseClockHoldingPrefix s q cut x
  stopped_decomposition s x :=
    localTime_eq_primedExternal_add_primedLazy
      s (favoriteCreationHorizon m k s) x

@[simp] theorem concretePrimed_stoppedExternal
    (m k q : ℕ) (s : ℕ → Site) (x : Site) :
    (concretePrimedShiftedDeletionClock m k q).stoppedExternal s x =
      primedExternalLocalTime s (favoriteCreationHorizon m k s) x := rfl

@[simp] theorem concretePrimed_stoppedLazy
    (m k q : ℕ) (s : ℕ → Site) (x : Site) :
    (concretePrimedShiftedDeletionClock m k q).stoppedLazy s x =
      primedLazyLocalTime s (favoriteCreationHorizon m k s) x := rfl

@[simp] theorem concretePrimed_inverseProfile
    (m k q : ℕ) (s : ℕ → Site) (x : Site) :
    (concretePrimedShiftedDeletionClock m k q).inverseProfile s x =
      primedInverseClockProfile s q x := rfl

@[simp] theorem concretePrimed_inverseHoldingPrefix
    (m k q cut : ℕ) (s : ℕ → Site) (x : Site) :
    (concretePrimedShiftedDeletionClock m k q).inverseHoldingPrefix s cut x =
      primedInverseClockHoldingPrefix s q cut x := rfl

/-! ### Genuine primed stopped-prefix atoms -/

/-- Reverse the two directions in one increment pair.  This turns the
unprimed lazy pair `(+e₁, -e₁)` into the primed pair `(-e₁, +e₁)`. -/
def reverseIncrementPair (p : IncrementPair) : IncrementPair := ![p 1, p 0]

@[simp] theorem reverseIncrementPair_zero (p : IncrementPair) :
    reverseIncrementPair p 0 = p 1 := rfl

@[simp] theorem reverseIncrementPair_one (p : IncrementPair) :
    reverseIncrementPair p 1 = p 0 := rfl

@[simp] theorem reverseIncrementPair_reverseIncrementPair
    (p : IncrementPair) :
    reverseIncrementPair (reverseIncrementPair p) = p := by
  funext i
  fin_cases i <;> rfl

/-- The distinguished completed pair for the shifted (primed) deletion:
the odd-start increment is `-e₁` and the return increment is `+e₁`, as in
HLOZ (2.12). -/
def primedDistinguishedIncrementPair : IncrementPair :=
  reverseIncrementPair distinguishedIncrementPair

@[simp] theorem primedDistinguishedIncrementPair_zero :
    primedDistinguishedIncrementPair 0 = 1 := rfl

@[simp] theorem primedDistinguishedIncrementPair_one :
    primedDistinguishedIncrementPair 1 = 0 := rfl

theorem primedDistinguishedIncrementPair_steps :
    (directionStep (primedDistinguishedIncrementPair 0),
      directionStep (primedDistinguishedIncrementPair 1)) =
      (-paperE1, paperE1) := by
  norm_num [paperE1, directionStep]

@[simp] theorem reverseIncrementPair_distinguished :
    reverseIncrementPair distinguishedIncrementPair =
      primedDistinguishedIncrementPair := rfl

@[simp] theorem reverseIncrementPair_primedDistinguished :
    reverseIncrementPair primedDistinguishedIncrementPair =
      distinguishedIncrementPair := by
  exact reverseIncrementPair_reverseIncrementPair distinguishedIncrementPair

/-- Pair list for the primed deletion.  Reversing every pair converts it
to the existing unprimed reconstruction, while preserving all run lengths. -/
def primedStoppedPairList {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ) :
    List IncrementPair :=
  (stoppedPairList (fun i ↦ reverseIncrementPair (labels i)) v).map
    reverseIncrementPair

def primedStoppedDirectionList {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ) :
    List Direction :=
  flattenPairs (primedStoppedPairList labels v)

theorem primedStoppedPairList_length {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ) :
    (primedStoppedPairList labels v).length = q + ∑ i, v i := by
  have h := stoppedDirectionList_length
    (fun i ↦ reverseIncrementPair (labels i)) v
  rw [stoppedDirectionList, flattenPairs_length] at h
  rw [primedStoppedPairList, List.length_map]
  omega

theorem primedStoppedDirectionList_length {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ) :
    (primedStoppedDirectionList labels v).length =
      2 * (q + ∑ i, v i) := by
  rw [primedStoppedDirectionList, flattenPairs_length,
    primedStoppedPairList_length]

theorem primedStoppedPairList_injective {q : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair) :
    Function.Injective (primedStoppedPairList labels) := by
  intro v w hpairs
  have hreverse := congrArg (List.map reverseIncrementPair) hpairs
  have hstopped :
      stoppedPairList (fun i ↦ reverseIncrementPair (labels i)) v =
        stoppedPairList (fun i ↦ reverseIncrementPair (labels i)) w := by
    rw [primedStoppedPairList, primedStoppedPairList,
      List.map_map, List.map_map] at hreverse
    have hinvol : reverseIncrementPair ∘ reverseIncrementPair = id := by
      funext p
      exact reverseIncrementPair_reverseIncrementPair p
    rw [hinvol, List.map_id, List.map_id] at hreverse
    exact hreverse
  have hnondist' : ∀ i,
      reverseIncrementPair (labels i) ≠ distinguishedIncrementPair := by
    intro i hi
    apply hnondist i
    have := congrArg reverseIncrementPair hi
    simpa using this
  apply reconstructedStoppedPrefix_injective
    (fun i ↦ reverseIncrementPair (labels i)) hnondist'
  exact congrArg (fun pairs ↦
    stoppedPrefixOfDirectionList (flattenPairs pairs)) hstopped

/-- A stopped prefix for the shifted pairing at an odd original horizon:
the unpaired first increment is retained and all later increments form
complete shifted pairs. -/
def reconstructedPrimedStoppedPrefix {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) : StoppedPrefix :=
  stoppedPrefixOfDirectionList (first :: primedStoppedDirectionList labels v)

theorem reconstructedPrimedStoppedPrefix_length {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) :
    (reconstructedPrimedStoppedPrefix first labels v).1 =
      2 * (q + ∑ i, v i) + 1 := by
  unfold reconstructedPrimedStoppedPrefix stoppedPrefixOfDirectionList
  simp only [List.length_cons, primedStoppedDirectionList_length]

theorem reconstructedPrimedStoppedPrefix_threshold_odd {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) :
    Odd (reconstructedPrimedStoppedPrefix first labels v).1 := by
  rw [reconstructedPrimedStoppedPrefix_length]
  use q + ∑ i, v i

theorem reconstructedPrimedStoppedPrefix_injective {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair) :
    Function.Injective (reconstructedPrimedStoppedPrefix first labels) := by
  intro v w hpref
  have hdirs := congrArg stoppedPrefixDirections hpref
  simp only [reconstructedPrimedStoppedPrefix,
    stoppedPrefixDirections_stoppedPrefixOfDirectionList] at hdirs
  have htail := (List.cons.inj hdirs).2
  exact primedStoppedPairList_injective labels hnondist
    (flattenPairs_injective htail)

theorem reconstructedPrimedStoppedPrefix_prob {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) :
    incrementLaw
        (stoppedPrefixAtom
          (reconstructedPrimedStoppedPrefix first labels v)) =
      (4 : ℝ≥0∞)⁻¹ * ((16 : ℝ≥0∞)⁻¹) ^ q *
        stoppedBernoulliWeight v := by
  rw [stoppedPrefixAtom_prob]
  rw [reconstructedPrimedStoppedPrefix_length, pow_add, pow_mul]
  have hbase : (4 : ℝ≥0∞)⁻¹ ^ 2 = (16 : ℝ≥0∞)⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (by finiteness) (by finiteness)).mp
    norm_num
  rw [hbase, pow_add]
  unfold stoppedBernoulliWeight
  rw [Finset.prod_pow_eq_pow_sum]
  ring

noncomputable local instance primedIsFirstKStoppedPrefixDecidable
    (m k : ℕ) (p : StoppedPrefix) :
    Decidable (IsFirstKStoppedPrefix m k p) :=
  Classical.propDecidable _

noncomputable local instance primedIsFirstKPrefixAtDecidable
    (m k T n : ℕ) (w : Prefix n) :
    Decidable (IsFirstKPrefixAt m k T w) :=
  Classical.propDecidable _

noncomputable def actualAdmissiblePrimedStoppedVectors {q : ℕ}
    (m k : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (E : Finset (Fin (q + 1) → ℕ)) :
    Finset (Fin (q + 1) → ℕ) :=
  E.filter fun v ↦
    IsFirstKStoppedPrefix m k
      (reconstructedPrimedStoppedPrefix first labels v)

noncomputable def actualPrimedStoppedVectorEvent {q : ℕ}
    (m k : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (E : Finset (Fin (q + 1) → ℕ)) : Set (ℕ → Direction) :=
  ⋃ v ∈ actualAdmissiblePrimedStoppedVectors m k first labels E,
    stoppedPrefixAtom (reconstructedPrimedStoppedPrefix first labels v)

theorem actualPrimedStoppedVectorEvent_prob {q : ℕ}
    (m k : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (E : Finset (Fin (q + 1) → ℕ)) :
    incrementLaw (actualPrimedStoppedVectorEvent m k first labels E) =
      (4 : ℝ≥0∞)⁻¹ * ((16 : ℝ≥0∞)⁻¹) ^ q *
        ∑ v ∈ actualAdmissiblePrimedStoppedVectors m k first labels E,
          stoppedBernoulliWeight v := by
  unfold actualPrimedStoppedVectorEvent
  have hd : ((actualAdmissiblePrimedStoppedVectors m k first labels E :
      Finset (Fin (q + 1) → ℕ)) : Set (Fin (q + 1) → ℕ)).PairwiseDisjoint
        (fun v ↦ stoppedPrefixAtom
          (reconstructedPrimedStoppedPrefix first labels v)) := by
    intro v hv w hw hvw
    have hvstop := (Finset.mem_filter.mp hv).2
    have hwstop := (Finset.mem_filter.mp hw).2
    apply stoppedPrefixAtom_pairwiseDisjoint_on_firstK m k hvstop hwstop
    exact fun hp ↦ hvw
      (reconstructedPrimedStoppedPrefix_injective first labels hnondist hp)
  have hm : ∀ v ∈ actualAdmissiblePrimedStoppedVectors
      m k first labels E,
      MeasurableSet
        (stoppedPrefixAtom
          (reconstructedPrimedStoppedPrefix first labels v)) := by
    intro v _
    exact measurableSet_stoppedPrefixAtom _
  rw [measure_biUnion_finset hd hm]
  calc
    ∑ v ∈ actualAdmissiblePrimedStoppedVectors m k first labels E,
        incrementLaw
          (stoppedPrefixAtom
            (reconstructedPrimedStoppedPrefix first labels v)) =
        ∑ v ∈ actualAdmissiblePrimedStoppedVectors m k first labels E,
          ((4 : ℝ≥0∞)⁻¹ * ((16 : ℝ≥0∞)⁻¹) ^ q) *
            stoppedBernoulliWeight v := by
      apply Finset.sum_congr rfl
      intro v _
      rw [reconstructedPrimedStoppedPrefix_prob]
    _ = (4 : ℝ≥0∞)⁻¹ * ((16 : ℝ≥0∞)⁻¹) ^ q *
        ∑ v ∈ actualAdmissiblePrimedStoppedVectors m k first labels E,
          stoppedBernoulliWeight v := by
      rw [Finset.mul_sum]

/-- Primed, odd-original-horizon Proposition 4.3 atom law.  The initial
unpaired increment contributes a common factor `1/4`, which cancels; the
unfinished final run contributes no success label, whose common factor also
cancels. -/
theorem reconstructedPrimedStoppedPrefix_conditional_geometric {q : ℕ}
    (m k : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (E : Finset (Fin (q + 1) → ℕ))
    (v : Fin (q + 1) → ℕ) :
    incrementLaw
        (stoppedPrefixAtom
          (reconstructedPrimedStoppedPrefix first labels v)) /
      incrementLaw
        (actualPrimedStoppedVectorEvent m k first labels E) =
      stoppedGeometricWeight v /
        ∑ w ∈ actualAdmissiblePrimedStoppedVectors
            m k first labels E,
          stoppedGeometricWeight w := by
  rw [reconstructedPrimedStoppedPrefix_prob,
    actualPrimedStoppedVectorEvent_prob
      m k first labels hnondist E]
  rw [ENNReal.mul_div_mul_left _ _
    (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num)))
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (by norm_num)))]
  exact stoppedBernoulli_ratio_eq_geometric_ratio _ v

/-! ### Even original horizon: observe the terminal shifted pair through
`T+1`, exactly as in the unprimed odd-terminal construction. -/

def reconstructedPrimedTerminalStoppedPrefix {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (terminal : IncrementPair) : StoppedPrefix :=
  stoppedPrefixOfDirectionList
    (first :: flattenPairs (primedStoppedPairList labels v ++ [terminal]))

theorem reconstructedPrimedTerminalStoppedPrefix_length {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (terminal : IncrementPair) :
    (reconstructedPrimedTerminalStoppedPrefix
      first labels v terminal).1 =
      2 * (q + ∑ i, v i + 1) + 1 := by
  simp [reconstructedPrimedTerminalStoppedPrefix,
    stoppedPrefixOfDirectionList, flattenPairs_length,
    primedStoppedPairList_length]

theorem reconstructedPrimedTerminal_threshold_even {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (terminal : IncrementPair) :
    Even ((reconstructedPrimedTerminalStoppedPrefix
      first labels v terminal).1 - 1) := by
  rw [reconstructedPrimedTerminalStoppedPrefix_length]
  use q + ∑ i, v i + 1
  omega

theorem reconstructedPrimedTerminalStoppedPrefix_injective {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair) :
    Function.Injective (fun v ↦
      reconstructedPrimedTerminalStoppedPrefix
        first labels v terminal) := by
  intro v w hpref
  have hdirs := congrArg stoppedPrefixDirections hpref
  simp only [reconstructedPrimedTerminalStoppedPrefix,
    stoppedPrefixDirections_stoppedPrefixOfDirectionList] at hdirs
  have htail := (List.cons.inj hdirs).2
  have hpairs : primedStoppedPairList labels v ++ [terminal] =
      primedStoppedPairList labels w ++ [terminal] :=
    flattenPairs_injective htail
  have hstopped : primedStoppedPairList labels v =
      primedStoppedPairList labels w :=
    (List.append_left_inj [terminal]).mp hpairs
  exact primedStoppedPairList_injective labels hnondist hstopped

theorem reconstructedPrimedTerminalStoppedPrefix_prob {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (terminal : IncrementPair) :
    incrementLaw
        (stoppedPrefixAtom
          (reconstructedPrimedTerminalStoppedPrefix
            first labels v terminal)) =
      (4 : ℝ≥0∞)⁻¹ * ((16 : ℝ≥0∞)⁻¹) ^ (q + 1) *
        stoppedBernoulliWeight v := by
  rw [stoppedPrefixAtom_prob]
  rw [reconstructedPrimedTerminalStoppedPrefix_length,
    pow_add, pow_mul]
  have hbase : (4 : ℝ≥0∞)⁻¹ ^ 2 = (16 : ℝ≥0∞)⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (by finiteness) (by finiteness)).mp
    norm_num
  rw [hbase, pow_add, pow_add]
  unfold stoppedBernoulliWeight
  rw [Finset.prod_pow_eq_pow_sum]
  ring

noncomputable def actualAdmissiblePrimedTerminalVectors {q : ℕ}
    (m k : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) (E : Finset (Fin (q + 1) → ℕ)) :
    Finset (Fin (q + 1) → ℕ) :=
  E.filter fun v ↦
    IsFirstKPrefixAt m k
      ((reconstructedPrimedTerminalStoppedPrefix
        first labels v terminal).1 - 1)
      (reconstructedPrimedTerminalStoppedPrefix
        first labels v terminal).2

noncomputable def actualPrimedTerminalVectorEvent {q : ℕ}
    (m k : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (terminal : IncrementPair) (E : Finset (Fin (q + 1) → ℕ)) :
    Set (ℕ → Direction) :=
  ⋃ v ∈ actualAdmissiblePrimedTerminalVectors
      m k first labels terminal E,
    stoppedPrefixAtom
      (reconstructedPrimedTerminalStoppedPrefix
        first labels v terminal)

theorem actualPrimedTerminalVectorEvent_prob {q : ℕ}
    (m k : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair) (E : Finset (Fin (q + 1) → ℕ)) :
    incrementLaw
        (actualPrimedTerminalVectorEvent
          m k first labels terminal E) =
      (4 : ℝ≥0∞)⁻¹ * ((16 : ℝ≥0∞)⁻¹) ^ (q + 1) *
        ∑ v ∈ actualAdmissiblePrimedTerminalVectors
            m k first labels terminal E,
          stoppedBernoulliWeight v := by
  unfold actualPrimedTerminalVectorEvent
  have hd : ((actualAdmissiblePrimedTerminalVectors
      m k first labels terminal E : Finset (Fin (q + 1) → ℕ)) :
      Set (Fin (q + 1) → ℕ)).PairwiseDisjoint
        (fun v ↦ stoppedPrefixAtom
          (reconstructedPrimedTerminalStoppedPrefix
            first labels v terminal)) := by
    intro v hv w hw hvw
    have hvstop := (Finset.mem_filter.mp hv).2
    have hwstop := (Finset.mem_filter.mp hw).2
    change Disjoint
      (stoppedPrefixAtom
        (reconstructedPrimedTerminalStoppedPrefix first labels v terminal))
      (stoppedPrefixAtom
        (reconstructedPrimedTerminalStoppedPrefix first labels w terminal))
    rw [Set.disjoint_left]
    intro ω hωv hωw
    have hTv := prefixAtom_subset_firstKSitesReachLevel_fiber_at
      (T := (reconstructedPrimedTerminalStoppedPrefix
        first labels v terminal).1 - 1)
      (n := (reconstructedPrimedTerminalStoppedPrefix
        first labels v terminal).1) (by omega) hvstop hωv
    have hTw := prefixAtom_subset_firstKSitesReachLevel_fiber_at
      (T := (reconstructedPrimedTerminalStoppedPrefix
        first labels w terminal).1 - 1)
      (n := (reconstructedPrimedTerminalStoppedPrefix
        first labels w terminal).1) (by omega) hwstop hωw
    have hT : (reconstructedPrimedTerminalStoppedPrefix
        first labels v terminal).1 - 1 =
        (reconstructedPrimedTerminalStoppedPrefix
          first labels w terminal).1 - 1 :=
      WithTop.coe_eq_coe.mp (hTv.symm.trans hTw)
    have hlen : (reconstructedPrimedTerminalStoppedPrefix
        first labels v terminal).1 =
        (reconstructedPrimedTerminalStoppedPrefix
          first labels w terminal).1 := by
      rw [reconstructedPrimedTerminalStoppedPrefix_length,
        reconstructedPrimedTerminalStoppedPrefix_length] at hT ⊢
      omega
    apply hvw
    apply reconstructedPrimedTerminalStoppedPrefix_injective
      first labels hnondist terminal
    cases pv : reconstructedPrimedTerminalStoppedPrefix
        first labels v terminal with
    | mk nv wv =>
      cases pw : reconstructedPrimedTerminalStoppedPrefix
          first labels w terminal with
      | mk nw ww =>
        simp only [pv, pw] at hlen hωv hωw ⊢
        subst nw
        have hww : wv = ww :=
          (Set.mem_singleton_iff.mp hωv).symm.trans
            (Set.mem_singleton_iff.mp hωw)
        subst ww
        rfl
  have hm : ∀ v ∈ actualAdmissiblePrimedTerminalVectors
      m k first labels terminal E,
      MeasurableSet
        (stoppedPrefixAtom
          (reconstructedPrimedTerminalStoppedPrefix
            first labels v terminal)) := by
    intro v _
    exact measurableSet_stoppedPrefixAtom _
  rw [measure_biUnion_finset hd hm]
  calc
    ∑ v ∈ actualAdmissiblePrimedTerminalVectors
        m k first labels terminal E,
        incrementLaw
          (stoppedPrefixAtom
            (reconstructedPrimedTerminalStoppedPrefix
              first labels v terminal)) =
        ∑ v ∈ actualAdmissiblePrimedTerminalVectors
            m k first labels terminal E,
          ((4 : ℝ≥0∞)⁻¹ * ((16 : ℝ≥0∞)⁻¹) ^ (q + 1)) *
            stoppedBernoulliWeight v := by
      apply Finset.sum_congr rfl
      intro v _
      rw [reconstructedPrimedTerminalStoppedPrefix_prob]
    _ = (4 : ℝ≥0∞)⁻¹ * ((16 : ℝ≥0∞)⁻¹) ^ (q + 1) *
        ∑ v ∈ actualAdmissiblePrimedTerminalVectors
            m k first labels terminal E,
          stoppedBernoulliWeight v := by
      rw [Finset.mul_sum]

/-- Primed, even-original-horizon Proposition 4.3 atom law, with the
terminal shifted pair observed through `T+1`. -/
theorem reconstructedPrimedTerminal_conditional_geometric {q : ℕ}
    (m k : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (terminal : IncrementPair) (E : Finset (Fin (q + 1) → ℕ))
    (v : Fin (q + 1) → ℕ) :
    incrementLaw
        (stoppedPrefixAtom
          (reconstructedPrimedTerminalStoppedPrefix
            first labels v terminal)) /
      incrementLaw
        (actualPrimedTerminalVectorEvent
          m k first labels terminal E) =
      stoppedGeometricWeight v /
        ∑ w ∈ actualAdmissiblePrimedTerminalVectors
            m k first labels terminal E,
          stoppedGeometricWeight w := by
  rw [reconstructedPrimedTerminalStoppedPrefix_prob,
    actualPrimedTerminalVectorEvent_prob
      m k first labels hnondist terminal E]
  rw [ENNReal.mul_div_mul_left _ _
    (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num)))
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (by norm_num)))]
  exact stoppedBernoulli_ratio_eq_geometric_ratio _ v

/-! ### Concrete Proposition 4.5 interface

The stopped geometric-ratio statements above are Proposition 4.3 inputs.
They do not by themselves imply the untruncated Proposition 4.2 law used by
the Chernoff argument.  The theorem below therefore exposes that law under
the external profile atom `C`, but specializes both the profile and the
holding-prefix random variables to the actual primed deletion.  The horizon
event `H` is used only in the stopped-to-inverse-clock inclusions and never
added to the conditioning measure.
-/

theorem mem_concretePrimed_inverseProfileAtom_iff
    (m k q : ℕ) (sites : Finset Site) (profile : Site → ℕ)
    (s : ℕ → Site) :
    s ∈ primedInverseProfileAtom
        (concretePrimedShiftedDeletionClock m k q) sites profile ↔
      ∀ x ∈ sites, primedInverseClockProfile s q x = profile x := by
  rfl

theorem concretePrimed_inverseHoldingPrefix_hasLaw
    (m k q cut : ℕ) (x : Site) (μ : Measure (ℕ → Site))
    (C : Set (ℕ → Site))
    (hLaw : HasLaw (fun s ↦ primedInverseClockHoldingPrefix s q cut x)
      (negBinMeasure cut) μ[|C]) :
    HasLaw (fun s ↦
        (concretePrimedShiftedDeletionClock m k q).inverseHoldingPrefix
          s cut x)
      (negBinMeasure cut) μ[|C] := by
  simpa only [concretePrimed_inverseHoldingPrefix] using hLaw

theorem concretePrimedStoppedThetaMinus_subset_canonicalDotTheta
    (m k q a : ℕ) (sites : Finset Site) (profile : Site → ℕ)
    (C H : Set (ℕ → Site))
    (hProfile : C ⊆ primedInverseProfileAtom
      (concretePrimedShiftedDeletionClock m k q) sites profile)
    (hCompatible :
      C ∩ H ∩ primedIntervalStoppedThetaMinusEvent
          (concretePrimedShiftedDeletionClock m k q) sites a ⊆
        primedMinusPrefixCompatibleEvent
          (concretePrimedShiftedDeletionClock m k q) sites a profile) :
    C ∩ H ∩ primedIntervalStoppedThetaMinusEvent
        (concretePrimedShiftedDeletionClock m k q) sites a ⊆
      primedIntervalCanonicalDotThetaMinusEvent
        (concretePrimedShiftedDeletionClock m k q) sites a profile := by
  intro s hs
  apply primedStoppedThetaMinus_subset_canonicalDotTheta
    (concretePrimedShiftedDeletionClock m k q) sites a profile
  exact ⟨⟨hs.2, hProfile hs.1.1⟩, hCompatible hs⟩

theorem concretePrimedStoppedThetaPlus_subset_canonicalDotTheta
    (m k q b : ℕ) (sites : Finset Site) (profile : Site → ℕ)
    (C H : Set (ℕ → Site))
    (hProfile : C ⊆ primedInverseProfileAtom
      (concretePrimedShiftedDeletionClock m k q) sites profile)
    (hCompatible :
      C ∩ H ∩ primedIntervalStoppedThetaPlusEvent
          (concretePrimedShiftedDeletionClock m k q) sites b ⊆
        primedPlusInitialPrefixCompatibleEvent
          (concretePrimedShiftedDeletionClock m k q) sites b) :
    C ∩ H ∩ primedIntervalStoppedThetaPlusEvent
        (concretePrimedShiftedDeletionClock m k q) sites b ⊆
      primedIntervalCanonicalDotThetaPlusEvent
        (concretePrimedShiftedDeletionClock m k q) sites b profile := by
  intro s hs
  apply primedStoppedThetaPlus_subset_canonicalDotTheta
    (concretePrimedShiftedDeletionClock m k q) sites b profile
  exact ⟨⟨hs.2, hProfile hs.1.1⟩, hCompatible hs⟩

/-- The four-way stopped-event estimate with the actual primed deletion.
No abstract `PrimedShiftedDeletionClock` is supplied by the caller. -/
theorem cond_inter_fullProp45ConcretePrimedStoppedEvent_le
    (q qPrime m a b k : ℕ)
    (hsLower : SourceIntervalScale m a)
    (hsUpper : SourceUpperScale m b)
    (μ : Measure (ℕ → Site)) (C H : Set (ℕ → Site))
    (sites : Finset Site) (unprimedProfile primedProfile : Site → ℕ)
    (hUnprimedProfile : C ⊆
      inverseClockProfileAtom q sites unprimedProfile)
    (hUnprimedMinusCompatible :
      C ∩ H ∩ intervalStoppedThetaMinusEvent sites m a k ⊆
        intervalClockPrefixCompatibleEvent
          q sites m a k unprimedProfile)
    (hUnprimedPlusCompatible :
      C ∩ H ∩ intervalStoppedThetaPlusEvent sites m b k ⊆
        intervalClockInitialPrefixCompatibleEvent q sites m b k)
    (hPrimedProfile : C ⊆ primedInverseProfileAtom
      (concretePrimedShiftedDeletionClock m k qPrime) sites primedProfile)
    (hPrimedMinusCompatible :
      C ∩ H ∩ primedIntervalStoppedThetaMinusEvent
          (concretePrimedShiftedDeletionClock m k qPrime) sites a ⊆
        primedMinusPrefixCompatibleEvent
          (concretePrimedShiftedDeletionClock m k qPrime)
          sites a primedProfile)
    (hPrimedPlusCompatible :
      C ∩ H ∩ primedIntervalStoppedThetaPlusEvent
          (concretePrimedShiftedDeletionClock m k qPrime) sites b ⊆
        primedPlusInitialPrefixCompatibleEvent
          (concretePrimedShiftedDeletionClock m k qPrime) sites b)
    (hUnprimedProp44 :
      ((sourceProp44Candidates sites m unprimedProfile).card : ℝ) ≤
        Real.exp (16 * sourceRate m))
    (hPrimedProp44 :
      ((sourceProp44Candidates sites m primedProfile).card : ℝ) ≤
        Real.exp (16 * sourceRate m))
    (hHorizonCard : (sites.card : ℝ) ≤
      Real.exp (16 * Real.sqrt (m : ℝ)))
    (hUnprimedMinusLaw : ∀ x ∈ sites,
      HasLaw (fun s ↦ inverseClockHoldingPrefix s q
        (intervalDotIndex m a unprimedProfile x) x)
        (negBinMeasure (intervalDotIndex m a unprimedProfile x)) μ[|C])
    (hUnprimedPlusLaw :
      ∀ x ∈ intervalPlusCandidates sites m b unprimedProfile,
      HasLaw (fun s ↦ inverseClockHoldingPrefix s q
        (intervalHighCut m b) x)
        (negBinMeasure (intervalHighCut m b)) μ[|C])
    (hPrimedMinusLaw : ∀ x ∈ sites,
      HasLaw (fun s ↦ primedInverseClockHoldingPrefix s qPrime
        (intervalDotIndex m a primedProfile x) x)
        (negBinMeasure (intervalDotIndex m a primedProfile x)) μ[|C])
    (hPrimedPlusLaw :
      ∀ x ∈ intervalPlusCandidates sites m b primedProfile,
      HasLaw (fun s ↦ primedInverseClockHoldingPrefix s qPrime
        (intervalHighCut m b) x)
        (negBinMeasure (intervalHighCut m b)) μ[|C]) :
    μ[|C] (C ∩ H ∩ fullProp45StoppedEvent
      (concretePrimedShiftedDeletionClock m k qPrime) sites a b) ≤
      (ENNReal.ofReal (Real.exp (-sourceRate m)) +
          ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ)))) +
        ENNReal.ofReal (Real.exp (-sourceRate m)) +
        (ENNReal.ofReal (Real.exp (-sourceRate m)) +
          ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ)))) +
        ENNReal.ofReal (Real.exp (-sourceRate m)) := by
  apply cond_inter_fullProp45StoppedEvent_le
    q m a b k hsLower hsUpper
    (concretePrimedShiftedDeletionClock m k qPrime)
    μ C H sites unprimedProfile primedProfile
  · intro s hs
    apply intervalStoppedThetaMinus_subset_canonicalDotTheta
      q sites m a k unprimedProfile
    exact ⟨⟨hs.2, hUnprimedProfile hs.1.1⟩,
      hUnprimedMinusCompatible hs⟩
  · intro s hs
    apply intervalStoppedThetaPlus_subset_canonicalDotTheta
      q sites m b k unprimedProfile
    exact ⟨⟨hs.2, hUnprimedProfile hs.1.1⟩,
      hUnprimedPlusCompatible hs⟩
  · exact concretePrimedStoppedThetaMinus_subset_canonicalDotTheta
      m k qPrime a sites primedProfile C H hPrimedProfile
      hPrimedMinusCompatible
  · exact concretePrimedStoppedThetaPlus_subset_canonicalDotTheta
      m k qPrime b sites primedProfile C H hPrimedProfile
      hPrimedPlusCompatible
  · exact hUnprimedProp44
  · exact hPrimedProp44
  · exact hHorizonCard
  · exact hUnprimedMinusLaw
  · exact hUnprimedPlusLaw
  · intro x hx
    exact concretePrimed_inverseHoldingPrefix_hasLaw
      m k qPrime (intervalDotIndex m a primedProfile x) x μ C
      (hPrimedMinusLaw x hx)
  · intro x hx
    exact concretePrimed_inverseHoldingPrefix_hasLaw
      m k qPrime (intervalHighCut m b) x μ C
      (hPrimedPlusLaw x hx)

end Erdos1166.HLOZPrimedStopped
