import ErdosProblems.Erdos1165.PreStoppingConditionalLaw

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace Erdos1165.VariableStoppedFiber

open LazyDecomposition PathInsertion StoppedInsertion SpatialInsertionFiber
open PreStoppingFiber HLOZPathEvents

noncomputable section

/-!
# Variable-time prefix-free stopped fibres

Fixing a physical threshold-creation time together with a retained external
word fixes the total number of deleted blocks.  The resulting law is a
product law conditioned on a global sum, not HLOZ (6.7).  The sound
disintegration therefore keeps the creation time variable.

For a deterministic clock cutoff, the fibres below fix only the retained
word and the canonical zero-or-one direction boundary tail.  Their insertion
vectors have variable lengths, and prefix-freeness comes from uniqueness of
the threshold-creation time.  They form a countable disjoint partition of the
strict event `truncatedLevelTime m k cutoff < cutoff`.
-/

/-- A canonical incomplete terminal block has at most one direction. -/
abbrev BoundaryTail := {tail : List Direction // tail.length ≤ 1}

/-- Countable external-word data, without a physical stopping time. -/
structure ExternalWordCode (o : Orientation) where
  retainedCount : ℕ
  retained : Fin retainedCount → RetainedBlock o
  tail : BoundaryTail

private def externalWordCodeKey {o : Orientation} (c : ExternalWordCode o) :
    ℕ × List Block × List Direction :=
  (c.retainedCount, retainedWord c.retained, c.tail.1)

private theorem externalWordCodeKey_injective {o : Orientation} :
    Function.Injective (@externalWordCodeKey o) := by
  intro c d h
  rcases c with ⟨i, r, tail⟩
  rcases d with ⟨j, s, tail'⟩
  simp only [externalWordCodeKey, Prod.mk.injEq] at h
  obtain ⟨hij, hrs, htail⟩ := h
  subst j
  have hr : r = s := by
    funext k
    apply Subtype.ext
    exact congrFun (List.ofFn_injective hrs) k
  subst s
  have ht : tail = tail' := by
    apply Subtype.ext
    exact htail
  subst tail'
  rfl

noncomputable instance externalWordCodeCountable (o : Orientation) :
    Countable (ExternalWordCode o) :=
  externalWordCodeKey_injective.countable

/-! ## Canonical pairing of an insertion prefix -/

theorem pairDirectionList_flatten_append_shortTail
    (blocks : List Block) (tail : List Direction) (htail : tail.length ≤ 1) :
    pairDirectionList
        (blocks.flatMap (fun b ↦ [b.1, b.2]) ++ tail) = blocks := by
  induction blocks with
  | nil =>
      cases tail with
      | nil => rfl
      | cons a rest =>
          cases rest with
          | nil => rfl
          | cons b rest => simp at htail
  | cons b blocks ih =>
      rcases b with ⟨b₁, b₂⟩
      change pairDirectionList
        (b₁ :: b₂ :: (blocks.flatMap (fun b ↦ [b.1, b.2]) ++ tail)) =
          (b₁, b₂) :: blocks
      rw [pairDirectionList]
      exact congrArg (List.cons (b₁, b₂)) ih

theorem unpairedDirectionTail_flatten_append_shortTail
    (blocks : List Block) (tail : List Direction) (htail : tail.length ≤ 1) :
    unpairedDirectionTail
        (blocks.flatMap (fun b ↦ [b.1, b.2]) ++ tail) = tail := by
  induction blocks with
  | nil =>
      cases tail with
      | nil => rfl
      | cons a rest =>
          cases rest with
          | nil => rfl
          | cons b rest => simp at htail
  | cons b blocks ih =>
      rcases b with ⟨b₁, b₂⟩
      change unpairedDirectionTail
        (b₁ :: b₂ :: (blocks.flatMap (fun b ↦ [b.1, b.2]) ++ tail)) = tail
      rw [unpairedDirectionTail]
      exact ih

theorem prefixBlockWord_eq_of_creationAtom
    {o : Orientation} {i : ℕ} (m k cutoff : ℕ)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (tail : BoundaryTail) {omega : StepPath}
    (homega : omega ∈ stoppedInsertionAtom
      (truncatedLevelTime m k cutoff) r q tail.1) :
    prefixBlockWord (truncatedLevelTime m k cutoff omega) omega =
      insertGapVector r q := by
  have hlength := homega.1
  have hlist := homega.2
  rw [hlength]
  unfold prefixBlockWord
  rw [hlist]
  exact pairDirectionList_flatten_append_shortTail
    (insertGapVector r q) tail.1 tail.2

theorem prefixDirectionTail_eq_of_creationAtom
    {o : Orientation} {i : ℕ} (m k cutoff : ℕ)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (tail : BoundaryTail) {omega : StepPath}
    (homega : omega ∈ stoppedInsertionAtom
      (truncatedLevelTime m k cutoff) r q tail.1) :
    prefixDirectionTail (truncatedLevelTime m k cutoff omega) omega = tail.1 := by
  have hlength := homega.1
  have hlist := homega.2
  rw [hlength]
  unfold prefixDirectionTail
  rw [hlist]
  exact unpairedDirectionTail_flatten_append_shortTail
    (insertGapVector r q) tail.1 tail.2

/-! ## One finite coordinate cap, without fixing the stopping time -/

/-- The coordinate predicate which excludes the artificial fallback branch
of the capped clock. -/
def StrictlyBeforeClockCutoff {o : Orientation} {i cap : ℕ}
    (r : Fin i → RetainedBlock o) (tail : BoundaryTail)
    (cutoff : ℕ) (q : CappedCoordinates i cap) : Prop :=
  insertionPrefixLength r (fun j ↦ (q j : ℕ)) tail.1 < cutoff

/-- A finite capped fibre with variable physical stopping time. -/
def strictCappedCreationFiber {o : Orientation} (m k cutoff cap : ℕ)
    (code : ExternalWordCode o) : Set StepPath :=
  preStoppingFiberEvent (truncatedLevelTime m k cutoff)
    code.retained cap code.tail.1
    (StrictlyBeforeClockCutoff code.retained code.tail cutoff)

theorem measurableSet_strictCappedCreationFiber {o : Orientation}
    (m k cutoff cap : ℕ) (code : ExternalWordCode o) :
    MeasurableSet (strictCappedCreationFiber m k cutoff cap code) := by
  exact measurableSet_preStoppingFiberEvent
    (isFiniteStoppingTime_truncatedLevelTime m k cutoff)
    code.retained cap code.tail.1 _

/-- Membership in a strict fibre really is strictly before the artificial
clock fallback. -/
theorem truncatedLevelTime_lt_of_mem_strictCappedCreationFiber
    {o : Orientation} {m k cutoff cap : ℕ} {code : ExternalWordCode o}
    {omega : StepPath} (homega : omega ∈
      strictCappedCreationFiber m k cutoff cap code) :
    truncatedLevelTime m k cutoff omega < cutoff := by
  rcases Set.mem_iUnion.mp homega with ⟨q, hq⟩
  exact hq.1.symm ▸ q.2.1

/-- Distinct external-word codes give disjoint variable-time fibres. -/
theorem disjoint_strictCappedCreationFiber_of_ne {o : Orientation}
    (m k cutoff cap : ℕ) {c d : ExternalWordCode o} (hcd : c ≠ d) :
    Disjoint (strictCappedCreationFiber m k cutoff cap c)
      (strictCappedCreationFiber m k cutoff cap d) := by
  classical
  rw [Set.disjoint_left]
  intro omega hc hd
  rcases Set.mem_iUnion.mp hc with ⟨q, hq⟩
  rcases Set.mem_iUnion.mp hd with ⟨q', hq'⟩
  apply hcd
  apply externalWordCodeKey_injective
  have hword := (prefixBlockWord_eq_of_creationAtom m k cutoff
    c.retained (fun j ↦ (q.1 j : ℕ)) c.tail hq).symm.trans
      (prefixBlockWord_eq_of_creationAtom m k cutoff
        d.retained (fun j ↦ (q'.1 j : ℕ)) d.tail hq')
  have hretained : retainedWord c.retained = retainedWord d.retained := by
    rw [← deleteRemovableBlocks_insertGapVector c.retained
      (fun j ↦ (q.1 j : ℕ)), hword,
      deleteRemovableBlocks_insertGapVector d.retained]
  have hcount : c.retainedCount = d.retainedCount := by
    have := congrArg List.length hretained
    simpa [retainedWord] using this
  have htail := (prefixDirectionTail_eq_of_creationAtom m k cutoff
    c.retained (fun j ↦ (q.1 j : ℕ)) c.tail hq).symm.trans
      (prefixDirectionTail_eq_of_creationAtom m k cutoff
        d.retained (fun j ↦ (q'.1 j : ℕ)) d.tail hq')
  exact Prod.ext hcount (Prod.ext hretained htail)

/-- At the intrinsic cap `cutoff`, the variable-time external-word fibres
partition exactly the strict branch of the capped threshold clock.  In
particular the index does not contain the physical threshold-creation time. -/
theorem iUnion_strictCappedCreationFiber {o : Orientation}
    (m k cutoff : ℕ) :
    (⋃ code : ExternalWordCode o,
        strictCappedCreationFiber m k cutoff cutoff code) =
      {omega | truncatedLevelTime m k cutoff omega < cutoff} := by
  classical
  ext omega
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨code, homega⟩
    exact truncatedLevelTime_lt_of_mem_strictCappedCreationFiber homega
  · intro hstrict
    let tau := truncatedLevelTime m k cutoff
    let w := prefixBlockWord (tau omega) omega
    obtain ⟨i, r, q, hq⟩ := exists_insertGapVector o w
    let tail : BoundaryTail :=
      ⟨prefixDirectionTail (tau omega) omega,
        unpairedDirectionTail_length_le_one (incrementPrefixList (tau omega) omega)⟩
    have hdelete : deleteRemovableBlocks o
        (prefixBlockWord (tau omega) omega) = retainedWord r := by
      change deleteRemovableBlocks o w = retainedWord r
      rw [← hq]
      exact deleteRemovableBlocks_insertGapVector r q
    have htail : prefixDirectionTail (tau omega) omega = tail.1 := rfl
    have hfixed : omega ∈ preStoppingFiberEvent tau r cutoff tail.1
        (fun _ ↦ True) := by
      exact mem_preStoppingFiberEvent_of_fixed_external
        (isFiniteStoppingTime_truncatedLevelTime m k cutoff)
        r tail.1 omega (Nat.le_of_lt hstrict) hdelete htail
    rcases Set.mem_iUnion.mp hfixed with ⟨qc, hqc⟩
    have hcoordinate : StrictlyBeforeClockCutoff r tail cutoff qc.1 := by
      unfold StrictlyBeforeClockCutoff
      rw [← hqc.1]
      exact hstrict
    let qs : AcceptedCappedCoordinates tau r cutoff tail.1
        (StrictlyBeforeClockCutoff r tail cutoff) :=
      ⟨qc.1, hcoordinate, qc.2.2⟩
    refine ⟨⟨i, r, tail⟩, ?_⟩
    apply Set.mem_iUnion.mpr
    exact ⟨qs, hqc⟩

/-- Exact finite mass transport on one sound variable-time fibre. -/
theorem fairSteps_strictCappedCreationFiber_eq_geometricSum
    {o : Orientation} (m k cutoff cap : ℕ) (code : ExternalWordCode o) :
    fairSteps (strictCappedCreationFiber m k cutoff cap code) =
      ENNReal.ofReal
        (prefixFiberConstant code.retainedCount code.tail.1 *
          ∑ q : AcceptedCappedCoordinates
              (truncatedLevelTime m k cutoff) code.retained cap code.tail.1
              (StrictlyBeforeClockCutoff code.retained code.tail cutoff),
            gapVectorMass (fun j ↦ (q.1 j : ℕ))) := by
  exact fairSteps_preStoppingFiberEvent_eq_geometricSum
    (isFiniteStoppingTime_truncatedLevelTime m k cutoff)
    code.retained cap code.tail.1
    (StrictlyBeforeClockCutoff code.retained code.tail cutoff)

/-! ## Removing the insertion-coordinate cap on a variable-time fibre -/

/-- The strict-clock predicate on genuine natural-valued insertion
coordinates. -/
def StrictlyBeforeClockCutoffNat {o : Orientation} {i : ℕ}
    (r : Fin i → RetainedBlock o) (tail : BoundaryTail)
    (cutoff : ℕ) (q : Fin (i + 1) → ℕ) : Prop :=
  insertionPrefixLength r q tail.1 < cutoff

/-- The full countable variable-time fibre above one external word. -/
def strictUnboundedCreationFiber {o : Orientation} (m k cutoff : ℕ)
    (code : ExternalWordCode o) : Set StepPath :=
  unboundedPreStoppingFiberEvent (truncatedLevelTime m k cutoff)
    code.retained code.tail.1
    (StrictlyBeforeClockCutoffNat code.retained code.tail cutoff)

theorem strictCappedCreationFiber_eq_coherent {o : Orientation}
    (m k cutoff cap : ℕ) (code : ExternalWordCode o) :
    strictCappedCreationFiber m k cutoff cap code =
      coherentCappedFiberEvent (truncatedLevelTime m k cutoff)
        code.retained cap code.tail.1
        (StrictlyBeforeClockCutoffNat code.retained code.tail cutoff) := by
  rfl

theorem monotone_strictCappedCreationFiber {o : Orientation}
    (m k cutoff : ℕ) (code : ExternalWordCode o) :
    Monotone fun cap ↦ strictCappedCreationFiber m k cutoff cap code := by
  simpa only [strictCappedCreationFiber_eq_coherent] using
    monotone_coherentCappedFiberEvent
      (truncatedLevelTime m k cutoff) code.retained code.tail.1
      (StrictlyBeforeClockCutoffNat code.retained code.tail cutoff)

theorem iUnion_strictCappedCreationFiber_cap {o : Orientation}
    (m k cutoff : ℕ) (code : ExternalWordCode o) :
    (⋃ cap, strictCappedCreationFiber m k cutoff cap code) =
      strictUnboundedCreationFiber m k cutoff code := by
  simpa only [strictCappedCreationFiber_eq_coherent,
    strictUnboundedCreationFiber] using
    iUnion_coherentCappedFiberEvent
      (truncatedLevelTime m k cutoff) code.retained code.tail.1
      (StrictlyBeforeClockCutoffNat code.retained code.tail cutoff)

theorem measurableSet_strictUnboundedCreationFiber {o : Orientation}
    (m k cutoff : ℕ) (code : ExternalWordCode o) :
    MeasurableSet (strictUnboundedCreationFiber m k cutoff code) := by
  exact measurableSet_unboundedPreStoppingFiberEvent
    (isFiniteStoppingTime_truncatedLevelTime m k cutoff)
    code.retained code.tail.1
    (StrictlyBeforeClockCutoffNat code.retained code.tail cutoff)

theorem tendsto_fairSteps_strictCappedCreationFiber {o : Orientation}
    (m k cutoff : ℕ) (code : ExternalWordCode o) :
    Tendsto
      (fun cap ↦ fairSteps (strictCappedCreationFiber m k cutoff cap code))
      Filter.atTop
      (nhds (fairSteps (strictUnboundedCreationFiber m k cutoff code))) := by
  simpa only [strictCappedCreationFiber_eq_coherent,
    strictUnboundedCreationFiber] using
    tendsto_fairSteps_coherentCappedFiberEvent
      (truncatedLevelTime m k cutoff) code.retained code.tail.1
      (StrictlyBeforeClockCutoffNat code.retained code.tail cutoff)

/-! ## The whole unbounded threshold-creation stage -/

/-- One external-word fibre over the genuine threshold-creation stage.  It
is written as a countable union of strict deterministic-clock
approximations, but the cutoff is not part of the fibre index. -/
def variableCreationFiber {o : Orientation} (m k : ℕ)
    (code : ExternalWordCode o) : Set StepPath :=
  ⋃ cutoff, strictUnboundedCreationFiber m k cutoff code

theorem measurableSet_variableCreationFiber {o : Orientation}
    (m k : ℕ) (code : ExternalWordCode o) :
    MeasurableSet (variableCreationFiber m k code) := by
  exact MeasurableSet.iUnion fun cutoff ↦
    measurableSet_strictUnboundedCreationFiber m k cutoff code

theorem truncatedLevelTime_lt_of_mem_strictUnboundedCreationFiber
    {o : Orientation} {m k cutoff : ℕ} {code : ExternalWordCode o}
    {omega : StepPath}
    (homega : omega ∈ strictUnboundedCreationFiber m k cutoff code) :
    truncatedLevelTime m k cutoff omega < cutoff := by
  rcases Set.mem_iUnion.mp homega with ⟨q, hq⟩
  rw [hq.1]
  exact q.2.1

theorem exists_cutoff_truncatedLevelTime_lt_iff_reaches
    (m k : ℕ) (omega : StepPath) :
    (∃ cutoff, truncatedLevelTime m k cutoff omega < cutoff) ↔
      ReachesThreshold (trajectory omega) m k := by
  classical
  constructor
  · rintro ⟨cutoff, hcutoff⟩
    by_contra hnot
    rw [truncatedLevelTime_eq_cutoff_of_not_reaches m k cutoff omega hnot]
      at hcutoff
    exact (Nat.lt_irrefl cutoff) hcutoff
  · intro hreach
    refine ⟨Nat.find hreach + 1, ?_⟩
    rw [truncatedLevelTime_eq_min_find m k (Nat.find hreach + 1) omega hreach]
    omega

/-- Distinct external-word fibres remain disjoint after both cap and clock
cutoffs are removed.  Uniqueness of the genuine threshold-creation time is
what permits the two cutoff representatives to be compared. -/
theorem disjoint_variableCreationFiber_of_ne {o : Orientation}
    (m k : ℕ) {c d : ExternalWordCode o} (hcd : c ≠ d) :
    Disjoint (variableCreationFiber m k c) (variableCreationFiber m k d) := by
  classical
  rw [Set.disjoint_left]
  intro omega hc hd
  rcases Set.mem_iUnion.mp hc with ⟨cutoff, hc⟩
  rcases Set.mem_iUnion.mp hd with ⟨cutoff', hd⟩
  rcases Set.mem_iUnion.mp hc with ⟨q, hq⟩
  rcases Set.mem_iUnion.mp hd with ⟨q', hq'⟩
  have hlt : truncatedLevelTime m k cutoff omega < cutoff := by
    rw [hq.1]
    exact q.2.1
  have hlt' : truncatedLevelTime m k cutoff' omega < cutoff' := by
    rw [hq'.1]
    exact q'.2.1
  have hcreation : ThresholdCreation (trajectory omega) m k
      (truncatedLevelTime m k cutoff omega) :=
    (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k cutoff (truncatedLevelTime m k cutoff omega) omega hlt).mp rfl
  have hcreation' : ThresholdCreation (trajectory omega) m k
      (truncatedLevelTime m k cutoff' omega) :=
    (truncatedLevelTime_eq_iff_thresholdCreation_of_lt_cutoff
      m k cutoff' (truncatedLevelTime m k cutoff' omega) omega hlt').mp rfl
  have htime : truncatedLevelTime m k cutoff omega =
      truncatedLevelTime m k cutoff' omega :=
    HLOZSpatialAdapter.thresholdCreation_time_unique hcreation hcreation'
  apply hcd
  apply externalWordCodeKey_injective
  have hword := (prefixBlockWord_eq_of_creationAtom m k cutoff
    c.retained q.1 c.tail hq).symm.trans <| htime ▸
      prefixBlockWord_eq_of_creationAtom m k cutoff'
        d.retained q'.1 d.tail hq'
  have hretained : retainedWord c.retained = retainedWord d.retained := by
    rw [← deleteRemovableBlocks_insertGapVector c.retained q.1, hword,
      deleteRemovableBlocks_insertGapVector d.retained]
  have hcount : c.retainedCount = d.retainedCount := by
    have := congrArg List.length hretained
    simpa [retainedWord] using this
  have htail := (prefixDirectionTail_eq_of_creationAtom m k cutoff
    c.retained q.1 c.tail hq).symm.trans <| htime ▸
      prefixDirectionTail_eq_of_creationAtom m k cutoff'
        d.retained q'.1 d.tail hq'
  exact Prod.ext hcount (Prod.ext hretained htail)

/-- The sound external-word fibres form a countable disjoint partition of
the whole threshold-reaching stage. -/
theorem iUnion_variableCreationFiber {o : Orientation} (m k : ℕ) :
    (⋃ code : ExternalWordCode o, variableCreationFiber m k code) =
      {omega | ReachesThreshold (trajectory omega) m k} := by
  classical
  ext omega
  simp only [variableCreationFiber, Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨code, cutoff, homega⟩
    exact (exists_cutoff_truncatedLevelTime_lt_iff_reaches m k omega).mp
      ⟨cutoff,
        truncatedLevelTime_lt_of_mem_strictUnboundedCreationFiber homega⟩
  · intro hreach
    obtain ⟨cutoff, hstrict⟩ :=
      (exists_cutoff_truncatedLevelTime_lt_iff_reaches m k omega).mpr hreach
    have hcovered : omega ∈ ⋃ code : ExternalWordCode o,
        strictCappedCreationFiber m k cutoff cutoff code := by
      rw [iUnion_strictCappedCreationFiber]
      exact hstrict
    rcases Set.mem_iUnion.mp hcovered with ⟨code, hcode⟩
    have hunbounded : omega ∈ strictUnboundedCreationFiber m k cutoff code := by
      rw [← iUnion_strictCappedCreationFiber_cap]
      exact Set.mem_iUnion.mpr ⟨cutoff, hcode⟩
    exact ⟨code, cutoff, hunbounded⟩

/-! ## Why fixed physical-time refinements are unsound -/

/-- Inside a fixed retained-word and boundary-tail fibre, equality of the
physical prefix length fixes the global sum of all insertion coordinates. -/
theorem gap_sum_eq_of_prefixLength_eq
    {o : Orientation} {i : ℕ} (r : Fin i → RetainedBlock o)
    (tail : List Direction) (q q' : Fin (i + 1) → ℕ)
    (h : insertionPrefixLength r q tail = insertionPrefixLength r q' tail) :
    ∑ j, q j = ∑ j, q' j := by
  simp only [insertionPrefixLength, insertionPrefixList_length] at h
  omega

/-- Consequently, two insertion atoms in the same external-word fibre and
the same fixed physical stopping-time atom lie on one global-sum slice. -/
theorem gap_sum_eq_on_fixed_stopping_time
    {tau : StepPath → ℕ} {o : Orientation} {i n : ℕ}
    (r : Fin i → RetainedBlock o) (tail : List Direction)
    (q q' : Fin (i + 1) → ℕ) {omega omega' : StepPath}
    (homega : omega ∈ stoppedInsertionAtom tau r q tail)
    (homega' : omega' ∈ stoppedInsertionAtom tau r q' tail)
    (htime : tau omega = n) (htime' : tau omega' = n) :
    ∑ j, q j = ∑ j, q' j := by
  apply gap_sum_eq_of_prefixLength_eq r tail q q'
  exact homega.1.symm.trans (htime.trans (htime'.symm.trans homega'.1))

end

end Erdos1165.VariableStoppedFiber
