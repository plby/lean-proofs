import ErdosProblems.Erdos1165.SpatialInsertionFiber

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165.ShiftedPrefixBridge

open LazyDecomposition PathInsertion StoppedInsertion SpatialInsertionFiber

/-- The maximal word of complete two-increment blocks in the prefix through `n`. -/
def completePrefixBlocks (ω : StepPath) (n : ℕ) : List Block :=
  List.ofFn fun j : Fin (n / 2) => (ω (2 * (j : ℕ)), ω (2 * (j : ℕ) + 1))

/-- Complete blocks before a random finite time. -/
def preStoppingBlocks (τ : StepPath → ℕ) (ω : StepPath) : List Block :=
  completePrefixBlocks ω (τ ω)

/-- The singleton position left after the maximal complete block prefix. -/
def prefixRemainder (ω : StepPath) (n : ℕ) : List Point :=
  if n % 2 = 0 then [] else [trajectory ω n]

/-- Complete two-increment blocks in the segment starting at ordinary time `a`. -/
def completeSegmentBlocks (ω : StepPath) (a n : ℕ) : List Block :=
  List.ofFn fun j : Fin (n / 2) =>
    (ω (a + 2 * (j : ℕ)), ω (a + 2 * (j : ℕ) + 1))

/-- Positions in the segment from ordinary time `a` through `a+n`. -/
def segmentPath (ω : StepPath) (a n : ℕ) : List Point :=
  List.ofFn fun j : Fin (n + 1) => trajectory ω (a + (j : ℕ))

def segmentRemainder (ω : StepPath) (a n : ℕ) : List Point :=
  if n % 2 = 0 then [] else [trajectory ω (a + n)]

theorem blockPathTail_append_singleton (x : Point) (as : List Block) (b : Block) :
    blockPathTail x (as ++ [b]) =
      blockPathTail x as ++
        [blockMiddle (followBlocks x as) b, blockEnd (followBlocks x as) b] := by
  induction as generalizing x with
  | nil => rfl
  | cons a as ih =>
      simp only [List.cons_append, blockPathTail]
      congr 2
      simpa [followBlocks] using ih (blockEnd x a)

theorem blockPath_append_singleton (x : Point) (as : List Block) (b : Block) :
    blockPath x (as ++ [b]) =
      blockPath x as ++
        [blockMiddle (followBlocks x as) b, blockEnd (followBlocks x as) b] := by
  simp only [blockPath, blockPathTail_append_singleton, List.cons_append]

theorem followBlocks_completePrefixBlocks (ω : StepPath) (q : ℕ) :
    followBlocks (0, 0) (completePrefixBlocks ω (2 * q)) = trajectory ω (2 * q) := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [show 2 * (q + 1) = 2 * q + 2 by omega]
      unfold completePrefixBlocks
      rw [show (2 * q + 2) / 2 = q + 1 by omega, List.ofFn_succ_last]
      rw [followBlocks_append]
      change blockEnd
        (followBlocks (0, 0)
          (List.ofFn fun j : Fin q => (ω (2 * (j : ℕ)), ω (2 * (j : ℕ) + 1))))
        (ω (2 * q), ω (2 * q + 1)) = _
      rw [← show completePrefixBlocks ω (2 * q) =
        List.ofFn (fun j : Fin q => (ω (2 * (j : ℕ)), ω (2 * (j : ℕ) + 1))) by
          simp [completePrefixBlocks]]
      rw [ih]
      simp only [blockEnd]
      rw [trajectory_succ, trajectory_succ]

theorem evenPrefixPath_eq_blockPath (ω : StepPath) (q : ℕ) :
    finitePathList (pathPrefix (trajectory ω) (2 * q)) =
      blockPath (0, 0) (completePrefixBlocks ω (2 * q)) := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [show 2 * (q + 1) = 2 * q + 2 by omega]
      unfold finitePathList pathPrefix
      rw [List.ofFn_succ_last, List.ofFn_succ_last]
      unfold completePrefixBlocks
      rw [show (2 * q + 2) / 2 = q + 1 by omega]
      conv_rhs => rw [List.ofFn_succ_last]
      rw [blockPath_append_singleton]
      simp only [Fin.val_castSucc, Fin.val_last]
      simp only [List.append_assoc, List.singleton_append]
      change
        (List.ofFn fun j : Fin (2 * q + 1) => trajectory ω j) ++
            [trajectory ω (2 * q + 1), trajectory ω (2 * q + 2)] =
          blockPath (0, 0)
              (List.ofFn fun j : Fin q => (ω (2 * (j : ℕ)), ω (2 * (j : ℕ) + 1))) ++
            [blockMiddle
                (followBlocks (0, 0)
                  (List.ofFn fun j : Fin q =>
                    (ω (2 * (j : ℕ)), ω (2 * (j : ℕ) + 1))))
                (ω (2 * q), ω (2 * q + 1)),
              blockEnd
                (followBlocks (0, 0)
                  (List.ofFn fun j : Fin q =>
                    (ω (2 * (j : ℕ)), ω (2 * (j : ℕ) + 1))))
                (ω (2 * q), ω (2 * q + 1))]
      rw [← show completePrefixBlocks ω (2 * q) =
        List.ofFn (fun j : Fin q => (ω (2 * (j : ℕ)), ω (2 * (j : ℕ) + 1))) by
          simp [completePrefixBlocks]]
      rw [← ih, followBlocks_completePrefixBlocks]
      simp only [blockMiddle, blockEnd]
      rw [trajectory_succ, trajectory_succ]
      change finitePathList (pathPrefix (trajectory ω) (2 * q)) ++ _ =
        finitePathList (pathPrefix (trajectory ω) (2 * q)) ++ _
      congr 2
      rw [trajectory_succ]

theorem oddPrefixPath_eq_blockPath_append (ω : StepPath) (q : ℕ) :
    finitePathList (pathPrefix (trajectory ω) (2 * q + 1)) =
      blockPath (0, 0) (completePrefixBlocks ω (2 * q + 1)) ++
        [trajectory ω (2 * q + 1)] := by
  have hblocks : completePrefixBlocks ω (2 * q + 1) =
      completePrefixBlocks ω (2 * q) := by
    unfold completePrefixBlocks
    rw [show (2 * q + 1) / 2 = q by omega, show (2 * q) / 2 = q by omega]
  rw [hblocks, ← evenPrefixPath_eq_blockPath]
  unfold finitePathList pathPrefix
  rw [List.ofFn_succ_last]
  rfl

theorem prefixPath_eq_blockPath_append_remainder (ω : StepPath) (n : ℕ) :
    finitePathList (pathPrefix (trajectory ω) n) =
      blockPath (0, 0) (completePrefixBlocks ω n) ++
        if n % 2 = 0 then [] else [trajectory ω n] := by
  rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
  · have hn : n = 2 * (n / 2) := by
      have := Nat.div_add_mod n 2
      omega
    simp only [hmod, if_pos, List.append_nil]
    rw [hn]
    exact evenPrefixPath_eq_blockPath ω (n / 2)
  · have hn : n = 2 * (n / 2) + 1 := by
      have := Nat.div_add_mod n 2
      omega
    simp only [hmod, one_ne_zero, if_false]
    rw [hn]
    exact oddPrefixPath_eq_blockPath_append ω (n / 2)

theorem followBlocks_completeSegmentBlocks (ω : StepPath) (a q : ℕ) :
    followBlocks (trajectory ω a) (completeSegmentBlocks ω a (2 * q)) =
      trajectory ω (a + 2 * q) := by
  induction q with
  | zero => rfl
  | succ q ih =>
      rw [show 2 * (q + 1) = 2 * q + 2 by omega]
      unfold completeSegmentBlocks
      rw [show (2 * q + 2) / 2 = q + 1 by omega, List.ofFn_succ_last]
      rw [followBlocks_append]
      change blockEnd
        (followBlocks (trajectory ω a)
          (List.ofFn fun j : Fin q =>
            (ω (a + 2 * (j : ℕ)), ω (a + 2 * (j : ℕ) + 1))))
        (ω (a + 2 * q), ω (a + 2 * q + 1)) = _
      rw [← show completeSegmentBlocks ω a (2 * q) =
        List.ofFn (fun j : Fin q =>
          (ω (a + 2 * (j : ℕ)), ω (a + 2 * (j : ℕ) + 1))) by
            simp [completeSegmentBlocks]]
      rw [ih]
      simp only [blockEnd]
      have htwo : trajectory ω (a + (2 * q + 2)) =
          trajectory ω (a + 2 * q) + directionVector (ω (a + 2 * q)) +
            directionVector (ω (a + 2 * q + 1)) := by
        rw [show a + (2 * q + 2) = (a + 2 * q + 1) + 1 by omega,
          trajectory_succ,
          show a + 2 * q + 1 = (a + 2 * q) + 1 by omega, trajectory_succ]
      exact htwo.symm

theorem evenSegmentPath_eq_blockPath (ω : StepPath) (a q : ℕ) :
    segmentPath ω a (2 * q) =
      blockPath (trajectory ω a) (completeSegmentBlocks ω a (2 * q)) := by
  induction q with
  | zero => simp [segmentPath, completeSegmentBlocks, blockPath, blockPathTail]
  | succ q ih =>
      rw [show 2 * (q + 1) = 2 * q + 2 by omega]
      unfold segmentPath
      rw [List.ofFn_succ_last, List.ofFn_succ_last]
      unfold completeSegmentBlocks
      rw [show (2 * q + 2) / 2 = q + 1 by omega]
      conv_rhs => rw [List.ofFn_succ_last]
      rw [blockPath_append_singleton]
      simp only [Fin.val_castSucc, Fin.val_last]
      simp only [List.append_assoc, List.singleton_append]
      change
        (List.ofFn fun j : Fin (2 * q + 1) => trajectory ω (a + (j : ℕ))) ++
            [trajectory ω (a + (2 * q + 1)), trajectory ω (a + (2 * q + 2))] =
          blockPath (trajectory ω a)
              (List.ofFn fun j : Fin q =>
                (ω (a + 2 * (j : ℕ)), ω (a + 2 * (j : ℕ) + 1))) ++
            [blockMiddle
                (followBlocks (trajectory ω a)
                  (List.ofFn fun j : Fin q =>
                    (ω (a + 2 * (j : ℕ)), ω (a + 2 * (j : ℕ) + 1))))
                (ω (a + 2 * q), ω (a + 2 * q + 1)),
              blockEnd
                (followBlocks (trajectory ω a)
                  (List.ofFn fun j : Fin q =>
                    (ω (a + 2 * (j : ℕ)), ω (a + 2 * (j : ℕ) + 1))))
                (ω (a + 2 * q), ω (a + 2 * q + 1))]
      rw [← show completeSegmentBlocks ω a (2 * q) =
        List.ofFn (fun j : Fin q =>
          (ω (a + 2 * (j : ℕ)), ω (a + 2 * (j : ℕ) + 1))) by
            simp [completeSegmentBlocks]]
      rw [← ih, followBlocks_completeSegmentBlocks]
      simp only [blockMiddle, blockEnd]
      have hone : trajectory ω (a + (2 * q + 1)) =
          trajectory ω (a + 2 * q) + directionVector (ω (a + 2 * q)) := by
        rw [show a + (2 * q + 1) = (a + 2 * q) + 1 by omega, trajectory_succ]
      have htwo : trajectory ω (a + (2 * q + 2)) =
          trajectory ω (a + 2 * q) + directionVector (ω (a + 2 * q)) +
            directionVector (ω (a + 2 * q + 1)) := by
        rw [show a + (2 * q + 2) = (a + 2 * q + 1) + 1 by omega,
          trajectory_succ,
          show a + 2 * q + 1 = (a + 2 * q) + 1 by omega, trajectory_succ]
      rw [hone, htwo]
      rfl

theorem oddSegmentPath_eq_blockPath_append (ω : StepPath) (a q : ℕ) :
    segmentPath ω a (2 * q + 1) =
      blockPath (trajectory ω a) (completeSegmentBlocks ω a (2 * q + 1)) ++
        [trajectory ω (a + (2 * q + 1))] := by
  have hblocks : completeSegmentBlocks ω a (2 * q + 1) =
      completeSegmentBlocks ω a (2 * q) := by
    unfold completeSegmentBlocks
    rw [show (2 * q + 1) / 2 = q by omega, show (2 * q) / 2 = q by omega]
  rw [hblocks, ← evenSegmentPath_eq_blockPath]
  unfold segmentPath
  rw [List.ofFn_succ_last]
  rfl

theorem segmentPath_eq_blockPath_append_remainder (ω : StepPath) (a n : ℕ) :
    segmentPath ω a n =
      blockPath (trajectory ω a) (completeSegmentBlocks ω a n) ++
        segmentRemainder ω a n := by
  rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
  · have hn : n = 2 * (n / 2) := by
      have := Nat.div_add_mod n 2
      omega
    simp only [segmentRemainder, hmod, if_pos, List.append_nil]
    rw [hn]
    exact evenSegmentPath_eq_blockPath ω a (n / 2)
  · have hn : n = 2 * (n / 2) + 1 := by
      have := Nat.div_add_mod n 2
      omega
    simp only [segmentRemainder, hmod, one_ne_zero, if_false]
    rw [hn]
    exact oddSegmentPath_eq_blockPath_append ω a (n / 2)

theorem compressTail_blockPathTail_append_singleton (o : Orientation) (x z : Point) :
    ∀ bs : List Block,
      compressTail o x (blockPathTail x bs ++ [z]) =
        (blockPath x (deleteRemovableBlocks o bs)).tail ++ [z] := by
  intro bs
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih =>
      by_cases hb : b = removableBlock o
      · have hrem : Removable o x (blockMiddle x b) (blockEnd x b) :=
          (removable_block_iff o x b).2 hb
        simp only [blockPathTail, List.cons_append, compressTail, if_pos hrem]
        rw [ih]
        subst b
        simp [deleteRemovableBlocks, blockPath]
      · have hrem : ¬Removable o x (blockMiddle x b) (blockEnd x b) :=
          (removable_block_iff o x b).not.mpr hb
        simp only [blockPathTail, List.cons_append, compressTail, if_neg hrem]
        rw [ih]
        simp [deleteRemovableBlocks, hb, blockPath, blockPathTail]

theorem externalPath_blockPath_append_singleton (o : Orientation) (x z : Point)
    (bs : List Block) :
    externalPath o (blockPath x bs ++ [z]) =
      blockPath x (deleteRemovableBlocks o bs) ++ [z] := by
  simp only [blockPath, List.cons_append, externalPath]
  rw [compressTail_blockPathTail_append_singleton]
  simp [blockPath]

theorem removedTail_blockPathTail_append_singleton (o : Orientation) (x z : Point) :
    ∀ bs : List Block,
      removedTail o x (blockPathTail x bs ++ [z]) =
        removedTail o x (blockPathTail x bs) := by
  intro bs
  induction bs generalizing x with
  | nil => rfl
  | cons b bs ih =>
      by_cases hb : b = removableBlock o
      · have hrem : Removable o x (blockMiddle x b) (blockEnd x b) :=
          (removable_block_iff o x b).2 hb
        simp only [blockPathTail, List.cons_append, removedTail, if_pos hrem,
          List.cons.injEq, true_and]
        exact ih (blockEnd x b)
      · have hrem : ¬Removable o x (blockMiddle x b) (blockEnd x b) :=
          (removable_block_iff o x b).not.mpr hb
        simp only [blockPathTail, List.cons_append, removedTail, if_neg hrem]
        exact ih (blockEnd x b)

theorem lazyPoints_blockPath_append_singleton (o : Orientation) (x z : Point)
    (bs : List Block) :
    lazyPoints o (blockPath x bs ++ [z]) = lazyPoints o (blockPath x bs) := by
  simp only [blockPath, List.cons_append, lazyPoints]
  exact removedTail_blockPathTail_append_singleton o x z bs

theorem fixedFiber_prefixPath {o : Orientation} {i : ℕ} (ω : StepPath) (n : ℕ)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (hword : completePrefixBlocks ω n = insertGapVector r q) :
    finitePathList (pathPrefix (trajectory ω) n) =
      insertedPath (0, 0) r q ++ prefixRemainder ω n := by
  rw [prefixPath_eq_blockPath_append_remainder, hword]
  rfl

theorem fixedFiber_externalTrace {o : Orientation} {i : ℕ} (ω : StepPath) (n : ℕ)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (hword : completePrefixBlocks ω n = insertGapVector r q) :
    externalTraceAt o ω n =
      blockPath (0, 0) (retainedWord r) ++ prefixRemainder ω n := by
  unfold externalTraceAt finiteExternalPath
  change externalPath o (finitePathList (pathPrefix (trajectory ω) n)) = _
  rw [fixedFiber_prefixPath ω n r q hword]
  unfold prefixRemainder insertedPath
  by_cases hmod : n % 2 = 0
  · simp only [hmod, if_true, List.append_nil]
    exact externalPath_insertedPath (0, 0) r q
  · simp only [hmod, if_false]
    rw [externalPath_blockPath_append_singleton,
      deleteRemovableBlocks_insertGapVector]

theorem fixedFiber_deletedTrace {o : Orientation} {i : ℕ} (ω : StepPath) (n : ℕ)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (hword : completePrefixBlocks ω n = insertGapVector r q) :
    deletedTraceAt o ω n = lazyPoints o (insertedPath (0, 0) r q) := by
  unfold deletedTraceAt finiteLazyPoints
  change lazyPoints o (finitePathList (pathPrefix (trajectory ω) n)) = _
  rw [fixedFiber_prefixPath ω n r q hword]
  unfold prefixRemainder
  by_cases hmod : n % 2 = 0
  · simp [hmod]
  · simp only [hmod, if_false]
    exact lazyPoints_blockPath_append_singleton o (0, 0) (trajectory ω n)
      (insertGapVector r q)

theorem fixedFiber_time_eq {o : Orientation} {i : ℕ} (ω : StepPath) (n : ℕ)
    (r : Fin i → RetainedBlock o) (q : Fin (i + 1) → ℕ)
    (hword : completePrefixBlocks ω n = insertGapVector r q) :
    n = 2 * (i + ∑ j, q j) + n % 2 := by
  have hlen := congrArg List.length hword
  rw [completePrefixBlocks, List.length_ofFn, insertGapVector_length] at hlen
  have hdiv := Nat.div_add_mod n 2
  omega

/-- Exact random-prefix identification on one capped fixed external fibre. -/
theorem truncatedLevelTime_fixedCappedFiber
    (o : Orientation) (m k cutoff cap : ℕ) (ω : StepPath) {i : ℕ}
    (r : Fin i → RetainedBlock o) (q : CappedCoordinates i cap)
    (hword : completePrefixBlocks ω (truncatedLevelTime m k cutoff ω) =
      insertGapVector r (fun j => (q j : ℕ))) :
    let τ := truncatedLevelTime m k cutoff ω
    finitePathList (pathPrefix (trajectory ω) τ) =
        insertedPath (0, 0) r (fun j => (q j : ℕ)) ++ prefixRemainder ω τ ∧
      externalTraceAt o ω τ =
        blockPath (0, 0) (retainedWord r) ++ prefixRemainder ω τ ∧
      deletedTraceAt o ω τ =
        lazyPoints o (insertedPath (0, 0) r (fun j => (q j : ℕ))) ∧
      τ = 2 * (i + ∑ j, (q j : ℕ)) + τ % 2 := by
  dsimp only
  exact ⟨fixedFiber_prefixPath _ _ _ _ hword,
    fixedFiber_externalTrace _ _ _ _ hword,
    fixedFiber_deletedTrace _ _ _ _ hword,
    fixedFiber_time_eq _ _ _ _ hword⟩

/-! ## The genuine shifted HLOZ prefix (drop time zero) -/

def shiftedCompletePrefixBlocks (ω : StepPath) (n : ℕ) : List Block :=
  completeSegmentBlocks ω 1 (n - 1)

def shiftedPrefixRemainder (ω : StepPath) (n : ℕ) : List Point :=
  segmentRemainder ω 1 (n - 1)

theorem shiftedInput_eq_segmentPath (ω : StepPath) (n : ℕ) (hn : 0 < n) :
    shiftedInput (pathPrefix (trajectory ω) n) = segmentPath ω 1 (n - 1) := by
  cases n with
  | zero => omega
  | succ n =>
      simp [shiftedInput, finitePathList, pathPrefix, segmentPath, List.ofFn_succ]
      congr 1
      funext j
      congr 1
      omega

theorem shifted_fixedFiber_input {i : ℕ} (ω : StepPath) (n : ℕ) (hn : 0 < n)
    (r : Fin i → RetainedBlock .shifted) (q : Fin (i + 1) → ℕ)
    (hword : shiftedCompletePrefixBlocks ω n = insertGapVector r q) :
    shiftedInput (pathPrefix (trajectory ω) n) =
      insertedPath (trajectory ω 1) r q ++ shiftedPrefixRemainder ω n := by
  rw [shiftedInput_eq_segmentPath ω n hn,
    segmentPath_eq_blockPath_append_remainder]
  rw [show completeSegmentBlocks ω 1 (n - 1) = insertGapVector r q from hword]
  rfl

theorem shifted_fixedFiber_externalTrace {i : ℕ} (ω : StepPath) (n : ℕ) (hn : 0 < n)
    (r : Fin i → RetainedBlock .shifted) (q : Fin (i + 1) → ℕ)
    (hword : shiftedCompletePrefixBlocks ω n = insertGapVector r q) :
    shiftedExternalPath (pathPrefix (trajectory ω) n) =
      blockPath (trajectory ω 1) (retainedWord r) ++ shiftedPrefixRemainder ω n := by
  unfold shiftedExternalPath
  rw [shifted_fixedFiber_input ω n hn r q hword]
  unfold shiftedPrefixRemainder segmentRemainder insertedPath
  by_cases hmod : (n - 1) % 2 = 0
  · simp only [hmod, if_true, List.append_nil]
    exact externalPath_insertedPath (trajectory ω 1) r q
  · simp only [hmod, if_false]
    rw [externalPath_blockPath_append_singleton,
      deleteRemovableBlocks_insertGapVector]

theorem shifted_fixedFiber_lazyTrace {i : ℕ} (ω : StepPath) (n : ℕ) (hn : 0 < n)
    (r : Fin i → RetainedBlock .shifted) (q : Fin (i + 1) → ℕ)
    (hword : shiftedCompletePrefixBlocks ω n = insertGapVector r q) :
    shiftedLazyPoints (pathPrefix (trajectory ω) n) =
      lazyPoints .shifted (insertedPath (trajectory ω 1) r q) := by
  unfold shiftedLazyPoints
  rw [shifted_fixedFiber_input ω n hn r q hword]
  unfold shiftedPrefixRemainder segmentRemainder
  by_cases hmod : (n - 1) % 2 = 0
  · simp [hmod]
  · simp only [hmod, if_false]
    exact lazyPoints_blockPath_append_singleton .shifted (trajectory ω 1)
      (trajectory ω (1 + (n - 1))) (insertGapVector r q)

theorem shifted_fixedFiber_fullPrefix {i : ℕ} (ω : StepPath) (n : ℕ) (hn : 0 < n)
    (r : Fin i → RetainedBlock .shifted) (q : Fin (i + 1) → ℕ)
    (hword : shiftedCompletePrefixBlocks ω n = insertGapVector r q) :
    finitePathList (pathPrefix (trajectory ω) n) =
      [(0, 0)] ++ insertedPath (trajectory ω 1) r q ++ shiftedPrefixRemainder ω n := by
  rw [finitePathList_cons_tail, shifted_fixedFiber_input ω n hn r q hword]
  change trajectory ω 0 :: _ = (0, 0) :: _
  simp

/-- External local time with both shifted boundary corrections frozen:
the time-zero atom and the optional final singleton. -/
def fixedShiftedPrefixLocalTime {i : ℕ} (ω : StepPath) (n : ℕ)
    (r : Fin i → RetainedBlock .shifted) (y : Point) : ℕ :=
  (if (0, 0) = y then 1 else 0) +
    listLocalTime
      (blockPath (trajectory ω 1) (retainedWord r) ++ shiftedPrefixRemainder ω n) y

theorem shifted_fixedFiber_localTime {i : ℕ} (ω : StepPath) (n : ℕ) (hn : 0 < n)
    (r : Fin i → RetainedBlock .shifted) (q : Fin (i + 1) → ℕ)
    (hword : shiftedCompletePrefixBlocks ω n = insertGapVector r q) (y : Point) :
    listLocalTime (finitePathList (pathPrefix (trajectory ω) n)) y =
      fixedShiftedPrefixLocalTime ω n r y +
        insertionLazyLocalTime (trajectory ω 1) r q y := by
  rw [finitePathList_cons_tail]
  unfold listLocalTime
  rw [List.count_cons]
  simp only [beq_iff_eq]
  change listLocalTime (shiftedInput (pathPrefix (trajectory ω) n)) y +
    (if trajectory ω 0 = y then 1 else 0) = _
  rw [listLocalTime_split .shifted
    (shiftedInput (pathPrefix (trajectory ω) n)) y]
  rw [show externalPath .shifted (shiftedInput (pathPrefix (trajectory ω) n)) =
      blockPath (trajectory ω 1) (retainedWord r) ++ shiftedPrefixRemainder ω n from
        shifted_fixedFiber_externalTrace ω n hn r q hword,
    show lazyPoints .shifted (shiftedInput (pathPrefix (trajectory ω) n)) =
      lazyPoints .shifted (insertedPath (trajectory ω 1) r q) from
        shifted_fixedFiber_lazyTrace ω n hn r q hword]
  rw [lazyLocalTime_insertedPath]
  unfold fixedShiftedPrefixLocalTime
  simp only [pathPrefix, trajectory_zero, beq_iff_eq]
  omega

theorem shifted_start_compatible (ω : StepPath) :
    OrientationCompatible .shifted (trajectory ω 1) := by
  change OddPoint (trajectory ω 1)
  simpa using trajectory_odd_time ω 0

theorem shifted_fixedFiber_localTime_at_base {i : ℕ} (ω : StepPath) (n : ℕ)
    (hn : 0 < n) (r : Fin i → RetainedBlock .shifted) (q : Fin (i + 1) → ℕ)
    (hword : shiftedCompletePrefixBlocks ω n = insertGapVector r q)
    (b : ExternalDomino (trajectory ω 1) r) :
    listLocalTime (finitePathList (pathPrefix (trajectory ω) n)) b.1 =
      fixedShiftedPrefixLocalTime ω n r b.1 +
        dominoLazyTotal (trajectory ω 1) r q b := by
  rw [shifted_fixedFiber_localTime ω n hn r q hword]
  rw [insertionLazyLocalTime_at_base (trajectory ω 1) r q
    (baseMiddleDisjoint_of_compatible (trajectory ω 1) r (shifted_start_compatible ω)) b]

theorem shifted_fixedFiber_localTime_at_middle {i : ℕ} (ω : StepPath) (n : ℕ)
    (hn : 0 < n) (r : Fin i → RetainedBlock .shifted) (q : Fin (i + 1) → ℕ)
    (hword : shiftedCompletePrefixBlocks ω n = insertGapVector r q)
    (b : ExternalDomino (trajectory ω 1) r) :
    listLocalTime (finitePathList (pathPrefix (trajectory ω) n))
        (excursionMiddle .shifted b.1) =
      fixedShiftedPrefixLocalTime ω n r (excursionMiddle .shifted b.1) +
        dominoLazyTotal (trajectory ω 1) r q b := by
  rw [shifted_fixedFiber_localTime ω n hn r q hword]
  rw [insertionLazyLocalTime_at_middle (trajectory ω 1) r q
    (baseMiddleDisjoint_of_compatible (trajectory ω 1) r (shifted_start_compatible ω)) b]

theorem shifted_fixedFiber_time_eq {i : ℕ} (ω : StepPath) (n : ℕ) (hn : 0 < n)
    (r : Fin i → RetainedBlock .shifted) (q : Fin (i + 1) → ℕ)
    (hword : shiftedCompletePrefixBlocks ω n = insertGapVector r q) :
    n = 1 + 2 * (i + ∑ j, q j) + (n - 1) % 2 := by
  have hlen := congrArg List.length hword
  rw [shiftedCompletePrefixBlocks, completeSegmentBlocks, List.length_ofFn,
    insertGapVector_length] at hlen
  have hdiv := Nat.div_add_mod (n - 1) 2
  omega

/-- Exact capped random pre-stopping fibre identification for the shifted
decomposition. The positivity hypothesis isolates the genuine shifted input;
at `τ = 0`, that input is empty and has no spatial insertion base. -/
theorem truncatedLevelTime_shifted_fixedCappedFiber
    (m k cutoff cap : ℕ) (ω : StepPath) {i : ℕ}
    (r : Fin i → RetainedBlock .shifted) (q : CappedCoordinates i cap)
    (hτ : 0 < truncatedLevelTime m k cutoff ω)
    (hword : shiftedCompletePrefixBlocks ω (truncatedLevelTime m k cutoff ω) =
      insertGapVector r (fun j => (q j : ℕ))) :
    let τ := truncatedLevelTime m k cutoff ω
    shiftedInput (pathPrefix (trajectory ω) τ) =
        insertedPath (trajectory ω 1) r (fun j => (q j : ℕ)) ++
          shiftedPrefixRemainder ω τ ∧
      shiftedExternalPath (pathPrefix (trajectory ω) τ) =
        blockPath (trajectory ω 1) (retainedWord r) ++ shiftedPrefixRemainder ω τ ∧
      shiftedLazyPoints (pathPrefix (trajectory ω) τ) =
        lazyPoints .shifted
          (insertedPath (trajectory ω 1) r (fun j => (q j : ℕ))) ∧
      τ = 1 + 2 * (i + ∑ j, (q j : ℕ)) + (τ - 1) % 2 := by
  dsimp only
  exact ⟨shifted_fixedFiber_input _ _ hτ _ _ hword,
    shifted_fixedFiber_externalTrace _ _ hτ _ _ hword,
    shifted_fixedFiber_lazyTrace _ _ hτ _ _ hword,
    shifted_fixedFiber_time_eq _ _ hτ _ _ hword⟩

/-- Fixed-tail form: the optional incomplete final block is itself part of the
frozen external datum, so the external trace on the right is literally fixed. -/
theorem truncatedLevelTime_shifted_fixedCappedFiber_fixedTail
    (m k cutoff cap : ℕ) (ω : StepPath) {i : ℕ}
    (r : Fin i → RetainedBlock .shifted) (q : CappedCoordinates i cap)
    (tail : List Point)
    (hτ : 0 < truncatedLevelTime m k cutoff ω)
    (hword : shiftedCompletePrefixBlocks ω (truncatedLevelTime m k cutoff ω) =
      insertGapVector r (fun j => (q j : ℕ)))
    (htail : shiftedPrefixRemainder ω (truncatedLevelTime m k cutoff ω) = tail) :
    let τ := truncatedLevelTime m k cutoff ω
    shiftedInput (pathPrefix (trajectory ω) τ) =
        insertedPath (trajectory ω 1) r (fun j => (q j : ℕ)) ++ tail ∧
      shiftedExternalPath (pathPrefix (trajectory ω) τ) =
        blockPath (trajectory ω 1) (retainedWord r) ++ tail ∧
      shiftedLazyPoints (pathPrefix (trajectory ω) τ) =
        lazyPoints .shifted
          (insertedPath (trajectory ω 1) r (fun j => (q j : ℕ))) ∧
      τ = 1 + 2 * (i + ∑ j, (q j : ℕ)) + (τ - 1) % 2 := by
  simpa only [htail] using
    truncatedLevelTime_shifted_fixedCappedFiber m k cutoff cap ω r q hτ hword

end Erdos1165.ShiftedPrefixBridge
