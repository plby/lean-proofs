import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedMapLaw
import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedMixedReconstruction

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace Erdos1166.HLOZPrimedOddMixedReconstruction

open HLOZDecomposition HLOZReconstruction HLOZActualStopped
  HLOZPrimedStopped HLOZIncompleteStoppedBlocks HLOZMixedCreationBlocks
  HLOZStoppedSourcePartition HLOZStoppedMixedReconstruction
  HLOZStoppedMapLaw HLOZProp48Truncated

def primedPairBase (a : Site) : Site := a - paperE1

def primedInitialStart (first : Direction) : Site := directionStep first

def primedInitialBase (first : Direction) : Site :=
  primedPairBase (primedInitialStart first)

theorem primedPairBase_pairEndpoint (a : Site) (p : IncrementPair) :
    primedPairBase (pairEndpoint a p) =
      pairEndpoint (primedPairBase a) p := by
  unfold primedPairBase pairEndpoint
  abel

theorem primedInitialBase_chessEven (first : Direction) :
    HLOZPairing.chessEven (primedInitialBase first) := by
  have hzero : HLOZPairing.chessEven (0, 0) := by
    norm_num [HLOZPairing.chessEven]
  have hstart : ¬ HLOZPairing.chessEven (primedInitialStart first) := by
    have h := chessEven_add_directionStep_iff (0, 0) first
    have h' : HLOZPairing.chessEven (primedInitialStart first) ↔
        ¬ HLOZPairing.chessEven (0, 0) := by
      have hadd : (0, 0) + directionStep first = primedInitialStart first := by
        ext <;> simp [primedInitialStart]
      rw [hadd] at h
      exact h
    exact fun hs ↦ (h'.mp hs) hzero
  have hbase := (chessEven_add_directionStep_iff
    (primedInitialStart first) (1 : Direction)).mpr hstart
  simpa [primedInitialBase, primedPairBase, sub_eq_add_neg,
    directionStep, paperE1] using hbase

def expandPrimedPairRuns : List PairRun → List IncrementPair
  | [] => []
  | (t, p) :: runs =>
      List.replicate t primedDistinguishedIncrementPair ++
        p :: expandPrimedPairRuns runs

theorem completedRunsFromVector_reverse {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ) :
    completedRunsFromVector (fun i ↦ reverseIncrementPair (labels i)) v =
      (completedRunsFromVector labels v).map
        (fun run ↦ (run.1, reverseIncrementPair run.2)) := by
  unfold completedRunsFromVector
  rw [List.map_ofFn]
  congr 1

theorem map_reverse_expandPairRuns (runs : List PairRun) :
    (expandPairRuns
        (runs.map fun run ↦ (run.1, reverseIncrementPair run.2))).map
        reverseIncrementPair =
      expandPrimedPairRuns runs := by
  induction runs with
  | nil => rfl
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      simp only [List.map_cons, expandPairRuns, expandPrimedPairRuns,
        List.map_append, List.map_replicate,
        reverseIncrementPair_distinguished,
        reverseIncrementPair_reverseIncrementPair, ih]

theorem primedStoppedPairList_eq_direct {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ) :
    primedStoppedPairList labels v =
      expandPrimedPairRuns (completedRunsFromVector labels v) ++
        List.replicate (v (Fin.last q)) primedDistinguishedIncrementPair := by
  unfold primedStoppedPairList stoppedPairList
  rw [List.map_append, List.map_replicate,
    reverseIncrementPair_distinguished]
  rw [completedRunsFromVector_reverse]
  rw [map_reverse_expandPairRuns]

def prependPrimedLazyLoops (a : Site) : ℕ → List Site → List Site
  | 0, tail => tail
  | t + 1, tail =>
      primedPairBase a :: a :: prependPrimedLazyLoops a t tail

@[simp] theorem pairEndpoint_primedDistinguished (a : Site) :
    pairEndpoint a primedDistinguishedIncrementPair = a := by
  ext <;> simp [pairEndpoint, primedDistinguishedIncrementPair,
    reverseIncrementPair, distinguishedIncrementPair, directionStep]

theorem add_primedDistinguished_zero (a : Site) :
    a + directionStep (primedDistinguishedIncrementPair 0) =
      primedPairBase a := by
  ext
  · simp [primedPairBase, primedDistinguishedIncrementPair,
      reverseIncrementPair, distinguishedIncrementPair, directionStep,
      paperE1, sub_eq_add_neg]
  · simp [primedPairBase, primedDistinguishedIncrementPair,
      reverseIncrementPair, distinguishedIncrementPair, directionStep,
      paperE1]

theorem reconstructPairTail_replicate_primedDistinguished
    (a : Site) (t : ℕ) (pairs : List IncrementPair) :
    reconstructPairTail a
        (List.replicate t primedDistinguishedIncrementPair ++ pairs) =
      prependPrimedLazyLoops a t (reconstructPairTail a pairs) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [List.replicate_succ, List.cons_append,
        reconstructPairTail, prependPrimedLazyLoops]
      rw [pairEndpoint_primedDistinguished, ih,
        add_primedDistinguished_zero]

def reconstructPrimedRunTail : Site → List PairRun → List Site
  | _, [] => []
  | a, (t, p) :: runs =>
      prependPrimedLazyLoops a t
        ((a + directionStep (p 0)) :: pairEndpoint a p ::
          reconstructPrimedRunTail (pairEndpoint a p) runs)

theorem reconstructPairTail_expandPrimedPairRuns
    (a : Site) (runs : List PairRun) :
    reconstructPairTail a (expandPrimedPairRuns runs) =
      reconstructPrimedRunTail a runs := by
  induction runs generalizing a with
  | nil => rfl
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      simp only [expandPrimedPairRuns, reconstructPrimedRunTail]
      rw [reconstructPairTail_replicate_primedDistinguished]
      simp only [reconstructPairTail]
      rw [ih]

def primedRunFinalStart : Site → List PairRun → Site
  | a, [] => a
  | a, (_, p) :: runs => primedRunFinalStart (pairEndpoint a p) runs

theorem prependPrimedLazyLoops_append
    (a : Site) (t : ℕ) (xs ys : List Site) :
    prependPrimedLazyLoops a t (xs ++ ys) =
      prependPrimedLazyLoops a t xs ++ ys := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [prependPrimedLazyLoops, List.cons_append,
        List.cons.injEq, true_and]
      exact ih

theorem reconstructPairTail_primedIncomplete
    (a : Site) (runs : List PairRun) (t : ℕ) :
    reconstructPairTail a
        (expandPrimedPairRuns runs ++
          List.replicate t primedDistinguishedIncrementPair) =
      reconstructPrimedRunTail a runs ++
        prependPrimedLazyLoops (primedRunFinalStart a runs) t [] := by
  induction runs generalizing a with
  | nil =>
      simpa [expandPrimedPairRuns, reconstructPrimedRunTail,
        primedRunFinalStart, reconstructPairTail] using
        reconstructPairTail_replicate_primedDistinguished a t []
  | cons run runs ih =>
      rcases run with ⟨u, p⟩
      simp only [expandPrimedPairRuns, List.append_assoc]
      rw [reconstructPairTail_replicate_primedDistinguished]
      simp only [reconstructPrimedRunTail, primedRunFinalStart]
      change prependPrimedLazyLoops a u
          ((a + directionStep (p 0)) :: pairEndpoint a p ::
            reconstructPairTail (pairEndpoint a p)
              (expandPrimedPairRuns runs ++
                List.replicate t primedDistinguishedIncrementPair)) = _
      rw [ih (pairEndpoint a p)]
      simpa only [List.cons_append] using
        prependPrimedLazyLoops_append a u
          ((a + directionStep (p 0)) :: pairEndpoint a p ::
            reconstructPrimedRunTail (pairEndpoint a p) runs)
          (prependPrimedLazyLoops
            (primedRunFinalStart (pairEndpoint a p) runs) t [])

def primedLazyVisitCount : Site → List PairRun → Site → ℕ
  | _, [], _ => 0
  | a, (t, p) :: runs, x =>
      (if x = primedPairBase a then t else 0) +
        (if x = a then t else 0) +
          primedLazyVisitCount (pairEndpoint a p) runs x

def primedLazyBlockSum : Site → List PairRun → Site → ℕ
  | _, [], _ => 0
  | a, (t, p) :: runs, x =>
      (if primedPairBase a = x then t else 0) +
        primedLazyBlockSum (pairEndpoint a p) runs x

def primedIncompleteLazyVisitCount
    (a : Site) (runs : List PairRun) (t : ℕ) (x : Site) : ℕ :=
  primedLazyVisitCount a runs x +
    (if x = primedPairBase (primedRunFinalStart a runs) then t else 0) +
    (if x = primedRunFinalStart a runs then t else 0)

def primedIncompleteLazyBlockSum
    (a : Site) (runs : List PairRun) (t : ℕ) (x : Site) : ℕ :=
  primedLazyBlockSum a runs x +
    if primedPairBase (primedRunFinalStart a runs) = x then t else 0

theorem primedPairBase_add_paperE1 (a : Site) :
    primedPairBase a + paperE1 = a := by
  unfold primedPairBase
  abel

theorem count_prependPrimedLazyLoops
    (x a : Site) (t : ℕ) (tail : List Site) :
    List.count x (prependPrimedLazyLoops a t tail) =
      (if x = primedPairBase a then t else 0) +
        (if x = a then t else 0) + List.count x tail := by
  induction t with
  | zero => simp [prependPrimedLazyLoops]
  | succ t ih =>
      rw [prependPrimedLazyLoops, List.count_cons, List.count_cons, ih]
      simp only [beq_iff_eq]
      have hne : primedPairBase a ≠ a := by
        intro h
        have := congrArg (fun z ↦ z + paperE1) h
        rw [primedPairBase_add_paperE1] at this
        exact add_paperE1_ne_self a this.symm
      by_cases hxb : x = primedPairBase a
      · simp [hxb, hne, hne.symm]
        omega
      · by_cases hxa : x = a
        · simp [hxa, hne, hne.symm]
          omega
        · have hbx : primedPairBase a ≠ x := fun h ↦ hxb h.symm
          have hax : a ≠ x := fun h ↦ hxa h.symm
          simp [hxb, hxa, hbx, hax]

theorem count_reconstructPrimedRunTail
    (a : Site) (runs : List PairRun) (x : Site) :
    List.count x (reconstructPrimedRunTail a runs) =
      List.count x (reconstructExternalTail a (terminalLabels runs)) +
        primedLazyVisitCount a runs x := by
  induction runs generalizing a with
  | nil => rfl
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      simp only [reconstructPrimedRunTail, terminalLabels, List.map_cons,
        reconstructExternalTail, primedLazyVisitCount]
      rw [count_prependPrimedLazyLoops]
      simp only [List.count_cons]
      rw [show List.map Prod.snd runs = terminalLabels runs by rfl]
      rw [ih]
      omega

theorem count_primedIncomplete_reconstruction
    (a : Site) (runs : List PairRun) (t : ℕ) (x : Site) :
    List.count x
        (reconstructFromDirections a
          (flattenPairs (expandPrimedPairRuns runs ++
            List.replicate t primedDistinguishedIncrementPair))) =
      List.count x (a :: reconstructExternalTail a (terminalLabels runs)) +
        primedIncompleteLazyVisitCount a runs t x := by
  unfold reconstructFromDirections
  rw [reconstructTail_flattenPairs, reconstructPairTail_primedIncomplete]
  change List.count x
      ((a :: reconstructPrimedRunTail a runs) ++
        prependPrimedLazyLoops (primedRunFinalStart a runs) t []) = _
  rw [List.count_append, count_prependPrimedLazyLoops]
  simp only [List.count_nil, add_zero, List.count_cons,
    count_reconstructPrimedRunTail]
  unfold primedIncompleteLazyVisitCount
  omega

theorem primedRunFinalBase_chessEven
    (a : Site) (runs : List PairRun)
    (ha : HLOZPairing.chessEven (primedPairBase a)) :
    HLOZPairing.chessEven
      (primedPairBase (primedRunFinalStart a runs)) := by
  induction runs generalizing a with
  | nil => exact ha
  | cons run runs ih =>
      exact ih (pairEndpoint a run.2)
        ((chessEven_pairEndpoint_iff (primedPairBase a) run.2).mpr ha |>
          (primedPairBase_pairEndpoint a run.2 ▸ ·))

theorem primedIncompleteLazyVisitCount_eq_blockSum_base
    (a : Site) (runs : List PairRun) (t : ℕ) (x : Site)
    (ha : HLOZPairing.chessEven (primedPairBase a))
    (hx : HLOZPairing.chessEven x) :
    primedIncompleteLazyVisitCount a runs t x =
      primedIncompleteLazyBlockSum a runs t x := by
  have hfinal := primedRunFinalBase_chessEven a runs ha
  have hodd : ¬ HLOZPairing.chessEven (primedRunFinalStart a runs) := by
    rw [← primedPairBase_add_paperE1 (primedRunFinalStart a runs)]
    exact not_chessEven_add_paperE1 hfinal
  have hne : x ≠ primedRunFinalStart a runs := by
    intro h
    exact hodd (h ▸ hx)
  have hmain : primedLazyVisitCount a runs x =
      primedLazyBlockSum a runs x := by
    induction runs generalizing a with
    | nil => rfl
    | cons run runs ih =>
        rcases run with ⟨u, p⟩
        have haOdd : ¬ HLOZPairing.chessEven a := by
          rw [← primedPairBase_add_paperE1 a]
          exact not_chessEven_add_paperE1 ha
        have hxa : x ≠ a := fun h ↦ haOdd (h ▸ hx)
        have hnext : HLOZPairing.chessEven
            (primedPairBase (pairEndpoint a p)) := by
          rw [primedPairBase_pairEndpoint]
          exact (chessEven_pairEndpoint_iff (primedPairBase a) p).mpr ha
        simp only [primedLazyVisitCount, primedLazyBlockSum, if_neg hxa]
        rw [ih (pairEndpoint a p) hnext hfinal hodd hne]
        simp [eq_comm]
  rw [primedIncompleteLazyVisitCount, primedIncompleteLazyBlockSum,
    hmain, if_neg hne]
  by_cases h : primedPairBase (primedRunFinalStart a runs) = x
  · rw [if_pos h, if_pos h.symm]
    omega
  · rw [if_neg h, if_neg (fun h' ↦ h h'.symm)]

theorem primedIncompleteLazyVisitCount_eq_blockSum_partner
    (a : Site) (runs : List PairRun) (t : ℕ) (x : Site)
    (ha : HLOZPairing.chessEven (primedPairBase a))
    (hx : HLOZPairing.chessEven x) :
    primedIncompleteLazyVisitCount a runs t (x + paperE1) =
      primedIncompleteLazyBlockSum a runs t x := by
  have hmain : primedLazyVisitCount a runs (x + paperE1) =
      primedLazyBlockSum a runs x := by
    induction runs generalizing a with
    | nil => rfl
    | cons run runs ih =>
        rcases run with ⟨u, p⟩
        have hbEven : HLOZPairing.chessEven (primedPairBase a) := ha
        have hne : x + paperE1 ≠ primedPairBase a := by
          intro h
          exact not_chessEven_add_paperE1 hx (h ▸ hbEven)
        have heq : x + paperE1 = a ↔ primedPairBase a = x := by
          constructor
          · intro h
            apply add_paperE1_injective
            simpa [primedPairBase_add_paperE1] using h.symm
          · intro h
            rw [← h, primedPairBase_add_paperE1]
        simp only [primedLazyVisitCount, primedLazyBlockSum, if_neg hne]
        rw [if_congr heq rfl rfl]
        rw [ih (pairEndpoint a p)]
        · simp
        · rw [primedPairBase_pairEndpoint]
          exact (chessEven_pairEndpoint_iff (primedPairBase a) p).mpr ha
  have hf := primedRunFinalBase_chessEven a runs ha
  have hne : x + paperE1 ≠
      primedPairBase (primedRunFinalStart a runs) := by
    intro h
    exact not_chessEven_add_paperE1 hx (h ▸ hf)
  rw [primedIncompleteLazyVisitCount, primedIncompleteLazyBlockSum,
    hmain, if_neg hne]
  have heq : x + paperE1 = primedRunFinalStart a runs ↔
      primedPairBase (primedRunFinalStart a runs) = x := by
    constructor
    · intro h
      apply add_paperE1_injective
      simpa [primedPairBase_add_paperE1] using h.symm
    · intro h
      rw [← h, primedPairBase_add_paperE1]
  rw [if_congr heq rfl rfl]
  omega

theorem primedIncompleteLazyBlockSum_zip
    (a : Site) (labels : List IncrementPair) (values : List ℕ) (t : ℕ)
    (h : values.length = labels.length) (x : Site) :
    primedIncompleteLazyBlockSum a (List.zip values labels) t x =
      listBlockSum
        (stoppedExternalBasesFrom (primedPairBase a) labels)
        (values ++ [t]) x := by
  induction labels generalizing a values with
  | nil =>
      have hv : values = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst values
      by_cases ha : primedPairBase a = x <;>
        simp [primedIncompleteLazyBlockSum, primedLazyBlockSum,
          primedRunFinalStart, stoppedExternalBasesFrom, listBlockSum, ha]
  | cons p labels ih =>
      cases values with
      | nil => simp at h
      | cons u values =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          simp only [List.zip_cons_cons, primedIncompleteLazyBlockSum,
            primedLazyBlockSum, primedRunFinalStart,
            stoppedExternalBasesFrom, List.cons_append]
          rw [listBlockSum_cons]
          rw [Nat.add_assoc]
          change (if primedPairBase a = x then u else 0) +
              primedIncompleteLazyBlockSum (pairEndpoint a p)
                (values.zip labels) t x =
            (if primedPairBase a = x then u else 0) +
              listBlockSum
                (stoppedExternalBasesFrom
                  (pairEndpoint (primedPairBase a) p) labels)
                (values ++ [t]) x
          rw [ih (pairEndpoint a p) values h]
          rw [primedPairBase_pairEndpoint]

theorem primedIncompleteLazyBlockSum_completedRunsFromVector {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (x : Site) :
    primedIncompleteLazyBlockSum a (completedRunsFromVector labels v)
        (v (Fin.last q)) x =
      listBlockSum
        (stoppedExternalBasesFrom (primedPairBase a) (List.ofFn labels))
        (List.ofFn v) x := by
  rw [completedRunsFromVector]
  rw [ofFn_pair_eq_zip]
  rw [primedIncompleteLazyBlockSum_zip a (List.ofFn labels)
    (List.ofFn fun i : Fin q ↦ v i.castSucc) (v (Fin.last q))
    (by simp) x]
  rw [values_castSucc_append_last]

def primedStoppedExternalLocalTimeFrom {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair) (x : Site) : ℕ :=
  List.count x
    ((0, 0) :: primedInitialStart first ::
      reconstructExternalTail (primedInitialStart first) (List.ofFn labels))

def primedStoppedExternalLeft {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair) :
    StoppedExternalBase (primedInitialBase first) labels → ℕ :=
  fun b ↦ primedStoppedExternalLocalTimeFrom first labels b.1

def primedStoppedExternalRight {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair) :
    StoppedExternalBase (primedInitialBase first) labels → ℕ :=
  fun b ↦ primedStoppedExternalLocalTimeFrom first labels (b.1 + paperE1)

theorem primedStoppedExternalBase_chessEven {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (b : StoppedExternalBase (primedInitialBase first) labels) :
    HLOZPairing.chessEven b.1 := by
  apply chessEven_of_mem_stoppedExternalBasesFrom
    (primedInitialBase first) (List.ofFn labels) b.1
  · exact primedInitialBase_chessEven first
  · simpa only [stoppedExternalBaseSet, List.mem_toFinset] using b.2

theorem localTime_reconstructedPrimedStoppedPrefix {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (x : Site) :
    localTime
        (simpleRandomWalk
          (extendPrefix (reconstructedPrimedStoppedPrefix first labels v).2))
        (reconstructedPrimedStoppedPrefix first labels v).1 x =
      primedStoppedExternalLocalTimeFrom first labels x +
        primedIncompleteLazyVisitCount (primedInitialStart first)
          (completedRunsFromVector labels v) (v (Fin.last q)) x := by
  change localTime
      (simpleRandomWalk
        (extendPrefix (prefixOfDirectionList
          (first :: primedStoppedDirectionList labels v))))
      (first :: primedStoppedDirectionList labels v).length x = _
  rw [localTime_extendPrefix_prefixOfDirectionList_eq_count]
  unfold primedStoppedDirectionList
  rw [primedStoppedPairList_eq_direct]
  unfold reconstructFromDirections
  simp only [reconstructTail]
  have hstart : (0, 0) + directionStep first =
      primedInitialStart first := by
    ext <;> simp [primedInitialStart]
  rw [hstart]
  change List.count x
      ((0, 0) :: reconstructFromDirections (primedInitialStart first)
        (flattenPairs
          (expandPrimedPairRuns (completedRunsFromVector labels v) ++
            List.replicate (v (Fin.last q))
              primedDistinguishedIncrementPair))) = _
  rw [List.count_cons, count_primedIncomplete_reconstruction]
  unfold primedStoppedExternalLocalTimeFrom
  rw [terminalLabels_completedRunsFromVector]
  simp only [List.count_cons]
  omega

theorem localTime_reconstructedPrimedStoppedPrefix_base {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ)
    (b : StoppedExternalBase (primedInitialBase first) labels) :
    localTime
        (simpleRandomWalk
          (extendPrefix (reconstructedPrimedStoppedPrefix first labels v).2))
        (reconstructedPrimedStoppedPrefix first labels v).1 b.1 =
      primedStoppedExternalLeft first labels b +
        stoppedPaperBlockSums (primedInitialBase first) labels
          (stoppedPaperBlockVector (primedInitialBase first) labels v) b := by
  rw [localTime_reconstructedPrimedStoppedPrefix]
  rw [primedIncompleteLazyVisitCount_eq_blockSum_base
    (primedInitialStart first) (completedRunsFromVector labels v)
    (v (Fin.last q)) b.1]
  · rw [primedIncompleteLazyBlockSum_completedRunsFromVector]
    change primedStoppedExternalLocalTimeFrom first labels b.1 +
        listBlockSum
          (stoppedExternalBasesFrom (primedInitialBase first)
            (List.ofFn labels)) (List.ofFn v) b.1 = _
    rw [listBlockSum_eq_stoppedPaperBlockSums]
    rfl
  · exact primedInitialBase_chessEven first
  · exact primedStoppedExternalBase_chessEven first labels b

theorem localTime_reconstructedPrimedStoppedPrefix_partner {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ)
    (b : StoppedExternalBase (primedInitialBase first) labels) :
    localTime
        (simpleRandomWalk
          (extendPrefix (reconstructedPrimedStoppedPrefix first labels v).2))
        (reconstructedPrimedStoppedPrefix first labels v).1
          (b.1 + paperE1) =
      primedStoppedExternalRight first labels b +
        stoppedPaperBlockSums (primedInitialBase first) labels
          (stoppedPaperBlockVector (primedInitialBase first) labels v) b := by
  rw [localTime_reconstructedPrimedStoppedPrefix]
  rw [primedIncompleteLazyVisitCount_eq_blockSum_partner
    (primedInitialStart first) (completedRunsFromVector labels v)
    (v (Fin.last q)) b.1]
  · rw [primedIncompleteLazyBlockSum_completedRunsFromVector]
    change primedStoppedExternalLocalTimeFrom first labels
          (b.1 + paperE1) +
        listBlockSum
          (stoppedExternalBasesFrom (primedInitialBase first)
            (List.ofFn labels)) (List.ofFn v) b.1 = _
    rw [listBlockSum_eq_stoppedPaperBlockSums]
    rfl
  · exact primedInitialBase_chessEven first
  · exact primedStoppedExternalBase_chessEven first labels b

theorem listBlockSum_eq_zero_of_not_mem_from {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (x : Site)
    (hx : x ∉ stoppedExternalBaseSet a labels) :
    listBlockSum (stoppedExternalBasesFrom a (List.ofFn labels))
        (List.ofFn v) x = 0 := by
  let bases := stoppedExternalBasesFrom a (List.ofFn labels)
  have hlen : bases.length = q + 1 := by simp [bases]
  let e : Fin bases.length ≃ Fin (q + 1) := finCongr hlen
  have hv : List.ofFn v =
      List.ofFn (fun i : Fin bases.length ↦ v (e i)) := by
    apply List.ext_get
    · simp [hlen]
    · intro i hi₁ hi₂
      rw [List.get_ofFn, List.get_ofFn]
      rfl
  rw [hv, listBlockSum_ofFn]
  apply Finset.sum_eq_zero
  intro i _
  rw [if_neg]
  intro hi
  apply hx
  unfold stoppedExternalBaseSet
  rw [List.mem_toFinset]
  exact hi ▸ List.get_mem bases i

theorem localTime_reconstructedPrimedStoppedPrefix_offBase {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (x : Site)
    (hx : x ∉ stoppedExternalBaseSet (primedInitialBase first) labels)
    (heven : HLOZPairing.chessEven x) :
    localTime
        (simpleRandomWalk
          (extendPrefix (reconstructedPrimedStoppedPrefix first labels v).2))
        (reconstructedPrimedStoppedPrefix first labels v).1 x =
      primedStoppedExternalLocalTimeFrom first labels x := by
  rw [localTime_reconstructedPrimedStoppedPrefix]
  rw [primedIncompleteLazyVisitCount_eq_blockSum_base
    (primedInitialStart first) (completedRunsFromVector labels v)
    (v (Fin.last q)) x]
  · rw [primedIncompleteLazyBlockSum_completedRunsFromVector,
      show primedPairBase (primedInitialStart first) =
        primedInitialBase first by rfl,
      listBlockSum_eq_zero_of_not_mem_from
        (primedInitialBase first) labels v x hx, add_zero]
  · exact primedInitialBase_chessEven first
  · exact heven

theorem localTime_reconstructedPrimedStoppedPrefix_offBase_partner {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (x : Site)
    (hx : x ∉ stoppedExternalBaseSet (primedInitialBase first) labels)
    (heven : HLOZPairing.chessEven x) :
    localTime
        (simpleRandomWalk
          (extendPrefix (reconstructedPrimedStoppedPrefix first labels v).2))
        (reconstructedPrimedStoppedPrefix first labels v).1
          (x + paperE1) =
      primedStoppedExternalLocalTimeFrom first labels (x + paperE1) := by
  rw [localTime_reconstructedPrimedStoppedPrefix]
  rw [primedIncompleteLazyVisitCount_eq_blockSum_partner
    (primedInitialStart first) (completedRunsFromVector labels v)
    (v (Fin.last q)) x]
  · rw [primedIncompleteLazyBlockSum_completedRunsFromVector,
      show primedPairBase (primedInitialStart first) =
        primedInitialBase first by rfl,
      listBlockSum_eq_zero_of_not_mem_from
        (primedInitialBase first) labels v x hx, add_zero]
  · exact primedInitialBase_chessEven first
  · exact heven

def PrimedOddOffBaseMixedCondition {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (m : ℕ) (C : Finset Site) : Prop :=
  ∀ x, HLOZPairing.chessEven x →
    x ∉ stoppedExternalBaseSet (primedInitialBase first) labels →
      if _hC : x ∈ C ∨ x + paperE1 ∈ C then
        max (primedStoppedExternalLocalTimeFrom first labels x)
            (primedStoppedExternalLocalTimeFrom first labels
              (x + paperE1)) = m ∧
          (primedStoppedExternalLocalTimeFrom first labels x = m ↔
            x ∈ C) ∧
          (primedStoppedExternalLocalTimeFrom first labels
              (x + paperE1) = m ↔ x + paperE1 ∈ C)
      else
        max (primedStoppedExternalLocalTimeFrom first labels x)
          (primedStoppedExternalLocalTimeFrom first labels
            (x + paperE1)) < m

theorem mixedX1DominoCondition_reconstructedPrimedStoppedPrefix_iff {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (m : ℕ) (C : Finset Site) :
    MixedX1DominoCondition
        (simpleRandomWalk
          (extendPrefix (reconstructedPrimedStoppedPrefix first labels v).2))
        (reconstructedPrimedStoppedPrefix first labels v).1 m C ↔
      HLOZPairing.PairFree
          (HLOZPairing.XPair HLOZPairing.east) C ∧
        PrimedOddOffBaseMixedCondition first labels m C ∧
        stoppedPaperBlockSums (primedInitialBase first) labels
            (stoppedPaperBlockVector (primedInitialBase first) labels v) ∈
          stoppedMixedBlockSumEvent (primedInitialBase first) labels m C
            (primedStoppedExternalLeft first labels)
            (primedStoppedExternalRight first labels) := by
  constructor
  · rintro ⟨hfree, hmix⟩
    refine ⟨hfree, ?_, ?_⟩
    · intro x hxEven hxOff
      specialize hmix x hxEven
      rw [localTime_reconstructedPrimedStoppedPrefix_offBase
          first labels v x hxOff hxEven,
        localTime_reconstructedPrimedStoppedPrefix_offBase_partner
          first labels v x hxOff hxEven] at hmix
      exact hmix
    · intro b
      specialize hmix b.1
        (primedStoppedExternalBase_chessEven first labels b)
      rw [localTime_reconstructedPrimedStoppedPrefix_base first labels v b,
        localTime_reconstructedPrimedStoppedPrefix_partner
          first labels v b] at hmix
      exact hmix
  · rintro ⟨hfree, hoff, hblocks⟩
    refine ⟨hfree, ?_⟩
    intro x hxEven
    by_cases hxBase :
        x ∈ stoppedExternalBaseSet (primedInitialBase first) labels
    · let b : StoppedExternalBase (primedInitialBase first) labels :=
        ⟨x, hxBase⟩
      have hb := hblocks b
      rw [localTime_reconstructedPrimedStoppedPrefix_base first labels v b,
        localTime_reconstructedPrimedStoppedPrefix_partner
          first labels v b]
      exact hb
    · have hx := hoff x hxEven hxBase
      rw [localTime_reconstructedPrimedStoppedPrefix_offBase
          first labels v x hxBase hxEven,
        localTime_reconstructedPrimedStoppedPrefix_offBase_partner
          first labels v x hxBase hxEven]
      exact hx

theorem terminalBase_replicate_primedDistinguished
    (a : Site) (t : ℕ) :
    terminalBase a (List.replicate t primedDistinguishedIncrementPair) = a := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [List.replicate_succ, terminalBase,
        pairEndpoint_primedDistinguished]
      exact ih

theorem terminalBase_expandPrimedPairRuns
    (a : Site) (runs : List PairRun) :
    terminalBase a (expandPrimedPairRuns runs) =
      primedRunFinalStart a runs := by
  induction runs generalizing a with
  | nil => rfl
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      simp only [expandPrimedPairRuns, primedRunFinalStart]
      rw [terminalBase_append,
        terminalBase_replicate_primedDistinguished]
      simp only [terminalBase]
      exact ih (pairEndpoint a p)

theorem primedRunFinalStart_completedRunsFromVector {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) :
    primedRunFinalStart a (completedRunsFromVector labels v) =
      terminalBase a (List.ofFn labels) := by
  unfold completedRunsFromVector
  induction q generalizing a with
  | zero => rfl
  | succ q ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      simp only [primedRunFinalStart, terminalBase]
      simpa using ih (pairEndpoint a (labels 0))
        (fun i ↦ labels i.succ) (fun i ↦ v i.succ)

def primedStoppedTerminalSite {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair) : Site :=
  terminalBase (primedInitialStart first) (List.ofFn labels)

theorem reconstructedPrimedStoppedPrefix_current {q : ℕ}
    (first : Direction) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) :
    simpleRandomWalk
        (extendPrefix (reconstructedPrimedStoppedPrefix first labels v).2)
        (reconstructedPrimedStoppedPrefix first labels v).1 =
      primedStoppedTerminalSite first labels := by
  let ds := first :: primedStoppedDirectionList labels v
  have hwalk := foldl_directionPrefix_eq_walk
    (extendPrefix (prefixOfDirectionList ds)) ds.length
  rw [directionPrefix_extendPrefix_prefixOfDirectionList] at hwalk
  change simpleRandomWalk (extendPrefix (prefixOfDirectionList ds))
      ds.length = primedStoppedTerminalSite first labels
  rw [← hwalk]
  unfold ds primedStoppedDirectionList
  rw [primedStoppedPairList_eq_direct]
  simp only [List.foldl_cons]
  have hstart : (0, 0) + directionStep first =
      primedInitialStart first := by
    ext <;> simp [primedInitialStart]
  rw [hstart, foldl_flattenPairs_terminalBase,
    terminalBase_append, terminalBase_replicate_primedDistinguished,
    terminalBase_expandPrimedPairRuns,
    primedRunFinalStart_completedRunsFromVector]
  rfl

theorem mem_stoppedRunVectorBox_of_mem_mixedBlockSumEvent_from {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (m : ℕ) (C : Finset Site)
    (externalLeft externalRight : StoppedExternalBase a labels → ℕ)
    (hblocks : stoppedPaperBlockSums a labels
        (stoppedPaperBlockVector a labels v) ∈
      stoppedMixedBlockSumEvent a labels m C
        externalLeft externalRight) :
    v ∈ stoppedRunVectorBox q m := by
  classical
  unfold stoppedRunVectorBox
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_range]
  let b : StoppedExternalBase a labels :=
    ⟨stoppedExternalBaseAt a labels i,
      stoppedExternalBaseAt_mem a labels i⟩
  have hcoord := stoppedPaperBlockVector_coordinate_le_sum a labels v i
  have hb := hblocks b
  split at hb
  · have hsum : stoppedPaperBlockSums a labels
        (stoppedPaperBlockVector a labels v) b ≤ m := by
      have hleft : stoppedPaperBlockSums a labels
          (stoppedPaperBlockVector a labels v) b ≤
          externalLeft b + stoppedPaperBlockSums a labels
            (stoppedPaperBlockVector a labels v) b := Nat.le_add_left _ _
      have hmax := le_max_left
        (externalLeft b + stoppedPaperBlockSums a labels
          (stoppedPaperBlockVector a labels v) b)
        (externalRight b + stoppedPaperBlockSums a labels
          (stoppedPaperBlockVector a labels v) b)
      exact hleft.trans (hmax.trans_eq hb.1)
    change v i < m + 1
    exact lt_of_le_of_lt (hcoord.trans hsum) (Nat.lt_succ_self m)
  · have hsum : stoppedPaperBlockSums a labels
        (stoppedPaperBlockVector a labels v) b < m := by
      have hleft : stoppedPaperBlockSums a labels
          (stoppedPaperBlockVector a labels v) b ≤
          externalLeft b + stoppedPaperBlockSums a labels
            (stoppedPaperBlockVector a labels v) b := Nat.le_add_left _ _
      have hmax := le_max_left
        (externalLeft b + stoppedPaperBlockSums a labels
          (stoppedPaperBlockVector a labels v) b)
        (externalRight b + stoppedPaperBlockSums a labels
          (stoppedPaperBlockVector a labels v) b)
      exact hleft.trans_lt (hmax.trans_lt hb)
    change v i < m + 1
    exact (hcoord.trans_lt hsum).trans (Nat.lt_succ_self m)

theorem primedOddSourceConstraint_eq_mixedBlockPreimage {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : PrimedOddOffBaseMixedCondition first labels m C) :
    (primedOddSourceConstraint m k C first labels :
        Set (Fin (q + 1) → ℕ)) =
      (fun v ↦ stoppedPaperBlockSums (primedInitialBase first) labels
        (stoppedPaperBlockVector (primedInitialBase first) labels v)) ⁻¹'
        stoppedMixedBlockSumEvent (primedInitialBase first) labels m C
          (primedStoppedExternalLeft first labels)
          (primedStoppedExternalRight first labels) := by
  ext v
  change v ∈ primedOddSourceConstraint m k C first labels ↔ _
  simp only [primedOddSourceConstraint, mixedPrefixConstraint,
    Finset.mem_filter]
  constructor
  · rintro ⟨_, hmixed⟩
    exact (mixedX1DominoCondition_reconstructedPrimedStoppedPrefix_iff
      first labels v m C).mp hmixed |>.2.2
  · intro hblocks
    refine ⟨mem_stoppedRunVectorBox_of_mem_mixedBlockSumEvent_from
      (primedInitialBase first) labels v m C _ _ hblocks, ?_⟩
    exact (mixedX1DominoCondition_reconstructedPrimedStoppedPrefix_iff
      first labels v m C).mpr ⟨hfree, hoff, hblocks⟩

theorem actualAdmissible_primedOddSourceConstraint_eq_mixedBlockPreimage
    {q : ℕ} (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hm : 0 < m) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : PrimedOddOffBaseMixedCondition first labels m C)
    (hterminal : primedStoppedTerminalSite first labels ∈ C) :
    (actualAdmissiblePrimedStoppedVectors m k first labels
        (primedOddSourceConstraint m k C first labels) :
      Set (Fin (q + 1) → ℕ)) =
      (fun v ↦ stoppedPaperBlockSums (primedInitialBase first) labels
        (stoppedPaperBlockVector (primedInitialBase first) labels v)) ⁻¹'
        stoppedMixedBlockSumEvent (primedInitialBase first) labels m C
          (primedStoppedExternalLeft first labels)
          (primedStoppedExternalRight first labels) := by
  ext v
  rw [← primedOddSourceConstraint_eq_mixedBlockPreimage
    m k C first labels hfree hoff]
  change v ∈ actualAdmissiblePrimedStoppedVectors m k first labels
      (primedOddSourceConstraint m k C first labels) ↔
    v ∈ primedOddSourceConstraint m k C first labels
  simp only [actualAdmissiblePrimedStoppedVectors, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.1
  · intro hv
    refine ⟨hv, ?_⟩
    have hmixed : MixedX1DominoCondition
        (simpleRandomWalk
          (extendPrefix (reconstructedPrimedStoppedPrefix first labels v).2))
        (reconstructedPrimedStoppedPrefix first labels v).1 m C := by
      apply (mixedX1DominoCondition_reconstructedPrimedStoppedPrefix_iff
        first labels v m C).mpr
      refine ⟨hfree, hoff, ?_⟩
      have heq := primedOddSourceConstraint_eq_mixedBlockPreimage
        m k C first labels hfree hoff
      have hvSet : v ∈
          (primedOddSourceConstraint m k C first labels :
            Set (Fin (q + 1) → ℕ)) := hv
      rw [heq] at hvSet
      exact hvSet
    have hcurrent : simpleRandomWalk
        (extendPrefix (reconstructedPrimedStoppedPrefix first labels v).2)
        (reconstructedPrimedStoppedPrefix first labels v).1 ∈ C := by
      rw [reconstructedPrimedStoppedPrefix_current]
      exact hterminal
    exact firstKSitesReachLevel_eq_of_mixed_current_mem
      (simpleRandomWalk
        (extendPrefix (reconstructedPrimedStoppedPrefix first labels v).2))
      (reconstructedPrimedStoppedPrefix first labels v).1 m k C
      hm hcard hmixed hcurrent

theorem actualPrimedStoppedVector_fiber_inter_event {q : ℕ}
    (m k : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (E : Finset (Fin (q + 1) → ℕ)) (v : Fin (q + 1) → ℕ) :
    actualPrimedStoppedVectorEvent m k first labels E ∩
        (actualPrimedStoppedVector m k first labels E) ⁻¹' {v} =
      if v ∈ actualAdmissiblePrimedStoppedVectors m k first labels E then
        stoppedPrefixAtom (reconstructedPrimedStoppedPrefix first labels v)
      else ∅ := by
  classical
  let A := actualAdmissiblePrimedStoppedVectors m k first labels E
  let atom := fun w : Fin (q + 1) → ℕ ↦
    stoppedPrefixAtom (reconstructedPrimedStoppedPrefix first labels w)
  have hd : ∀ {u w}, u ∈ A → w ∈ A → u ≠ w →
      Disjoint (atom u) (atom w) := by
    intro u w hu hw huw
    apply stoppedPrefixAtom_pairwiseDisjoint_on_firstK m k
    · exact (Finset.mem_filter.mp hu).2
    · exact (Finset.mem_filter.mp hw).2
    · exact fun hp ↦ huw
        (reconstructedPrimedStoppedPrefix_injective
          first labels hnondist hp)
  change finiteAtomEvent A atom ∩
      {ω | finiteAtomDecoder A atom ω = v} = _
  simpa only [A, atom] using
    finiteAtomDecoder_fiber_inter_event A atom hd v

theorem measurable_actualPrimedStoppedVector {q : ℕ}
    (m k : ℕ) (first : Direction) (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (E : Finset (Fin (q + 1) → ℕ)) :
    Measurable (actualPrimedStoppedVector m k first labels E) := by
  classical
  let A := actualAdmissiblePrimedStoppedVectors m k first labels E
  let atom := fun w : Fin (q + 1) → ℕ ↦
    stoppedPrefixAtom (reconstructedPrimedStoppedPrefix first labels w)
  apply measurable_finiteAtomDecoder A atom
  · intro u w hu hw huw
    apply stoppedPrefixAtom_pairwiseDisjoint_on_firstK m k
    · exact (Finset.mem_filter.mp hu).2
    · exact (Finset.mem_filter.mp hw).2
    · exact fun hp ↦ huw
        (reconstructedPrimedStoppedPrefix_injective
          first labels hnondist hp)
  · intro w _
    exact measurableSet_stoppedPrefixAtom _

theorem primedOdd_vectorFiberPast {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (v : Fin (q + 1) → ℕ) (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      (((actualPrimedStoppedVectorEvent m k first labels
            (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C) ∩
          (actualPrimedStoppedVector m k first labels
            (primedOddSourceConstraint m k C first labels)) ⁻¹' {v}) ∩
        {ω | stoppedCreationTime m k ω = n}) := by
  classical
  rw [primedOdd_source_partition m k C first labels hm hk hfree]
  let E := primedOddSourceConstraint m k C first labels
  let p := reconstructedPrimedStoppedPrefix first labels v
  change MeasurableSet[iidHistory (X := Direction) n]
      ((actualPrimedStoppedVectorEvent m k first labels E ∩
          (actualPrimedStoppedVector m k first labels E) ⁻¹' {v}) ∩
        {ω | stoppedCreationTime m k ω = n})
  have hfiber := actualPrimedStoppedVector_fiber_inter_event
    m k first labels hnondist E v
  change actualPrimedStoppedVectorEvent m k first labels E ∩
      (actualPrimedStoppedVector m k first labels E) ⁻¹' {v} =
    (if v ∈ actualAdmissiblePrimedStoppedVectors m k first labels E then
      stoppedPrefixAtom p else ∅) at hfiber
  rw [hfiber]
  by_cases hv : v ∈ actualAdmissiblePrimedStoppedVectors
      m k first labels E
  · rw [if_pos hv]
    have hpstop : IsFirstKStoppedPrefix m k p :=
      (Finset.mem_filter.mp hv).2
    have hpT := prefixAtom_subset_firstKSitesReachLevel_fiber hpstop
    by_cases hpn : p.1 = n
    · have hsubset : stoppedPrefixAtom p ⊆
          {ω | stoppedCreationTime m k ω = n} := by
        intro ω hω
        have hT := hpT hω
        change firstKSitesReachLevel m k (simpleRandomWalk ω) = p.1 at hT
        change stoppedCreationTime m k ω = n
        unfold stoppedCreationTime
        rw [hT]
        exact hpn
      rw [Set.inter_eq_left.mpr hsubset, ← hpn]
      exact measurableSet_stoppedPrefixAtom_iidHistory p
    · have hempty : stoppedPrefixAtom p ∩
          {ω | stoppedCreationTime m k ω = n} = ∅ := by
        ext ω
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false]
        rintro ⟨hωp, hωn⟩
        have hT := hpT hωp
        change firstKSitesReachLevel m k (simpleRandomWalk ω) = p.1 at hT
        have htime : stoppedCreationTime m k ω = p.1 := by
          unfold stoppedCreationTime
          rw [hT]
          simp
        exact hpn (htime.symm.trans hωn)
      rw [hempty]
      exact @MeasurableSet.empty _ (iidHistory (X := Direction) n)
  · rw [if_neg hv, Set.empty_inter]
    exact @MeasurableSet.empty _ (iidHistory (X := Direction) n)

theorem primedOdd_sourcePast {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C) (n : ℕ) :
    MeasurableSet[iidHistory (X := Direction) n]
      ((actualPrimedStoppedVectorEvent m k first labels
          (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C) ∩
        {ω | stoppedCreationTime m k ω = n}) := by
  let A := actualPrimedStoppedVectorEvent m k first labels
      (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C
  let X := actualPrimedStoppedVector m k first labels
    (primedOddSourceConstraint m k C first labels)
  have heq : A ∩ {ω | stoppedCreationTime m k ω = n} =
      ⋃ v : Fin (q + 1) → ℕ,
        ((A ∩ X ⁻¹' {v}) ∩ {ω | stoppedCreationTime m k ω = n}) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage,
      Set.mem_singleton_iff, A, X]
    constructor
    · intro h
      exact ⟨actualPrimedStoppedVector m k first labels
        (primedOddSourceConstraint m k C first labels) ω,
        ⟨h.1, rfl⟩, h.2⟩
    · rintro ⟨v, ⟨hA, _hv⟩, hn⟩
      exact ⟨hA, hn⟩
  rw [show (actualPrimedStoppedVectorEvent m k first labels
      (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C) ∩
        {ω | stoppedCreationTime m k ω = n} =
      A ∩ {ω | stoppedCreationTime m k ω = n} by rfl, heq]
  exact MeasurableSet.iUnion fun v ↦
    primedOdd_vectorFiberPast m k C first labels hnondist
      hm hk hfree v n

theorem primedOdd_activeFreeWinning_capped_map_law {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (externalLeft externalRight :
      StoppedExternalBase (primedInitialBase first) labels → ℕ)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels))
    (hGroupedEvent :
      (actualAdmissiblePrimedStoppedVectors m k first labels
          (primedOddSourceConstraint m k C first labels) :
        Set (Fin (q + 1) → ℕ)) =
        (fun v ↦ stoppedPaperBlockSums (primedInitialBase first) labels
          (stoppedPaperBlockVector (primedInitialBase first) labels v)) ⁻¹'
          stoppedMixedBlockSumEvent (primedInitialBase first) labels m C
            externalLeft externalRight)
    (hMixedCoordinatePos : ∀ b, HLOZUrn.negBinMeasure
      (Fintype.card
        (StoppedExternalIndex (primedInitialBase first) labels b))
        (stoppedMixedBlockValues (primedInitialBase first) labels m C
          externalLeft externalRight b : Set ℕ) ≠ 0) :
    HasLaw
      (fun ω ↦
        (restrictActiveFreeStoppedBase (primedInitialBase first) labels C
            activeBases
            (stoppedPaperBlockSums (primedInitialBase first) labels
              (stoppedPaperBlockVector (primedInitialBase first) labels
                (actualPrimedStoppedVector m k first labels
                  (primedOddSourceConstraint m k C first labels) ω))),
          incrementShiftAfter (stoppedCreationTime m k) ω 0))
      ((sourceCappedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            activeBases)
          (activeFreeCapProfile (primedInitialBase first) labels C
            activeBases externalLeft externalRight)).prod directionLaw)
      incrementLaw[|
        actualPrimedStoppedVectorEvent m k first labels
            (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C] := by
  let E := primedOddSourceConstraint m k C first labels
  let A := actualPrimedStoppedVectorEvent m k first labels
      (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C
  let X := actualPrimedStoppedVector m k first labels E
  let τ := stoppedCreationTime m k
  let S := fun v : Fin (q + 1) → ℕ ↦
    stoppedPaperBlockSums (primedInitialBase first) labels
      (stoppedPaperBlockVector (primedInitialBase first) labels v)
  let R := restrictActiveFreeStoppedBase (primedInitialBase first)
    labels C activeBases
  have hτ : Measurable τ := measurable_stoppedCreationTime m k
  have hX : Measurable X :=
    measurable_actualPrimedStoppedVector m k first labels hnondist E
  have hsource : HasLaw X
      ((HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissiblePrimedStoppedVectors m k first labels E : Set _)])
      incrementLaw[|A] := by
    simpa only [E, A, X] using
      primedOdd_source_hasLaw m k C first labels hnondist hm hk hfree
  have hjoint : HasLaw (fun ω ↦ (X ω, incrementShiftAfter τ ω 0))
      (((HLOZUrn.runVectorMeasure (q + 1))[|
          (actualAdmissiblePrimedStoppedVectors
            m k first labels E : Set _)]).prod directionLaw)
      incrementLaw[|A] := by
    apply hasLaw_prod_direction_after τ A X _ hτ
    · intro n
      simpa only [A, τ] using
        primedOdd_sourcePast m k C first labels hnondist hm hk hfree n
    · exact hX
    · intro v n
      simpa only [A, X, τ, Set.inter_assoc] using
        primedOdd_vectorFiberPast m k C first labels hnondist
          hm hk hfree v n
    · exact hsource
  have hgrouped := stoppedPaperBlockSums_hasLaw_mixed_finset
    (primedInitialBase first) labels m C externalLeft externalRight
    (actualAdmissiblePrimedStoppedVectors m k first labels E) hGroupedEvent
  have hmapS :
      ((HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissiblePrimedStoppedVectors
          m k first labels E : Set _)]).map S =
        (stoppedBlockNegBinMeasure (primedInitialBase first) labels)[|
          stoppedMixedBlockSumEvent (primedInitialBase first) labels m C
            externalLeft externalRight] := by
    simpa only [S] using hgrouped.map_eq
  have hCappedLaw := stoppedBlockNegBinMeasure_cond_mixed_map_activeFree
    (primedInitialBase first) labels m C activeBases
    externalLeft externalRight hMixedCoordinatePos
  have hmapRS :
      ((HLOZUrn.runVectorMeasure (q + 1))[|
        (actualAdmissiblePrimedStoppedVectors
          m k first labels E : Set _)]).map (fun v ↦ R (S v)) =
        sourceCappedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            activeBases)
          (activeFreeCapProfile (primedInitialBase first) labels C
            activeBases externalLeft externalRight) := by
    change ((HLOZUrn.runVectorMeasure (q + 1))[|
      (actualAdmissiblePrimedStoppedVectors
        m k first labels E : Set _)]).map (R ∘ S) = _
    have hR : Measurable R :=
      measurable_restrictActiveFreeStoppedBase
        (primedInitialBase first) labels C activeBases
    have hS : Measurable S :=
      (measurable_stoppedPaperBlockSums
        (primedInitialBase first) labels).comp
        (measurable_stoppedPaperBlockVector
          (primedInitialBase first) labels)
    rw [← Measure.map_map hR hS, hmapS]
    exact hCappedLaw
  have hRS : Measurable (fun v ↦ R (S v)) :=
    (measurable_restrictActiveFreeStoppedBase
      (primedInitialBase first) labels C activeBases).comp
      ((measurable_stoppedPaperBlockSums
        (primedInitialBase first) labels).comp
        (measurable_stoppedPaperBlockVector
          (primedInitialBase first) labels))
  simpa only [A, X, τ, S, R] using
    hasLaw_map_fst_prod_direction hjoint (fun v ↦ R (S v)) hRS hmapRS

/-- Source-exact primed-odd stopped law.  The next direction is fresh because
the conditioning atom ends at the unfinished run boundary; no terminal pair
is included. -/
theorem primedOdd_activeFreeWinning_capped_map_law_of_source {q : ℕ}
    (m k : ℕ) (C : Finset Site) (first : Direction)
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ primedDistinguishedIncrementPair)
    (hm : 0 < m) (hk : 0 < k) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : PrimedOddOffBaseMixedCondition first labels m C)
    (hterminal : primedStoppedTerminalSite first labels ∈ C)
    (activeBases : Finset
      (StoppedExternalBase (primedInitialBase first) labels))
    (hMixedEvent :
      (stoppedMixedBlockSumEvent (primedInitialBase first) labels m C
        (primedStoppedExternalLeft first labels)
        (primedStoppedExternalRight first labels)).Nonempty) :
    HasLaw
      (fun ω ↦
        (restrictActiveFreeStoppedBase (primedInitialBase first) labels C
            activeBases
            (stoppedPaperBlockSums (primedInitialBase first) labels
              (stoppedPaperBlockVector (primedInitialBase first) labels
                (actualPrimedStoppedVector m k first labels
                  (primedOddSourceConstraint m k C first labels) ω))),
          incrementShiftAfter (stoppedCreationTime m k) ω 0))
      ((sourceCappedProfileMeasure m
          (activeFreeStoppedShape (primedInitialBase first) labels C
            activeBases)
          (activeFreeCapProfile (primedInitialBase first) labels C activeBases
            (primedStoppedExternalLeft first labels)
            (primedStoppedExternalRight first labels))).prod directionLaw)
      incrementLaw[|
        actualPrimedStoppedVectorEvent m k first labels
            (stoppedRunVectorBox q m) ∩ stoppedSourceCondition m k C] := by
  apply primedOdd_activeFreeWinning_capped_map_law
    m k C first labels hnondist hm hk hfree
    (primedStoppedExternalLeft first labels)
    (primedStoppedExternalRight first labels) activeBases
  · exact actualAdmissible_primedOddSourceConstraint_eq_mixedBlockPreimage
      m k C first labels hm hcard hfree hoff hterminal
  · exact stoppedMixedCoordinatePos_of_event_nonempty
      (primedInitialBase first) labels m C _ _ hMixedEvent

end Erdos1166.HLOZPrimedOddMixedReconstruction
