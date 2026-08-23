import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedBlockGrouping
import ErdosProblems.Erdos1166.Erdos1166HLOZMixedCreationBlocks
import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedSourcePartition

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Erdos1166.HLOZStoppedMixedReconstruction

/-!
# Mixed stopped-block reconstruction for the unprimed-even X1 pairing

This file identifies the genuine unfinished `q+1` stopped holding vector with
the grouped mixed (4.7)/(4.8) block-sum event.  Dominoes not visited at a pair
boundary are retained as a static external-profile condition.  The final
theorem also discharges the first-hit filter from the literal source facts
`C.card = k` and membership of the fixed terminal base in `C`.

No statement here is transported to rotated X-pairings or to the distinct
column-matching Y/Y' encodings.
-/
open HLOZDecomposition HLOZReconstruction HLOZActualStopped
  HLOZIncompleteStoppedBlocks HLOZMixedCreationBlocks
  HLOZStoppedSourcePartition

theorem foldl_directionPrefix_eq_walk
    (ω : ℕ → Direction) (N : ℕ) :
    (List.ofFn fun i : Fin N ↦ ω i).foldl
        (fun x d ↦ x + directionStep d) (0, 0) =
      simpleRandomWalk ω N := by
  induction N with
  | zero => simp [simpleRandomWalk]
  | succ N ih =>
      simp only [List.ofFn_succ', Fin.val_castSucc, Fin.val_last]
      rw [List.concat_eq_append, List.foldl_append, ih]
      simp [simpleRandomWalk_succ']

theorem take_directionPrefix
    {alpha : Type*} (f : ℕ → alpha) (N k : ℕ) (hk : k ≤ N) :
    (List.ofFn fun i : Fin N ↦ f i).take k =
      List.ofFn fun i : Fin k ↦ f i := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left hk]
  · intro i hi₁ hi₂
    rw [List.getElem_take]
    simp

theorem scanl_directionPrefix_eq_walkPrefix
    (ω : ℕ → Direction) (N : ℕ) :
    (List.ofFn fun i : Fin N ↦ ω i).scanl
        (fun x d ↦ x + directionStep d) (0, 0) =
      List.ofFn fun i : Fin (N + 1) ↦ simpleRandomWalk ω i := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    rw [List.getElem_scanl]
    rw [take_directionPrefix ω N i (by simpa using hi₁)]
    rw [foldl_directionPrefix_eq_walk]
    cases i <;> simp

theorem count_walkPrefix_eq_localTime
    (s : ℕ → Site) (n : ℕ) (x : Site) :
    (List.ofFn fun t : Fin (n + 1) ↦ s t).count x =
      localTime s n x := by
  induction n with
  | zero =>
      unfold localTime
      change List.count x [s 0] =
        (({0} : Finset ℕ).filter fun j ↦ s j = x).card
      rw [Finset.filter_singleton]
      by_cases h : s 0 = x <;> simp [h]
  | succ n ih =>
      rw [List.ofFn_succ']
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [List.concat_eq_append, List.count_append, ih]
      rw [localTime_succ]
      by_cases h : s (n + 1) = x <;> simp [h]

theorem reconstructFromDirections_eq_scanl
    (a : Site) (ds : List Direction) :
    reconstructFromDirections a ds =
      ds.scanl (fun x d ↦ x + directionStep d) a := by
  induction ds generalizing a with
  | nil => rfl
  | cons d ds ih =>
      simp only [reconstructFromDirections, reconstructTail, List.scanl_cons]
      rw [← ih]
      rfl

theorem directionPrefix_extendPrefix_prefixOfDirectionList
    (ds : List Direction) :
    List.ofFn (fun i : Fin ds.length ↦
      extendPrefix (prefixOfDirectionList ds) i) = ds := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp [extendPrefix, prefixOfDirectionList]

theorem walkPrefix_extendPrefix_eq_reconstructFromDirections
    (ds : List Direction) :
    List.ofFn (fun i : Fin (ds.length + 1) ↦
        simpleRandomWalk
          (extendPrefix (prefixOfDirectionList ds)) i) =
      reconstructFromDirections (0, 0) ds := by
  rw [← scanl_directionPrefix_eq_walkPrefix
    (extendPrefix (prefixOfDirectionList ds)) ds.length]
  rw [directionPrefix_extendPrefix_prefixOfDirectionList]
  exact (reconstructFromDirections_eq_scanl (0, 0) ds).symm

theorem localTime_extendPrefix_prefixOfDirectionList_eq_count
    (ds : List Direction) (x : Site) :
    localTime
        (simpleRandomWalk (extendPrefix (prefixOfDirectionList ds)))
        ds.length x =
      (reconstructFromDirections (0, 0) ds).count x := by
  rw [← count_walkPrefix_eq_localTime]
  rw [walkPrefix_extendPrefix_eq_reconstructFromDirections]

def runFinalBase : Site → List PairRun → Site
  | a, [] => a
  | a, (_, p) :: runs => runFinalBase (pairEndpoint a p) runs

def incompleteLazyBlockSum
    (a : Site) (runs : List PairRun) (t : ℕ) (x : Site) : ℕ :=
  lazyBlockSum a runs x + if runFinalBase a runs = x then t else 0

def incompleteLazyVisitCount
    (a : Site) (runs : List PairRun) (t : ℕ) (x : Site) : ℕ :=
  lazyVisitCount a runs x +
    (if x = runFinalBase a runs + paperE1 then t else 0) +
    (if x = runFinalBase a runs then t else 0)

theorem prependLazyLoops_append
    (a : Site) (t : ℕ) (xs ys : List Site) :
    prependLazyLoops a t (xs ++ ys) =
      prependLazyLoops a t xs ++ ys := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [prependLazyLoops, List.cons_append, List.cons.injEq, true_and]
      exact ih

theorem reconstructPairTail_incomplete
    (a : Site) (runs : List PairRun) (t : ℕ) :
    reconstructPairTail a
        (expandPairRuns runs ++
          List.replicate t distinguishedIncrementPair) =
      reconstructRunTail a runs ++
        prependLazyLoops (runFinalBase a runs) t [] := by
  induction runs generalizing a with
  | nil =>
      simpa [expandPairRuns, reconstructRunTail, runFinalBase,
        reconstructPairTail] using
        reconstructPairTail_replicate_distinguished a t []
  | cons run runs ih =>
      rcases run with ⟨u, p⟩
      simp only [expandPairRuns, List.append_assoc]
      rw [reconstructPairTail_replicate_distinguished]
      simp only [reconstructRunTail, runFinalBase]
      change prependLazyLoops a u
          ((a + directionStep (p 0)) :: pairEndpoint a p ::
            reconstructPairTail (pairEndpoint a p)
              (expandPairRuns runs ++
                List.replicate t distinguishedIncrementPair)) = _
      rw [ih (pairEndpoint a p)]
      simpa only [List.cons_append] using
        prependLazyLoops_append a u
          ((a + directionStep (p 0)) :: pairEndpoint a p ::
            reconstructRunTail (pairEndpoint a p) runs)
          (prependLazyLoops (runFinalBase (pairEndpoint a p) runs) t [])

theorem count_incomplete_reconstruction
    (a : Site) (runs : List PairRun) (t : ℕ) (x : Site) :
    List.count x
        (reconstructFromDirections a
          (flattenPairs (expandPairRuns runs ++
            List.replicate t distinguishedIncrementPair))) =
      reconstructedExternalLocalTime a runs x +
        incompleteLazyVisitCount a runs t x := by
  unfold reconstructFromDirections
  rw [reconstructTail_flattenPairs, reconstructPairTail_incomplete]
  change List.count x
      ((a :: reconstructRunTail a runs) ++
        prependLazyLoops (runFinalBase a runs) t []) = _
  rw [List.count_append, count_prependLazyLoops]
  simp only [List.count_nil, add_zero]
  rw [← reconstructedPrefix_eq_runReconstruction]
  rw [count_reconstructedPrefix]
  unfold reconstructedExternalLocalTime incompleteLazyVisitCount
  omega

theorem runFinalBase_chessEven
    (a : Site) (runs : List PairRun)
    (ha : HLOZPairing.chessEven a) :
    HLOZPairing.chessEven (runFinalBase a runs) := by
  induction runs generalizing a with
  | nil => exact ha
  | cons run runs ih =>
      exact ih (pairEndpoint a run.2)
        ((chessEven_pairEndpoint_iff a run.2).mpr ha)

theorem incompleteLazyVisitCount_eq_blockSum_base
    (a : Site) (runs : List PairRun) (t : ℕ) (x : Site)
    (ha : HLOZPairing.chessEven a) (hx : HLOZPairing.chessEven x) :
    incompleteLazyVisitCount a runs t x =
      incompleteLazyBlockSum a runs t x := by
  have hf := runFinalBase_chessEven a runs ha
  have hne : x ≠ runFinalBase a runs + paperE1 := by
    intro h
    exact not_chessEven_add_paperE1 hf (h ▸ hx)
  rw [incompleteLazyVisitCount, incompleteLazyBlockSum,
    lazyVisitCount_eq_lazyBlockSum_base a runs x ha hx, if_neg hne]
  by_cases h : runFinalBase a runs = x
  · rw [if_pos h, if_pos h.symm]
    simp
  · rw [if_neg h, if_neg (fun h' ↦ h h'.symm)]

theorem incompleteLazyVisitCount_eq_blockSum_partner
    (a : Site) (runs : List PairRun) (t : ℕ) (x : Site)
    (ha : HLOZPairing.chessEven a) (hx : HLOZPairing.chessEven x) :
    incompleteLazyVisitCount a runs t (x + paperE1) =
      incompleteLazyBlockSum a runs t x := by
  have hf := runFinalBase_chessEven a runs ha
  have hne : x + paperE1 ≠ runFinalBase a runs := by
    intro h
    exact not_chessEven_add_paperE1 hx (h ▸ hf)
  rw [incompleteLazyVisitCount, incompleteLazyBlockSum,
    lazyVisitCount_eq_lazyBlockSum_partner a runs x ha hx, if_neg hne]
  by_cases h : runFinalBase a runs = x
  · have he : x + paperE1 = runFinalBase a runs + paperE1 := by rw [h]
    rw [if_pos h, if_pos he]
    simp
  · have he : x + paperE1 ≠ runFinalBase a runs + paperE1 := by
      intro he
      exact h (add_paperE1_injective he).symm
    rw [if_neg h, if_neg he]

def incompleteReconstructedPairMax
    (a : Site) (runs : List PairRun) (t : ℕ) (x : Site) : ℕ :=
  max
    (List.count x
      (reconstructFromDirections a
        (flattenPairs (expandPairRuns runs ++
          List.replicate t distinguishedIncrementPair))))
    (List.count (x + paperE1)
      (reconstructFromDirections a
        (flattenPairs (expandPairRuns runs ++
          List.replicate t distinguishedIncrementPair))))

theorem incompleteReconstructedPairMax_eq_external_add_block
    (a : Site) (runs : List PairRun) (t : ℕ) (x : Site)
    (ha : HLOZPairing.chessEven a) (hx : HLOZPairing.chessEven x) :
    incompleteReconstructedPairMax a runs t x =
      incompleteLazyBlockSum a runs t x +
        reconstructedExternalPairMax a runs x := by
  unfold incompleteReconstructedPairMax
  rw [count_incomplete_reconstruction, count_incomplete_reconstruction,
    incompleteLazyVisitCount_eq_blockSum_base a runs t x ha hx,
    incompleteLazyVisitCount_eq_blockSum_partner a runs t x ha hx]
  unfold reconstructedExternalPairMax
  rw [add_comm (reconstructedExternalLocalTime a runs x) _,
    add_comm (reconstructedExternalLocalTime a runs (x + paperE1)) _]
  exact Nat.add_max_add_left _ _ _

def listBlockSum (bases : List Site) (values : List ℕ) (x : Site) : ℕ :=
  (((bases.zip values).filter fun z ↦ z.1 = x).map Prod.snd).sum

theorem listBlockSum_cons (a : Site) (bases : List Site)
    (t : ℕ) (values : List ℕ) (x : Site) :
    listBlockSum (a :: bases) (t :: values) x =
      (if a = x then t else 0) + listBlockSum bases values x := by
  by_cases h : a = x <;> simp [listBlockSum, h]

theorem listBlockSum_ofFn (bases : List Site)
    (f : Fin bases.length → ℕ) (x : Site) :
    listBlockSum bases (List.ofFn f) x =
      ∑ i, if bases.get i = x then f i else 0 := by
  induction bases with
  | nil => simp [listBlockSum]
  | cons a bases ih =>
      rw [List.ofFn_succ, listBlockSum_cons, ih]
      change (if a = x then f 0 else 0) +
          (∑ i : Fin bases.length,
            if bases.get i = x then f i.succ else 0) =
        ∑ i : Fin (bases.length + 1),
          if (a :: bases).get i = x then f i else 0
      rw [Fin.sum_univ_succ]
      rfl

theorem listBlockSum_eq_stoppedPaperBlockSums {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (b : StoppedExternalBase a labels) :
    listBlockSum (stoppedExternalBasesFrom a (List.ofFn labels))
        (List.ofFn v) b.1 =
      stoppedPaperBlockSums a labels
        (stoppedPaperBlockVector a labels v) b := by
  classical
  let bases := stoppedExternalBasesFrom a (List.ofFn labels)
  have hlen : bases.length = q + 1 := by
    simp [bases]
  let e : Fin bases.length ≃ Fin (q + 1) := finCongr hlen
  have hv : List.ofFn v = List.ofFn (fun i : Fin bases.length ↦ v (e i)) := by
    apply List.ext_get
    · simp [hlen]
    · intro i hi₁ hi₂
      rw [List.get_ofFn, List.get_ofFn]
      rfl
  rw [hv, listBlockSum_ofFn]
  have hsum :
      (∑ i : Fin bases.length,
          if bases.get i = b.1 then v (e i) else 0) =
        ∑ i : Fin (q + 1),
          if stoppedExternalBaseAt a labels i = b.1 then v i else 0 := by
    apply Fintype.sum_equiv e
    intro i
    simp only [e]
    congr 1
  rw [hsum]
  unfold stoppedPaperBlockSums stoppedPaperBlockVector
  symm
  change (∑ i : {i : Fin (q + 1) //
      stoppedExternalBaseAt a labels i = b.1}, v i.1) = _
  let s := Finset.univ.filter fun i : Fin (q + 1) ↦
    stoppedExternalBaseAt a labels i = b.1
  calc
    (∑ i : {i : Fin (q + 1) //
        stoppedExternalBaseAt a labels i = b.1}, v i.1) =
        ∑ i ∈ s, v i := by
      exact (Finset.sum_subtype
        (p := fun i : Fin (q + 1) ↦
          stoppedExternalBaseAt a labels i = b.1)
        s (by simp [s]) v).symm
    _ = ∑ i : Fin (q + 1),
        if stoppedExternalBaseAt a labels i = b.1 then v i else 0 := by
      simp [s, Finset.sum_filter]

theorem incompleteLazyBlockSum_zip
    (a : Site) (labels : List IncrementPair) (values : List ℕ) (t : ℕ)
    (h : values.length = labels.length) (x : Site) :
    incompleteLazyBlockSum a (List.zip values labels) t x =
      listBlockSum (stoppedExternalBasesFrom a labels)
        (values ++ [t]) x := by
  induction labels generalizing a values with
  | nil =>
      have hv : values = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
      subst values
      by_cases ha : a = x <;>
        simp [incompleteLazyBlockSum, lazyBlockSum, runFinalBase,
          stoppedExternalBasesFrom, listBlockSum, ha]
  | cons p labels ih =>
      cases values with
      | nil => simp at h
      | cons u values =>
          simp only [List.length_cons, Nat.succ.injEq] at h
          simp only [List.zip_cons_cons, incompleteLazyBlockSum,
            lazyBlockSum, runFinalBase, stoppedExternalBasesFrom,
            List.cons_append]
          rw [listBlockSum_cons]
          rw [Nat.add_assoc]
          change (if a = x then u else 0) +
              incompleteLazyBlockSum (pairEndpoint a p)
                (values.zip labels) t x = _
          rw [ih (pairEndpoint a p) values h]

theorem terminalLabels_completedRunsFromVector {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ) :
    terminalLabels (completedRunsFromVector labels v) = List.ofFn labels := by
  unfold terminalLabels completedRunsFromVector
  rw [List.map_ofFn]
  congr 1

theorem values_castSucc_append_last {q : ℕ}
    (v : Fin (q + 1) → ℕ) :
    List.ofFn (fun i : Fin q ↦ v i.castSucc) ++ [v (Fin.last q)] =
      List.ofFn v := by
  simpa only [List.concat_eq_append] using (List.ofFn_succ' v).symm

theorem ofFn_pair_eq_zip {q : ℕ} {alpha beta : Type*}
    (f : Fin q → alpha) (g : Fin q → beta) :
    List.ofFn (fun i ↦ (f i, g i)) =
      (List.ofFn f).zip (List.ofFn g) := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp

theorem incompleteLazyBlockSum_completedRunsFromVector {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) (x : Site) :
    incompleteLazyBlockSum a (completedRunsFromVector labels v)
        (v (Fin.last q)) x =
      listBlockSum (stoppedExternalBasesFrom a (List.ofFn labels))
        (List.ofFn v) x := by
  rw [completedRunsFromVector]
  rw [ofFn_pair_eq_zip]
  rw [incompleteLazyBlockSum_zip a (List.ofFn labels)
    (List.ofFn fun i : Fin q ↦ v i.castSucc) (v (Fin.last q))
    (by simp) x]
  rw [values_castSucc_append_last]

def stoppedExternalLocalTimeFrom {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) (x : Site) : ℕ :=
  List.count x (a :: reconstructExternalTail a (List.ofFn labels))

def stoppedExternalLeft {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) :
    StoppedExternalBase a labels → ℕ :=
  fun b ↦ stoppedExternalLocalTimeFrom a labels b.1

def stoppedExternalRight {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair) :
    StoppedExternalBase a labels → ℕ :=
  fun b ↦ stoppedExternalLocalTimeFrom a labels (b.1 + paperE1)

theorem chessEven_of_mem_stoppedExternalBasesFrom
    (a : Site) (labels : List IncrementPair) (x : Site)
    (ha : HLOZPairing.chessEven a)
    (hx : x ∈ stoppedExternalBasesFrom a labels) :
    HLOZPairing.chessEven x := by
  induction labels generalizing a with
  | nil =>
      simp only [stoppedExternalBasesFrom, List.mem_singleton] at hx
      simpa [hx] using ha
  | cons p labels ih =>
      simp only [stoppedExternalBasesFrom, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ha
      · exact ih (pairEndpoint a p)
          ((chessEven_pairEndpoint_iff a p).mpr ha) hx

theorem stoppedExternalBase_chessEven {q : ℕ}
    (labels : Fin q → IncrementPair)
    (b : StoppedExternalBase (0, 0) labels) :
    HLOZPairing.chessEven b.1 := by
  apply chessEven_of_mem_stoppedExternalBasesFrom
    (0, 0) (List.ofFn labels) b.1
  · norm_num [HLOZPairing.chessEven]
  · simpa only [stoppedExternalBaseSet, List.mem_toFinset] using b.2

theorem localTime_reconstructedStoppedPrefix {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (x : Site) :
    localTime
        (simpleRandomWalk
          (extendPrefix (reconstructedStoppedPrefix labels v).2))
        (reconstructedStoppedPrefix labels v).1 x =
      stoppedExternalLocalTimeFrom (0, 0) labels x +
        incompleteLazyVisitCount (0, 0)
          (completedRunsFromVector labels v) (v (Fin.last q)) x := by
  change localTime
      (simpleRandomWalk
        (extendPrefix (prefixOfDirectionList
          (stoppedDirectionList labels v))))
      (stoppedDirectionList labels v).length x = _
  rw [localTime_extendPrefix_prefixOfDirectionList_eq_count]
  unfold stoppedDirectionList stoppedPairList
  rw [count_incomplete_reconstruction]
  unfold reconstructedExternalLocalTime stoppedExternalLocalTimeFrom
  rw [terminalLabels_completedRunsFromVector]

theorem localTime_reconstructedStoppedPrefix_base {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (b : StoppedExternalBase (0, 0) labels) :
    localTime
        (simpleRandomWalk
          (extendPrefix (reconstructedStoppedPrefix labels v).2))
        (reconstructedStoppedPrefix labels v).1 b.1 =
      stoppedExternalLeft (0, 0) labels b +
        stoppedPaperBlockSums (0, 0) labels
          (stoppedPaperBlockVector (0, 0) labels v) b := by
  rw [localTime_reconstructedStoppedPrefix]
  rw [incompleteLazyVisitCount_eq_blockSum_base
    (0, 0) (completedRunsFromVector labels v) (v (Fin.last q)) b.1]
  · rw [incompleteLazyBlockSum_completedRunsFromVector]
    rw [listBlockSum_eq_stoppedPaperBlockSums]
    rfl
  · norm_num [HLOZPairing.chessEven]
  · exact stoppedExternalBase_chessEven labels b

theorem localTime_reconstructedStoppedPrefix_partner {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (b : StoppedExternalBase (0, 0) labels) :
    localTime
        (simpleRandomWalk
          (extendPrefix (reconstructedStoppedPrefix labels v).2))
        (reconstructedStoppedPrefix labels v).1 (b.1 + paperE1) =
      stoppedExternalRight (0, 0) labels b +
        stoppedPaperBlockSums (0, 0) labels
          (stoppedPaperBlockVector (0, 0) labels v) b := by
  rw [localTime_reconstructedStoppedPrefix]
  rw [incompleteLazyVisitCount_eq_blockSum_partner
    (0, 0) (completedRunsFromVector labels v) (v (Fin.last q)) b.1]
  · rw [incompleteLazyBlockSum_completedRunsFromVector]
    rw [listBlockSum_eq_stoppedPaperBlockSums]
    rfl
  · norm_num [HLOZPairing.chessEven]
  · exact stoppedExternalBase_chessEven labels b

theorem listBlockSum_eq_zero_of_not_mem {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (x : Site) (hx : x ∉ stoppedExternalBaseSet (0, 0) labels) :
    listBlockSum
        (stoppedExternalBasesFrom (0, 0) (List.ofFn labels))
        (List.ofFn v) x = 0 := by
  let bases := stoppedExternalBasesFrom (0, 0) (List.ofFn labels)
  have hlen : bases.length = q + 1 := by simp [bases]
  let e : Fin bases.length ≃ Fin (q + 1) := finCongr hlen
  have hv : List.ofFn v = List.ofFn (fun i : Fin bases.length ↦ v (e i)) := by
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

theorem localTime_reconstructedStoppedPrefix_offBase {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (x : Site) (hx : x ∉ stoppedExternalBaseSet (0, 0) labels)
    (heven : HLOZPairing.chessEven x) :
    localTime
        (simpleRandomWalk
          (extendPrefix (reconstructedStoppedPrefix labels v).2))
        (reconstructedStoppedPrefix labels v).1 x =
      stoppedExternalLocalTimeFrom (0, 0) labels x := by
  rw [localTime_reconstructedStoppedPrefix]
  rw [incompleteLazyVisitCount_eq_blockSum_base
    (0, 0) (completedRunsFromVector labels v) (v (Fin.last q)) x]
  · rw [incompleteLazyBlockSum_completedRunsFromVector,
      listBlockSum_eq_zero_of_not_mem labels v x hx, add_zero]
  · norm_num [HLOZPairing.chessEven]
  · exact heven

theorem localTime_reconstructedStoppedPrefix_offBase_partner {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (x : Site) (hx : x ∉ stoppedExternalBaseSet (0, 0) labels)
    (heven : HLOZPairing.chessEven x) :
    localTime
        (simpleRandomWalk
          (extendPrefix (reconstructedStoppedPrefix labels v).2))
        (reconstructedStoppedPrefix labels v).1 (x + paperE1) =
      stoppedExternalLocalTimeFrom (0, 0) labels (x + paperE1) := by
  rw [localTime_reconstructedStoppedPrefix]
  rw [incompleteLazyVisitCount_eq_blockSum_partner
    (0, 0) (completedRunsFromVector labels v) (v (Fin.last q)) x]
  · rw [incompleteLazyBlockSum_completedRunsFromVector,
      listBlockSum_eq_zero_of_not_mem labels v x hx, add_zero]
  · norm_num [HLOZPairing.chessEven]
  · exact heven

/-- The portion of the mixed condition on horizontal dominoes which never
occur as pair-boundary bases in the fixed external label path.  It is static:
no holding-run coordinate occurs in it. -/
def UnprimedEvenOffBaseMixedCondition {q : ℕ}
    (labels : Fin q → IncrementPair) (m : ℕ) (C : Finset Site) : Prop :=
  ∀ x, HLOZPairing.chessEven x →
    x ∉ stoppedExternalBaseSet (0, 0) labels →
      if _hC : x ∈ C ∨ x + paperE1 ∈ C then
        max (stoppedExternalLocalTimeFrom (0, 0) labels x)
            (stoppedExternalLocalTimeFrom (0, 0) labels (x + paperE1)) = m ∧
          (stoppedExternalLocalTimeFrom (0, 0) labels x = m ↔ x ∈ C) ∧
          (stoppedExternalLocalTimeFrom (0, 0) labels (x + paperE1) = m ↔
            x + paperE1 ∈ C)
      else
        max (stoppedExternalLocalTimeFrom (0, 0) labels x)
          (stoppedExternalLocalTimeFrom (0, 0) labels (x + paperE1)) < m

/-- Exact deterministic mixed-event connector for the genuine unfinished
`q+1` unprimed-even stopped vector.  The global horizontal-domino condition
is the conjunction of the static off-base profile and the grouped block-sum
event. -/
theorem mixedX1DominoCondition_reconstructedStoppedPrefix_iff {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (m : ℕ) (C : Finset Site) :
    MixedX1DominoCondition
        (simpleRandomWalk
          (extendPrefix (reconstructedStoppedPrefix labels v).2))
        (reconstructedStoppedPrefix labels v).1 m C ↔
      HLOZPairing.PairFree
          (HLOZPairing.XPair HLOZPairing.east) C ∧
        UnprimedEvenOffBaseMixedCondition labels m C ∧
        stoppedPaperBlockSums (0, 0) labels
            (stoppedPaperBlockVector (0, 0) labels v) ∈
          stoppedMixedBlockSumEvent (0, 0) labels m C
            (stoppedExternalLeft (0, 0) labels)
            (stoppedExternalRight (0, 0) labels) := by
  constructor
  · rintro ⟨hfree, hmix⟩
    refine ⟨hfree, ?_, ?_⟩
    · intro x hxEven hxOff
      specialize hmix x hxEven
      rw [localTime_reconstructedStoppedPrefix_offBase labels v x hxOff hxEven,
        localTime_reconstructedStoppedPrefix_offBase_partner
          labels v x hxOff hxEven] at hmix
      exact hmix
    · intro b
      specialize hmix b.1 (stoppedExternalBase_chessEven labels b)
      rw [localTime_reconstructedStoppedPrefix_base labels v b,
        localTime_reconstructedStoppedPrefix_partner labels v b] at hmix
      exact hmix
  · rintro ⟨hfree, hoff, hblocks⟩
    refine ⟨hfree, ?_⟩
    intro x hxEven
    by_cases hxBase : x ∈ stoppedExternalBaseSet (0, 0) labels
    · let b : StoppedExternalBase (0, 0) labels := ⟨x, hxBase⟩
      have hb := hblocks b
      rw [localTime_reconstructedStoppedPrefix_base labels v b,
        localTime_reconstructedStoppedPrefix_partner labels v b]
      exact hb
    · have hx := hoff x hxEven hxBase
      rw [localTime_reconstructedStoppedPrefix_offBase labels v x hxBase hxEven,
        localTime_reconstructedStoppedPrefix_offBase_partner
          labels v x hxBase hxEven]
      exact hx

/-- A mixed profile whose current site is one of exactly `k` level-`m`
sites is attained at the first `k`-site threshold, not merely after it. -/
theorem firstKSitesReachLevel_eq_of_mixed_current_mem
    (s : ℕ → Site) (T m k : ℕ) (C : Finset Site)
    (hm : 0 < m) (hcard : C.card = k)
    (hmix : MixedX1DominoCondition s T m C)
    (hcurrent : s T ∈ C) :
    firstKSitesReachLevel m k s = T := by
  have hlevels :=
    (mixedX1DominoCondition_iff_level_sets s T m C hm hmix.1).mp hmix
  rcases hlevels with ⟨hlevel, hplus⟩
  have hcurrentLevel : s T ∈ sitesAtLeastLevel s T m := by
    rw [hlevel]
    exact hcurrent
  have hcurrentVisited : s T ∈ visitedSites s T :=
    (Finset.mem_filter.mp hcurrentLevel).1
  have hcurrentGe : m ≤ localTime s T (s T) :=
    (Finset.mem_filter.mp hcurrentLevel).2
  have hcurrentLt : localTime s T (s T) < m + 1 := by
    by_contra hnot
    have hmem : s T ∈ sitesAtLeastLevel s T (m + 1) :=
      Finset.mem_filter.mpr ⟨hcurrentVisited, by omega⟩
    rw [hplus] at hmem
    simp at hmem
  have hcurrentEq : localTime s T (s T) = m := by omega
  have htarget : (sitesAtLeastLevel s T m).card ∈ Set.Ici k := by
    rw [hlevel, hcard]
    change k ≤ k
    exact le_rfl
  have hupper : firstKSitesReachLevel m k s ≤ (T : WithTop ℕ) := by
    exact hittingAfter_le_of_mem (Nat.zero_le T) htarget
  have hfinite : firstKSitesReachLevel m k s ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (WithTop.coe_ne_top : (T : WithTop ℕ) ≠ ⊤) hupper
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hfinite
  have hrT : r ≤ T := by
    exact WithTop.coe_le_coe.mp (hr.trans_le hupper)
  have huntop : (firstKSitesReachLevel m k s).untopA = r := by
    rw [← hr]
    rfl
  have hrmem : (sitesAtLeastLevel s r m).card ∈ Set.Ici k := by
    have h := hittingAfter_mem_set_of_ne_top
      (u := fun n s ↦ (sitesAtLeastLevel s n m).card)
      (s := Set.Ici k) (n := 0) (ω := s) hfinite
    change (sitesAtLeastLevel s
      (firstKSitesReachLevel m k s).untopA m).card ∈ Set.Ici k at h
    rwa [huntop] at h
  have hTr : T ≤ r := by
    by_contra hnot
    have hrlt : r < T := Nat.lt_of_not_ge hnot
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0)
    have hrt : r ≤ t := by omega
    have hprev : localTime s t (s (t + 1)) + 1 = m := by
      rw [← hcurrentEq]
      rw [localTime_succ, if_pos rfl]
    have hsub : sitesAtLeastLevel s r m ⊆ C.erase (s (t + 1)) := by
      intro x hx
      have hxT := sitesAtLeastLevel_mono_time (s := s) (m := m)
        (hrT) hx
      have hxC : x ∈ C := by
        rw [← hlevel]
        exact hxT
      refine Finset.mem_erase.mpr ⟨?_, hxC⟩
      intro hxeq
      subst x
      have hxr : m ≤ localTime s r (s (t + 1)) :=
        (Finset.mem_filter.mp hx).2
      have hmono := localTime_mono (s := s) hrt (s (t + 1))
      omega
    have hcardErase : (C.erase (s (t + 1))).card = k - 1 := by
      rw [Finset.card_erase_of_mem hcurrent, hcard]
    have hle := Finset.card_le_card hsub
    have hkpos : 0 < k := by
      rw [← hcard]
      exact Finset.card_pos.mpr ⟨s (t + 1), hcurrent⟩
    have hge : k ≤ (sitesAtLeastLevel s r m).card := hrmem
    omega
  have hre : r = T := Nat.le_antisymm hrT hTr
  exact hr.symm.trans (WithTop.coe_eq_coe.mpr hre)

def terminalBase : Site → List IncrementPair → Site
  | a, [] => a
  | a, p :: labels => terminalBase (pairEndpoint a p) labels

theorem terminalBase_append (a : Site)
    (labels more : List IncrementPair) :
    terminalBase a (labels ++ more) =
      terminalBase (terminalBase a labels) more := by
  induction labels generalizing a with
  | nil => rfl
  | cons p labels ih => exact ih (pairEndpoint a p)

theorem terminalBase_replicate_distinguished (a : Site) (t : ℕ) :
    terminalBase a (List.replicate t distinguishedIncrementPair) = a := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [List.replicate_succ, terminalBase,
        pairEndpoint_distinguished]
      exact ih

theorem terminalBase_expandPairRuns (a : Site) (runs : List PairRun) :
    terminalBase a (expandPairRuns runs) = runFinalBase a runs := by
  induction runs generalizing a with
  | nil => rfl
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      simp only [expandPairRuns, runFinalBase]
      rw [terminalBase_append, terminalBase_replicate_distinguished]
      simp only [terminalBase]
      exact ih (pairEndpoint a p)

theorem terminalBase_completedRunsFromVector {q : ℕ}
    (a : Site) (labels : Fin q → IncrementPair)
    (v : Fin (q + 1) → ℕ) :
    runFinalBase a (completedRunsFromVector labels v) =
      terminalBase a (List.ofFn labels) := by
  unfold completedRunsFromVector
  induction q generalizing a with
  | zero => rfl
  | succ q ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      simp only [runFinalBase, terminalBase]
      simpa using ih (pairEndpoint a (labels 0))
        (fun i ↦ labels i.succ) (fun i ↦ v i.succ)

theorem foldl_flattenPairs_terminalBase
    (a : Site) (pairs : List IncrementPair) :
    (flattenPairs pairs).foldl
        (fun x d ↦ x + directionStep d) a =
      terminalBase a pairs := by
  induction pairs generalizing a with
  | nil => rfl
  | cons p pairs ih =>
      simp only [flattenPairs, terminalBase]
      change (flattenPairs pairs).foldl
          (fun x d ↦ x + directionStep d) (pairEndpoint a p) = _
      exact ih (pairEndpoint a p)

def stoppedTerminalBase {q : ℕ}
    (labels : Fin q → IncrementPair) : Site :=
  terminalBase (0, 0) (List.ofFn labels)

theorem reconstructedStoppedPrefix_current {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ) :
    simpleRandomWalk
        (extendPrefix (reconstructedStoppedPrefix labels v).2)
        (reconstructedStoppedPrefix labels v).1 =
      stoppedTerminalBase labels := by
  let ds := stoppedDirectionList labels v
  have hwalk := foldl_directionPrefix_eq_walk
    (extendPrefix (prefixOfDirectionList ds)) ds.length
  rw [directionPrefix_extendPrefix_prefixOfDirectionList] at hwalk
  change simpleRandomWalk (extendPrefix (prefixOfDirectionList ds))
      ds.length = stoppedTerminalBase labels
  rw [← hwalk]
  unfold ds stoppedDirectionList stoppedPairList
  rw [foldl_flattenPairs_terminalBase, terminalBase_append,
    terminalBase_replicate_distinguished,
    terminalBase_expandPairRuns,
    terminalBase_completedRunsFromVector]
  rfl

theorem mem_stoppedRunVectorBox_of_mem_mixedBlockSumEvent {q : ℕ}
    (labels : Fin q → IncrementPair) (v : Fin (q + 1) → ℕ)
    (m : ℕ) (C : Finset Site)
    (externalLeft externalRight :
      StoppedExternalBase (0, 0) labels → ℕ)
    (hblocks : stoppedPaperBlockSums (0, 0) labels
        (stoppedPaperBlockVector (0, 0) labels v) ∈
      stoppedMixedBlockSumEvent (0, 0) labels m C
        externalLeft externalRight) :
    v ∈ stoppedRunVectorBox q m := by
  classical
  unfold stoppedRunVectorBox
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_range]
  let b : StoppedExternalBase (0, 0) labels :=
    ⟨stoppedExternalBaseAt (0, 0) labels i,
      stoppedExternalBaseAt_mem (0, 0) labels i⟩
  have hcoord := stoppedPaperBlockVector_coordinate_le_sum
    (0, 0) labels v i
  have hb := hblocks b
  split at hb
  · have hsum : stoppedPaperBlockSums (0, 0) labels
        (stoppedPaperBlockVector (0, 0) labels v) b ≤ m := by
      have hleft : stoppedPaperBlockSums (0, 0) labels
          (stoppedPaperBlockVector (0, 0) labels v) b ≤
          externalLeft b + stoppedPaperBlockSums (0, 0) labels
            (stoppedPaperBlockVector (0, 0) labels v) b :=
        Nat.le_add_left _ _
      have hmax := le_max_left
        (externalLeft b + stoppedPaperBlockSums (0, 0) labels
          (stoppedPaperBlockVector (0, 0) labels v) b)
        (externalRight b + stoppedPaperBlockSums (0, 0) labels
          (stoppedPaperBlockVector (0, 0) labels v) b)
      exact hleft.trans (hmax.trans_eq hb.1)
    change v i < m + 1
    exact lt_of_le_of_lt (hcoord.trans hsum) (Nat.lt_succ_self m)
  · have hsum : stoppedPaperBlockSums (0, 0) labels
        (stoppedPaperBlockVector (0, 0) labels v) b < m := by
      have hleft : stoppedPaperBlockSums (0, 0) labels
          (stoppedPaperBlockVector (0, 0) labels v) b ≤
          externalLeft b + stoppedPaperBlockSums (0, 0) labels
            (stoppedPaperBlockVector (0, 0) labels v) b :=
        Nat.le_add_left _ _
      have hmax := le_max_left
        (externalLeft b + stoppedPaperBlockSums (0, 0) labels
          (stoppedPaperBlockVector (0, 0) labels v) b)
        (externalRight b + stoppedPaperBlockSums (0, 0) labels
          (stoppedPaperBlockVector (0, 0) labels v) b)
      exact hleft.trans_lt (hmax.trans_lt hb)
    change v i < m + 1
    exact (hcoord.trans_lt hsum).trans (Nat.lt_succ_self m)

/-- The mixed source vector constraint is exactly the pullback of the
grouped block-sum event once the fixed external-label path satisfies its
static off-base part.  The coordinate box is redundant because every mixed
block bounds each nonnegative run coordinate by `m`. -/
theorem unprimedEvenSourceConstraint_eq_mixedBlockPreimage {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : UnprimedEvenOffBaseMixedCondition labels m C) :
    (unprimedEvenSourceConstraint m k C labels :
        Set (Fin (q + 1) → ℕ)) =
      (fun v ↦ stoppedPaperBlockSums (0, 0) labels
        (stoppedPaperBlockVector (0, 0) labels v)) ⁻¹'
        stoppedMixedBlockSumEvent (0, 0) labels m C
          (stoppedExternalLeft (0, 0) labels)
          (stoppedExternalRight (0, 0) labels) := by
  ext v
  change v ∈ unprimedEvenSourceConstraint m k C labels ↔ _
  simp only [unprimedEvenSourceConstraint, mixedPrefixConstraint,
    Finset.mem_filter]
  constructor
  · rintro ⟨_, hmixed⟩
    exact (mixedX1DominoCondition_reconstructedStoppedPrefix_iff
      labels v m C).mp hmixed |>.2.2
  · intro hblocks
    refine ⟨mem_stoppedRunVectorBox_of_mem_mixedBlockSumEvent
      labels v m C _ _ hblocks, ?_⟩
    exact (mixedX1DominoCondition_reconstructedStoppedPrefix_iff
      labels v m C).mpr ⟨hfree, hoff, hblocks⟩

/-- Under the literal source cardinality and terminal-creation-site facts,
the first-hit filter in `actualAdmissibleStoppedVectors` is automatic.
Consequently this is the exact `hGroupedEvent` needed by the stopped map-law:
there is no caller-supplied reconstruction equality left. -/
theorem actualAdmissible_unprimedEvenSourceConstraint_eq_mixedBlockPreimage
    {q : ℕ}
    (m k : ℕ) (C : Finset Site) (labels : Fin q → IncrementPair)
    (hm : 0 < m) (hcard : C.card = k)
    (hfree : HLOZPairing.PairFree
      (HLOZPairing.XPair HLOZPairing.east) C)
    (hoff : UnprimedEvenOffBaseMixedCondition labels m C)
    (hterminal : stoppedTerminalBase labels ∈ C) :
    (actualAdmissibleStoppedVectors m k labels
        (unprimedEvenSourceConstraint m k C labels) :
      Set (Fin (q + 1) → ℕ)) =
      (fun v ↦ stoppedPaperBlockSums (0, 0) labels
        (stoppedPaperBlockVector (0, 0) labels v)) ⁻¹'
        stoppedMixedBlockSumEvent (0, 0) labels m C
          (stoppedExternalLeft (0, 0) labels)
          (stoppedExternalRight (0, 0) labels) := by
  ext v
  rw [← unprimedEvenSourceConstraint_eq_mixedBlockPreimage
    m k C labels hfree hoff]
  change v ∈ actualAdmissibleStoppedVectors m k labels
      (unprimedEvenSourceConstraint m k C labels) ↔
    v ∈ unprimedEvenSourceConstraint m k C labels
  simp only [actualAdmissibleStoppedVectors, Finset.mem_filter]
  constructor
  · exact fun h ↦ h.1
  · intro hv
    refine ⟨hv, ?_⟩
    have hmixed : MixedX1DominoCondition
        (simpleRandomWalk
          (extendPrefix (reconstructedStoppedPrefix labels v).2))
        (reconstructedStoppedPrefix labels v).1 m C := by
      apply (mixedX1DominoCondition_reconstructedStoppedPrefix_iff
        labels v m C).mpr
      refine ⟨hfree, hoff, ?_⟩
      have heq := unprimedEvenSourceConstraint_eq_mixedBlockPreimage
        m k C labels hfree hoff
      have hvSet : v ∈
          (unprimedEvenSourceConstraint m k C labels :
            Set (Fin (q + 1) → ℕ)) := hv
      rw [heq] at hvSet
      exact hvSet
    have hcurrent : simpleRandomWalk
        (extendPrefix (reconstructedStoppedPrefix labels v).2)
        (reconstructedStoppedPrefix labels v).1 ∈ C := by
      rw [reconstructedStoppedPrefix_current]
      exact hterminal
    exact firstKSitesReachLevel_eq_of_mixed_current_mem
      (simpleRandomWalk
        (extendPrefix (reconstructedStoppedPrefix labels v).2))
      (reconstructedStoppedPrefix labels v).1 m k C
      hm hcard hmixed hcurrent

end Erdos1166.HLOZStoppedMixedReconstruction
