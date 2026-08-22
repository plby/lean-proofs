/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularRadialProfileWords
import ErdosProblems.Erdos1165.AnnularSpatialSpliceKernelDefs
import ErdosProblems.Erdos1165.AnnularSpatialSpliceMembership
import ErdosProblems.Erdos1165.AnnularProfileLiteralAtoms
import ErdosProblems.Erdos1165.PoissonKernelGreenPole

/-!
# Pathwise interpretation of the spatially spliced radial chain

The kernel calculation in `AnnularRadialSplicedChain` is deliberately made
in coordinates centred at the candidate point.  This file supplies the
missing pathwise half of that construction.  In particular, it keeps the
random endpoint at which the chronological radial word first reaches level
zero and identifies the fresh final factor at exactly that stopping time.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace Erdos1165.AnnularRadialSplicedPathwise

open AnnularRadialLabelWord AnnularRadialProfileWords
  AppendixFirstMoment
  AnnularRadialSplicedChain AnnularSpatialSplice
  AnnularProfileLiteralAtoms
  AnnularSpatialSpliceKernelDefs AnnularSpatialSpliceMembership
  BoundaryStoppedHarnack MarkedBoundaryVisitKernel PlanarPotential
  MarkedBridgeFactorization
  PotentialEuclideanGeometry Proposition13Assembly
  Proposition13Measurability TerminalExcursionBridge
  TerminalSequentialVisitLaw TerminalSpliceProfileGeometry ThickPoint
  TerminalBoundaryScan

noncomputable section

private theorem trajectoryFrom_shiftSteps_eq_absolute
    (start : Point) (omega : StepPath) (t q : ℕ) :
    trajectoryFrom (trajectoryFrom start omega t) (shiftSteps t omega) q =
      trajectoryFrom start omega (t + q) := by
  unfold trajectoryFrom
  rw [← trajectory_add_sub_trajectory omega t q]
  abel

private theorem shiftSteps_add' (omega : StepPath) (a b : ℕ) :
    shiftSteps b (shiftSteps a omega) = shiftSteps (a + b) omega := by
  funext q
  simp only [shiftSteps]
  congr 1
  omega

private theorem absoluteBoundaryFirstAt_concat
    {boundary : Set Point} {start point : Point} {omega : StepPath}
    {t q : ℕ} (hbefore : ∀ r < t,
      trajectoryFrom start omega r ∉ boundary)
    (hpoint : trajectoryFrom start omega t = point)
    (htail : AbsoluteBoundaryFirstAt boundary point
      (shiftSteps t omega) q) :
    AbsoluteBoundaryFirstAt boundary start omega (t + q) := by
  constructor
  · rw [← trajectoryFrom_shiftSteps_eq_absolute start omega t q, hpoint]
    exact htail.1
  · intro r hr
    by_cases hrt : r < t
    · exact hbefore r hrt
    · have htr : t ≤ r := Nat.le_of_not_gt hrt
      rw [← Nat.add_sub_of_le htr,
        ← trajectoryFrom_shiftSteps_eq_absolute, hpoint]
      exact htail.2 (r - t) (by omega)

/-- Forgetting the fresh final factor leaves the ordinary chronological
radial-chain event. -/
theorem radialChainFinalAtom_subset_radialChainAtom
    (n : ℕ) (center : Point) (final : Point → Set StepPath) :
    ∀ source targets start,
      radialChainFinalAtom n center final source targets start ⊆
        radialChainAtom n center source targets start := by
  intro source targets
  induction targets generalizing source with
  | nil =>
      intro start omega _
      simp [radialChainAtom]
  | cons target tail ih =>
      intro start omega homega
      rw [radialChainFinalAtom] at homega
      obtain ⟨endpoint, hstep, htail⟩ := Set.mem_iUnion.mp homega
      rw [radialChainAtom]
      refine Set.mem_iUnion.mpr ⟨endpoint, hstep, ?_⟩
      change postWithTopStoppingSteps
        (boundaryExitTime (otherRadialBoundaries n center source) start)
          omega ∈ radialChainAtom n center target tail endpoint.1
      exact ih target endpoint.1 htail

/-- The endpoint-dependent fresh factor in a chain ending at level zero is
seen immediately after the literal first level-zero hit. -/
private theorem final_after_firstZero_of_mem
    (n : ℕ) (center : Point) (final : Point → Set StepPath) :
    ∀ (source : Fin (n + 2)) (beforeZero : List (Fin (n + 2)))
      (start : Point) (omega : StepPath),
      (⟨0, by omega⟩ : Fin (n + 2)) ∉ source :: beforeZero →
      omega ∈ radialChainFinalAtom n center final source
        (beforeZero ++ [⟨0, by omega⟩]) start →
      ∃ horizon : ℕ,
        AbsoluteBoundaryFirstAt
          (radialBoundary n center ⟨0, by omega⟩) start omega horizon ∧
        shiftSteps horizon omega ∈
          final (trajectoryFrom start omega horizon) := by
  intro source beforeZero
  induction beforeZero generalizing source with
  | nil =>
      intro start omega hnozero homega
      change omega ∈ radialChainFinalAtom n center final source
        [⟨0, by omega⟩] start at homega
      rw [radialChainFinalAtom] at homega
      obtain ⟨endpoint, hstep, htail⟩ := Set.mem_iUnion.mp homega
      obtain ⟨t, hfirst, hpoint⟩ :=
        (mem_boundaryExitMarkedSteps_iff_exists_first _ _ _ _).1 hstep
      have hpointEq : trajectoryFrom start omega t = endpoint.1 := by
        simpa only [Set.mem_singleton_iff] using hpoint
      have htime := boundaryExitTime_eq_of_absoluteBoundaryFirstAt hfirst
      have hpost := postWithTopStoppingSteps_eq_shiftSteps_of_eq htime
      change postWithTopStoppingSteps
        (boundaryExitTime (otherRadialBoundaries n center source) start)
          omega ∈ final endpoint.1 at htail
      rw [hpost] at htail
      refine ⟨t, ?_, ?_⟩
      · constructor
        · rw [hpointEq]
          exact endpoint.2
        · intro r hr hzero
          apply hfirst.2 r hr
          rw [otherRadialBoundaries]
          refine Set.mem_iUnion.mpr ⟨⟨0, by omega⟩, ?_⟩
          rw [if_neg]
          · exact hzero
          · simpa using hnozero
      · simpa only [hpointEq] using htail
  | cons target tail ih =>
      intro start omega hnozero homega
      change omega ∈ radialChainFinalAtom n center final source
        (target :: (tail ++ [⟨0, by omega⟩])) start at homega
      rw [radialChainFinalAtom] at homega
      obtain ⟨endpoint, hstep, htail⟩ := Set.mem_iUnion.mp homega
      obtain ⟨t, hfirst, hpoint⟩ :=
        (mem_boundaryExitMarkedSteps_iff_exists_first _ _ _ _).1 hstep
      have hpointEq : trajectoryFrom start omega t = endpoint.1 := by
        simpa only [Set.mem_singleton_iff] using hpoint
      have htime := boundaryExitTime_eq_of_absoluteBoundaryFirstAt hfirst
      have hpost := postWithTopStoppingSteps_eq_shiftSteps_of_eq htime
      change postWithTopStoppingSteps
        (boundaryExitTime (otherRadialBoundaries n center source) start)
          omega ∈ radialChainFinalAtom n center final target
            (tail ++ [⟨0, by omega⟩]) endpoint.1 at htail
      rw [hpost] at htail
      have hparts :
          (⟨0, by omega⟩ : Fin (n + 2)) ≠ source ∧
          (⟨0, by omega⟩ : Fin (n + 2)) ∉ target :: tail := by
        simpa using hnozero
      obtain ⟨q, htailFirst, hfinal⟩ := ih target endpoint.1
        (shiftSteps t omega) hparts.2 htail
      refine ⟨t + q, absoluteBoundaryFirstAt_concat ?_ hpointEq htailFirst, ?_⟩
      · intro r hr hzero
        apply hfirst.2 r hr
        rw [otherRadialBoundaries]
        refine Set.mem_iUnion.mpr ⟨⟨0, by omega⟩, ?_⟩
        rw [if_neg hparts.1]
        exact hzero
      · rw [← shiftSteps_add']
        have hposition : trajectoryFrom start omega (t + q) =
            trajectoryFrom endpoint.1 (shiftSteps t omega) q := by
          rw [← hpointEq, trajectoryFrom_shiftSteps_eq_absolute]
        rwa [hposition]

/-- A chain with a fresh final factor produces, at one and the same stopping
time, the first level-zero certificate, the exact chronological trace, and
the fresh suffix event. -/
theorem radialChainFinalAtom_pathwise
    {n : ℕ} (hn : 2 ≤ n) (center : Point)
    (final : Point → Set StepPath)
    (source : Fin (n + 2)) (beforeZero : List (Fin (n + 2)))
    (start : Point)
    (hchain : List.IsChain
      (fun left right : Fin (n + 2) ↦ left ≠ right)
      (source :: beforeZero ++ [⟨0, by omega⟩]))
    (hnozero : (⟨0, by omega⟩ : Fin (n + 2)) ∉ source :: beforeZero)
    (hstart : start ∈ radialBoundary n center source) :
    ∀ {omega : StepPath},
      omega ∈ radialChainFinalAtom n center final source
          (beforeZero ++ [⟨0, by omega⟩]) start →
      ∃ horizon : ℕ,
        AbsoluteBoundaryFirstAt
          (radialBoundary n center ⟨0, by omega⟩) start omega horizon ∧
        chronologicalRadialLabels n center
          (fun r ↦ trajectoryFrom start omega r) horizon =
            source :: beforeZero ++ [⟨0, by omega⟩] ∧
        shiftSteps horizon omega ∈
          final (trajectoryFrom start omega horizon) := by
  intro omega homega
  obtain ⟨finalHorizon, hfinalFirst, hfinal⟩ :=
    final_after_firstZero_of_mem n center final source beforeZero
      start omega hnozero homega
  have hchainMem : omega ∈ radialChainAtom n center source
      (beforeZero ++ [⟨0, by omega⟩]) start :=
    radialChainFinalAtom_subset_radialChainAtom n center final
      source _ start homega
  rw [radialChainAtom_eq_firstZeroTraceEvent hn center start source beforeZero
    hchain hnozero hstart] at hchainMem
  obtain ⟨traceHorizon, htraceFirst, htrace⟩ := hchainMem
  have heq : traceHorizon = finalHorizon :=
    absoluteBoundaryFirstAt_unique htraceFirst hfinalFirst
  subst traceHorizon
  exact ⟨finalHorizon, hfinalFirst, htrace, hfinal⟩

/-- Chronological radial word with the endpoint-dependent fresh factor. -/
def radialWordChainFinalAtom {n L : ℕ} (center start : Point)
    (final : Point → Set StepPath) (word : RadialLabelWord n L) :
    Set StepPath :=
  radialChainFinalAtom n center final (word.level ⟨0, by omega⟩)
    word.toList.tail start

/-- Word-specialized pathwise extraction. -/
theorem radialWordChainFinalAtom_pathwise
    {n L : ℕ} (hn : 2 ≤ n) (center start : Point)
    (final : Point → Set StepPath) (word : RadialLabelWord n L)
    (hstart : start ∈ radialBoundary n center ⟨1, by omega⟩) :
    ∀ {omega : StepPath},
      omega ∈ radialWordChainFinalAtom center start final word →
      ∃ horizon : ℕ,
        AbsoluteBoundaryFirstAt
          (radialBoundary n center ⟨0, by omega⟩) start omega horizon ∧
        chronologicalRadialLabels n center
          (fun r ↦ trajectoryFrom start omega r) horizon = word.toList ∧
        shiftSteps horizon omega ∈
          final (trajectoryFrom start omega horizon) := by
  classical
  intro omega homega
  have hLpos : 0 < L := by
    by_contra hnot
    have hLzero : L = 0 := by omega
    subst L
    have hindex : (⟨0, by omega⟩ : Fin (0 + 1)) = Fin.last 0 := by ext <;> rfl
    have hlevel := congrArg word.level hindex
    have : (⟨1, by omega⟩ : Fin (n + 2)) = ⟨0, by omega⟩ := by
      rw [← word.startsAtOne, hlevel, word.endsAtZero]
    have hval := congrArg Fin.val this
    norm_num at hval
  let source : Fin (n + 2) := word.level ⟨0, by omega⟩
  let targets : List (Fin (n + 2)) := word.toList.tail
  have hlist : word.toList = source ::
      List.ofFn (fun j : Fin L ↦ word.level j.succ) := by
    simp [RadialLabelWord.toList, List.ofFn_succ, source]
  have htargets : targets =
      List.ofFn (fun j : Fin L ↦ word.level j.succ) := by
    change word.toList.tail = _
    rw [hlist]
    rfl
  have hlistTargets : word.toList = source :: targets :=
    hlist.trans (congrArg (source :: ·) htargets.symm)
  have htargetsNe : targets ≠ [] := by
    intro hnil
    have hlength := congrArg List.length htargets
    rw [hnil] at hlength
    simp only [List.length_nil, List.length_ofFn] at hlength
    omega
  have hlast : targets.getLast htargetsNe = ⟨0, by omega⟩ := by
    have hfnNe : List.ofFn (fun j : Fin L ↦ word.level j.succ) ≠ [] := by
      intro hnil
      have hlength := congrArg List.length hnil
      simp only [List.length_ofFn, List.length_nil] at hlength
      omega
    calc
      targets.getLast htargetsNe =
          (List.ofFn (fun j : Fin L ↦ word.level j.succ)).getLast hfnNe :=
        List.getLast_congr htargetsNe hfnNe htargets
      _ = ⟨0, by omega⟩ := by
        rw [List.getLast_ofFn]
        have hindex : (⟨L - 1, by omega⟩ : Fin L).succ = Fin.last L := by
          ext
          simp only [Fin.succ_mk, Fin.val_last]
          omega
        rw [hindex]
        exact word.endsAtZero
  have hsplit : targets.dropLast ++ [⟨0, by omega⟩] = targets := by
    have h := List.dropLast_append_getLast htargetsNe
    rwa [hlast] at h
  have hadjacent : List.IsChain
      (fun left right : Fin (n + 2) ↦ Nat.dist left.val right.val = 1)
      word.toList := by
    rw [RadialLabelWord.toList, List.isChain_ofFn]
    intro i hi
    exact word.adjacent ⟨i, by omega⟩
  have hdifferent : List.IsChain
      (fun left right : Fin (n + 2) ↦ left ≠ right) word.toList :=
    hadjacent.imp (by
      intro left right hdist heq
      subst right
      simp at hdist)
  have hchain : List.IsChain
      (fun left right : Fin (n + 2) ↦ left ≠ right)
      (source :: targets.dropLast ++ [⟨0, by omega⟩]) := by
    simpa only [List.cons_append, hsplit, ← hlistTargets] using hdifferent
  have hdrop : source :: targets.dropLast = word.toList.dropLast := by
    rw [hlistTargets, List.dropLast_cons_of_ne_nil htargetsNe]
  have hnozero : (⟨0, by omega⟩ : Fin (n + 2)) ∉
      source :: targets.dropLast := by
    rw [hdrop]
    intro hmem
    obtain ⟨i, hi⟩ := List.get_of_mem hmem
    have hiLt : i.val < word.toList.dropLast.length := i.isLt
    have hiWord : word.toList[i.val] = (⟨0, by omega⟩ : Fin (n + 2)) := by
      rw [← List.getElem_dropLast hiLt]
      exact hi
    have hiBound : i.val < L := by
      have hdropLength : word.toList.dropLast.length = L := by
        rw [List.length_dropLast, RadialLabelWord.length_toList]
        omega
      omega
    have hiLevel : word.level ⟨i.val, by omega⟩ =
        (⟨0, by omega⟩ : Fin (n + 2)) := by
      change (List.ofFn word.level)[i.val] = _ at hiWord
      rw [List.getElem_ofFn] at hiWord
      exact hiWord
    exact word.beforeFinal_ne_zero ⟨i.val, hiBound⟩
      (congrArg Fin.val hiLevel)
  have hsource : source = ⟨1, by omega⟩ := word.startsAtOne
  have hstartSource : start ∈ radialBoundary n center source := by
    rw [hsource]
    exact hstart
  change omega ∈ radialChainFinalAtom n center final source targets start at homega
  have homegaSplit : omega ∈ radialChainFinalAtom n center final source
      (targets.dropLast ++ [⟨0, by omega⟩]) start := by
    rwa [hsplit]
  obtain ⟨horizon, hfirst, htrace, hfinal⟩ :=
    radialChainFinalAtom_pathwise hn center final source targets.dropLast start
      hchain hnozero hstartSource homegaSplit
  refine ⟨horizon, hfirst, ?_, hfinal⟩
  simpa only [List.cons_append, hsplit, ← hlistTargets] using htrace

/-! ## The literal three-piece stopped path -/

/-- Initial centred hit, chronological radial word, and final centred escape,
with both random splice points retained. -/
def spatiallySplicedRadialWordAtom {n L : ℕ} (x : Point)
    (word : RadialLabelWord n L) : Set StepPath :=
  spatiallySplicedRadialChainAtom n 0 (-x) (initialSpliceBoundary n)
    ⟨1, by omega⟩ word.toList.tail (finalSpliceEvent n)

/-- Exact three-piece parsing of a spatially spliced radial word. -/
theorem spatiallySplicedRadialWordAtom_pathwise
    {n L : ℕ} (hn : 2 ≤ n) (x : Point) (word : RadialLabelWord n L) :
    ∀ {omega : StepPath}, omega ∈ spatiallySplicedRadialWordAtom x word →
      ∃ (initialTime radialTime finalTime : ℕ) (entrance zeroExit : Point),
        AbsoluteBoundaryFirstAt (initialSpliceBoundary n) (-x) omega
            initialTime ∧
        trajectoryFrom (-x) omega initialTime = entrance ∧
        entrance ∈ radialBoundary n 0 ⟨1, by omega⟩ ∧
        AbsoluteBoundaryFirstAt (radialBoundary n 0 ⟨0, by omega⟩)
          entrance (shiftSteps initialTime omega) radialTime ∧
        trajectoryFrom entrance (shiftSteps initialTime omega) radialTime =
          zeroExit ∧
        chronologicalRadialLabels n 0
          (fun r ↦ trajectoryFrom entrance (shiftSteps initialTime omega) r)
          radialTime = word.toList ∧
        AbsoluteBoundaryFirstAt (finalSpliceBoundary n) zeroExit
          (shiftSteps (initialTime + radialTime) omega) finalTime ∧
        trajectoryFrom zeroExit (shiftSteps (initialTime + radialTime) omega)
          finalTime ∈ discBoundary 0 (32 * scaleRadius n 0) := by
  intro omega homega
  rw [spatiallySplicedRadialWordAtom,
    spatiallySplicedRadialChainAtom] at homega
  obtain ⟨entrancePoint, hinitial, htail⟩ := Set.mem_iUnion.mp homega
  obtain ⟨initialTime, hinitialFirst, hinitialPoint⟩ :=
    (mem_boundaryExitMarkedSteps_iff_exists_first _ _ _ _).1 hinitial
  have hentranceEq : trajectoryFrom (-x) omega initialTime = entrancePoint.1 := by
    simpa only [Set.mem_singleton_iff] using hinitialPoint
  have hinitialClock := boundaryExitTime_eq_of_absoluteBoundaryFirstAt
    hinitialFirst
  have hinitialPost := postWithTopStoppingSteps_eq_shiftSteps_of_eq hinitialClock
  change postWithTopStoppingSteps
    (boundaryExitTime (initialSpliceBoundary n) (-x)) omega ∈
      radialChainFinalAtom n 0 (finalSpliceEvent n) ⟨1, by omega⟩
        word.toList.tail entrancePoint.1 at htail
  rw [hinitialPost] at htail
  have htailWord : shiftSteps initialTime omega ∈
      radialWordChainFinalAtom 0 entrancePoint.1 (finalSpliceEvent n) word := by
    change shiftSteps initialTime omega ∈
      radialChainFinalAtom n 0 (finalSpliceEvent n)
        (word.level ⟨0, by omega⟩) word.toList.tail entrancePoint.1
    simpa only [word.startsAtOne] using htail
  obtain ⟨radialTime, hradialFirst, hradialTrace, hfinal⟩ :=
    radialWordChainFinalAtom_pathwise hn 0 entrancePoint.1
      (finalSpliceEvent n) word entrancePoint.2 htailWord
  let zeroExit : Point := trajectoryFrom entrancePoint.1
    (shiftSteps initialTime omega) radialTime
  have hzero : zeroExit ∈ radialBoundary n 0 ⟨0, by omega⟩ := by
    exact hradialFirst.1
  have hshift : shiftSteps radialTime (shiftSteps initialTime omega) =
      shiftSteps (initialTime + radialTime) omega :=
    shiftSteps_add' omega initialTime radialTime
  have hfinal' : shiftSteps (initialTime + radialTime) omega ∈
      finalSpliceEvent n zeroExit := by
    rw [← hshift]
    exact hfinal
  obtain ⟨finalTime, hfinalFirst, hfinalPoint⟩ :=
    (mem_boundaryExitMarkedSteps_iff_exists_first _ _ _ _).1 hfinal'
  refine ⟨initialTime, radialTime, finalTime, entrancePoint.1, zeroExit,
    hinitialFirst, hentranceEq, entrancePoint.2, hradialFirst, rfl,
    hradialTrace, hfinalFirst, ?_⟩
  simpa [finalSpliceEvent, Set.mem_singleton_iff] using hfinalPoint

/-! ## Compression and entrance/extension geometry -/

private def lastPrevious {Label : Type*}
    (previous : Option Label) : List Label → Option Label
  | [] => previous
  | head :: tail => lastPrevious (some head) tail

private theorem compressLabelsFrom_append
    {Label : Type*} [DecidableEq Label] :
    ∀ (previous : Option Label) (left right : List Label),
      compressLabelsFrom previous (left ++ right) =
        compressLabelsFrom previous left ++
          compressLabelsFrom (lastPrevious previous left) right := by
  intro previous left
  induction left generalizing previous with
  | nil =>
      intro right
      simp [compressLabelsFrom, lastPrevious]
  | cons head tail ih =>
      intro right
      rw [List.cons_append]
      simp only [compressLabelsFrom]
      split
      · rw [ih]
        simp [lastPrevious, *]
      · rw [ih]
        simp [lastPrevious]

private theorem compressLabelsFrom_eq_nil_of_all_eq
    {Label : Type*} [DecidableEq Label] (label : Label) :
    ∀ labels : List Label,
      (∀ z ∈ labels, z = label) →
      compressLabelsFrom (some label) labels = [] := by
  intro labels hall
  induction labels with
  | nil => rfl
  | cons head tail ih =>
      have hhead := hall head (by simp)
      subst head
      simp only [compressLabelsFrom, if_pos rfl]
      exact ih (fun z hz ↦ hall z (by simp [hz]))

private theorem compressLabels_eq_singleton_of_nonempty_all_eq
    {Label : Type*} [DecidableEq Label] {label : Label} {labels : List Label}
    (hnil : labels ≠ []) (hall : ∀ z ∈ labels, z = label) :
    compressLabels labels = [label] := by
  obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil hnil
  have hhead := hall head (by simp)
  subst head
  unfold compressLabels
  simp only [compressLabelsFrom, reduceCtorEq, if_false]
  rw [compressLabelsFrom_eq_nil_of_all_eq label tail]
  exact fun z hz ↦ hall z (by simp [hz])

private theorem compressLabelsFrom_eq_compressLabels_of_head_ne
    {Label : Type*} [DecidableEq Label]
    {previous head : Label} {tail : List Label} (hne : previous ≠ head) :
    compressLabelsFrom (some previous) (head :: tail) =
      compressLabels (head :: tail) := by
  unfold compressLabels
  simp only [compressLabelsFrom, Option.some.injEq, hne, if_false,
    reduceCtorEq]

private theorem range_add_succ_eq_append_shift
    (t q : ℕ) :
    List.range (t + q + 1) =
      List.range t ++ List.map (fun r ↦ t + r) (List.range (q + 1)) := by
  have h := (List.range'_append
    (s := 0) (m := t) (n := q + 1) (step := 1)).symm
  simpa [List.range'_eq_map_range, Nat.add_assoc] using h

private theorem range_add_succ_eq_append_after
    (t q : ℕ) :
    List.range (t + q + 1) =
      List.range (t + 1) ++
        List.map (fun r ↦ t + 1 + r) (List.range q) := by
  have h := (List.range'_append
    (s := 0) (m := t + 1) (n := q) (step := 1)).symm
  simpa [List.range'_eq_map_range, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using h

/-- A nearest-neighbour path starting outside a disc and reaching the disc
has met its literal inner vertex boundary by that time. -/
private theorem exists_discBoundary_at_or_before_entry
    {center start : Point} {radius : ℝ} {omega : StepPath} {N : ℕ}
    (hstart : start ∉ disc center radius)
    (hentry : trajectoryFrom start omega N ∈ disc center radius) :
    ∃ t ≤ N, trajectoryFrom start omega t ∈ discBoundary center radius := by
  classical
  let P : ℕ → Prop := fun t ↦ trajectoryFrom start omega t ∈ disc center radius
  have hP : ∃ t, P t := ⟨N, hentry⟩
  let t := Nat.find hP
  have htMem : trajectoryFrom start omega t ∈ disc center radius :=
    Nat.find_spec hP
  have htN : t ≤ N := Nat.find_min' hP hentry
  have htpos : 0 < t := by
    by_contra hnot
    have htzero : t = 0 := by omega
    rw [htzero] at htMem
    exact hstart (by simpa using htMem)
  let q := t - 1
  have hqt : q < t := by dsimp [q]; omega
  have hqOut : trajectoryFrom start omega q ∉ disc center radius := by
    intro hmem
    exact (Nat.not_le_of_gt hqt) (Nat.find_min' hP hmem)
  have hsucc : q + 1 = t := by dsimp [q]; omega
  refine ⟨t, htN, htMem, trajectoryFrom start omega q, hqOut, ?_⟩
  have hadj := TerminalGlobalExitSplice.adjacent_trajectoryFrom_succ
    start omega q
  rw [hsucc] at hadj
  unfold Adjacent at hadj ⊢
  have hfirst :
      ((trajectoryFrom start omega t).1 -
          (trajectoryFrom start omega q).1).natAbs =
        ((trajectoryFrom start omega q).1 -
          (trajectoryFrom start omega t).1).natAbs := by
    rw [show (trajectoryFrom start omega t).1 -
        (trajectoryFrom start omega q).1 =
      -((trajectoryFrom start omega q).1 -
        (trajectoryFrom start omega t).1) by ring, Int.natAbs_neg]
  have hsecond :
      ((trajectoryFrom start omega t).2 -
          (trajectoryFrom start omega q).2).natAbs =
        ((trajectoryFrom start omega q).2 -
          (trajectoryFrom start omega t).2).natAbs := by
    rw [show (trajectoryFrom start omega t).2 -
        (trajectoryFrom start omega q).2 =
      -((trajectoryFrom start omega q).2 -
        (trajectoryFrom start omega t).2) by ring, Int.natAbs_neg]
  rw [hfirst, hsecond]
  exact hadj

/-- Avoiding a disc's inner boundary keeps a walk that starts in the disc
inside it through the avoidance horizon. -/
private theorem trajectoryFrom_mem_disc_of_avoids_boundary
    {center start : Point} {radius : ℝ} {omega : StepPath} {N : ℕ}
    (hstart : start ∈ disc center radius)
    (havoid : ∀ q < N,
      trajectoryFrom start omega q ∉ discBoundary center radius) :
    ∀ q ≤ N, trajectoryFrom start omega q ∈ disc center radius := by
  intro q hq
  induction q with
  | zero => simpa using hstart
  | succ q ih =>
      have hqN : q < N := by omega
      have hcurrent := ih hqN.le
      by_contra hnext
      exact havoid q hqN
        ⟨hcurrent, trajectoryFrom start omega (q + 1), hnext,
          TerminalGlobalExitSplice.adjacent_trajectoryFrom_succ start omega q⟩

private theorem lastPrevious_eq_some_of_nonempty_all_eq
    {Label : Type*} {previous : Option Label} {label : Label}
    {labels : List Label} (hnil : labels ≠ [])
    (hall : ∀ z ∈ labels, z = label) :
    lastPrevious previous labels = some label := by
  induction labels generalizing previous with
  | nil => simp at hnil
  | cons head tail ih =>
      have hhead := hall head (by simp)
      subst head
      cases tail with
      | nil => rfl
      | cons next rest =>
          apply ih (previous := some label)
          · simp
          · intro z hz
            exact hall z (by simp [hz])

private theorem radialBoundary_subset_disc_one
    {n : ℕ} (hn : 1 ≤ n) (label : Fin (n + 2))
    (hlabel : 1 ≤ (label : ℕ)) :
    radialBoundary n 0 label ⊆ disc 0 (scaleRadius n 1) := by
  intro z hz
  have hzDisc : z ∈ disc 0 (scaleRadius n label) := hz.1
  change latticeDistance 0 z ≤ scaleRadius n 1
  change latticeDistance 0 z ≤ scaleRadius n label at hzDisc
  apply hzDisc.trans
  by_cases hregular : (label : ℕ) ≤ n
  · exact scaleRadius_antitone_of_le hlabel hregular
  · have hterminal : (label : ℕ) = n + 1 := by omega
    rw [hterminal]
    exact (terminalRadius_le_regularRadius_self n hn).trans
      (scaleRadius_antitone_of_le hn le_rfl)

/-- Before the initial level-one entrance, the only possible local radial
label is level zero, and level zero is actually hit. -/
private theorem initial_prefix_labels_are_zero
    {n initialTime : ℕ} (hn : 3 ≤ n) {x entrance : Point}
    (hx : x ∈ candidateBox n) {omega : StepPath}
    (hfirst : AbsoluteBoundaryFirstAt (initialSpliceBoundary n) (-x)
      omega initialTime)
    (hentrance : trajectoryFrom (-x) omega initialTime = entrance)
    (hentranceOne : entrance ∈ radialBoundary n 0 ⟨1, by omega⟩) :
    let rawPrefix := (List.range initialTime).flatMap
      (fun q ↦ radialLabelsAt n 0 (trajectoryFrom (-x) omega q))
    rawPrefix ≠ [] ∧
      ∀ label ∈ rawPrefix, label = (⟨0, by omega⟩ : Fin (n + 2)) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hlarge : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hstartAnnulus := initial_start_mem_annulus hn1 hlarge hx
  have hstartOutsideOne : -x ∉ disc 0 (scaleRadius n 1) :=
    (LiteralRealAnnulus.mem_literalRealAnnulus_raw.mp hstartAnnulus).2.2.2
  have hr1le0 : scaleRadius n 1 ≤ scaleRadius n 0 :=
    scaleRadius_antitone_of_le (by omega) (by omega)
  have hentranceDisc0 : entrance ∈ disc 0 (scaleRadius n 0) :=
    hentranceOne.1.trans hr1le0
  have hgeom := candidate_neg_euclideanRadius_bounds hx
  have hr0pos : 0 < scaleRadius n 0 := by
    have hnRadius : (n : ℝ) ≤ scaleRadius n 1 :=
      natCast_le_scaleRadius_one n hn1
    have : (0 : ℝ) < n := by positivity
    linarith
  have hstartOutsideZero : -x ∉ disc 0 (scaleRadius n 0) := by
    intro hmem
    have hupper : euclideanRadius (-x) ≤ scaleRadius n 0 := by
      simpa [disc, RadialHarnackSpecialization.latticeDistance_zero_eq_euclideanRadius]
        using hmem
    nlinarith
  obtain ⟨zeroTime, hzeroLe, hzero⟩ :=
    exists_discBoundary_at_or_before_entry hstartOutsideZero
      (hentrance ▸ hentranceDisc0)
  have hzeroLt : zeroTime < initialTime := by
    rcases hzeroLe.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      apply Set.disjoint_left.mp
        (radialBoundaries_disjoint_of_ne (by omega) 0
          (show (⟨0, by omega⟩ : Fin (n + 2)) ≠ ⟨1, by omega⟩ by
            intro h
            have hval := congrArg Fin.val h
            norm_num at hval))
        hzero
      rw [heq, hentrance]
      exact hentranceOne
  let rawPrefix := (List.range initialTime).flatMap
    (fun q ↦ radialLabelsAt n 0 (trajectoryFrom (-x) omega q))
  have hzeroMem : (⟨0, by omega⟩ : Fin (n + 2)) ∈ rawPrefix := by
    rw [List.mem_flatMap]
    refine ⟨zeroTime, by simpa using hzeroLt, ?_⟩
    exact mem_radialLabelsAt.mpr hzero
  refine ⟨List.ne_nil_of_mem hzeroMem, ?_⟩
  intro label hlabel
  rw [List.mem_flatMap] at hlabel
  obtain ⟨q, hqRange, hqLabel⟩ := hlabel
  have hqLt : q < initialTime := by simpa using hqRange
  by_contra hne
  have hpos : 1 ≤ (label : ℕ) := by
    have : (label : ℕ) ≠ 0 := by
      intro hz
      apply hne
      exact Fin.ext hz
    omega
  have hinsideOne : trajectoryFrom (-x) omega q ∈
      disc 0 (scaleRadius n 1) :=
    radialBoundary_subset_disc_one hn1 label hpos
      (mem_radialLabelsAt.mp hqLabel)
  obtain ⟨entryTime, hentryLe, hentryBoundary⟩ :=
    exists_discBoundary_at_or_before_entry hstartOutsideOne hinsideOne
  apply hfirst.2 entryTime (hentryLe.trans_lt hqLt)
  rw [initialSpliceBoundary]
  exact Or.inl hentryBoundary

/-- The initial spatial piece prepends exactly one level-zero label to the
radial word. -/
private theorem chronological_trace_through_radial_word
    {n L initialTime radialTime : ℕ} (hn : 3 ≤ n)
    {x entrance : Point} (hx : x ∈ candidateBox n)
    {omega : StepPath} (word : RadialLabelWord n L)
    (hfirst : AbsoluteBoundaryFirstAt (initialSpliceBoundary n) (-x)
      omega initialTime)
    (hentrance : trajectoryFrom (-x) omega initialTime = entrance)
    (hentranceOne : entrance ∈ radialBoundary n 0 ⟨1, by omega⟩)
    (htrace : chronologicalRadialLabels n 0
      (fun r ↦ trajectoryFrom entrance (shiftSteps initialTime omega) r)
      radialTime = word.toList) :
    chronologicalRadialLabels n 0
      (fun r ↦ trajectoryFrom (-x) omega r) (initialTime + radialTime) =
        (⟨0, by omega⟩ : Fin (n + 2)) :: word.toList := by
  classical
  let rawPrefix := (List.range initialTime).flatMap
    (fun q ↦ radialLabelsAt n 0 (trajectoryFrom (-x) omega q))
  let shifted : WalkPath := fun q ↦
    trajectoryFrom entrance (shiftSteps initialTime omega) q
  let suffix := observedRadialLabels n 0 shifted radialTime
  have hprefix := initial_prefix_labels_are_zero hn hx hfirst hentrance
    hentranceOne
  have hraw : observedRadialLabels n 0
      (fun r ↦ trajectoryFrom (-x) omega r) (initialTime + radialTime) =
      rawPrefix ++ suffix := by
    unfold observedRadialLabels rawPrefix suffix
    rw [range_add_succ_eq_append_shift, List.flatMap_append,
      List.flatMap_map]
    congr 1
    apply List.flatMap_congr
    intro q _
    apply congrArg (radialLabelsAt n 0)
    dsimp [shifted]
    rw [← hentrance, trajectoryFrom_shiftSteps_eq_absolute]
  let suffixRest := (List.map Nat.succ (List.range radialTime)).flatMap
    (fun q ↦ radialLabelsAt n 0 (shifted q))
  have hsuffix : suffix = (⟨1, by omega⟩ : Fin (n + 2)) :: suffixRest := by
    unfold suffix observedRadialLabels suffixRest
    rw [List.range_succ_eq_map]
    simp only [List.flatMap_cons, List.flatMap_map]
    rw [show shifted 0 = entrance by simp [shifted, trajectoryFrom],
      radialLabelsAt_eq_singleton_of_mem (by omega) 0 entrance
        ⟨1, by omega⟩ hentranceOne]
    rfl
  have hprefixCompressed : compressLabels rawPrefix =
      [(⟨0, by omega⟩ : Fin (n + 2))] :=
    compressLabels_eq_singleton_of_nonempty_all_eq hprefix.1 hprefix.2
  have hprefixLast : lastPrevious none rawPrefix =
      some (⟨0, by omega⟩ : Fin (n + 2)) :=
    lastPrevious_eq_some_of_nonempty_all_eq hprefix.1 hprefix.2
  have hsuffixPrevious : compressLabelsFrom
      (some (⟨0, by omega⟩ : Fin (n + 2))) suffix =
      compressLabels suffix := by
    rw [hsuffix]
    exact compressLabelsFrom_eq_compressLabels_of_head_ne (by
      intro h
      have hval := congrArg Fin.val h
      norm_num at hval)
  have htraceSuffix : compressLabels suffix = word.toList := by
    simpa [suffix, shifted, chronologicalRadialLabels] using htrace
  unfold chronologicalRadialLabels
  rw [hraw]
  change compressLabelsFrom none (rawPrefix ++ suffix) = _
  rw [compressLabelsFrom_append]
  change compressLabels rawPrefix ++
    compressLabelsFrom (lastPrevious none rawPrefix) suffix = _
  rw [hprefixCompressed, hprefixLast, hsuffixPrevious, htraceSuffix]
  rfl

/-! ## Passage to the literal global stopping boundary -/

private theorem three_le_scaleRadius_zero
    {n : ℕ} (hn : 3 ≤ n) : (3 : ℝ) ≤ scaleRadius n 0 := by
  have hn1 : 1 ≤ n := by omega
  have hnReal : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnr1 : (n : ℝ) ≤ scaleRadius n 1 :=
    natCast_le_scaleRadius_one n hn1
  exact hnReal.trans (hnr1.trans
    (scaleRadius_antitone_of_le (by omega) (by omega)))

/-- A point at centred radius at most `8 r₀` around a candidate has a full
nearest-neighbour buffer before the global radius `16 r₀`. -/
private theorem candidate_eight_disc_disjoint_globalBoundary
    {n : ℕ} (hn : 3 ≤ n) {x z : Point} (hx : x ∈ candidateBox n)
    (hz : z - x ∈ disc 0 (8 * scaleRadius n 0)) :
    z ∉ discBoundary 0 (outerScale n) := by
  let r := scaleRadius n 0
  have hr3 : (3 : ℝ) ≤ r := three_le_scaleRadius_zero hn
  have hzCentered : euclideanRadius (z - x) ≤ 8 * r := by
    change latticeDistance 0 (z - x) ≤ 8 * r at hz
    rwa [RadialHarnackSpecialization.latticeDistance_zero_eq_euclideanRadius]
      at hz
  have hxRadius : euclideanRadius (-x) ≤ 5 * r :=
    (candidate_neg_euclideanRadius_bounds hx).2
  have hzRadius : euclideanRadius z ≤ 13 * r := by
    calc
      euclideanRadius z = euclideanRadius ((z - x) - (-x)) := by
        congr 1
        abel
      _ ≤ euclideanRadius (z - x) + euclideanRadius (-x) :=
        PoissonKernelGreenPole.euclideanRadius_sub_le_add _ _
      _ ≤ 13 * r := by linarith
  apply not_mem_discBoundary_of_mem_disc_of_add_one_le
    (r := 13 * r)
  · change latticeDistance 0 z ≤ 13 * r
    rw [RadialHarnackSpecialization.latticeDistance_zero_eq_euclideanRadius]
    exact hzRadius
  · rw [outerScale_eq_sixteen_mul_radius_zero]
    dsimp only [r]
    linarith

/-- Translating the selected radius-`32 r₀` endpoint back to the actual
walk puts it strictly outside the global radius-`16 r₀` disc. -/
private theorem translated_thirtytwo_boundary_outside_globalDisc
    {n : ℕ} (hn : 3 ≤ n) {x z : Point} (hx : x ∈ candidateBox n)
    (hz : z - x ∈ discBoundary 0 (32 * scaleRadius n 0)) :
    z ∉ disc 0 (outerScale n) := by
  let r := scaleRadius n 0
  have hr3 : (3 : ℝ) ≤ r := three_le_scaleRadius_zero hn
  intro hzGlobal
  have hzRadius : euclideanRadius z ≤ 16 * r := by
    change latticeDistance 0 z ≤ outerScale n at hzGlobal
    rw [outerScale_eq_sixteen_mul_radius_zero,
      RadialHarnackSpecialization.latticeDistance_zero_eq_euclideanRadius]
      at hzGlobal
    exact hzGlobal
  have hxNeg : euclideanRadius (-x) ≤ 5 * r :=
    (candidate_neg_euclideanRadius_bounds hx).2
  have hxRadius : euclideanRadius x ≤ 5 * r := by
    simpa [euclideanRadius, euclideanRadiusSq] using hxNeg
  have hcenteredRadius : euclideanRadius (z - x) ≤ 21 * r :=
    (PoissonKernelGreenPole.euclideanRadius_sub_le_add z x).trans (by linarith)
  have hcenteredDisc : z - x ∈ disc 0 (21 * r) := by
    change latticeDistance 0 (z - x) ≤ 21 * r
    rw [RadialHarnackSpecialization.latticeDistance_zero_eq_euclideanRadius]
    exact hcenteredRadius
  exact (not_mem_discBoundary_of_mem_disc_of_add_one_le hcenteredDisc
    (by dsimp only [r]; linarith : 21 * r + 1 ≤ 32 * r)) hz

private theorem lastPrevious_append
    {Label : Type*} (previous : Option Label) (left right : List Label) :
    lastPrevious previous (left ++ right) =
      lastPrevious (lastPrevious previous left) right := by
  induction left generalizing previous with
  | nil => rfl
  | cons head tail ih =>
      exact ih (some head)

private theorem trajectory_sub_candidate_eq_centered
    (x : Point) (omega : StepPath) (q : ℕ) :
    trajectory omega q - x = trajectoryFrom (-x) omega q := by
  simpa [trajectoryFrom] using
    (BoundaryStoppedHarnack.trajectoryFrom_sub_center
      (0 : Point) x omega q)

private theorem radialLabelsAt_translate
    (n : ℕ) (x z : Point) :
    radialLabelsAt n x z = radialLabelsAt n 0 (z - x) := by
  classical
  unfold radialLabelsAt
  congr 1
  ext label
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold radialBoundary
  exact BoundaryStoppedHarnack.mem_discBoundary_translate x
    (scaleRadius n label) z

private theorem chronologicalRadialLabels_translate
    (n horizon : ℕ) (x : Point) (omega : StepPath) :
    chronologicalRadialLabels n x (trajectory omega) horizon =
      chronologicalRadialLabels n 0
        (fun q ↦ trajectoryFrom (-x) omega q) horizon := by
  unfold chronologicalRadialLabels observedRadialLabels
  congr 1
  apply List.flatMap_congr
  intro q _
  rw [radialLabelsAt_translate,
    trajectory_sub_candidate_eq_centered]

/-- The literal spatial splice reaches the *first global* outer boundary
after the radial word has ended.  At that stopping time its actual walk,
centred at the candidate `x`, has exactly the initial zero label followed by
the selected chronological word. -/
theorem spatiallySplicedRadialWordAtom_global_pathwise
    {n L : ℕ} (hn : 3 ≤ n) {x : Point} (hx : x ∈ candidateBox n)
    (word : RadialLabelWord n L) {omega : StepPath}
    (homega : omega ∈ spatiallySplicedRadialWordAtom x word) :
    ∃ horizon : ℕ,
      IsOuterExitTime (trajectory omega) n horizon ∧
      chronologicalRadialLabels n x (trajectory omega) horizon =
        (⟨0, by omega⟩ : Fin (n + 2)) :: word.toList := by
  classical
  obtain ⟨initialTime, radialTime, finalTime, entrance, zeroExit,
      hinitialFirst, hentrance, hentranceOne, hradialFirst, hzeroExit,
      hradialTrace, hfinalFirst, hfinalPoint⟩ :=
    spatiallySplicedRadialWordAtom_pathwise (by omega) x word homega
  let chainTime := initialTime + radialTime
  let totalTime := chainTime + finalTime
  let centered : WalkPath := fun q ↦ trajectoryFrom (-x) omega q
  have hchainPosition : centered chainTime = zeroExit := by
    dsimp only [centered, chainTime]
    rw [← hzeroExit, ← hentrance,
      trajectoryFrom_shiftSteps_eq_absolute]
  have hcenteredPrefix : ∀ q ≤ chainTime,
      centered q ∈ disc 0 (8 * scaleRadius n 0) := by
    intro q hq
    have hr0nonneg : 0 ≤ scaleRadius n 0 :=
      (three_le_scaleRadius_zero hn).trans' (by norm_num)
    by_cases hqInitial : q ≤ initialTime
    · have hlarge : (3 : ℝ) ≤ n := by exact_mod_cast hn
      have hstart := initial_start_mem_annulus (by omega) hlarge hx
      apply trajectoryFrom_mem_disc_of_avoids_boundary
        (N := initialTime)
        (LiteralRealAnnulus.mem_literalRealAnnulus_raw.mp hstart).2.1
        (fun r hr hboundary ↦ hinitialFirst.2 r hr (Or.inr hboundary))
        q hqInitial
    · have hiq : initialTime ≤ q := Nat.le_of_not_ge hqInitial
      let u := q - initialTime
      have hu : u ≤ radialTime := by
        dsimp only [u, chainTime] at *
        omega
      have hentranceDisc : entrance ∈ disc 0 (scaleRadius n 0) :=
        hentranceOne.1.trans
          (by simpa using
            (scaleRadius_antitone_of_le (n := n) (k := 0) (l := 1)
              (by omega) (by omega)))
      have hradialDisc : trajectoryFrom entrance
          (shiftSteps initialTime omega) u ∈ disc 0 (scaleRadius n 0) :=
        trajectoryFrom_mem_disc_of_avoids_boundary hentranceDisc
          hradialFirst.2 u hu
      have hposition : centered q = trajectoryFrom entrance
          (shiftSteps initialTime omega) u := by
        have hqEq : initialTime + u = q := by
          dsimp only [u]
          exact Nat.add_sub_of_le hiq
        calc
          centered q = centered (initialTime + u) := congrArg centered hqEq.symm
          _ = trajectoryFrom (centered initialTime)
              (shiftSteps initialTime omega) u := by
            exact (trajectoryFrom_shiftSteps_eq_absolute
              (-x) omega initialTime u).symm
          _ = trajectoryFrom entrance (shiftSteps initialTime omega) u := by
            rw [show centered initialTime = entrance by
              exact hentrance]
      rw [hposition]
      change latticeDistance 0
        (trajectoryFrom entrance (shiftSteps initialTime omega) u) ≤
          8 * scaleRadius n 0
      change latticeDistance 0
        (trajectoryFrom entrance (shiftSteps initialTime omega) u) ≤
          scaleRadius n 0 at hradialDisc
      nlinarith
  have hprefixAvoidsGlobal : ∀ q ≤ chainTime,
      trajectory omega q ∉ discBoundary 0 (outerScale n) := by
    intro q hq
    apply candidate_eight_disc_disjoint_globalBoundary hn hx
    rw [trajectory_sub_candidate_eq_centered]
    exact hcenteredPrefix q hq
  have htotalCentered : centered totalTime ∈
      discBoundary 0 (32 * scaleRadius n 0) := by
    have heq : centered totalTime = trajectoryFrom zeroExit
        (shiftSteps chainTime omega) finalTime := by
      change centered (chainTime + finalTime) = _
      calc
        centered (chainTime + finalTime) =
            trajectoryFrom (centered chainTime)
              (shiftSteps chainTime omega) finalTime := by
          exact (trajectoryFrom_shiftSteps_eq_absolute
            (-x) omega chainTime finalTime).symm
        _ = trajectoryFrom zeroExit (shiftSteps chainTime omega) finalTime := by
          rw [hchainPosition]
    rw [heq]
    exact hfinalPoint
  have htotalOutside : trajectory omega totalTime ∉
      disc 0 (outerScale n) := by
    apply translated_thirtytwo_boundary_outside_globalDisc hn hx
    rw [trajectory_sub_candidate_eq_centered]
    exact htotalCentered
  obtain ⟨boundaryTime, hboundaryTimeLe, hboundaryTime⟩ :=
    exists_innerBoundary_before_of_exit (trajectory omega)
      (disc 0 (outerScale n)) (adjacent_trajectory_succ omega)
      (by
        show trajectory omega 0 ∈ disc 0 (outerScale n)
        rw [trajectory_zero]
        change (0, 0) ∈ disc (0, 0) (outerScale n)
        exact zero_mem_outerDisc n)
      ⟨totalTime, le_rfl, htotalOutside⟩
  have hexists : ∃ q : ℕ,
      trajectory omega q ∈ discBoundary 0 (outerScale n) :=
    ⟨boundaryTime, hboundaryTime⟩
  let horizon := Nat.find hexists
  have hexit : IsOuterExitTime (trajectory omega) n horizon := by
    refine ⟨Nat.find_spec hexists, ?_⟩
    intro q hq hqBoundary
    exact (Nat.not_le_of_gt hq)
      (Nat.find_min' hexists hqBoundary)
  have hhorizonLe : horizon ≤ totalTime :=
    (Nat.find_min' hexists hboundaryTime).trans hboundaryTimeLe
  have hchainLt : chainTime < horizon := by
    by_contra hnot
    exact hprefixAvoidsGlobal horizon (Nat.le_of_not_gt hnot) hexit.1
  have hhorizonLt : horizon < totalTime := by
    rcases hhorizonLe.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      apply htotalOutside
      have hinside := hexit.1.1
      rwa [heq] at hinside
  have hzeroOutsideOne : zeroExit ∉ disc 0 (scaleRadius n 1) := by
    intro hinside
    have hzeroBoundary : zeroExit ∈
        discBoundary 0 (scaleRadius n 0) := by
      rw [← hzeroExit]
      exact hradialFirst.1
    exact (not_mem_discBoundary_of_mem_disc_of_add_one_le hinside
      (by simpa using
        (TerminalProfileBoundarySeparation.scaleRadius_add_one_le_previous
          (by omega : 2 ≤ n)
          (by omega : 0 < 1) (by omega : 1 ≤ n + 1)))) hzeroBoundary
  have htailLabels : ∀ q, chainTime < q → q ≤ horizon →
      ∀ label ∈ radialLabelsAt n 0 (centered q),
        label = (⟨0, by omega⟩ : Fin (n + 2)) := by
    intro q hchainQ hqHorizon label hlabel
    by_contra hne
    have hlabelPos : 1 ≤ (label : ℕ) := by
      have : (label : ℕ) ≠ 0 := by
        intro hzero
        apply hne
        exact Fin.ext hzero
      omega
    let u := q - chainTime
    have huPos : 0 < u := by dsimp only [u]; omega
    have huFinal : u < finalTime := by
      dsimp only [u, totalTime] at *
      omega
    have hposition : centered q = trajectoryFrom zeroExit
        (shiftSteps chainTime omega) u := by
      have hqEq : chainTime + u = q := by
        dsimp only [u]
        exact Nat.add_sub_of_le hchainQ.le
      calc
        centered q = centered (chainTime + u) := congrArg centered hqEq.symm
        _ = trajectoryFrom (centered chainTime)
            (shiftSteps chainTime omega) u := by
          exact (trajectoryFrom_shiftSteps_eq_absolute
            (-x) omega chainTime u).symm
        _ = trajectoryFrom zeroExit (shiftSteps chainTime omega) u := by
          rw [hchainPosition]
    have hinsideOne : trajectoryFrom zeroExit
        (shiftSteps chainTime omega) u ∈ disc 0 (scaleRadius n 1) := by
      rw [← hposition]
      exact radialBoundary_subset_disc_one (by omega) label hlabelPos
        (mem_radialLabelsAt.mp hlabel)
    obtain ⟨entryTime, hentryLe, hentryBoundary⟩ :=
      exists_discBoundary_at_or_before_entry hzeroOutsideOne hinsideOne
    apply hfinalFirst.2 entryTime (hentryLe.trans_lt huFinal)
    rw [finalSpliceBoundary]
    exact Or.inl hentryBoundary
  have hchainTrace : chronologicalRadialLabels n 0 centered chainTime =
      (⟨0, by omega⟩ : Fin (n + 2)) :: word.toList := by
    exact chronological_trace_through_radial_word hn hx word hinitialFirst
      hentrance hentranceOne hradialTrace
  let tailLength := horizon - chainTime
  let rawBase := observedRadialLabels n 0 centered chainTime
  let rawExtra := (List.map (fun r ↦ chainTime + 1 + r)
      (List.range tailLength)).flatMap
        (fun q ↦ radialLabelsAt n 0 (centered q))
  have hraw : observedRadialLabels n 0 centered horizon =
      rawBase ++ rawExtra := by
    unfold rawBase rawExtra
    unfold observedRadialLabels
    rw [← Nat.add_sub_of_le hchainLt.le,
      range_add_succ_eq_append_after, List.flatMap_append,
      List.flatMap_map]
  have hrawExtraAll : ∀ label ∈ rawExtra,
      label = (⟨0, by omega⟩ : Fin (n + 2)) := by
    intro label hlabel
    rw [List.mem_flatMap] at hlabel
    obtain ⟨q, hq, hlabel⟩ := hlabel
    rw [List.mem_map] at hq
    obtain ⟨r, hr, rfl⟩ := hq
    have hrLt : r < tailLength := by simpa using hr
    apply htailLabels (chainTime + 1 + r)
    · omega
    · change r < horizon - chainTime at hrLt
      omega
    · exact hlabel
  have hbaseCompressed : compressLabels rawBase =
      (⟨0, by omega⟩ : Fin (n + 2)) :: word.toList := by
    simpa [rawBase, chronologicalRadialLabels] using hchainTrace
  have hbaseRawEnd : lastPrevious none rawBase =
      some (⟨0, by omega⟩ : Fin (n + 2)) := by
    have hzeroBoundary : centered chainTime ∈
        radialBoundary n 0 (⟨0, by omega⟩ : Fin (n + 2)) := by
      rw [hchainPosition, ← hzeroExit]
      exact hradialFirst.1
    have hsplit : rawBase =
        (List.range chainTime).flatMap
            (fun q ↦ radialLabelsAt n 0 (centered q)) ++
          [(⟨0, by omega⟩ : Fin (n + 2))] := by
      unfold rawBase observedRadialLabels
      rw [List.range_succ, List.flatMap_append,
        List.flatMap_singleton,
        radialLabelsAt_eq_singleton_of_mem (by omega) 0
          (centered chainTime) _ hzeroBoundary]
    rw [hsplit, lastPrevious_append]
    rfl
  have hcenteredTrace : chronologicalRadialLabels n 0 centered horizon =
      (⟨0, by omega⟩ : Fin (n + 2)) :: word.toList := by
    unfold chronologicalRadialLabels
    rw [hraw]
    change compressLabelsFrom none (rawBase ++ rawExtra) = _
    rw [compressLabelsFrom_append]
    change compressLabels rawBase ++
      compressLabelsFrom (lastPrevious none rawBase) rawExtra = _
    rw [hbaseCompressed, hbaseRawEnd,
      compressLabelsFrom_eq_nil_of_all_eq _ rawExtra hrawExtraAll]
    simp
  refine ⟨horizon, hexit, ?_⟩
  rw [chronologicalRadialLabels_translate]
  exact hcenteredTrace

/-! ## Excursion coordinates of the stopped splice -/

private theorem foldl_radial_one_seekingOuter_of_avoids_zero
    {n completed : ℕ} {labels : List (Fin (n + 2))}
    (havoid : ∀ label ∈ labels, (label : ℕ) ≠ 0) :
    labels.foldl (radialLabelVisit 1) ⟨true, completed⟩ =
      ⟨true, completed⟩ := by
  induction labels generalizing completed with
  | nil => rfl
  | cons label tail ih =>
      rw [List.foldl_cons]
      simp only [radialLabelVisit, Bool.true_eq, if_true, Nat.reduceSubDiff,
        if_neg (havoid label (by simp))]
      exact ih (fun z hz ↦ havoid z (by simp [hz]))

private theorem scanRadialLabels_zero_cons_eq
    {n k : ℕ} (hk : 2 ≤ k) (labels : List (Fin (n + 2))) :
    scanRadialLabels k
        ((⟨0, by omega⟩ : Fin (n + 2)) :: labels) =
      scanRadialLabels k labels := by
  have hne : (0 : ℕ) ≠ k - 1 := by omega
  unfold scanRadialLabels
  rw [List.foldl_cons]
  change labels.foldl (radialLabelVisit k)
      (radialLabelVisit k ⟨true, 0⟩
        (⟨0, by omega⟩ : Fin (n + 2))) = _
  simp [radialLabelVisit, hne]
  change labels.foldl (radialLabelVisit k) ⟨true, 0⟩ =
    labels.foldl (radialLabelVisit k) ⟨true, 0⟩
  rfl

private theorem scanRadialLabels_zero_cons_word_one
    {n L : ℕ} (word : RadialLabelWord n L) :
    (scanRadialLabels 1
      ((⟨0, by omega⟩ : Fin (n + 2)) :: word.toList)).completed = 1 := by
  classical
  have hLpos : 0 < L := by
    by_contra hnot
    have hLzero : L = 0 := by omega
    subst L
    have hindex : (⟨0, by omega⟩ : Fin (0 + 1)) = Fin.last 0 := by
      ext <;> rfl
    have hlevel := congrArg word.level hindex
    have hbad : (⟨1, by omega⟩ : Fin (n + 2)) =
        (⟨0, by omega⟩ : Fin (n + 2)) := by
      rw [← word.startsAtOne, hlevel, word.endsAtZero]
    have hval := congrArg Fin.val hbad
    norm_num at hval
  have hwordCons : word.toList =
      (⟨1, by omega⟩ : Fin (n + 2)) :: word.toList.tail := by
    have hbase : word.toList =
        (⟨1, by omega⟩ : Fin (n + 2)) ::
          List.ofFn (fun j : Fin L ↦ word.level j.succ) := by
      rw [RadialLabelWord.toList, List.ofFn_succ]
      congr 1
      exact word.startsAtOne
    have htail : word.toList.tail =
        List.ofFn (fun j : Fin L ↦ word.level j.succ) := by
      rw [hbase]
      rfl
    exact hbase.trans (congrArg
      (fun tail ↦ (⟨1, by omega⟩ : Fin (n + 2)) :: tail)
      htail.symm)
  have htailLength : word.toList.tail.length = L := by
    simp [RadialLabelWord.toList]
  have htailNe : word.toList.tail ≠ [] := by
    intro hnil
    rw [hnil] at htailLength
    simp at htailLength
    omega
  have hwordNe : word.toList ≠ [] := by
    rw [hwordCons]
    exact List.cons_ne_nil _ _
  have hlast : word.toList.getLast hwordNe =
      (⟨0, by omega⟩ : Fin (n + 2)) := by
    have hfnNe : List.ofFn word.level ≠ [] := by simp
    calc
      word.toList.getLast hwordNe =
          (List.ofFn word.level).getLast hfnNe :=
        List.getLast_congr hwordNe hfnNe rfl
      _ = (⟨0, by omega⟩ : Fin (n + 2)) := by
        rw [List.getLast_ofFn]
        exact word.endsAtZero
  have hwordSplit : word.toList.dropLast ++
      [(⟨0, by omega⟩ : Fin (n + 2))] = word.toList := by
    have h := List.dropLast_append_getLast hwordNe
    rwa [hlast] at h
  have hdropCons : word.toList.dropLast =
      (⟨1, by omega⟩ : Fin (n + 2)) ::
        word.toList.tail.dropLast := by
    calc
      word.toList.dropLast =
          ((⟨1, by omega⟩ : Fin (n + 2)) ::
            word.toList.tail).dropLast := congrArg List.dropLast hwordCons
      _ = (⟨1, by omega⟩ : Fin (n + 2)) ::
          word.toList.tail.dropLast :=
        List.dropLast_cons_of_ne_nil htailNe
  have hdropLength : word.toList.dropLast.length = L := by
    rw [List.length_dropLast, word.length_toList]
    omega
  have hdropNoZero : ∀ label ∈ word.toList.dropLast,
      (label : ℕ) ≠ 0 := by
    intro label hlabel
    obtain ⟨i, hi⟩ := List.get_of_mem hlabel
    have hiLt : i.val < L := by
      simpa [hdropLength] using i.isLt
    have hiWord : word.toList[i.val] = label := by
      rw [← List.getElem_dropLast i.isLt]
      exact hi
    have hiLevel : word.level ⟨i.val, by omega⟩ = label := by
      change (List.ofFn word.level)[i.val] = label at hiWord
      rwa [List.getElem_ofFn] at hiWord
    intro hzero
    apply word.beforeFinal_ne_zero ⟨i.val, hiLt⟩
    have hcast : (⟨i.val, hiLt⟩ : Fin L).castSucc =
        (⟨i.val, by omega⟩ : Fin (L + 1)) := Fin.ext rfl
    rw [hcast, hiLevel]
    exact hzero
  have hmiddleNoZero : ∀ label ∈ word.toList.tail.dropLast,
      (label : ℕ) ≠ 0 := by
    intro label hlabel
    apply hdropNoZero label
    rw [hdropCons]
    simp [hlabel]
  have hfirst : radialLabelVisit 1
      (radialLabelVisit 1 TerminalBoundaryScan.initialState
        (⟨0, by omega⟩ : Fin (n + 2)))
      (⟨1, by omega⟩ : Fin (n + 2)) = ⟨true, 1⟩ := by
    simp [radialLabelVisit, TerminalBoundaryScan.initialState]
  have hmiddle := foldl_radial_one_seekingOuter_of_avoids_zero
    (completed := 1) hmiddleNoZero
  unfold scanRadialLabels
  rw [← hwordSplit, hdropCons]
  simp only [List.cons_append, List.foldl_append, List.foldl_cons,
    hfirst, hmiddle]
  simp [radialLabelVisit]

private theorem excursionProfile_eq_scan_of_trace_zero_cons
    {n L horizon : ℕ} (hn : 2 ≤ n) {x : Point} {s : WalkPath}
    (word : RadialLabelWord n L)
    (htrace : chronologicalRadialLabels n x s horizon =
      (⟨0, by omega⟩ : Fin (n + 2)) :: word.toList)
    (k : Fin (n + 2)) (hk : 0 < (k : ℕ)) :
    excursionProfile s n horizon x k =
      (scanRadialLabels (k : ℕ)
        ((⟨0, by omega⟩ : Fin (n + 2)) :: word.toList)).completed := by
  have hscan := chronologicalRadialLabels_completed_eq_completedExcursionCount
    hn hk k.isLt x s horizon
  rw [htrace] at hscan
  unfold radialCompletedExcursionCount at hscan
  unfold excursionProfile
  rw [dif_neg hk.ne']
  exact hscan.symm

private theorem fixedSuccessfulProfile_of_trace_zero_cons
    {n L horizon : ℕ} (hn : 2 ≤ n) {delta : ℝ} {x : Point}
    {s : WalkPath} {m : Profile n} (word : RadialLabelWord n L)
    (hfixed : ∀ i : Fin (n - 1),
      radialUpcrossingCount word
        ⟨scaleIndex i, by unfold scaleIndex; omega⟩ = m i)
    (hterminalLower : terminalLower n delta ≤
      (radialUpcrossingCount word ⟨n + 1, by omega⟩ : ℝ))
    (hterminalUpper :
      radialUpcrossingCount word ⟨n + 1, by omega⟩ ≤ n ^ 3)
    (htrace : chronologicalRadialLabels n x s horizon =
      (⟨0, by omega⟩ : Fin (n + 2)) :: word.toList) :
    FixedSuccessfulProfile n delta m
      (excursionProfile s n horizon x) := by
  let N := excursionProfile s n horizon x
  have hcount (k : Fin (n + 2)) (hk : 0 < (k : ℕ)) :
      N k = (scanRadialLabels (k : ℕ)
        ((⟨0, by omega⟩ : Fin (n + 2)) :: word.toList)).completed := by
    exact excursionProfile_eq_scan_of_trace_zero_cons hn word htrace k hk
  have hone : N ⟨1, by omega⟩ = 1 := by
    rw [hcount ⟨1, by omega⟩ (by norm_num)]
    exact scanRadialLabels_zero_cons_word_one word
  have hinternal : ∀ i : Fin (n - 1),
      N ⟨scaleIndex i, by unfold scaleIndex; omega⟩ = m i := by
    intro i
    let k : Fin (n + 2) :=
      ⟨scaleIndex i, by unfold scaleIndex; omega⟩
    have hk2 : 2 ≤ (k : ℕ) := by simp [k, scaleIndex]
    rw [hcount k (by omega),
      show (scanRadialLabels (k : ℕ)
        ((⟨0, by omega⟩ : Fin (n + 2)) :: word.toList)).completed =
          radialWordCompletedCount word k by
        rw [scanRadialLabels_zero_cons_eq hk2]
        rfl,
      radialWordCompletedCount_eq_radialUpcrossingCount word k hk2]
    exact hfixed i
  let terminal : Fin (n + 2) := ⟨n + 1, by omega⟩
  have hterminal2 : 2 ≤ (terminal : ℕ) := by
    dsimp only [terminal]
    omega
  have hterminal : N terminal = radialUpcrossingCount word terminal := by
    rw [hcount terminal (by dsimp only [terminal]; omega),
      show (scanRadialLabels (terminal : ℕ)
        ((⟨0, by omega⟩ : Fin (n + 2)) :: word.toList)).completed =
          radialWordCompletedCount word terminal by
        rw [scanRadialLabels_zero_cons_eq hterminal2]
        rfl,
      radialWordCompletedCount_eq_radialUpcrossingCount word terminal
        hterminal2]
  change N ⟨1, by omega⟩ = 1 ∧
    (∀ i, N ⟨scaleIndex i, by unfold scaleIndex; omega⟩ = m i) ∧
    terminalLower n delta ≤ (N ⟨n + 1, by omega⟩ : ℝ) ∧
    N ⟨n + 1, by omega⟩ ≤ n ^ 3
  refine ⟨hone, hinternal, ?_, ?_⟩
  · rw [show (⟨n + 1, by omega⟩ : Fin (n + 2)) = terminal by rfl,
      hterminal]
    exact hterminalLower
  · rw [show (⟨n + 1, by omega⟩ : Fin (n + 2)) = terminal by rfl,
      hterminal]
    exact hterminalUpper

/-- A fixed-profile spatially spliced word is a literal stopped fixed-profile
event: the stopping horizon is the first global outer-boundary hit, the
initial excursion count is one, and every stored/terminal count is the
upcrossing count carried by the selected word. -/
theorem spatiallySplicedRadialWordAtom_subset_stoppedFixedProfileEvent
    {n : ℕ} (hn : 3 ≤ n) {delta : ℝ} {x : Point}
    (hx : x ∈ candidateBox n) {m : Profile n}
    (word : BoundedRadialLabelWord n (profileRadialWordMaxTransitions n))
    (hfixed : IsFixedProfileRadialWord n delta m word) :
    spatiallySplicedRadialWordAtom x word.2 ⊆
      stoppedFixedProfileEvent 0 n delta x m := by
  intro omega homega
  obtain ⟨horizon, hexit, htrace⟩ :=
    spatiallySplicedRadialWordAtom_global_pathwise hn hx word.2 homega
  have hshift : Proposition13Assembly.shiftedWalk 0 omega =
      trajectory omega := by
    have hsteps : shiftSteps 0 omega = omega := by
      funext q
      simp [shiftSteps]
    rw [Proposition13Assembly.shiftedWalk, hsteps]
  apply Set.mem_iUnion.mpr
  refine ⟨horizon, ?_, hx, ?_⟩
  ·
    rw [hshift]
    exact hexit
  · apply fixedSuccessfulProfile_of_trace_zero_cons (by omega) word.2
      hfixed.1 hfixed.2.1 hfixed.2.2
    rw [hshift]
    exact htrace

end

end Erdos1165.AnnularRadialSplicedPathwise
