import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedPairRuns
import ErdosProblems.Erdos1166.Erdos1166HLOZReconstruction

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal ProbabilityTheory

namespace Erdos1166

/-- Number of complete increment pairs encoded by a finite list of labeled
runs.  Every run contributes its distinguished pairs and its terminal
non-distinguished pair. -/
def pairRunsPairCount (runs : List (ℕ × IncrementPair)) : ℕ :=
  (runs.map fun run => run.1 + 1).sum

@[simp] theorem pairRunsPairCount_nil : pairRunsPairCount [] = 0 := rfl

@[simp] theorem pairRunsPairCount_cons
    (t : ℕ) (p : IncrementPair) (runs : List (ℕ × IncrementPair)) :
    pairRunsPairCount ((t, p) :: runs) =
      t + 1 + pairRunsPairCount runs := by
  simp [pairRunsPairCount]

/-- An exact labeled-run cylinder fixes every complete pair up to its
terminal horizon. -/
theorem firstPairRunsWithLabelsEqFrom_pair_eq
    (start : ℕ) (runs : List (ℕ × IncrementPair))
    {ω η : ℕ → Direction}
    (hω : ω ∈ firstPairRunsWithLabelsEqFrom start runs)
    (hη : η ∈ firstPairRunsWithLabelsEqFrom start runs)
    {r : ℕ} (hstart : start ≤ r)
    (hr : r < start + pairRunsPairCount runs) :
    incrementPair r ω = incrementPair r η := by
  induction runs generalizing start r with
  | nil => simp only [pairRunsPairCount_nil, Nat.add_zero] at hr; omega
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      rw [firstPairRunsWithLabelsEqFrom] at hω hη
      by_cases hpre : r < start + t
      · have hrt : r - start < t := by omega
        have hωr := hω.1.1 (r - start) hrt
        have hηr := hη.1.1 (r - start) hrt
        have hidx : start + (r - start) = r := Nat.add_sub_of_le hstart
        rw [hidx] at hωr hηr
        exact hωr.trans hηr.symm
      · by_cases hterminal : r = start + t
        · subst r
          exact hω.1.2.trans hη.1.2.symm
        · apply ih (start := start + t + 1) hω.2 hη.2
              (r := r) (by omega)
          simp only [pairRunsPairCount_cons] at hr
          omega

/-- An exact labeled-run cylinder fixes every increment before its complete
pair horizon. -/
theorem firstPairRunsWithLabelsEqFrom_increment_eq
    (runs : List (ℕ × IncrementPair))
    {ω η : ℕ → Direction}
    (hω : ω ∈ firstPairRunsWithLabelsEqFrom 0 runs)
    (hη : η ∈ firstPairRunsWithLabelsEqFrom 0 runs)
    {j : ℕ} (hj : j < 2 * pairRunsPairCount runs) :
    ω j = η j := by
  let r := j / 2
  let i : Fin 2 := ⟨j % 2, Nat.mod_lt _ (by omega)⟩
  have hr : r < pairRunsPairCount runs := by
    dsimp only [r]
    omega
  have hp := firstPairRunsWithLabelsEqFrom_pair_eq 0 runs hω hη
    (r := r) (by omega) (by simpa using hr)
  have hi := congrFun hp i
  change ω (2 * r + i) = η (2 * r + i) at hi
  have hjrepr : 2 * r + (i : ℕ) = j := by
    dsimp only [r, i]
    omega
  simpa only [hjrepr] using hi

/-- Hence the two reconstructed walks agree through the complete-pair
horizon. -/
theorem firstPairRunsWithLabelsEqFrom_simpleRandomWalk_eq
    (runs : List (ℕ × IncrementPair))
    {ω η : ℕ → Direction}
    (hω : ω ∈ firstPairRunsWithLabelsEqFrom 0 runs)
    (hη : η ∈ firstPairRunsWithLabelsEqFrom 0 runs)
    {n : ℕ} (hn : n ≤ 2 * pairRunsPairCount runs) :
    simpleRandomWalk ω n = simpleRandomWalk η n := by
  unfold simpleRandomWalk
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [firstPairRunsWithLabelsEqFrom_increment_eq runs hω hη
    (j := j) (hj.trans_le hn)]

@[instance_reducible] private def prefixMeasurableSpace
    (n : ℕ) : MeasurableSpace (ℕ → Site) where
  MeasurableSet' B := ∀ ⦃s t : ℕ → Site⦄,
    (∀ j, j ≤ n → s j = t j) → (s ∈ B ↔ t ∈ B)
  measurableSet_empty := by simp
  measurableSet_compl B hB := by
    intro s t hst
    simpa only [Set.mem_compl_iff] using not_congr (hB hst)
  measurableSet_iUnion f hf := by
    intro s t hst
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, (hf i hst).mp hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, (hf i hst).mpr hi⟩

/-- Every event in the canonical path filtration at time `n` is constant on
path prefixes through time `n`. -/
theorem mem_iff_of_measurableSet_canonicalFiltration
    (n : ℕ) {A : Set (ℕ → Site)}
    (hA : MeasurableSet[HLOZFoundation.canonicalFiltration n] A)
    {s t : ℕ → Site} (hst : ∀ j, j ≤ n → s j = t j) :
    s ∈ A ↔ t ∈ A := by
  have hle : HLOZFoundation.canonicalFiltration n ≤
      prefixMeasurableSpace n := by
    simp only [HLOZFoundation.canonicalFiltration, Filtration.natural]
    refine iSup_le fun i ↦ iSup_le fun hin ↦ ?_
    apply Measurable.comap_le
    intro B hB s t hst
    change (s i ∈ B ↔ t i ∈ B)
    rw [hst i hin]
  exact hle A hA hst

/-- The actual stopped path event `M_m^k ∩ {T_m^k=n}`. -/
def hlozMThresholdFiberPathEvent (m k n : ℕ) : Set (ℕ → Site) :=
  {s | firstKSitesReachLevel m k s <
      firstKSitesReachLevel (m + 1) 1 s} ∩
    {s | firstKSitesReachLevel m k s = n}

theorem measurableSet_hlozMThresholdFiberPathEvent (m k n : ℕ) :
    MeasurableSet[HLOZFoundation.canonicalFiltration n]
      (hlozMThresholdFiberPathEvent m k n) := by
  let T := isStoppingTime_firstKSitesReachLevel m k
  have hstop : MeasurableSet[T.measurableSpace]
      (hlozMThresholdFiberPathEvent m k n) := by
    exact (measurableSet_hlozMAtThreshold m k).inter
      (T.measurableSet_eq' n)
  exact (T.measurableSet_inter_eq_iff
    {s | firstKSitesReachLevel m k s <
      firstKSitesReachLevel (m + 1) 1 s} n).mp hstop

theorem firstPairRunsWithLabelsEqFrom_nonempty
    (runs : List (ℕ × IncrementPair)) :
    (firstPairRunsWithLabelsEqFrom 0 runs).Nonempty := by
  apply MeasureTheory.nonempty_of_measure_ne_zero (μ := incrementLaw)
  rw [firstPairRunsWithLabelsEqFrom_prob]
  simp

/-- A canonical increment representative of an exact run-vector atom. -/
noncomputable def pairRunsRepresentative
    (labels : List IncrementPair) (v : Fin labels.length → ℕ) :
    ℕ → Direction :=
  Classical.choose
    (firstPairRunsWithLabelsEqFrom_nonempty
      (List.zip (List.ofFn v) labels))

theorem pairRunsRepresentative_spec
    (labels : List IncrementPair) (v : Fin labels.length → ℕ) :
    pairRunsRepresentative labels v ∈
      firstPairRunsWithLabelsEqFrom 0
        (List.zip (List.ofFn v) labels) :=
  Classical.choose_spec
    (firstPairRunsWithLabelsEqFrom_nonempty
      (List.zip (List.ofFn v) labels))

def pairRunVectorHorizon
    (labels : List IncrementPair) (v : Fin labels.length → ℕ) : ℕ :=
  2 * pairRunsPairCount (List.zip (List.ofFn v) labels)

/-- Exact run-vector constraint obtained by reconstructing the actual stopped
event.  The representative is harmless because the event is prefix
measurable and the vector fixes the entire prefix. -/
noncomputable def hlozStoppedRunConstraint
    (m k n : ℕ) (labels : List IncrementPair) :
    Set (Fin labels.length → ℕ) :=
  {v | pairRunVectorHorizon labels v = n ∧
    simpleRandomWalk (pairRunsRepresentative labels v) ∈
      hlozMThresholdFiberPathEvent m k n}

theorem measurableSet_hlozStoppedRunConstraint
    (m k n : ℕ) (labels : List IncrementPair) :
    MeasurableSet (hlozStoppedRunConstraint m k n labels) := by
  measurability

/-- On a fixed terminal-label/external-path atom, the actual stopped HLOZ
fiber is exactly the pullback of its reconstructed run-vector constraint.
No reconstruction equality is required from a caller. -/
theorem externalPath_hlozThresholdFiber_eq_runConstraint
    (m k n : ℕ) (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair) :
    firstPairExternalPathEqFrom 0 (externalPathFromLabels labels) ∩
          {ω | pairRunVectorHorizon labels
            (conditionalPairRunVector 0 labels ω) = n} ∩
          (simpleRandomWalk ⁻¹' hlozMThresholdFiberPathEvent m k n) =
      firstPairExternalPathEqFrom 0 (externalPathFromLabels labels) ∩
        conditionalPairRunVector 0 labels ⁻¹'
          hlozStoppedRunConstraint m k n labels := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨⟨hpath, hhorizon⟩, hM⟩
    refine ⟨hpath, hhorizon, ?_⟩
    let v := conditionalPairRunVector 0 labels ω
    change pairRunVectorHorizon labels v = n at hhorizon
    have hrun : ω ∈ firstPairRunsWithLabelsEqFrom 0
        (List.zip (List.ofFn v) labels) := by
      exact (conditionalPairRunVector_eq_iff 0 labels hnondist v
        (by simpa [firstPairExternalPathEqFrom_reconstructed] using hpath)).mp rfl
    have hrep := pairRunsRepresentative_spec labels v
    have hpref : ∀ j, j ≤ n →
        simpleRandomWalk ω j =
          simpleRandomWalk (pairRunsRepresentative labels v) j := by
      intro j hj
      apply firstPairRunsWithLabelsEqFrom_simpleRandomWalk_eq
        (List.zip (List.ofFn v) labels) hrun hrep
      change j ≤ pairRunVectorHorizon labels v
      simpa only [hhorizon] using hj
    exact (mem_iff_of_measurableSet_canonicalFiltration n
      (measurableSet_hlozMThresholdFiberPathEvent m k n) hpref).mp hM
  · rintro ⟨hpath, hhorizon, hMrep⟩
    refine ⟨⟨hpath, hhorizon⟩, ?_⟩
    let v := conditionalPairRunVector 0 labels ω
    change pairRunVectorHorizon labels v = n at hhorizon
    have hrun : ω ∈ firstPairRunsWithLabelsEqFrom 0
        (List.zip (List.ofFn v) labels) := by
      exact (conditionalPairRunVector_eq_iff 0 labels hnondist v
        (by simpa [firstPairExternalPathEqFrom_reconstructed] using hpath)).mp rfl
    have hrep := pairRunsRepresentative_spec labels v
    have hpref : ∀ j, j ≤ n →
        simpleRandomWalk ω j =
          simpleRandomWalk (pairRunsRepresentative labels v) j := by
      intro j hj
      apply firstPairRunsWithLabelsEqFrom_simpleRandomWalk_eq
        (List.zip (List.ofFn v) labels) hrun hrep
      change j ≤ pairRunVectorHorizon labels v
      simpa only [hhorizon] using hj
    exact (mem_iff_of_measurableSet_canonicalFiltration n
      (measurableSet_hlozMThresholdFiberPathEvent m k n) hpref).mpr hMrep

/-- Past-side finite Proposition 4.3 law on a genuine stopped threshold
fiber.  Given the finite external path, the completed run vector is the iid
geometric product law filtered by the exact reconstructed `M_m^k`
constraint. -/
theorem conditionalPairRunVector_hasLaw_on_stopped_hlozM
    (m k n : ℕ) (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair) :
    HasLaw (conditionalPairRunVector 0 labels)
      (HLOZUrn.runVectorMeasure labels.length)[|
        hlozStoppedRunConstraint m k n labels]
      incrementLaw[|
        firstPairExternalPathEqFrom 0 (externalPathFromLabels labels) ∩
          {ω | pairRunVectorHorizon labels
            (conditionalPairRunVector 0 labels ω) = n} ∩
          (simpleRandomWalk ⁻¹' hlozMThresholdFiberPathEvent m k n)] := by
  rw [externalPath_hlozThresholdFiber_eq_runConstraint
    m k n labels hnondist]
  exact conditionalPairRunVector_hasLaw_on_inter 0 labels hnondist
    (hlozStoppedRunConstraint m k n labels)
    (measurableSet_hlozStoppedRunConstraint m k n labels)

open HLOZReconstruction

def incrementPairsFrom (start N : ℕ) (ω : ℕ → Direction) : List IncrementPair :=
  (List.range' start N).map fun r => incrementPair r ω

theorem incrementPairsFrom_eq_expandPairRuns
    (start : ℕ) (runs : List PairRun) {ω : ℕ → Direction}
    (hω : ω ∈ firstPairRunsWithLabelsEqFrom start runs) :
    incrementPairsFrom start (pairRunsPairCount runs) ω =
      expandPairRuns runs := by
  induction runs generalizing start with
  | nil => simp [incrementPairsFrom, expandPairRuns]
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      rw [firstPairRunsWithLabelsEqFrom] at hω
      rw [pairRunsPairCount_cons, show t + 1 + pairRunsPairCount runs =
        (t + 1) + pairRunsPairCount runs by omega]
      unfold incrementPairsFrom
      rw [← List.range'_append, List.map_append, expandPairRuns]
      have hprefix :
          List.map (fun r => incrementPair r ω)
              (List.range' start (t + 1)) =
            List.replicate t distinguishedIncrementPair ++ [p] := by
        apply List.ext_get
        · simp
        · intro n hnleft hnright
          simp only [List.length_map, List.length_range', List.length_append,
            List.length_replicate, List.length_singleton] at hnleft hnright
          by_cases hnt : n < t
          · have hseg := hω.1.1 n hnt
            simpa [List.getElem_append, hnt] using hseg
          · have hne : n = t := by omega
            subst n
            simpa [List.getElem_append] using hω.1.2
      rw [hprefix]
      simp only [one_mul]
      change (List.replicate t distinguishedIncrementPair ++ [p]) ++
          incrementPairsFrom (start + t + 1)
            (pairRunsPairCount runs) ω =
        List.replicate t distinguishedIncrementPair ++
          p :: expandPairRuns runs
      rw [ih (start := start + t + 1) hω.2]
      simp

theorem filterTerminal_expandPairRuns
    (runs : List PairRun)
    (hnondist : ∀ run ∈ runs,
      run.2 ≠ distinguishedIncrementPair) :
    (expandPairRuns runs).filterMap (fun p =>
        if p = distinguishedIncrementPair then none else some p) =
      terminalLabels runs := by
  induction runs with
  | nil => rfl
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      have hp : p ≠ distinguishedIncrementPair := hnondist (t, p) (by simp)
      have htail : ∀ run ∈ runs,
          run.2 ≠ distinguishedIncrementPair := by
        intro run hrun
        exact hnondist run (by simp [hrun])
      simp [expandPairRuns, terminalLabels, hp, ih htail]

theorem terminalPairLabelsThrough_eq_terminalLabels
    (runs : List PairRun) {ω : ℕ → Direction}
    (hω : ω ∈ firstPairRunsWithLabelsEqFrom 0 runs)
    (hnondist : ∀ run ∈ runs,
      run.2 ≠ distinguishedIncrementPair) :
    terminalPairLabelsThrough ω (pairRunsPairCount runs) =
      terminalLabels runs := by
  calc
    terminalPairLabelsThrough ω (pairRunsPairCount runs) =
        (incrementPairsFrom 0 (pairRunsPairCount runs) ω).filterMap
          (fun p => if p = distinguishedIncrementPair then none else some p) := by
      simp [terminalPairLabelsThrough, incrementPairsFrom,
        List.range'_eq_map_range]
    _ = (expandPairRuns runs).filterMap
          (fun p => if p = distinguishedIncrementPair then none else some p) := by
      rw [incrementPairsFrom_eq_expandPairRuns 0 runs hω]
    _ = terminalLabels runs :=
      filterTerminal_expandPairRuns runs hnondist

/-! Canonical grouping of run-vector coordinates by their even external
base site. -/

def zeroPairRuns (labels : List IncrementPair) : List PairRun :=
  List.zip (List.ofFn (0 : Fin labels.length → ℕ)) labels

@[simp] theorem terminalLabels_zeroPairRuns (labels : List IncrementPair) :
    terminalLabels (zeroPairRuns labels) = labels := by
  unfold zeroPairRuns terminalLabels
  apply List.map_snd_zip
  simp

@[simp] theorem terminalLabels_zip_ofFn
    (labels : List IncrementPair) (v : Fin labels.length → ℕ) :
    terminalLabels (List.zip (List.ofFn v) labels) = labels := by
  unfold terminalLabels
  apply List.map_snd_zip
  simp

theorem externalPairBases_eq_of_terminalLabels
    (a : Site) {runs₁ runs₂ : List PairRun}
    (h : terminalLabels runs₁ = terminalLabels runs₂) :
    externalPairBases a runs₁ = externalPairBases a runs₂ := by
  induction runs₁ generalizing a runs₂ with
  | nil =>
      cases runs₂ with
      | nil => rfl
      | cons run runs => simp [terminalLabels] at h
  | cons run₁ tail₁ ih =>
      cases runs₂ with
      | nil => simp [terminalLabels] at h
      | cons run₂ tail₂ =>
          rcases run₁ with ⟨t₁, p₁⟩
          rcases run₂ with ⟨t₂, p₂⟩
          simp only [terminalLabels, List.map_cons, List.cons.injEq] at h
          rcases h with ⟨rfl, htail⟩
          simp only [externalPairBases, List.cons.injEq, true_and]
          exact ih (a := pairEndpoint a p₁) htail

def paperRunBaseSet (labels : List IncrementPair) : Finset Site :=
  (externalPairBases (0, 0) (zeroPairRuns labels)).toFinset

abbrev PaperRunBase (labels : List IncrementPair) :=
  {x : Site // x ∈ paperRunBaseSet labels}

abbrev PaperRunIndex
    (labels : List IncrementPair) (b : PaperRunBase labels) :=
  Fin (runLengthsAtBase (0, 0) (zeroPairRuns labels) b.1).length

theorem runLengthsAtBase_length_zip_ofFn
    (labels : List IncrementPair) (v : Fin labels.length → ℕ) (x : Site) :
    (runLengthsAtBase (0, 0)
      (List.zip (List.ofFn v) labels) x).length =
    (runLengthsAtBase (0, 0) (zeroPairRuns labels) x).length := by
  rw [length_runLengthsAtBase, length_runLengthsAtBase]
  apply congrArg (List.count x)
  apply externalPairBases_eq_of_terminalLabels
  rw [terminalLabels_zip_ofFn, terminalLabels_zeroPairRuns]

noncomputable def paperBlockVector
    (labels : List IncrementPair) (v : Fin labels.length → ℕ) :
    ∀ b : PaperRunBase labels, PaperRunIndex labels b → ℕ :=
  fun b i =>
    (runLengthsAtBase (0, 0)
      (List.zip (List.ofFn v) labels) b.1).get
        (Fin.cast (runLengthsAtBase_length_zip_ofFn labels v b.1).symm i)

theorem sum_paperBlockVector
    (labels : List IncrementPair) (v : Fin labels.length → ℕ)
    (b : PaperRunBase labels) :
    (∑ i, paperBlockVector labels v b i) =
      lazyBlockSum (0, 0) (List.zip (List.ofFn v) labels) b.1 := by
  rw [← sum_runLengthsAtBase]
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_get
  · simpa [paperBlockVector] using
      (runLengthsAtBase_length_zip_ofFn labels v b.1).symm
  · intro n hn₁ hn₂
    simp [paperBlockVector]

theorem chessEven_of_mem_externalPairBases
    (a : Site) (runs : List PairRun) (ha : HLOZPairing.chessEven a)
    {x : Site} (hx : x ∈ externalPairBases a runs) :
    HLOZPairing.chessEven x := by
  induction runs generalizing a with
  | nil =>
      change x ∈ ([] : List Site) at hx
      simp at hx
  | cons run runs ih =>
      rcases run with ⟨t, p⟩
      simp only [externalPairBases, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ha
      · exact ih (pairEndpoint a p)
          ((chessEven_pairEndpoint_iff a p).2 ha) hx

theorem paperRunBase_chessEven
    (labels : List IncrementPair) (b : PaperRunBase labels) :
    HLOZPairing.chessEven b.1 := by
  rcases b with ⟨x, hx⟩
  change x ∈ paperRunBaseSet labels at hx
  unfold paperRunBaseSet at hx
  simp only [List.mem_toFinset] at hx
  exact chessEven_of_mem_externalPairBases (0, 0)
    (zeroPairRuns labels) (by simp [HLOZPairing.chessEven]) hx

/-- The actual paper block constraints attached canonically to a fixed
terminal-label path.  The external profile is evaluated on the zero-run
representative; deletion makes it independent of that harmless choice. -/
noncomputable def paperBlockConstraintsFromLabels
    (labels : List IncrementPair) (m : ℕ) :
    ∀ b : PaperRunBase labels,
      Finset (PaperRunIndex labels b → ℕ) :=
  paperBlockConstraints
    (simpleRandomWalk
      (pairRunsRepresentative labels (0 : Fin labels.length → ℕ)))
    (2 * pairRunsPairCount (zeroPairRuns labels)) m
    (fun b : PaperRunBase labels => b.1)

theorem mem_paperBlockConstraintsFromLabels_iff_reconstructed
    (labels : List IncrementPair)
    (hnondist : ∀ p ∈ labels, p ≠ distinguishedIncrementPair)
    (v : Fin labels.length → ℕ) (m : ℕ) :
    paperBlockVector labels v ∈
        HLOZConditionalProduct.blockEvent
          (paperBlockConstraintsFromLabels labels m) ↔
      ∀ b : PaperRunBase labels,
        reconstructedPairMax (0, 0)
          (List.zip (List.ofFn v) labels) b.1 < m := by
  let z : Fin labels.length → ℕ := 0
  let ω := pairRunsRepresentative labels z
  let N := pairRunsPairCount (zeroPairRuns labels)
  let runs := List.zip (List.ofFn v) labels
  have hzrun : ω ∈ firstPairRunsWithLabelsEqFrom 0
      (zeroPairRuns labels) := by
    simpa [ω, z, zeroPairRuns] using pairRunsRepresentative_spec labels z
  have hzeroNondist : ∀ run ∈ zeroPairRuns labels,
      run.2 ≠ distinguishedIncrementPair := by
    intro run hrun
    have hp : run.2 ∈ labels := by
      rw [← terminalLabels_zeroPairRuns labels]
      exact List.mem_map.mpr ⟨run, hrun, rfl⟩
    exact hnondist run.2 hp
  have hlabels : terminalLabels runs = terminalPairLabelsThrough ω N := by
    rw [terminalPairLabelsThrough_eq_terminalLabels
      (zeroPairRuns labels) hzrun hzeroNondist]
    simp [runs]
  exact mem_paperBlockEvent_iff_reconstructed_constraints
    ω N runs hlabels m (fun b : PaperRunBase labels => b.1)
      (paperBlockVector labels v)
      (paperRunBase_chessEven labels)
      (sum_paperBlockVector labels v)


end Erdos1166
