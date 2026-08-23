import ErdosProblems.Erdos1166.Erdos1166HLOZPairRuns
import ErdosProblems.Erdos1166.Erdos1166HLOZDecomposition

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace Erdos1166

open HLOZDecomposition

/-! A finite pairwise reconstruction of the HLOZ external path. -/

@[simp] theorem incrementPair_zero (r : ℕ) (ω : ℕ → Direction) :
    incrementPair r ω 0 = ω (2 * r) := by
  rfl

@[simp] theorem incrementPair_one (r : ℕ) (ω : ℕ → Direction) :
    incrementPair r ω 1 = ω (2 * r + 1) := by
  rfl

theorem directionStep_injective : Function.Injective directionStep := by
  intro d e h
  fin_cases d <;> fin_cases e <;> simp_all [directionStep]

/-- The two original directions encoded by one retained pair label. -/
def pairDirections (p : IncrementPair) : List Direction := [p 0, p 1]

/-- The external increments reconstructed from the successive terminal
non-distinguished pair labels. -/
def externalDirectionsFromLabels (labels : List IncrementPair) : List Direction :=
  labels.flatMap pairDirections

/-- The finite external path, including its initial position. -/
def externalPathFromLabels (labels : List IncrementPair) : List Site :=
  (externalDirectionsFromLabels labels).scanl
    (fun x d ↦ x + directionStep d) (0, 0)

@[simp] theorem pairDirections_length (p : IncrementPair) :
    (pairDirections p).length = 2 := by
  simp [pairDirections]

@[simp] theorem externalDirectionsFromLabels_length (labels : List IncrementPair) :
    (externalDirectionsFromLabels labels).length = 2 * labels.length := by
  induction labels with
  | nil => simp [externalDirectionsFromLabels]
  | cons p labels ih =>
      simp [externalDirectionsFromLabels]
      omega

@[simp] theorem externalPathFromLabels_length (labels : List IncrementPair) :
    (externalPathFromLabels labels).length = 2 * labels.length + 1 := by
  simp [externalPathFromLabels]

/-- Labels of precisely the non-lazy pairs among the first `N` pairs. -/
def terminalPairLabelsThrough (ω : ℕ → Direction) (N : ℕ) : List IncrementPair :=
  (List.range N).filterMap fun r ↦
    if incrementPair r ω = distinguishedIncrementPair then none
    else some (incrementPair r ω)

/-- The actual increment list left after deleting the distinguished pairs. -/
def deletedDirectionsThrough (ω : ℕ → Direction) (N : ℕ) : List Direction :=
  (List.range N).flatMap fun r ↦
    if incrementPair r ω = distinguishedIncrementPair then []
    else [ω (2 * r), ω (2 * r + 1)]

theorem externalDirections_terminalPairLabelsThrough (ω : ℕ → Direction) (N : ℕ) :
    externalDirectionsFromLabels (terminalPairLabelsThrough ω N) =
      deletedDirectionsThrough ω N := by
  induction N with
  | zero => simp [terminalPairLabelsThrough, deletedDirectionsThrough,
      externalDirectionsFromLabels]
  | succ N ih =>
      rw [terminalPairLabelsThrough, deletedDirectionsThrough, List.range_succ,
        List.filterMap_append, List.flatMap_append]
      rw [externalDirectionsFromLabels, List.flatMap_append]
      change externalDirectionsFromLabels (terminalPairLabelsThrough ω N) ++
          externalDirectionsFromLabels
            ([N].filterMap fun r ↦
              if incrementPair r ω = distinguishedIncrementPair then none
              else some (incrementPair r ω)) =
        deletedDirectionsThrough ω N ++
          [N].flatMap (fun r ↦
            if incrementPair r ω = distinguishedIncrementPair then []
            else [ω (2 * r), ω (2 * r + 1)])
      rw [ih]
      by_cases h : incrementPair N ω = distinguishedIncrementPair
      · simp [h, externalDirectionsFromLabels]
      · simp [h, externalDirectionsFromLabels, pairDirections]

theorem distinguishedPair_step_sum_zero :
    directionStep (distinguishedIncrementPair 0) +
      directionStep (distinguishedIncrementPair 1) = (0, 0) := by
  decide

theorem simpleRandomWalk_pair_succ (ω : ℕ → Direction) (N : ℕ) :
    simpleRandomWalk ω (2 * (N + 1)) =
      simpleRandomWalk ω (2 * N) + directionStep (ω (2 * N)) +
        directionStep (ω (2 * N + 1)) := by
  unfold simpleRandomWalk
  rw [show 2 * (N + 1) = (2 * N + 1) + 1 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ]

theorem simpleRandomWalk_succ' (ω : ℕ → Direction) (n : ℕ) :
    simpleRandomWalk ω (n + 1) = simpleRandomWalk ω n + directionStep (ω n) := by
  simp [simpleRandomWalk, Finset.sum_range_succ]

theorem incrementPair_eq_distinguished_iff (ω : ℕ → Direction) (r : ℕ) :
    incrementPair r ω = distinguishedIncrementPair ↔
      ω (2 * r) = 0 ∧ ω (2 * r + 1) = 1 := by
  constructor
  · intro h
    exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
  · rintro ⟨h0, h1⟩
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1

theorem isLazyEnd_simpleRandomWalk_pair_iff (ω : ℕ → Direction) (r : ℕ) :
    IsLazyEnd (simpleRandomWalk ω) (2 * r + 2) ↔
      incrementPair r ω = distinguishedIncrementPair := by
  simp only [IsLazyEnd]
  rw [show 2 * r + 2 - 2 = 2 * r by omega,
    show 2 * r + 2 - 1 = 2 * r + 1 by omega,
    simpleRandomWalk_succ' ω (2 * r),
    show 2 * r + 2 = (2 * r + 1) + 1 by omega,
    simpleRandomWalk_succ' ω (2 * r + 1),
    simpleRandomWalk_succ' ω (2 * r),
    incrementPair_eq_distinguished_iff]
  have heven : Even (2 * r + 2) := by
    use r + 1
    omega
  simp only [show 2 ≤ 2 * r + 2 by omega, heven, true_and]
  generalize hbase : simpleRandomWalk ω (2 * r) = base
  rcases base with ⟨x, y⟩
  generalize hfirst : ω (2 * r) = first
  generalize hsecond : ω (2 * r + 1) = second
  fin_cases first <;> fin_cases second <;>
    norm_num [paperE1, directionStep] <;> omega

/-- Pair indices deleted by the HLOZ decomposition through pair horizon `N`. -/
def distinguishedPairIndicesThrough (ω : ℕ → Direction) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter fun r ↦
    incrementPair r ω = distinguishedIncrementPair

theorem lazyEndsThrough_even_eq_image (ω : ℕ → Direction) (N : ℕ) :
    lazyEndsThrough (simpleRandomWalk ω) (2 * N) =
      (distinguishedPairIndicesThrough ω N).image (fun r ↦ 2 * r + 2) := by
  classical
  ext k
  constructor
  · intro hk
    rw [lazyEndsThrough, Finset.mem_filter] at hk
    rcases hk with ⟨hkIcc, hLazy⟩
    rcases hLazy.2.1 with ⟨a, ha⟩
    have ha1 : 1 ≤ a := by
      rcases Finset.mem_Icc.mp hkIcc with ⟨hk2, _⟩
      omega
    rw [Finset.mem_image]
    refine ⟨a - 1, ?_, ?_⟩
    · rw [distinguishedPairIndicesThrough, Finset.mem_filter]
      refine ⟨Finset.mem_range.mpr ?_, ?_⟩
      · rcases Finset.mem_Icc.mp hkIcc with ⟨_, hkN⟩
        omega
      · apply (isLazyEnd_simpleRandomWalk_pair_iff ω (a - 1)).mp
        have hk : 2 * (a - 1) + 2 = k := by omega
        rw [hk]
        exact hLazy
    · omega
  · rw [Finset.mem_image]
    rintro ⟨r, hr, rfl⟩
    rw [lazyEndsThrough, Finset.mem_filter]
    rw [distinguishedPairIndicesThrough, Finset.mem_filter] at hr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by
      have := Finset.mem_range.mp hr.1
      omega⟩, ?_⟩
    exact (isLazyEnd_simpleRandomWalk_pair_iff ω r).mpr hr.2

theorem lazyEndsThrough_even_card (ω : ℕ → Direction) (N : ℕ) :
    (lazyEndsThrough (simpleRandomWalk ω) (2 * N)).card =
      (distinguishedPairIndicesThrough ω N).card := by
  rw [lazyEndsThrough_even_eq_image]
  exact Finset.card_image_of_injective _ (by
    intro a b h
    exact Nat.mul_left_cancel (by omega) (Nat.add_right_cancel h))

theorem terminalPairLabelsThrough_length (ω : ℕ → Direction) (N : ℕ) :
    (terminalPairLabelsThrough ω N).length =
      ((Finset.range N).filter fun r ↦
        incrementPair r ω ≠ distinguishedIncrementPair).card := by
  induction N with
  | zero => simp [terminalPairLabelsThrough]
  | succ N ih =>
      rw [terminalPairLabelsThrough, List.range_succ, List.filterMap_append]
      change (terminalPairLabelsThrough ω N ++
        [N].filterMap (fun r ↦
          if h : incrementPair r ω = distinguishedIncrementPair then none
          else some (incrementPair r ω))).length = _
      rw [List.length_append, ih, Finset.range_add_one]
      rw [Finset.filter_insert]
      by_cases h : incrementPair N ω = distinguishedIncrementPair
      · simp [h]
      · simp [h]

theorem distinguished_add_terminal_count (ω : ℕ → Direction) (N : ℕ) :
    (distinguishedPairIndicesThrough ω N).card +
      (terminalPairLabelsThrough ω N).length = N := by
  rw [distinguishedPairIndicesThrough, terminalPairLabelsThrough_length]
  simpa using Finset.card_filter_add_card_filter_not
    (s := Finset.range N)
    (p := fun r ↦ incrementPair r ω = distinguishedIncrementPair)

theorem not_isLazyEnd_odd (s : ℕ → Site) (N : ℕ) :
    ¬ IsLazyEnd s (2 * N + 1) := by
  intro h
  rcases h.2.1 with ⟨a, ha⟩
  omega

/-- The decomposition clock at an even horizon is precisely the length of
the reconstructed external increment list. -/
theorem paperExternalClock_even_eq_external_length (ω : ℕ → Direction) (N : ℕ) :
    paperExternalClock (simpleRandomWalk ω) (2 * N) =
      (externalDirectionsFromLabels (terminalPairLabelsThrough ω N)).length := by
  rw [paperExternalClock, lazyEndsThrough_even_card,
    externalDirectionsFromLabels_length, if_neg]
  · have hcount := distinguished_add_terminal_count ω N
    omega
  · exact not_isLazyEnd_odd (simpleRandomWalk ω) N

/-- Delete, pair by pair, exactly those increments whose endpoint belongs to
the decomposition's `IsLazyEnd` set. -/
noncomputable def paperDeletedDirectionsAtPairHorizon
    (ω : ℕ → Direction) (N : ℕ) : List Direction := by
  classical
  exact (List.range N).flatMap fun r ↦
    if IsLazyEnd (simpleRandomWalk ω) (2 * r + 2) then []
    else [ω (2 * r), ω (2 * r + 1)]

/-- The HLOZ deleted path through the deterministic original time `2N`. -/
noncomputable def paperDeletedPathAtPairHorizon
    (ω : ℕ → Direction) (N : ℕ) : List Site :=
  (paperDeletedDirectionsAtPairHorizon ω N).scanl
    (fun x d ↦ x + directionStep d) (0, 0)

theorem paperDeletedDirectionsAtPairHorizon_eq (ω : ℕ → Direction) (N : ℕ) :
    paperDeletedDirectionsAtPairHorizon ω N = deletedDirectionsThrough ω N := by
  classical
  unfold paperDeletedDirectionsAtPairHorizon deletedDirectionsThrough
  apply List.flatMap_congr
  intro r hr
  rw [if_congr (isLazyEnd_simpleRandomWalk_pair_iff ω r) rfl rfl]

/-- Exact path identity: terminal non-distinguished labels reconstruct the
decomposition's deleted path at every deterministic pair horizon. -/
theorem externalPathFromLabels_eq_paperDeletedPath (ω : ℕ → Direction) (N : ℕ) :
    externalPathFromLabels (terminalPairLabelsThrough ω N) =
      paperDeletedPathAtPairHorizon ω N := by
  unfold externalPathFromLabels paperDeletedPathAtPairHorizon
  rw [externalDirections_terminalPairLabelsThrough,
    paperDeletedDirectionsAtPairHorizon_eq]

theorem paperDeletedPath_length_eq_clock_add_one (ω : ℕ → Direction) (N : ℕ) :
    (paperDeletedPathAtPairHorizon ω N).length =
      paperExternalClock (simpleRandomWalk ω) (2 * N) + 1 := by
  rw [← externalPathFromLabels_eq_paperDeletedPath,
    externalPathFromLabels_length,
    paperExternalClock_even_eq_external_length,
    externalDirectionsFromLabels_length]

/-! The external-path atom and the finite conditional law. -/

theorem scanl_directionSteps_injective (x : Site) :
    Function.Injective (fun ds : List Direction ↦
      ds.scanl (fun y d ↦ y + directionStep d) x) := by
  intro ds
  induction ds generalizing x with
  | nil =>
      intro es h
      cases es with
      | nil => rfl
      | cons e es =>
          have hlen := congrArg List.length h
          simp at hlen
  | cons d ds ih =>
      intro es h
      cases es with
      | nil =>
          have hlen := congrArg List.length h
          simp at hlen
      | cons e es =>
          simp only [List.scanl_cons] at h
          have htail := (List.cons.inj h).2
          have hhead := congrArg List.head? htail
          simp only [List.head?_scanl] at hhead
          have hstep : directionStep d = directionStep e := by
            apply add_left_cancel (a := x)
            simpa using hhead
          have hde : d = e := directionStep_injective hstep
          subst e
          have hrest : ds = es := ih (x := x + directionStep d) htail
          subst es
          rfl

theorem externalDirectionsFromLabels_injective :
    Function.Injective externalDirectionsFromLabels := by
  intro labels
  induction labels with
  | nil =>
      intro labels' h
      cases labels' with
      | nil => rfl
      | cons p labels' =>
          have hlen := congrArg List.length h
          simp at hlen
  | cons p labels ih =>
      intro labels' h
      cases labels' with
      | nil =>
          have hlen := congrArg List.length h
          simp at hlen
      | cons q labels' =>
          simp only [externalDirectionsFromLabels, List.flatMap_cons,
            pairDirections] at h
          have hp0 : p 0 = q 0 := by simpa using congrArg List.head? h
          have h1 := (List.cons.inj h).2
          have hp1 : p 1 = q 1 := by simpa using congrArg List.head? h1
          have hpq : p = q := by
            funext i
            fin_cases i
            · exact hp0
            · exact hp1
          subst q
          have htail := (List.cons.inj h1).2
          have hlabels : labels = labels' := ih htail
          subst labels'
          rfl

theorem externalPathFromLabels_injective :
    Function.Injective externalPathFromLabels := by
  intro labels labels' h
  apply externalDirectionsFromLabels_injective
  exact scanl_directionSteps_injective (0, 0) h

/-- The cylinder saying that the successive external terminal-pair labels
reconstruct the specified finite external path.  Injectivity of the
reconstruction makes the union a single atom whenever the path is valid. -/
noncomputable def firstPairExternalPathEqFrom
    (start : ℕ) (path : List Site) : Set (ℕ → Direction) :=
  ⋃ labels : List IncrementPair,
    if externalPathFromLabels labels = path then
      firstPairTerminalLabelsEqFrom start labels
    else ∅

theorem firstPairExternalPathEqFrom_reconstructed
    (start : ℕ) (labels : List IncrementPair) :
    firstPairExternalPathEqFrom start (externalPathFromLabels labels) =
      firstPairTerminalLabelsEqFrom start labels := by
  ext ω
  constructor
  · intro h
    rw [firstPairExternalPathEqFrom] at h
    simp only [Set.mem_iUnion] at h
    rcases h with ⟨labels', h⟩
    by_cases hp : externalPathFromLabels labels' = externalPathFromLabels labels
    · have hll : labels' = labels :=
        externalPathFromLabels_injective hp
      subst labels'
      simpa using h
    · simp [hp] at h
  · intro h
    rw [firstPairExternalPathEqFrom]
    simp only [Set.mem_iUnion]
    refine ⟨labels, ?_⟩
    simp [h]

/-- Finite form of the first sentence of HLOZ Proposition 4.2: conditional
on a fixed reconstructed external path, the intervening lazy run lengths
have the iid geometric `(15/16)` product law. -/
theorem firstPairRunLengths_conditional_on_externalPath
    (start : ℕ) (runs : List (ℕ × IncrementPair))
    (hnondist : ∀ run ∈ runs,
      run.2 ≠ distinguishedIncrementPair) :
    incrementLaw (firstPairRunsWithLabelsEqFrom start runs) /
        incrementLaw (firstPairExternalPathEqFrom start
          (externalPathFromLabels (runs.map Prod.snd))) =
      (runs.map fun run ↦
        (15 : ENNReal) / 16 ^ (run.1 + 1)).prod := by
  rw [firstPairExternalPathEqFrom_reconstructed]
  exact firstPairRunLengths_conditional_on_terminalLabels start runs hnondist

theorem foldl_deletedDirectionsThrough (ω : ℕ → Direction) (N : ℕ) :
    (deletedDirectionsThrough ω N).foldl
      (fun x d ↦ x + directionStep d) (0, 0) = simpleRandomWalk ω (2 * N) := by
  induction N with
  | zero => simp [deletedDirectionsThrough, simpleRandomWalk]
  | succ N ih =>
      rw [deletedDirectionsThrough, List.range_succ, List.flatMap_append,
        List.foldl_append]
      simp only [List.flatMap_singleton]
      change List.foldl (fun x d ↦ x + directionStep d)
        (List.foldl (fun x d ↦ x + directionStep d) (0, 0)
          (deletedDirectionsThrough ω N))
        (if incrementPair N ω = distinguishedIncrementPair then []
          else [ω (2 * N), ω (2 * N + 1)]) = _
      rw [ih, simpleRandomWalk_pair_succ]
      by_cases h : incrementPair N ω = distinguishedIncrementPair
      · simp [h]
        have h0 : ω (2 * N) = distinguishedIncrementPair 0 := by
          simpa using congrFun h 0
        have h1 : ω (2 * N + 1) = distinguishedIncrementPair 1 := by
          simpa using congrFun h 1
        rw [h0, h1]
        rcases simpleRandomWalk ω (2 * N) with ⟨x, y⟩
        norm_num [directionStep]
      · simp [h, add_assoc]

/-- At every deterministic pair horizon, the endpoint of the reconstructed
external path is the endpoint of the original walk. -/
theorem externalPathFromLabels_terminal_endpoint (ω : ℕ → Direction) (N : ℕ) :
    (externalPathFromLabels (terminalPairLabelsThrough ω N)).getLast
        (by simp [externalPathFromLabels]) = simpleRandomWalk ω (2 * N) := by
  change ((externalDirectionsFromLabels (terminalPairLabelsThrough ω N)).scanl
    (fun x d ↦ x + directionStep d) (0, 0)).getLast _ = _
  rw [List.getLast_scanl]
  rw [externalDirections_terminalPairLabelsThrough]
  exact foldl_deletedDirectionsThrough ω N

end Erdos1166
