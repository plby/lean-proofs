import ErdosProblems.Erdos1166.Erdos1166HLOZSourceInstantiation

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal ProbabilityTheory

namespace Erdos1166.HLOZSourceInstantiation

open Erdos1166 HLOZDecomposition HLOZReconstruction HLOZActualStopped
  HLOZIncompleteStoppedBlocks HLOZProp45SourceClock

theorem terminalPairLabelsThrough_succ_length
    (ω : ℕ → Direction) (R : ℕ) :
    (terminalPairLabelsThrough ω (R + 1)).length =
      (terminalPairLabelsThrough ω R).length +
        if incrementPair R ω = distinguishedIncrementPair then 0 else 1 := by
  rw [terminalPairLabelsThrough, List.range_succ, List.filterMap_append,
    List.length_append]
  change (terminalPairLabelsThrough ω R).length +
      ([R].filterMap fun r ↦
        if incrementPair r ω = distinguishedIncrementPair then none
        else some (incrementPair r ω)).length = _
  by_cases h : incrementPair R ω = distinguishedIncrementPair <;> simp [h]

theorem terminalPairLabelsThrough_prefix
    (ω : ℕ → Direction) {N R : ℕ} (hNR : N ≤ R) :
    terminalPairLabelsThrough ω N <+:
      terminalPairLabelsThrough ω R := by
  unfold terminalPairLabelsThrough
  apply List.IsPrefix.filterMap
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNR
  rw [List.range_add]
  exact List.prefix_append _ _

theorem terminalPairLabelsThrough_succ_eq_append
    (ω : ℕ → Direction) (R : ℕ)
    (hR : incrementPair R ω ≠ distinguishedIncrementPair) :
    terminalPairLabelsThrough ω (R + 1) =
      terminalPairLabelsThrough ω R ++ [incrementPair R ω] := by
  rw [terminalPairLabelsThrough, List.range_succ, List.filterMap_append]
  change terminalPairLabelsThrough ω R ++
      [R].filterMap (fun r ↦
        if incrementPair r ω = distinguishedIncrementPair then none
        else some (incrementPair r ω)) = _
  simp [hR]

theorem lazyEndsThrough_odd_eq_even (s : ℕ → Site) (R : ℕ) :
    lazyEndsThrough s (2 * R + 1) = lazyEndsThrough s (2 * R) := by
  ext k
  simp only [lazyEndsThrough, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hk2, hkR⟩, hkL⟩
    refine ⟨⟨hk2, ?_⟩, hkL⟩
    rcases hkL.2.1 with ⟨a, ha⟩
    omega
  · rintro ⟨⟨hk2, hkR⟩, hkL⟩
    exact ⟨⟨hk2, by omega⟩, hkL⟩

theorem paperExternalClock_odd_eq_terminal_length
    (ω : ℕ → Direction) (R : ℕ) :
    paperExternalClock (simpleRandomWalk ω) (2 * R + 1) =
      2 * (terminalPairLabelsThrough ω R).length +
        if incrementPair R ω = distinguishedIncrementPair then 0 else 1 := by
  unfold paperExternalClock
  rw [lazyEndsThrough_odd_eq_even,
    lazyEndsThrough_even_card]
  simp only [show 2 * R + 1 + 1 = 2 * R + 2 by omega,
    isLazyEnd_simpleRandomWalk_pair_iff]
  have hc := distinguished_add_terminal_count ω R
  by_cases h : incrementPair R ω = distinguishedIncrementPair
  · simp [h]
    omega
  · simp [h]
    omega

theorem exists_terminalPairIndex_of_lt_length
    (ω : ℕ → Direction) {N i : ℕ}
    (hi : i < (terminalPairLabelsThrough ω N).length) :
    ∃ R, i < (terminalPairLabelsThrough ω (R + 1)).length := by
  exact ⟨N, hi.trans_le (terminalPairLabelsThrough_length_mono ω (by omega))⟩

noncomputable def terminalPairIndex (ω : ℕ → Direction) (i : ℕ) : ℕ := by
  classical
  exact if h : ∃ R, i < (terminalPairLabelsThrough ω (R + 1)).length then
    Nat.find h else 0

theorem terminalPairIndex_spec
    (ω : ℕ → Direction) (i : ℕ)
    (h : ∃ R, i < (terminalPairLabelsThrough ω (R + 1)).length) :
    i < (terminalPairLabelsThrough ω (terminalPairIndex ω i + 1)).length := by
  rw [terminalPairIndex, dif_pos h]
  exact Nat.find_spec h

theorem terminalPairIndex_minimal
    (ω : ℕ → Direction) (i R : ℕ)
    (hR : i < (terminalPairLabelsThrough ω (R + 1)).length) :
    terminalPairIndex ω i ≤ R := by
  have hex : ∃ a, i < (terminalPairLabelsThrough ω (a + 1)).length := ⟨R, hR⟩
  rw [terminalPairIndex, dif_pos hex]
  exact Nat.find_min' hex hR

theorem terminalPairIndex_count
    (ω : ℕ → Direction) (i : ℕ)
    (h : ∃ R, i < (terminalPairLabelsThrough ω (R + 1)).length) :
    (terminalPairLabelsThrough ω (terminalPairIndex ω i)).length = i ∧
      incrementPair (terminalPairIndex ω i) ω ≠ distinguishedIncrementPair := by
  have hspec := terminalPairIndex_spec ω i h
  have hle : (terminalPairLabelsThrough ω (terminalPairIndex ω i)).length ≤ i := by
    by_contra hnot
    have hlt : i < (terminalPairLabelsThrough ω (terminalPairIndex ω i)).length := by omega
    cases hidx : terminalPairIndex ω i with
    | zero => simpa [hidx, terminalPairLabelsThrough] using hlt
    | succ R =>
        have hmin := terminalPairIndex_minimal ω i R (by simpa [hidx] using hlt)
        rw [hidx] at hmin
        omega
  have hstep := terminalPairLabelsThrough_succ_length ω (terminalPairIndex ω i)
  by_cases hp : incrementPair (terminalPairIndex ω i) ω = distinguishedIncrementPair
  · rw [if_pos hp] at hstep
    omega
  · rw [if_neg hp] at hstep
    constructor
    · omega
    · exact hp

theorem terminalPairIndex_count_le
    (ω : ℕ → Direction) (i : ℕ)
    (h : ∃ R, i < (terminalPairLabelsThrough ω (R + 1)).length)
    {a : ℕ} (ha : a ≤ terminalPairIndex ω i) :
    (terminalPairLabelsThrough ω a).length ≤ i := by
  calc
    (terminalPairLabelsThrough ω a).length ≤
        (terminalPairLabelsThrough ω (terminalPairIndex ω i)).length :=
      terminalPairLabelsThrough_length_mono ω ha
    _ = i := (terminalPairIndex_count ω i h).1

theorem simpleRandomWalk_even_eq_of_terminal_count_eq
    (ω : ℕ → Direction) {a b : ℕ} (hab : a ≤ b)
    (hlen : (terminalPairLabelsThrough ω a).length =
      (terminalPairLabelsThrough ω b).length) :
    simpleRandomWalk ω (2 * a) = simpleRandomWalk ω (2 * b) := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
      have hmonoA := terminalPairLabelsThrough_length_mono ω hab
      have hmonoB := terminalPairLabelsThrough_length_mono ω
        (show b ≤ b + 1 by omega)
      have hlenB : (terminalPairLabelsThrough ω a).length =
          (terminalPairLabelsThrough ω b).length := by omega
      have hstep := terminalPairLabelsThrough_succ_length ω b
      have hp : incrementPair b ω = distinguishedIncrementPair := by
        by_contra hp
        rw [if_neg hp] at hstep
        omega
      calc
        simpleRandomWalk ω (2 * a) = simpleRandomWalk ω (2 * b) := ih hlenB
        _ = simpleRandomWalk ω (2 * (b + 1)) := by
          rw [simpleRandomWalk_pair_succ]
          have h0 := congrFun hp 0
          have h1 := congrFun hp 1
          simp only [incrementPair_zero] at h0
          simp only [incrementPair_one] at h1
          rw [h0, h1, add_assoc, distinguishedPair_step_sum_zero]
          simp

theorem terminalPairIndex_strictMono
    (ω : ℕ → Direction) {i j : ℕ} (hij : i < j)
    (hi : ∃ R, i < (terminalPairLabelsThrough ω (R + 1)).length)
    (hj : ∃ R, j < (terminalPairLabelsThrough ω (R + 1)).length) :
    terminalPairIndex ω i < terminalPairIndex ω j := by
  by_contra hnot
  have hmono := terminalPairLabelsThrough_length_mono ω
    (show terminalPairIndex ω j ≤ terminalPairIndex ω i by omega)
  rw [(terminalPairIndex_count ω j hj).1,
    (terminalPairIndex_count ω i hi).1] at hmono
  omega

theorem externalInverseMinus_even_succ
    (ω : ℕ → Direction) (i : ℕ)
    (h : ∃ R, i < (terminalPairLabelsThrough ω (R + 1)).length) :
    externalInverseMinus (simpleRandomWalk ω) (2 * (i + 1)) =
      2 * terminalPairIndex ω i + 2 := by
  let R := terminalPairIndex ω i
  have hcount := terminalPairIndex_count ω i h
  have hcand : paperExternalClock (simpleRandomWalk ω) (2 * R + 2) =
      2 * (i + 1) := by
    rw [show 2 * R + 2 = 2 * (R + 1) by omega,
      paperExternalClock_even_eq_external_length,
      externalDirectionsFromLabels_length,
      terminalPairLabelsThrough_succ_length, if_neg hcount.2, hcount.1]
  apply le_antisymm (externalInverseMinus_minimal hcand)
  have hspec : paperExternalClock (simpleRandomWalk ω)
      (externalInverseMinus (simpleRandomWalk ω) (2 * (i + 1))) =
        2 * (i + 1) := externalInverseMinus_spec ⟨2 * R + 2, hcand⟩
  by_contra hnot
  have hlt : externalInverseMinus (simpleRandomWalk ω) (2 * (i + 1)) <
      2 * R + 2 := by omega
  let n := externalInverseMinus (simpleRandomWalk ω) (2 * (i + 1))
  change paperExternalClock (simpleRandomWalk ω) n = 2 * (i + 1) at hspec
  rcases Nat.even_or_odd' n with ⟨a, ha | ha⟩
  · rw [ha, paperExternalClock_even_eq_external_length,
      externalDirectionsFromLabels_length] at hspec
    have haR : a ≤ R := by omega
    have hle := terminalPairIndex_count_le ω i h haR
    omega
  · rw [ha, paperExternalClock_odd_eq_terminal_length] at hspec
    have haR : a ≤ R := by omega
    have hle := terminalPairIndex_count_le ω i h haR
    split at hspec <;> omega

theorem externalInverseMinus_odd
    (ω : ℕ → Direction) (i : ℕ)
    (h : ∃ R, i < (terminalPairLabelsThrough ω (R + 1)).length) :
    externalInverseMinus (simpleRandomWalk ω) (2 * i + 1) =
      2 * terminalPairIndex ω i + 1 := by
  let R := terminalPairIndex ω i
  have hcount := terminalPairIndex_count ω i h
  have hcand : paperExternalClock (simpleRandomWalk ω) (2 * R + 1) =
      2 * i + 1 := by
    rw [paperExternalClock_odd_eq_terminal_length, hcount.1,
      if_neg hcount.2]
  apply le_antisymm (externalInverseMinus_minimal hcand)
  have hspec : paperExternalClock (simpleRandomWalk ω)
      (externalInverseMinus (simpleRandomWalk ω) (2 * i + 1)) =
        2 * i + 1 := externalInverseMinus_spec ⟨2 * R + 1, hcand⟩
  by_contra hnot
  have hlt : externalInverseMinus (simpleRandomWalk ω) (2 * i + 1) <
      2 * R + 1 := by omega
  let n := externalInverseMinus (simpleRandomWalk ω) (2 * i + 1)
  change paperExternalClock (simpleRandomWalk ω) n = 2 * i + 1 at hspec
  rcases Nat.even_or_odd' n with ⟨a, ha | ha⟩
  · rw [ha, paperExternalClock_even_eq_external_length,
      externalDirectionsFromLabels_length] at hspec
    omega
  · rw [ha, paperExternalClock_odd_eq_terminal_length] at hspec
    have haR : a < R := by omega
    have hle := terminalPairIndex_count_le ω i h (show a ≤ R by omega)
    by_cases hp : incrementPair a ω = distinguishedIncrementPair
    · rw [if_pos hp] at hspec
      omega
    · rw [if_neg hp] at hspec
      have hstep := terminalPairLabelsThrough_succ_length ω a
      rw [if_neg hp] at hstep
      have hmin := terminalPairIndex_minimal ω i a (by omega)
      dsimp only [R] at haR
      omega

theorem externalInverseMinus_zero (ω : ℕ → Direction) :
    externalInverseMinus (simpleRandomWalk ω) 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply externalInverseMinus_minimal
  simp [paperExternalClock, lazyEndsThrough, IsLazyEnd]

theorem realized_terminalPairLabelsThrough {q : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    {ω : ℕ → Direction}
    (hω : ω ∈ firstPairExternalPathEqFrom 0
      (externalPathFromLabels (List.ofFn labels))) :
    ∃ N, terminalPairLabelsThrough ω N = List.ofFn labels := by
  have hterm : ω ∈ firstPairTerminalLabelsEqFrom 0 (List.ofFn labels) := by
    simpa [firstPairExternalPathEqFrom_reconstructed] using hω
  let v := conditionalPairRunVector 0 (List.ofFn labels) ω
  have hnondistList : ∀ p ∈ List.ofFn labels,
      p ≠ distinguishedIncrementPair := by
    intro p hp
    rw [List.mem_ofFn] at hp
    rcases hp with ⟨i, rfl⟩
    exact hnondist i
  have hrun : ω ∈ pairRunsAndLabelsEqFrom 0
      (List.ofFn v) (List.ofFn labels) :=
    (conditionalPairRunVector_eq_iff 0 (List.ofFn labels)
      hnondistList v hterm).mp rfl
  let runs := List.zip (List.ofFn v) (List.ofFn labels)
  refine ⟨pairRunsPairCount runs, ?_⟩
  have hrun' : ω ∈ firstPairRunsWithLabelsEqFrom 0 runs := hrun
  have hrunsNondist : ∀ run ∈ runs,
      run.2 ≠ distinguishedIncrementPair := by
    intro run hrunMem
    have hsnd : run.2 ∈ List.ofFn labels := by
      rcases run with ⟨t, p⟩
      exact (List.of_mem_zip hrunMem).2
    exact hnondistList run.2 hsnd
  rw [terminalPairLabelsThrough_eq_terminalLabels runs hrun' hrunsNondist]
  simpa [runs] using terminalLabels_zip_ofFn (List.ofFn labels) v

theorem terminalPairIndex_label_of_realized {q : ℕ}
    (labels : Fin q → IncrementPair) {ω : ℕ → Direction} {N : ℕ}
    (hlabels : terminalPairLabelsThrough ω N = List.ofFn labels)
    (i : Fin q) :
    incrementPair (terminalPairIndex ω i) ω = labels i := by
  have hiN : i.val < (terminalPairLabelsThrough ω N).length := by
    rw [hlabels]
    simp
  have hNpos : 0 < N := by
    by_contra hN
    have : N = 0 := by omega
    subst N
    simp [terminalPairLabelsThrough] at hiN
  have hex : ∃ R, i.val <
      (terminalPairLabelsThrough ω (R + 1)).length :=
    ⟨N - 1, by simpa [Nat.sub_add_cancel (by omega : 1 ≤ N)] using hiN⟩
  have hidxLe : terminalPairIndex ω i.val ≤ N - 1 :=
    terminalPairIndex_minimal ω i.val (N - 1)
      (by simpa [Nat.sub_add_cancel (by omega : 1 ≤ N)] using hiN)
  have hprefix := terminalPairLabelsThrough_prefix ω
    (show terminalPairIndex ω i.val + 1 ≤ N by omega)
  rcases hprefix with ⟨tail, htail⟩
  have hcount := terminalPairIndex_count ω i.val hex
  rw [terminalPairLabelsThrough_succ_eq_append ω _ hcount.2] at htail
  have hdrop := congrArg (fun l : List IncrementPair ↦
    (l.drop i.val).head?) htail
  have hdropLabels := congrArg (fun l : List IncrementPair ↦
    (l.drop i.val).head?) hlabels
  simp [hcount.1] at hdrop hdropLabels
  exact Option.some.inj (hdrop.trans hdropLabels)

def fixedExternalBase {q : ℕ}
    (labels : Fin q → IncrementPair) (i : ℕ) : Site :=
  (List.take i (List.ofFn labels)).foldl pairEndpoint (0, 0)

@[simp] theorem fixedExternalBase_zero {q : ℕ}
    (labels : Fin q → IncrementPair) :
    fixedExternalBase labels 0 = (0, 0) := rfl

theorem fixedExternalBase_succ {q : ℕ}
    (labels : Fin q → IncrementPair) {i : ℕ} (hi : i < q) :
    fixedExternalBase labels (i + 1) =
      pairEndpoint (fixedExternalBase labels i) (labels ⟨i, hi⟩) := by
  unfold fixedExternalBase
  rw [List.take_succ_eq_append_getElem (by simpa using hi), List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [List.getElem_ofFn]

theorem terminalPairIndex_exists_of_realized {q : ℕ}
    (labels : Fin q → IncrementPair) {ω : ℕ → Direction} {N i : ℕ}
    (hlabels : terminalPairLabelsThrough ω N = List.ofFn labels)
    (hi : i < q) :
    ∃ R, i < (terminalPairLabelsThrough ω (R + 1)).length := by
  have hiN : i < (terminalPairLabelsThrough ω N).length := by
    rw [hlabels]
    simpa using hi
  exact exists_terminalPairIndex_of_lt_length ω hiN

theorem externalStateAt_even_eq_fixedExternalBase {q : ℕ}
    (labels : Fin q → IncrementPair) {ω : ℕ → Direction} {N : ℕ}
    (hlabels : terminalPairLabelsThrough ω N = List.ofFn labels)
    (n : ℕ) (hn : n ≤ q) :
    externalStateAt (simpleRandomWalk ω) (2 * n) =
      fixedExternalBase labels n := by
  induction n with
  | zero =>
      change simpleRandomWalk ω
        (externalInverseMinus (simpleRandomWalk ω) 0) = (0, 0)
      rw [externalInverseMinus_zero]
      rfl
  | succ n ih =>
      have hnq : n < q := by omega
      have hex := terminalPairIndex_exists_of_realized labels hlabels hnq
      have hstart : simpleRandomWalk ω (2 * terminalPairIndex ω n) =
          fixedExternalBase labels n := by
        cases n with
        | zero =>
            have hcount := terminalPairIndex_count ω 0 hex
            have hw := simpleRandomWalk_even_eq_of_terminal_count_eq ω
                (a := 0) (b := terminalPairIndex ω 0) (by omega) (by
                  simpa [terminalPairLabelsThrough] using hcount.1.symm)
            have hzero : (0 : Site) = (0, 0) := rfl
            simpa only [simpleRandomWalk, Nat.mul_zero, Finset.range_zero, Finset.sum_empty,
              fixedExternalBase_zero, hzero] using hw.symm
        | succ k =>
            have hkq : k < q := by omega
            have hexk := terminalPairIndex_exists_of_realized labels hlabels hkq
            have horder := terminalPairIndex_strictMono ω (show k < k + 1 by omega)
              hexk hex
            have hcountk := terminalPairIndex_count ω k hexk
            have hcountn := terminalPairIndex_count ω (k + 1) hex
            have hstep := terminalPairLabelsThrough_succ_length ω
              (terminalPairIndex ω k)
            rw [if_neg hcountk.2, hcountk.1] at hstep
            have hwalk := simpleRandomWalk_even_eq_of_terminal_count_eq ω
              (a := terminalPairIndex ω k + 1)
              (b := terminalPairIndex ω (k + 1)) (by omega) (by omega)
            have ihk := ih (by omega)
            unfold externalStateAt at ihk
            rw [externalInverseMinus_even_succ ω k hexk] at ihk
            rw [show 2 * terminalPairIndex ω k + 2 =
              2 * (terminalPairIndex ω k + 1) by omega] at ihk
            exact hwalk.symm.trans ihk
      unfold externalStateAt
      rw [externalInverseMinus_even_succ ω n hex]
      rw [show 2 * terminalPairIndex ω n + 2 =
        2 * (terminalPairIndex ω n + 1) by omega,
        simpleRandomWalk_pair_succ, hstart]
      have hlabel := terminalPairIndex_label_of_realized labels hlabels
        ⟨n, hnq⟩
      have h0 := congrFun hlabel 0
      have h1 := congrFun hlabel 1
      simp only [incrementPair_zero] at h0
      simp only [incrementPair_one] at h1
      rw [h0, h1, fixedExternalBase_succ labels hnq]
      rfl

theorem chessEven_simpleRandomWalk_iff
    (ω : ℕ → Direction) (n : ℕ) :
    HLOZPairing.chessEven (simpleRandomWalk ω n) ↔ Even n := by
  induction n with
  | zero => simp [simpleRandomWalk, HLOZPairing.chessEven]
  | succ n ih =>
      rw [show n + 1 = n.succ by rfl, simpleRandomWalk_succ',
        chessEven_add_directionStep_iff, ih]
      simpa only [Nat.even_add_one]

theorem externalStateAt_odd_ne_of_realized {q : ℕ}
    (labels : Fin q → IncrementPair) {ω : ℕ → Direction} {N : ℕ}
    (hlabels : terminalPairLabelsThrough ω N = List.ofFn labels)
    (x : Site) (hx : HLOZPairing.chessEven x)
    (i : ℕ) (hi : i < q) :
    externalStateAt (simpleRandomWalk ω) (2 * i + 1) ≠ x := by
  have hex := terminalPairIndex_exists_of_realized labels hlabels hi
  unfold externalStateAt
  rw [externalInverseMinus_odd ω i hex]
  intro heq
  have hpar := (chessEven_simpleRandomWalk_iff ω
    (2 * terminalPairIndex ω i + 1)).mp (heq ▸ hx)
  rcases hpar with ⟨a, ha⟩
  omega

theorem filter_range_two_mul_of_odd_false
    (P : ℕ → Prop) [DecidablePred P]
    (q : ℕ) (hodd : ∀ i < q, ¬ P (2 * i + 1)) :
    (List.range (2 * q)).filter P =
      ((List.range q).filter fun i ↦ P (2 * i)).map fun i ↦ 2 * i := by
  induction q with
  | zero => rfl
  | succ q ih =>
      have ih' := ih (fun i hi ↦ hodd i (by omega))
      rw [show 2 * (q + 1) = (2 * q + 1) + 1 by omega,
        List.range_succ, List.range_succ, List.range_succ, List.filter_append,
        List.filter_append, List.filter_append, List.map_append, ih']
      by_cases hP : P (2 * q)
      · simp [hP, hodd q (by omega)]
      · simp [hP, hodd q (by omega)]

theorem externalVisitIndexList_eq_fixedExternalBases {q : ℕ}
    (labels : Fin q → IncrementPair) {ω : ℕ → Direction} {N : ℕ}
    (hlabels : terminalPairLabelsThrough ω N = List.ofFn labels)
    (x : Site) (hx : HLOZPairing.chessEven x) (hq : 0 < q) :
    externalVisitIndexList (simpleRandomWalk ω) (2 * q - 1) x =
      ((List.range q).filter fun i ↦ fixedExternalBase labels i = x).map
        fun i ↦ 2 * i := by
  unfold externalVisitIndexList
  rw [show 2 * q - 1 + 1 = 2 * q by omega]
  rw [filter_range_two_mul_of_odd_false
    (fun r ↦ externalStateAt (simpleRandomWalk ω) r = x) q (by
      intro i hi
      exact externalStateAt_odd_ne_of_realized labels hlabels x hx i hi)]
  congr 1
  apply List.filter_congr
  intro i hi
  rw [List.mem_range] at hi
  rw [externalStateAt_even_eq_fixedExternalBase labels hlabels i (by omega)]

def chronologicalExternalIndexList {q : ℕ}
    (labels : Fin q → IncrementPair) (x : Site) : List (Fin q) :=
  (List.ofFn id).filter fun i ↦ fixedExternalBase labels i.val = x

theorem map_chronologicalExternalIndexList {q : ℕ}
    (labels : Fin q → IncrementPair) (x : Site) :
    (chronologicalExternalIndexList labels x).map (fun i ↦ i.val) =
      (List.range q).filter fun i ↦ fixedExternalBase labels i = x := by
  unfold chronologicalExternalIndexList
  rw [List.ofFn_id]
  rw [← List.map_coe_finRange_eq_range, List.filter_map]
  rfl

theorem inverseClockProfile_eq_chronological_length {q : ℕ}
    (labels : Fin q → IncrementPair) {ω : ℕ → Direction} {N : ℕ}
    (hlabels : terminalPairLabelsThrough ω N = List.ofFn labels)
    (x : Site) (hx : HLOZPairing.chessEven x) (hq : 0 < q) :
    inverseClockProfile (simpleRandomWalk ω) (2 * q - 1) x =
      (chronologicalExternalIndexList labels x).length := by
  unfold inverseClockProfile
  rw [externalVisitIndexList_eq_fixedExternalBases labels hlabels x hx hq,
    List.length_map]
  have hmap := map_chronologicalExternalIndexList labels x
  simpa only [List.length_map] using (congrArg List.length hmap).symm

theorem chronologicalExternalIndexList_nodup {q : ℕ}
    (labels : Fin q → IncrementPair) (x : Site) :
    (chronologicalExternalIndexList labels x).Nodup := by
  apply List.Nodup.filter
  rw [List.nodup_ofFn]
  exact Function.injective_id

noncomputable def chronologicalExternalEmbedding {q cut : ℕ}
    (labels : Fin q → IncrementPair) (x : Site)
    (hcut : cut ≤ (chronologicalExternalIndexList labels x).length) :
    Fin cut → Fin q :=
  fun i ↦ ((chronologicalExternalIndexList labels x).take cut).get
    (Fin.cast (List.length_take_of_le hcut).symm i :
      Fin ((chronologicalExternalIndexList labels x).take cut).length)

theorem chronologicalExternalEmbedding_injective {q cut : ℕ}
    (labels : Fin q → IncrementPair) (x : Site)
    (hcut : cut ≤ (chronologicalExternalIndexList labels x).length) :
    Function.Injective (chronologicalExternalEmbedding labels x hcut) := by
  unfold chronologicalExternalEmbedding
  have hnd : ((chronologicalExternalIndexList labels x).take cut).Nodup :=
    (List.take_sublist cut _).nodup
      (chronologicalExternalIndexList_nodup labels x)
  intro i j hij
  have hcast := hnd.injective_get hij
  exact Fin.cast_injective _ hcast

noncomputable def decodedChronologicalHoldingPrefix {q cut : ℕ}
    (labels : Fin q → IncrementPair) (x : Site)
    (hcut : cut ≤ (chronologicalExternalIndexList labels x).length)
    (v : Fin q → ℕ) : ℕ :=
  ∑ i : Fin cut, v (chronologicalExternalEmbedding labels x hcut i)

theorem decodedChronologicalHoldingVector_hasLaw {q cut : ℕ}
    (labels : Fin q → IncrementPair) (x : Site)
    (hcut : cut ≤ (chronologicalExternalIndexList labels x).length) :
    HasLaw (runSubvector (chronologicalExternalEmbedding labels x hcut))
      (HLOZUrn.runVectorMeasure cut) (HLOZUrn.runVectorMeasure q) :=
  runSubvector_hasLaw _
    (chronologicalExternalEmbedding_injective labels x hcut)

theorem decodedChronologicalHoldingPrefix_hasLaw {q cut : ℕ}
    (labels : Fin q → IncrementPair) (x : Site)
    (hcut : cut ≤ (chronologicalExternalIndexList labels x).length) :
    HasLaw (decodedChronologicalHoldingPrefix labels x hcut)
      (HLOZUrn.negBinMeasure cut) (HLOZUrn.runVectorMeasure q) :=
  runSubvectorSum_hasLaw _
    (chronologicalExternalEmbedding_injective labels x hcut)

theorem firstPairRunsWithLabelsEqFrom_take
    (start : ℕ) (runs : List PairRun) {ω : ℕ → Direction}
    (hω : ω ∈ firstPairRunsWithLabelsEqFrom start runs)
    (i : ℕ) :
    ω ∈ firstPairRunsWithLabelsEqFrom start (runs.take i) := by
  induction runs generalizing start i with
  | nil => simp [firstPairRunsWithLabelsEqFrom]
  | cons run runs ih =>
      cases i with
      | zero => simp [firstPairRunsWithLabelsEqFrom]
      | succ i =>
          rcases run with ⟨t, p⟩
          simp only [List.take_succ_cons]
          rw [firstPairRunsWithLabelsEqFrom.eq_def] at hω ⊢
          exact ⟨hω.1, ih (start := start + t + 1) hω.2 i⟩

theorem firstPairRunsWithLabelsEqFrom_drop
    (start : ℕ) (runs : List PairRun) {ω : ℕ → Direction}
    (hω : ω ∈ firstPairRunsWithLabelsEqFrom start runs)
    (i : ℕ) :
    ω ∈ firstPairRunsWithLabelsEqFrom
      (start + pairRunsPairCount (runs.take i)) (runs.drop i) := by
  induction runs generalizing start i with
  | nil => simp [firstPairRunsWithLabelsEqFrom]
  | cons run runs ih =>
      cases i with
      | zero => simpa using hω
      | succ i =>
          rcases run with ⟨t, p⟩
          rw [firstPairRunsWithLabelsEqFrom] at hω
          simp only [List.take_succ_cons, List.drop_succ_cons,
            pairRunsPairCount_cons]
          simpa only [Nat.add_assoc] using
            ih (start := start + t + 1) hω.2 i

theorem terminalPairLabelsThrough_length_add_of_distinguished
    (ω : ℕ → Direction) (start t : ℕ)
    (hpre : ω ∈ distinguishedPairPrefixFrom start t) :
    (terminalPairLabelsThrough ω (start + t)).length =
      (terminalPairLabelsThrough ω start).length := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hprefix : ω ∈ distinguishedPairPrefixFrom start t :=
        fun r hr ↦ hpre r (by omega)
      have ht : incrementPair (start + t) ω = distinguishedIncrementPair :=
        hpre t (by omega)
      rw [show start + (t + 1) = (start + t) + 1 by omega,
        terminalPairLabelsThrough_succ_length, if_pos ht, ih hprefix]
      omega

theorem terminalPairLabelsThrough_length_add_le_of_distinguished
    (ω : ℕ → Direction) (start t r : ℕ)
    (hpre : ω ∈ distinguishedPairPrefixFrom start t) (hr : r ≤ t) :
    (terminalPairLabelsThrough ω (start + r)).length =
      (terminalPairLabelsThrough ω start).length := by
  apply terminalPairLabelsThrough_length_add_of_distinguished
  intro j hj
  exact hpre j (hj.trans_le hr)

theorem firstPairRunsWithLabelsEqFrom_segmentAt
    (start : ℕ) (runs : List PairRun) {ω : ℕ → Direction}
    (hω : ω ∈ firstPairRunsWithLabelsEqFrom start runs)
    (i : ℕ) (hi : i < runs.length) :
    ω ∈ distinguishedPairRunSegmentWithLabel
      (start + pairRunsPairCount (runs.take i)) runs[i].1 runs[i].2 := by
  have hdrop := firstPairRunsWithLabelsEqFrom_drop start runs hω i
  rw [List.drop_eq_getElem_cons hi,
    firstPairRunsWithLabelsEqFrom.eq_def] at hdrop
  exact hdrop.1

theorem terminalPairIndex_eq_pairRunStart_add_length
    (runs : List PairRun) {ω : ℕ → Direction}
    (hω : ω ∈ firstPairRunsWithLabelsEqFrom 0 runs)
    (hnondist : ∀ run ∈ runs,
      run.2 ≠ distinguishedIncrementPair)
    (i : ℕ) (hi : i < runs.length) :
    terminalPairIndex ω i =
      pairRunsPairCount (runs.take i) + runs[i].1 := by
  let start := pairRunsPairCount (runs.take i)
  let t := runs[i].1
  have hseg : ω ∈ distinguishedPairRunSegmentWithLabel start t runs[i].2 := by
    simpa [start, t] using
      firstPairRunsWithLabelsEqFrom_segmentAt 0 runs hω i hi
  have hprefix := firstPairRunsWithLabelsEqFrom_take 0 runs hω i
  have hnondistPrefix : ∀ run ∈ runs.take i,
      run.2 ≠ distinguishedIncrementPair := by
    intro run hrun
    exact hnondist run (List.mem_of_mem_take hrun)
  have hcountStart : (terminalPairLabelsThrough ω start).length = i := by
    have hterm := terminalPairLabelsThrough_eq_terminalLabels
      (runs.take i) hprefix hnondistPrefix
    change terminalPairLabelsThrough ω start = terminalLabels (runs.take i) at hterm
    have hile : i ≤ runs.length := Nat.le_of_lt hi
    have hlen := congrArg List.length hterm
    rw [show (terminalLabels (runs.take i)).length = (runs.take i).length by
      simp [terminalLabels], List.length_take_of_le hile] at hlen
    exact hlen
  have hcountCandidate :
      (terminalPairLabelsThrough ω (start + t)).length = i := by
    rw [terminalPairLabelsThrough_length_add_of_distinguished
      ω start t hseg.1, hcountStart]
  have hterminalNondist : runs[i].2 ≠ distinguishedIncrementPair :=
    hnondist runs[i] (List.getElem_mem hi)
  have hcandidatePair : incrementPair (start + t) ω = runs[i].2 := hseg.2
  have hcandidateNondist :
      incrementPair (start + t) ω ≠ distinguishedIncrementPair := by
    rw [hcandidatePair]
    exact hterminalNondist
  have hstep := terminalPairLabelsThrough_succ_length ω (start + t)
  rw [if_neg hcandidateNondist, hcountCandidate] at hstep
  have hex : ∃ R, i <
      (terminalPairLabelsThrough ω (R + 1)).length := ⟨start + t, by omega⟩
  apply le_antisymm
  · exact terminalPairIndex_minimal ω i (start + t) (by omega)
  · by_contra hnot
    have hlt : terminalPairIndex ω i < start + t := by omega
    have hcountIndex := terminalPairIndex_count ω i hex
    have hstepIndex := terminalPairLabelsThrough_succ_length ω
      (terminalPairIndex ω i)
    rw [if_neg hcountIndex.2, hcountIndex.1] at hstepIndex
    have hmono := terminalPairLabelsThrough_length_mono ω
      (show terminalPairIndex ω i + 1 ≤ start + t by omega)
    rw [hstepIndex, hcountCandidate] at hmono
    omega

theorem completedPairBlockIndices_eq_pairRunIco
    (runs : List PairRun) {ω : ℕ → Direction}
    (hω : ω ∈ firstPairRunsWithLabelsEqFrom 0 runs)
    (hnondist : ∀ run ∈ runs,
      run.2 ≠ distinguishedIncrementPair)
    (i : ℕ) (hi : i < runs.length) :
    completedPairBlockIndices ω (pairRunsPairCount runs) (2 * i) =
      Finset.Ico (pairRunsPairCount (runs.take i))
        (pairRunsPairCount (runs.take i) + runs[i].1) := by
  let start := pairRunsPairCount (runs.take i)
  let t := runs[i].1
  let candidate := start + t
  have hseg : ω ∈ distinguishedPairRunSegmentWithLabel start t runs[i].2 := by
    simpa [start, t] using
      firstPairRunsWithLabelsEqFrom_segmentAt 0 runs hω i hi
  have hprefix := firstPairRunsWithLabelsEqFrom_take 0 runs hω i
  have hnondistPrefix : ∀ run ∈ runs.take i,
      run.2 ≠ distinguishedIncrementPair := by
    intro run hrun
    exact hnondist run (List.mem_of_mem_take hrun)
  have hcountStart : (terminalPairLabelsThrough ω start).length = i := by
    have hterm := terminalPairLabelsThrough_eq_terminalLabels
      (runs.take i) hprefix hnondistPrefix
    change terminalPairLabelsThrough ω start = terminalLabels (runs.take i) at hterm
    have hile : i ≤ runs.length := Nat.le_of_lt hi
    have hlen := congrArg List.length hterm
    rw [show (terminalLabels (runs.take i)).length = (runs.take i).length by
      simp [terminalLabels], List.length_take_of_le hile] at hlen
    exact hlen
  have hcountCandidate :
      (terminalPairLabelsThrough ω candidate).length = i := by
    dsimp only [candidate]
    rw [terminalPairLabelsThrough_length_add_of_distinguished
      ω start t hseg.1, hcountStart]
  have hterminalNondist : runs[i].2 ≠ distinguishedIncrementPair :=
    hnondist runs[i] (List.getElem_mem hi)
  have hcandidatePair : incrementPair candidate ω = runs[i].2 := by
    exact hseg.2
  have hcandidateNondist :
      incrementPair candidate ω ≠ distinguishedIncrementPair := by
    rw [hcandidatePair]
    exact hterminalNondist
  have hstepCandidate := terminalPairLabelsThrough_succ_length ω candidate
  rw [if_neg hcandidateNondist, hcountCandidate] at hstepCandidate
  have hindex : terminalPairIndex ω i = candidate := by
    simpa [candidate, start, t] using
      terminalPairIndex_eq_pairRunStart_add_length runs hω hnondist i hi
  have hfullLabels := terminalPairLabelsThrough_eq_terminalLabels
    runs hω hnondist
  have hNpos : 0 < pairRunsPairCount runs := by
    by_contra hN
    have hNzero : pairRunsPairCount runs = 0 := by omega
    rw [hNzero] at hfullLabels
    have hlen := congrArg List.length hfullLabels
    simp [terminalPairLabelsThrough, terminalLabels] at hlen
    omega
  have hcandidateN : candidate < pairRunsPairCount runs := by
    have hfullLen : i < (terminalPairLabelsThrough ω
        (pairRunsPairCount runs)).length := by
      rw [hfullLabels]
      simpa [terminalLabels] using hi
    have hmin := terminalPairIndex_minimal ω i
      (pairRunsPairCount runs - 1) (by
        simpa [Nat.sub_add_cancel (by omega : 1 ≤ pairRunsPairCount runs)]
          using hfullLen)
    rw [hindex] at hmin
    omega
  ext r
  rw [Finset.mem_Ico]
  unfold completedPairBlockIndices
  rw [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hrN, hrDist, hrCount⟩
    have hlenr : (terminalPairLabelsThrough ω r).length = i := by omega
    have hrStart : start ≤ r := by
      by_contra hnot
      have hrlt : r < start := by omega
      cases i with
      | zero =>
          simp [start, pairRunsPairCount] at hrlt
      | succ k =>
          have hk : k < runs.length := by omega
          have hprev := terminalPairIndex_eq_pairRunStart_add_length
            runs hω hnondist k hk
          have hstartPrev : start =
              pairRunsPairCount (runs.take k) + runs[k].1 + 1 := by
            unfold start pairRunsPairCount
            rw [List.map_take, List.sum_take_succ]
            · rw [List.map_take, List.getElem_map]
              omega
            · simpa using hk
          have hrPrev : r ≤ terminalPairIndex ω k := by
            rw [hstartPrev, ← hprev] at hrlt
            omega
          have hmono := terminalPairLabelsThrough_length_mono ω hrPrev
          rw [hlenr, (terminalPairIndex_count ω k (by
            refine ⟨candidate, ?_⟩
            omega)).1] at hmono
          omega
    have hrCandidate : r < candidate := by
      by_contra hnot
      have hle : candidate ≤ r := by omega
      rcases hle.eq_or_lt with rfl | hlt
      · exact hcandidateNondist hrDist
      · have hmono := terminalPairLabelsThrough_length_mono ω
          (show candidate + 1 ≤ r by omega)
        rw [hstepCandidate, hlenr] at hmono
        omega
    exact ⟨hrStart, hrCandidate⟩
  · rintro ⟨hrStart, hrCandidate⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrStart
    have hd : d < t := by
      change start + d < start + t at hrCandidate
      omega
    have hdist : incrementPair (start + d) ω =
        distinguishedIncrementPair := hseg.1 d hd
    have hlen : (terminalPairLabelsThrough ω (start + d)).length = i := by
      rw [terminalPairLabelsThrough_length_add_le_of_distinguished
        ω start t d hseg.1 (by omega), hcountStart]
    have hrN : start + d < pairRunsPairCount runs := by
      have : start + d < candidate := by
        unfold candidate
        omega
      exact this.trans hcandidateN
    exact ⟨hrN, hdist, by rw [hlen]⟩

theorem completedPairBlockIndices_card_eq_pairRunLength
    (runs : List PairRun) {ω : ℕ → Direction}
    (hω : ω ∈ firstPairRunsWithLabelsEqFrom 0 runs)
    (hnondist : ∀ run ∈ runs,
      run.2 ≠ distinguishedIncrementPair)
    (i : ℕ) (hi : i < runs.length) :
    (completedPairBlockIndices ω (pairRunsPairCount runs) (2 * i)).card =
      runs[i].1 := by
  rw [completedPairBlockIndices_eq_pairRunIco runs hω hnondist i hi]
  simp

theorem paperHoldingNat_even_eq_conditionalPairRunVector {q : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    {ω : ℕ → Direction}
    (hω : ω ∈ firstPairExternalPathEqFrom 0
      (externalPathFromLabels (List.ofFn labels)))
    (i : Fin q) :
    paperHoldingNat (simpleRandomWalk ω) (2 * i.val) =
      listVectorToFin labels
        (conditionalPairRunVector 0 (List.ofFn labels) ω) i := by
  have hterm : ω ∈ firstPairTerminalLabelsEqFrom 0 (List.ofFn labels) := by
    simpa [firstPairExternalPathEqFrom_reconstructed] using hω
  let v := conditionalPairRunVector 0 (List.ofFn labels) ω
  have hnondistList : ∀ p ∈ List.ofFn labels,
      p ≠ distinguishedIncrementPair := by
    intro p hp
    rw [List.mem_ofFn] at hp
    rcases hp with ⟨j, rfl⟩
    exact hnondist j
  have hrunPair : ω ∈ pairRunsAndLabelsEqFrom 0
      (List.ofFn v) (List.ofFn labels) :=
    (conditionalPairRunVector_eq_iff 0 (List.ofFn labels)
      hnondistList v hterm).mp rfl
  let runs := List.zip (List.ofFn v) (List.ofFn labels)
  have hrun : ω ∈ firstPairRunsWithLabelsEqFrom 0 runs := hrunPair
  have hrunsNondist : ∀ run ∈ runs,
      run.2 ≠ distinguishedIncrementPair := by
    intro run hrunMem
    rcases run with ⟨t, p⟩
    exact hnondistList p (List.of_mem_zip hrunMem).2
  have hlabels : terminalPairLabelsThrough ω (pairRunsPairCount runs) =
      List.ofFn labels := by
    rw [terminalPairLabelsThrough_eq_terminalLabels runs hrun hrunsNondist]
    simpa [runs] using terminalLabels_zip_ofFn (List.ofFn labels) v
  have hiLabels : i.val <
      (terminalPairLabelsThrough ω (pairRunsPairCount runs)).length := by
    rw [hlabels]
    simp
  have hiRuns : i.val < runs.length := by
    simp [runs]
  calc
    paperHoldingNat (simpleRandomWalk ω) (2 * i.val) =
        stoppedExcursionBlock (simpleRandomWalk ω)
          (2 * pairRunsPairCount runs) (2 * i.val) :=
      paperHoldingNat_even_eq_stoppedExcursionBlock ω
        (pairRunsPairCount runs) i.val hiLabels
    _ = (completedPairBlockIndices ω (pairRunsPairCount runs)
          (2 * i.val)).card :=
      stoppedExcursionBlock_even_eq_pairBlock_card ω
        (pairRunsPairCount runs) (2 * i.val)
    _ = runs[i.val].1 :=
      completedPairBlockIndices_card_eq_pairRunLength runs hrun
        hrunsNondist i.val hiRuns
    _ = listVectorToFin labels v i := by
      simp [runs, listVectorToFin]

theorem externalVisitIndexList_eq_chronologicalExternalIndexList {q : ℕ}
    (labels : Fin q → IncrementPair) {ω : ℕ → Direction} {N : ℕ}
    (hlabels : terminalPairLabelsThrough ω N = List.ofFn labels)
    (x : Site) (hx : HLOZPairing.chessEven x) (hq : 0 < q) :
    externalVisitIndexList (simpleRandomWalk ω) (2 * q - 1) x =
      (chronologicalExternalIndexList labels x).map fun i ↦ 2 * i.val := by
  rw [externalVisitIndexList_eq_fixedExternalBases labels hlabels x hx hq,
    ← map_chronologicalExternalIndexList labels x, List.map_map]
  rfl

theorem sum_map_take_eq_chronological_sum {q cut : ℕ}
    (labels : Fin q → IncrementPair) (x : Site)
    (hcut : cut ≤ (chronologicalExternalIndexList labels x).length)
    (v : Fin q → ℕ) :
    (((chronologicalExternalIndexList labels x).take cut).map v).sum =
      decodedChronologicalHoldingPrefix labels x hcut v := by
  unfold decodedChronologicalHoldingPrefix chronologicalExternalEmbedding
  rw [← List.sum_ofFn]
  apply congrArg List.sum
  apply List.ext_get
  · simp only [List.length_map, List.length_ofFn]
    exact List.length_take_of_le hcut
  · intro k hk₁ hk₂
    simp

theorem inverseClockHoldingPrefix_eq_decodedChronological {q cut : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    {ω : ℕ → Direction}
    (hω : ω ∈ firstPairExternalPathEqFrom 0
      (externalPathFromLabels (List.ofFn labels)))
    (x : Site) (hx : HLOZPairing.chessEven x) (hq : 0 < q)
    (hcut : cut ≤ (chronologicalExternalIndexList labels x).length) :
    inverseClockHoldingPrefix (simpleRandomWalk ω) (2 * q - 1) cut x =
      decodedChronologicalHoldingPrefix labels x hcut
        (listVectorToFin labels
          (conditionalPairRunVector 0 (List.ofFn labels) ω)) := by
  obtain ⟨N, hlabels⟩ :=
    realized_terminalPairLabelsThrough labels hnondist hω
  unfold inverseClockHoldingPrefix
  rw [externalVisitIndexList_eq_chronologicalExternalIndexList
    labels hlabels x hx hq, ← List.map_take, List.map_map]
  change ((((chronologicalExternalIndexList labels x).take cut).map
    fun i : Fin q ↦ paperHoldingNat (simpleRandomWalk ω) (2 * i.val))).sum = _
  simp_rw [paperHoldingNat_even_eq_conditionalPairRunVector
    labels hnondist hω]
  exact sum_map_take_eq_chronological_sum labels x hcut _

theorem conditional_decodedChronologicalHoldingVector_hasLaw {q cut : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (x : Site)
    (hcut : cut ≤ (chronologicalExternalIndexList labels x).length) :
    HasLaw
      (fun ω ↦ runSubvector (chronologicalExternalEmbedding labels x hcut)
        (listVectorToFin labels
          (conditionalPairRunVector 0 (List.ofFn labels) ω)))
      (HLOZUrn.runVectorMeasure cut)
      incrementLaw[|firstPairExternalPathEqFrom 0
        (externalPathFromLabels (List.ofFn labels))] := by
  have hvec := conditionalPairRunVector_hasLaw 0 (List.ofFn labels) (by
    intro p hp
    rw [List.mem_ofFn] at hp
    rcases hp with ⟨i, rfl⟩
    exact hnondist i)
  have hcast := (listVectorToFin_hasLaw labels).fun_comp hvec
  exact (decodedChronologicalHoldingVector_hasLaw labels x hcut).fun_comp hcast

theorem conditional_decodedChronologicalHoldingPrefix_hasLaw {q cut : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (x : Site)
    (hcut : cut ≤ (chronologicalExternalIndexList labels x).length) :
    HasLaw
      (fun ω ↦ decodedChronologicalHoldingPrefix labels x hcut
        (listVectorToFin labels
          (conditionalPairRunVector 0 (List.ofFn labels) ω)))
      (HLOZUrn.negBinMeasure cut)
      incrementLaw[|firstPairExternalPathEqFrom 0
        (externalPathFromLabels (List.ofFn labels))] := by
  have hvec := conditionalPairRunVector_hasLaw 0 (List.ofFn labels) (by
    intro p hp
    rw [List.mem_ofFn] at hp
    rcases hp with ⟨i, rfl⟩
    exact hnondist i)
  have hcast := (listVectorToFin_hasLaw labels).fun_comp hvec
  exact (decodedChronologicalHoldingPrefix_hasLaw labels x hcut).fun_comp hcast

theorem measurable_conditionalDecodedChronologicalHoldingPrefix {q cut : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (x : Site)
    (hcut : cut ≤ (chronologicalExternalIndexList labels x).length) :
    Measurable
      (fun ω ↦ decodedChronologicalHoldingPrefix labels x hcut
        (listVectorToFin labels
          (conditionalPairRunVector 0 (List.ofFn labels) ω))) := by
  have hruns : Measurable
      (conditionalPairRunVector 0 (List.ofFn labels)) :=
    measurable_conditionalPairRunVector 0 (List.ofFn labels) (by
      intro p hp
      rw [List.mem_ofFn] at hp
      rcases hp with ⟨i, rfl⟩
      exact hnondist i)
  exact (measurable_of_countable
    (fun v : Fin q → ℕ ↦ decodedChronologicalHoldingPrefix labels x hcut v)).comp
      ((measurable_of_countable (listVectorToFin labels)).comp hruns)

noncomputable def pathDecodedChronologicalHoldingPrefix {q cut : ℕ}
    (labels : Fin q → IncrementPair) (x : Site)
    (hcut : cut ≤ (chronologicalExternalIndexList labels x).length) :
    (ℕ → Site) → ℕ :=
  Function.extend simpleRandomWalk
    (fun ω ↦ decodedChronologicalHoldingPrefix labels x hcut
      (listVectorToFin labels
        (conditionalPairRunVector 0 (List.ofFn labels) ω))) 0

theorem measurable_pathDecodedChronologicalHoldingPrefix {q cut : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (x : Site)
    (hcut : cut ≤ (chronologicalExternalIndexList labels x).length) :
    Measurable (pathDecodedChronologicalHoldingPrefix labels x hcut) := by
  apply measurableEmbedding_simpleRandomWalk.measurable_extend
  · exact measurable_conditionalDecodedChronologicalHoldingPrefix
      labels hnondist x hcut
  · exact measurable_const

theorem pathDecodedChronologicalHoldingPrefix_simpleRandomWalk {q cut : ℕ}
    (labels : Fin q → IncrementPair) (x : Site)
    (hcut : cut ≤ (chronologicalExternalIndexList labels x).length)
    (ω : ℕ → Direction) :
    pathDecodedChronologicalHoldingPrefix labels x hcut (simpleRandomWalk ω) =
      decodedChronologicalHoldingPrefix labels x hcut
        (listVectorToFin labels
          (conditionalPairRunVector 0 (List.ofFn labels) ω)) := by
  unfold pathDecodedChronologicalHoldingPrefix
  exact simpleRandomWalk_injective.extend_apply _ _ ω

theorem pathDecodedChronologicalHoldingPrefix_hasLaw {q cut : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (x : Site)
    (hcut : cut ≤ (chronologicalExternalIndexList labels x).length) :
    HasLaw (pathDecodedChronologicalHoldingPrefix labels x hcut)
      (HLOZUrn.negBinMeasure cut)
      simpleRandomWalkLaw[|externalPathWalkAtom (List.ofFn labels)] := by
  rw [simpleRandomWalkLaw]
  apply HasLaw.cond_map_image measurableEmbedding_simpleRandomWalk
    (measurableSet_externalPathAtom 0 (List.ofFn labels))
  · exact measurable_conditionalDecodedChronologicalHoldingPrefix
      labels hnondist x hcut
  · intro ω _
    exact pathDecodedChronologicalHoldingPrefix_simpleRandomWalk labels x hcut ω
  · exact conditional_decodedChronologicalHoldingPrefix_hasLaw
      labels hnondist x hcut

/-- The unfiltered inverse-clock holding-prefix law on a fixed finite
external-path atom.  Endpoint parity and profile support are explicit. -/
theorem inverseClockHoldingPrefix_hasLaw_fixedExternalPath {q cut : ℕ}
    (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    (x : Site) (hx : HLOZPairing.chessEven x) (hq : 0 < q)
    (hcut : cut ≤ (chronologicalExternalIndexList labels x).length) :
    HasLaw
      (fun s ↦ inverseClockHoldingPrefix s (2 * q - 1) cut x)
      (HLOZUrn.negBinMeasure cut)
      simpleRandomWalkLaw[|externalPathWalkAtom (List.ofFn labels)] := by
  rw [simpleRandomWalkLaw]
  apply HasLaw.cond_map_image measurableEmbedding_simpleRandomWalk
    (measurableSet_externalPathAtom 0 (List.ofFn labels))
  · exact measurable_conditionalDecodedChronologicalHoldingPrefix
      labels hnondist x hcut
  · intro ω hω
    exact inverseClockHoldingPrefix_eq_decodedChronological
      labels hnondist hω x hx hq hcut
  · exact conditional_decodedChronologicalHoldingPrefix_hasLaw
      labels hnondist x hcut

end Erdos1166.HLOZSourceInstantiation
