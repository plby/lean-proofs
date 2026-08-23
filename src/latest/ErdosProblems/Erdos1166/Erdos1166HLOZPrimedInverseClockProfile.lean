import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Prop45XEast

/-!
# Exact inverse-clock profile for the one-step-shifted deletion

The primed deletion begins after the first increment.  Swapping each pair in
the remaining increment sequence converts its distinguished pair to the
ordinary unprimed distinguished pair.  This file proves the full deterministic
transport: primed clocks, inverse states, profiles, and holding prefixes are
the translated unprimed objects of the swapped suffix.
-/

namespace Erdos1166.HLOZProp47Prop45XEastPrimed

open HLOZDecomposition HLOZReconstruction HLOZPrimedStopped
open HLOZProp42InverseLaw HLOZSourceInstantiation
open HLOZProp45SourceClock

noncomputable def primedOneShift : (ℕ → Direction) → ℕ := fun _ ↦ 1

def primedRelativeSite (first : Direction) (x : Site) : Site :=
  x - directionStep first

@[simp] theorem swappedIncrementShiftAfter_one_even
    (omega : ℕ → Direction) (r : ℕ) :
    swappedIncrementShiftAfter primedOneShift omega (2 * r) =
      omega (2 * r + 2) := by
  simp [swappedIncrementShiftAfter, swapAdjacentPairs, incrementShiftAfter,
    primedOneShift]
  congr 1
  omega

@[simp] theorem swappedIncrementShiftAfter_one_odd
    (omega : ℕ → Direction) (r : ℕ) :
    swappedIncrementShiftAfter primedOneShift omega (2 * r + 1) =
      omega (2 * r + 1) := by
  simp [swappedIncrementShiftAfter, swapAdjacentPairs, incrementShiftAfter,
    primedOneShift]
  congr 1
  omega

theorem isPrimedLazyEnd_simpleRandomWalk_pair_iff
    (omega : ℕ → Direction) (r : ℕ) :
    IsPrimedLazyEnd (simpleRandomWalk omega) (2 * r + 3) ↔
      incrementPair r (swappedIncrementShiftAfter primedOneShift omega) =
        distinguishedIncrementPair := by
  rw [incrementPair_eq_distinguished_iff]
  simp only [IsPrimedLazyEnd]
  rw [show 2 * r + 3 - 2 = 2 * r + 1 by omega,
    show 2 * r + 3 - 1 = 2 * r + 2 by omega,
    show 2 * r + 2 = (2 * r + 1) + 1 by omega,
    simpleRandomWalk_succ' omega (2 * r + 1),
    show 2 * r + 3 = (2 * r + 2) + 1 by omega,
    simpleRandomWalk_succ' omega (2 * r + 2),
    simpleRandomWalk_succ' omega (2 * r + 1)]
  simp only [swappedIncrementShiftAfter_one_even,
    swappedIncrementShiftAfter_one_odd]
  have hodd : Odd (2 * r + 3) := by
    use r + 1
    omega
  simp only [show 3 ≤ 2 * r + 3 by omega, hodd, true_and]
  generalize hbase : simpleRandomWalk omega (2 * r + 1) = base
  rcases base with ⟨x, y⟩
  generalize hfirst : omega (2 * r + 1) = first
  generalize hsecond : omega (2 * r + 2) = second
  fin_cases first <;> fin_cases second <;>
    norm_num [paperE1, directionStep] <;> omega

theorem isPrimedLazyEnd_succ_iff_isLazyEnd_swapped
    (omega : ℕ → Direction) (n : ℕ) :
    IsPrimedLazyEnd (simpleRandomWalk omega) (n + 1) ↔
      IsLazyEnd
        (simpleRandomWalk (swappedIncrementShiftAfter primedOneShift omega)) n := by
  rcases Nat.even_or_odd' n with ⟨r, hr | hr⟩
  · subst n
    cases r with
    | zero => simp [IsPrimedLazyEnd, IsLazyEnd]
    | succ r =>
        rw [show 2 * (r + 1) + 1 = 2 * r + 3 by omega,
          isPrimedLazyEnd_simpleRandomWalk_pair_iff,
          show 2 * (r + 1) = 2 * r + 2 by omega,
          isLazyEnd_simpleRandomWalk_pair_iff]
  · subst n
    have heven : Even (2 * r + 2) := ⟨r + 1, by omega⟩
    simp [IsPrimedLazyEnd, IsLazyEnd, heven]

theorem primedLazyEndsThrough_succ_eq_image
    (omega : ℕ → Direction) (n : ℕ) :
    primedLazyEndsThrough (simpleRandomWalk omega) (n + 1) =
      (lazyEndsThrough
        (simpleRandomWalk (swappedIncrementShiftAfter primedOneShift omega)) n).image
          Nat.succ := by
  classical
  ext j
  simp only [primedLazyEndsThrough, lazyEndsThrough, Finset.mem_filter,
    Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hj3, hjn⟩, hjlazy⟩
    refine ⟨j - 1, ?_, by omega⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have h := (isPrimedLazyEnd_succ_iff_isLazyEnd_swapped omega (j - 1)).mp ?_
    · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j)] using h
    · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j)] using hjlazy
  · rintro ⟨i, ⟨⟨hi2, hin⟩, hilazy⟩, rfl⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    simpa only using
      (isPrimedLazyEnd_succ_iff_isLazyEnd_swapped omega i).mpr hilazy

theorem primedExternalClock_succ_eq_paperExternalClock
    (omega : ℕ → Direction) (n : ℕ) :
    primedExternalClock (simpleRandomWalk omega) (n + 1) =
      paperExternalClock
        (simpleRandomWalk (swappedIncrementShiftAfter primedOneShift omega)) n + 1 := by
  classical
  let eta := swappedIncrementShiftAfter primedOneShift omega
  rcases Nat.even_or_odd' n with ⟨r, hr | hr⟩
  · subst n
    unfold primedExternalClock paperExternalClock
    rw [primedLazyEndsThrough_succ_eq_image]
    rw [Finset.card_image_of_injective _ Nat.succ_injective]
    have hpartial : ¬ IsPrimedLazyEnd (simpleRandomWalk omega)
        (2 * r + 1 + 1) := by
      rw [isPrimedLazyEnd_succ_iff_isLazyEnd_swapped]
      exact not_isLazyEnd_odd (simpleRandomWalk eta) r
    have hpaper : ¬ IsLazyEnd (simpleRandomWalk eta) (2 * r + 1) :=
      not_isLazyEnd_odd (simpleRandomWalk eta) r
    rw [if_neg hpartial, if_neg hpaper, lazyEndsThrough_even_card]
    have hcount := distinguished_add_terminal_count eta r
    dsimp only [eta] at hcount
    omega
  · subst n
    unfold primedExternalClock paperExternalClock
    rw [primedLazyEndsThrough_succ_eq_image]
    rw [Finset.card_image_of_injective _ Nat.succ_injective]
    rw [lazyEndsThrough_odd_eq_even, lazyEndsThrough_even_card]
    have hpartial : IsPrimedLazyEnd (simpleRandomWalk omega)
          (2 * r + 1 + 1 + 1) ↔
        IsLazyEnd (simpleRandomWalk eta) (2 * r + 1 + 1) := by
      simpa only [add_assoc] using
        isPrimedLazyEnd_succ_iff_isLazyEnd_swapped omega (2 * r + 1 + 1)
    rw [if_congr hpartial rfl rfl]
    have hcount := distinguished_add_terminal_count eta r
    dsimp only [eta] at hcount
    split <;> omega

@[simp] theorem primedExternalClock_zero (omega : ℕ → Direction) :
    primedExternalClock (simpleRandomWalk omega) 0 = 0 := by
  classical
  unfold primedExternalClock primedLazyEndsThrough IsPrimedLazyEnd
  simp

theorem primedExternalInverseMinus_succ_eq
    (omega : ℕ → Direction) (q : ℕ)
    (hex : ∃ n, paperExternalClock
      (simpleRandomWalk (swappedIncrementShiftAfter primedOneShift omega)) n = q) :
    primedExternalInverseMinus (simpleRandomWalk omega) (q + 1) =
      externalInverseMinus
        (simpleRandomWalk (swappedIncrementShiftAfter primedOneShift omega)) q + 1 := by
  let eta := swappedIncrementShiftAfter primedOneShift omega
  let t := simpleRandomWalk eta
  have hextSpec : paperExternalClock t (externalInverseMinus t q) = q :=
    externalInverseMinus_spec hex
  have hprimedCand : primedExternalClock (simpleRandomWalk omega)
      (externalInverseMinus t q + 1) = q + 1 := by
    rw [primedExternalClock_succ_eq_paperExternalClock]
    exact congrArg (fun a ↦ a + 1) hextSpec
  apply le_antisymm
  · exact primedExternalInverseMinus_minimal hprimedCand
  · have hprimedSpec : primedExternalClock (simpleRandomWalk omega)
        (primedExternalInverseMinus (simpleRandomWalk omega) (q + 1)) = q + 1 :=
      primedExternalInverseMinus_spec ⟨_, hprimedCand⟩
    have hne : primedExternalInverseMinus (simpleRandomWalk omega) (q + 1) ≠ 0 := by
      intro hz
      rw [hz, primedExternalClock_zero] at hprimedSpec
      omega
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hne
    rw [hn, primedExternalClock_succ_eq_paperExternalClock] at hprimedSpec
    have ht : paperExternalClock t n = q := by
      dsimp only [t, eta]
      omega
    have hmin := externalInverseMinus_minimal ht
    dsimp only [t, eta] at hmin
    omega

theorem simpleRandomWalk_odd_eq_first_add_swapped_even
    (omega : ℕ → Direction) (r : ℕ) :
    simpleRandomWalk omega (2 * r + 1) =
      directionStep (omega 0) +
        simpleRandomWalk (swappedIncrementShiftAfter primedOneShift omega) (2 * r) := by
  induction r with
  | zero => simp [simpleRandomWalk]
  | succ r ih =>
      rw [show 2 * (r + 1) + 1 = (2 * r + 1 + 1) + 1 by omega,
        simpleRandomWalk_succ', simpleRandomWalk_succ', ih]
      rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega,
        simpleRandomWalk_succ', simpleRandomWalk_succ']
      simp only [swappedIncrementShiftAfter_one_even,
        swappedIncrementShiftAfter_one_odd]
      abel

theorem primedExcursionEndSet_succ_eq_image
    (omega : ℕ → Direction) (q : ℕ) :
    primedExcursionEndSet (simpleRandomWalk omega) (q + 1) =
      Nat.succ '' excursionEndSet
        (simpleRandomWalk (swappedIncrementShiftAfter primedOneShift omega)) q := by
  ext j
  constructor
  · rintro ⟨hjlazy, hjclock⟩
    have hj3 : 3 ≤ j := hjlazy.1
    refine ⟨j - 1, ?_, by omega⟩
    refine ⟨?_, ?_⟩
    · apply (isPrimedLazyEnd_succ_iff_isLazyEnd_swapped omega (j - 1)).mp
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j)] using hjlazy
    · have hclock := primedExternalClock_succ_eq_paperExternalClock
          omega (j - 3)
      have hjsub : j - 2 = (j - 3) + 1 := by omega
      rw [hjsub, hclock] at hjclock
      simpa only [show j - 1 - 2 = j - 3 by omega] using
        (show paperExternalClock
            (simpleRandomWalk (swappedIncrementShiftAfter primedOneShift omega))
              (j - 3) = q by omega)
  · rintro ⟨i, ⟨hilazy, hiclock⟩, rfl⟩
    have hi2 : 2 ≤ i := hilazy.1
    refine ⟨?_, ?_⟩
    · exact (isPrimedLazyEnd_succ_iff_isLazyEnd_swapped omega i).mpr hilazy
    · have hclock := primedExternalClock_succ_eq_paperExternalClock
          omega (i - 2)
      have hsub : i + 1 - 2 = (i - 2) + 1 := by omega
      rw [hsub, hclock]
      have : paperExternalClock
          (simpleRandomWalk (swappedIncrementShiftAfter primedOneShift omega))
            (i - 2) = q := by
        simpa only using hiclock
      omega

theorem primedHoldingNat_succ_eq_paperHoldingNat
    (omega : ℕ → Direction) (q : ℕ) :
    primedHoldingNat (simpleRandomWalk omega) (q + 1) =
      paperHoldingNat
        (simpleRandomWalk (swappedIncrementShiftAfter primedOneShift omega)) q := by
  unfold primedHoldingNat primedHoldingTime paperHoldingNat paperHoldingTime
  rw [primedExcursionEndSet_succ_eq_image,
    Nat.succ_injective.encard_image]

@[simp] theorem primedExternalInverseMinus_zero
    (omega : ℕ → Direction) :
    primedExternalInverseMinus (simpleRandomWalk omega) 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply primedExternalInverseMinus_minimal
  exact primedExternalClock_zero omega

theorem paperExternalClock_even_terminal_succ
    {q : ℕ} (labels : Fin q → IncrementPair)
    {eta : ℕ → Direction} {N i : ℕ}
    (hlabels : terminalPairLabelsThrough eta N = List.ofFn labels)
    (hi : i < q) :
    ∃ n, paperExternalClock (simpleRandomWalk eta) n = 2 * (i + 1) := by
  have hex := terminalPairIndex_exists_of_realized labels hlabels hi
  let R := terminalPairIndex eta i
  refine ⟨2 * (R + 1), ?_⟩
  rw [paperExternalClock_even_eq_external_length,
    externalDirectionsFromLabels_length,
    terminalPairLabelsThrough_succ_length,
    if_neg (terminalPairIndex_count eta i hex).2,
    (terminalPairIndex_count eta i hex).1]

theorem primedExternalStateAt_odd_eq_fixedExternalBase
    {q : ℕ} (labels : Fin q → IncrementPair)
    {omega : ℕ → Direction} {N : ℕ}
    (hlabels : terminalPairLabelsThrough
      (swappedIncrementShiftAfter primedOneShift omega) N = List.ofFn labels)
    (i : ℕ) (hi : i < q) :
    primedExternalStateAt (simpleRandomWalk omega) (2 * i + 1) =
      directionStep (omega 0) + fixedExternalBase labels i := by
  let eta := swappedIncrementShiftAfter primedOneShift omega
  have hex : ∃ n, paperExternalClock (simpleRandomWalk eta) n = 2 * i := by
    cases i with
    | zero =>
        refine ⟨0, ?_⟩
        simp [paperExternalClock, lazyEndsThrough, IsLazyEnd]
    | succ j =>
        exact paperExternalClock_even_terminal_succ labels hlabels
          (i := j) (by omega)
  unfold primedExternalStateAt
  rw [show 2 * i + 1 = 2 * i + 1 by rfl,
    primedExternalInverseMinus_succ_eq omega (2 * i) hex]
  cases i with
  | zero =>
      rw [externalInverseMinus_zero]
      simpa [simpleRandomWalk] using
        simpleRandomWalk_odd_eq_first_add_swapped_even omega 0
  | succ j =>
      have hexj := terminalPairIndex_exists_of_realized labels hlabels
        (show j < q by omega)
      rw [externalInverseMinus_even_succ eta j hexj]
      rw [show 2 * terminalPairIndex eta j + 2 =
        2 * (terminalPairIndex eta j + 1) by omega]
      rw [simpleRandomWalk_odd_eq_first_add_swapped_even]
      have hstate := externalStateAt_even_eq_fixedExternalBase labels hlabels
        (j + 1) (show j + 1 ≤ q by omega)
      unfold externalStateAt at hstate
      rw [externalInverseMinus_even_succ eta j hexj] at hstate
      rw [show 2 * terminalPairIndex eta j + 2 =
        2 * (terminalPairIndex eta j + 1) by omega] at hstate
      exact congrArg (fun y ↦ directionStep (omega 0) + y) hstate

theorem primedExternalStateAt_even_chessEven
    {q : ℕ} (labels : Fin q → IncrementPair)
    {omega : ℕ → Direction} {N : ℕ}
    (hlabels : terminalPairLabelsThrough
      (swappedIncrementShiftAfter primedOneShift omega) N = List.ofFn labels)
    (i : ℕ) (hi : i < q) :
    HLOZPairing.chessEven
      (primedExternalStateAt (simpleRandomWalk omega) (2 * i)) := by
  let eta := swappedIncrementShiftAfter primedOneShift omega
  cases i with
  | zero =>
      unfold primedExternalStateAt
      rw [primedExternalInverseMinus_zero]
      simp [simpleRandomWalk, HLOZPairing.chessEven]
  | succ j =>
      have hexj := terminalPairIndex_exists_of_realized labels hlabels
        (show j < q by omega)
      have hexOdd : ∃ n, paperExternalClock (simpleRandomWalk eta) n =
          2 * j + 1 := by
        let R := terminalPairIndex eta j
        refine ⟨2 * R + 1, ?_⟩
        rw [paperExternalClock_odd_eq_terminal_length,
          (terminalPairIndex_count eta j hexj).1,
          if_neg (terminalPairIndex_count eta j hexj).2]
      unfold primedExternalStateAt
      rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega,
        primedExternalInverseMinus_succ_eq omega (2 * j + 1) hexOdd,
        externalInverseMinus_odd eta j hexj]
      apply (chessEven_simpleRandomWalk_iff omega _).mpr
      use terminalPairIndex eta j + 1
      omega

theorem filter_range_two_mul_of_even_false
    (P : ℕ → Prop) [DecidablePred P]
    (q : ℕ) (heven : ∀ i < q, ¬ P (2 * i)) :
    (List.range (2 * q)).filter P =
      ((List.range q).filter fun i ↦ P (2 * i + 1)).map fun i ↦ 2 * i + 1 := by
  induction q with
  | zero => rfl
  | succ q ih =>
      have ih' := ih (fun i hi ↦ heven i (by omega))
      rw [show 2 * (q + 1) = (2 * q + 1) + 1 by omega,
        List.range_succ, List.range_succ, List.range_succ, List.filter_append,
        List.filter_append, List.filter_append, List.map_append, ih']
      by_cases hP : P (2 * q + 1)
      · simp [hP, heven q (by omega)]
      · simp [hP, heven q (by omega)]

theorem primedExternalVisitIndexList_eq_chronological
    {q : ℕ} (labels : Fin q → IncrementPair)
    {omega : ℕ → Direction} {N : ℕ}
    (hlabels : terminalPairLabelsThrough
      (swappedIncrementShiftAfter primedOneShift omega) N = List.ofFn labels)
    (x : Site) (hx : ¬ HLOZPairing.chessEven x) (hq : 0 < q) :
    primedExternalVisitIndexList (simpleRandomWalk omega) (2 * q - 1) x =
      (chronologicalExternalIndexList labels
        (primedRelativeSite (omega 0) x)).map fun i ↦ 2 * i.val + 1 := by
  unfold primedExternalVisitIndexList
  rw [show 2 * q - 1 + 1 = 2 * q by omega]
  rw [filter_range_two_mul_of_even_false
    (fun r ↦ primedExternalStateAt (simpleRandomWalk omega) r = x) q (by
      intro i hi heq
      exact hx (heq ▸ primedExternalStateAt_even_chessEven
        labels hlabels i hi))]
  calc
    ((List.range q).filter fun i ↦
          primedExternalStateAt (simpleRandomWalk omega) (2 * i + 1) = x).map
        (fun i ↦ 2 * i + 1) =
        ((List.range q).filter fun i ↦
          fixedExternalBase labels i = primedRelativeSite (omega 0) x).map
            (fun i ↦ 2 * i + 1) := by
      congr 1
      apply List.filter_congr
      intro i hi
      rw [List.mem_range] at hi
      rw [primedExternalStateAt_odd_eq_fixedExternalBase labels hlabels i hi]
      unfold primedRelativeSite
      rw [decide_eq_decide]
      constructor
      · intro heq
        rw [← heq]
        abel
      · intro heq
        rw [heq]
        abel
    _ = (chronologicalExternalIndexList labels
          (primedRelativeSite (omega 0) x)).map fun i ↦ 2 * i.val + 1 := by
      rw [← map_chronologicalExternalIndexList]
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      rfl

theorem primedInverseClockProfile_eq_chronological_length
    {q : ℕ} (labels : Fin q → IncrementPair)
    {omega : ℕ → Direction} {N : ℕ}
    (hlabels : terminalPairLabelsThrough
      (swappedIncrementShiftAfter primedOneShift omega) N = List.ofFn labels)
    (x : Site) (hx : ¬ HLOZPairing.chessEven x) (hq : 0 < q) :
    primedInverseClockProfile (simpleRandomWalk omega) (2 * q - 1) x =
      (chronologicalExternalIndexList labels
        (primedRelativeSite (omega 0) x)).length := by
  unfold primedInverseClockProfile
  rw [primedExternalVisitIndexList_eq_chronological labels hlabels x hx hq,
    List.length_map]

theorem primedInverseClockHoldingPrefix_eq_decodedChronological
    {q cut : ℕ} (labels : Fin q → IncrementPair)
    (hnondist : ∀ i, labels i ≠ distinguishedIncrementPair)
    {omega : ℕ → Direction}
    (homega : swappedIncrementShiftAfter primedOneShift omega ∈
      firstPairExternalPathEqFrom 0
        (externalPathFromLabels (List.ofFn labels)))
    (x : Site) (hx : ¬ HLOZPairing.chessEven x) (hq : 0 < q)
    (hcut : cut ≤ (chronologicalExternalIndexList labels
      (primedRelativeSite (omega 0) x)).length) :
    primedInverseClockHoldingPrefix (simpleRandomWalk omega) (2 * q - 1) cut x =
      decodedChronologicalHoldingPrefix labels
        (primedRelativeSite (omega 0) x) hcut
        (listVectorToFin labels
          (conditionalPairRunVector 0 (List.ofFn labels)
            (swappedIncrementShiftAfter primedOneShift omega))) := by
  obtain ⟨N, hlabels⟩ :=
    realized_terminalPairLabelsThrough labels hnondist homega
  unfold primedInverseClockHoldingPrefix
  rw [primedExternalVisitIndexList_eq_chronological
    labels hlabels x hx hq, ← List.map_take, List.map_map]
  change ((((chronologicalExternalIndexList labels
    (primedRelativeSite (omega 0) x)).take cut).map
      fun i : Fin q ↦ primedHoldingNat (simpleRandomWalk omega)
        (2 * i.val + 1))).sum = _
  simp_rw [primedHoldingNat_succ_eq_paperHoldingNat,
    paperHoldingNat_even_eq_conditionalPairRunVector labels hnondist homega]
  exact sum_map_take_eq_chronological_sum labels
    (primedRelativeSite (omega 0) x) hcut _

end Erdos1166.HLOZProp47Prop45XEastPrimed
