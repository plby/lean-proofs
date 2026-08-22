import ErdosProblems.Erdos1165.ShiftedPrefixBridge

open scoped BigOperators

namespace Erdos1165.PrefixLevelTruncation

open LazyDecomposition PathInsertion SpatialInsertionFiber ShiftedPrefixBridge

/-!
# Exact level truncation on genuine finite prefixes

`SpatialInsertionFiber.fixedExternalLocalTime` is the external local time of
the complete two-step block word.  At an odd ordinary time there is one more
position, which belongs to the frozen external datum.  This file includes that
position and proves the literal endpoint inequalities for both HLOZ parity
decompositions.
-/

/-- External local time of the complete even blocks together with the
optional terminal singleton. -/
def fixedEvenPrefixLocalTime {i : ℕ} (ω : StepPath) (n : ℕ)
    (r : Fin i → RetainedBlock .even) (y : Point) : ℕ :=
  listLocalTime
    (blockPath (0, 0) (retainedWord r) ++ prefixRemainder ω n) y

theorem even_fixedFiber_localTime {i : ℕ} (ω : StepPath) (n : ℕ)
    (r : Fin i → RetainedBlock .even) (q : Fin (i + 1) → ℕ)
    (hword : completePrefixBlocks ω n = insertGapVector r q) (y : Point) :
    listLocalTime (finitePathList (pathPrefix (trajectory ω) n)) y =
      fixedEvenPrefixLocalTime ω n r y +
        insertionLazyLocalTime (0, 0) r q y := by
  rw [listLocalTime_split .even]
  change listLocalTime (StoppedInsertion.externalTraceAt .even ω n) y +
      listLocalTime (StoppedInsertion.deletedTraceAt .even ω n) y = _
  rw [fixedFiber_externalTrace ω n r q hword,
    fixedFiber_deletedTrace ω n r q hword]
  rw [lazyLocalTime_insertedPath]
  rfl

theorem even_start_compatible : OrientationCompatible .even (0, 0) := by
  change EvenPoint (0, 0)
  simp [EvenPoint, pointParity]

theorem even_fixedFiber_localTime_at_base {i : ℕ} (ω : StepPath) (n : ℕ)
    (r : Fin i → RetainedBlock .even) (q : Fin (i + 1) → ℕ)
    (hword : completePrefixBlocks ω n = insertGapVector r q)
    (b : ExternalDomino (0, 0) r) :
    listLocalTime (finitePathList (pathPrefix (trajectory ω) n)) b.1 =
      fixedEvenPrefixLocalTime ω n r b.1 + dominoLazyTotal (0, 0) r q b := by
  rw [even_fixedFiber_localTime ω n r q hword]
  rw [insertionLazyLocalTime_at_base (0, 0) r q
    (baseMiddleDisjoint_of_compatible (0, 0) r even_start_compatible) b]

theorem even_fixedFiber_localTime_at_middle {i : ℕ} (ω : StepPath) (n : ℕ)
    (r : Fin i → RetainedBlock .even) (q : Fin (i + 1) → ℕ)
    (hword : completePrefixBlocks ω n = insertGapVector r q)
    (b : ExternalDomino (0, 0) r) :
    listLocalTime (finitePathList (pathPrefix (trajectory ω) n))
        (excursionMiddle .even b.1) =
      fixedEvenPrefixLocalTime ω n r (excursionMiddle .even b.1) +
        dominoLazyTotal (0, 0) r q b := by
  rw [even_fixedFiber_localTime ω n r q hword]
  rw [insertionLazyLocalTime_at_middle (0, 0) r q
    (baseMiddleDisjoint_of_compatible (0, 0) r even_start_compatible) b]

/-- Corrected frozen maximum for an even-prefix domino. -/
def fixedEvenPrefixDominoMax {i : ℕ} (ω : StepPath) (n : ℕ)
    (r : Fin i → RetainedBlock .even) (b : ExternalDomino (0, 0) r) : ℕ :=
  max (fixedEvenPrefixLocalTime ω n r b.1)
    (fixedEvenPrefixLocalTime ω n r (excursionMiddle .even b.1))

/-- At a genuine even-oriented finite prefix, the two endpoint bounds away
from `D` are exactly coordinatewise truncations of the domino totals. -/
theorem even_actualEndpointsBelow_iff_dominoTruncation {i : ℕ}
    (ω : StepPath) (n : ℕ) (r : Fin i → RetainedBlock .even)
    (q : Fin (i + 1) → ℕ)
    (hword : completePrefixBlocks ω n = insertGapVector r q)
    (m : ℕ) (D : Finset Point) :
    (∀ b : ExternalDomino (0, 0) r, b.1 ∉ D →
        listLocalTime (finitePathList (pathPrefix (trajectory ω) n)) b.1 < m ∧
        listLocalTime (finitePathList (pathPrefix (trajectory ω) n))
          (excursionMiddle .even b.1) < m) ↔
      ∀ b : ExternalDomino (0, 0) r, b.1 ∉ D →
        dominoLazyTotal (0, 0) r q b < m - fixedEvenPrefixDominoMax ω n r b := by
  constructor
  · intro h b hb
    have hend := h b hb
    rw [even_fixedFiber_localTime_at_base ω n r q hword b,
      even_fixedFiber_localTime_at_middle ω n r q hword b] at hend
    apply Nat.lt_sub_iff_add_lt.mpr
    unfold fixedEvenPrefixDominoMax
    rw [add_comm, max_add]
    exact max_lt hend.1 hend.2
  · intro h b hb
    have hsum := Nat.lt_sub_iff_add_lt.mp (h b hb)
    unfold fixedEvenPrefixDominoMax at hsum
    rw [add_comm, max_add, max_lt_iff] at hsum
    rw [even_fixedFiber_localTime_at_base ω n r q hword b,
      even_fixedFiber_localTime_at_middle ω n r q hword b]
    exact hsum

/-- Corrected frozen maximum for a shifted-prefix domino.  This includes the
time-zero atom as well as the optional final singleton. -/
def fixedShiftedPrefixDominoMax {i : ℕ} (ω : StepPath) (n : ℕ)
    (r : Fin i → RetainedBlock .shifted)
    (b : ExternalDomino (trajectory ω 1) r) : ℕ :=
  max (fixedShiftedPrefixLocalTime ω n r b.1)
    (fixedShiftedPrefixLocalTime ω n r (excursionMiddle .shifted b.1))

/-- Shifted analogue of `even_actualEndpointsBelow_iff_dominoTruncation`. -/
theorem shifted_actualEndpointsBelow_iff_dominoTruncation {i : ℕ}
    (ω : StepPath) (n : ℕ) (hn : 0 < n)
    (r : Fin i → RetainedBlock .shifted) (q : Fin (i + 1) → ℕ)
    (hword : shiftedCompletePrefixBlocks ω n = insertGapVector r q)
    (m : ℕ) (D : Finset Point) :
    (∀ b : ExternalDomino (trajectory ω 1) r, b.1 ∉ D →
        listLocalTime (finitePathList (pathPrefix (trajectory ω) n)) b.1 < m ∧
        listLocalTime (finitePathList (pathPrefix (trajectory ω) n))
          (excursionMiddle .shifted b.1) < m) ↔
      ∀ b : ExternalDomino (trajectory ω 1) r, b.1 ∉ D →
        dominoLazyTotal (trajectory ω 1) r q b <
          m - fixedShiftedPrefixDominoMax ω n r b := by
  constructor
  · intro h b hb
    have hend := h b hb
    rw [shifted_fixedFiber_localTime_at_base ω n hn r q hword b,
      shifted_fixedFiber_localTime_at_middle ω n hn r q hword b] at hend
    apply Nat.lt_sub_iff_add_lt.mpr
    unfold fixedShiftedPrefixDominoMax
    rw [add_comm, max_add]
    exact max_lt hend.1 hend.2
  · intro h b hb
    have hsum := Nat.lt_sub_iff_add_lt.mp (h b hb)
    unfold fixedShiftedPrefixDominoMax at hsum
    rw [add_comm, max_add, max_lt_iff] at hsum
    rw [shifted_fixedFiber_localTime_at_base ω n hn r q hword b,
      shifted_fixedFiber_localTime_at_middle ω n hn r q hword b]
    exact hsum

end Erdos1165.PrefixLevelTruncation
