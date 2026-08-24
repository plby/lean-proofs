/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.ControlledNumericalLedger

/-!
# Eventual controlled numerical rooms

This file proves the seven scalar inequalities isolated in
`ControlledNumericalLedger`.  We begin with the two terminal inequalities,
whose only content is exact natural-number division arithmetic.  Keeping
these finite lemmas separate makes all rounding losses explicit before the
remaining real-asymptotic estimates are introduced.
-/

namespace Erdos360

open Filter
open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Selecting one eighth of `M` through `ell` equal cells never selects more
than one eighth of the original mass. -/
lemma controlledPrime_selectedBlock_eighth (M ell : ℕ) :
    8 * (ell * (M / (8 * ell))) ≤ M := by
  calc
    8 * (ell * (M / (8 * ell))) =
        (M / (8 * ell)) * (8 * ell) := by ring
    _ ≤ M := Nat.div_mul_le_self M (8 * ell)

/-- The canonical `140y ≤ n` endpoint margin pays both the selected half
sum and the divisor-rounding unit. -/
lemma controlledPrime_sum_room_of_endpoint
    {n y : ℕ} (hUy : controlledPrimeU n ≤ y) (hlinear : 140 * y ≤ n) :
    2 *
        (controlledPrimeEll *
          (controlledPrimeClassCapTwelve n y /
            (8 * controlledPrimeEll))) * y +
        controlledPrimeU n ≤ n := by
  let s := controlledPrimeEll *
    (controlledPrimeClassCapTwelve n y / (8 * controlledPrimeEll))
  let M := controlledPrimeClassCapTwelve n y
  have hs : 8 * s ≤ M := by
    simpa [s, M] using
      controlledPrime_selectedBlock_eighth M controlledPrimeEll
  have hM : M * (4 * y) ≤ 5 * n := by
    dsimp [M, controlledPrimeClassCapTwelve]
    simpa [mul_comm] using Nat.div_mul_le_self (5 * n) (4 * y)
  have hselected : 32 * (s * y) ≤ 5 * n := by
    calc
      32 * (s * y) = (8 * s) * (4 * y) := by ring
      _ ≤ M * (4 * y) := Nat.mul_le_mul_right (4 * y) hs
      _ ≤ 5 * n := hM
  have hU : 140 * controlledPrimeU n ≤ n :=
    (Nat.mul_le_mul_left 140 hUy).trans hlinear
  have hroom : 2 * (s * y) + controlledPrimeU n ≤ n := by omega
  change 2 * s * y + controlledPrimeU n ≤ n
  simpa [mul_assoc] using hroom

/-- The exact floor `6n/(5y)` still has enough mass after the selected
eighth of `5n/(4y)` is removed. -/
lemma controlledPrime_unused_room_of_endpoint
    {n y : ℕ} (hy : 0 < y) (hlinear : 140 * y ≤ n) :
    n ≤ y *
      (controlledPrimeExtractedFloorTwelve n y -
        controlledPrimeEll *
          (controlledPrimeClassCapTwelve n y /
            (8 * controlledPrimeEll))) := by
  let s := controlledPrimeEll *
    (controlledPrimeClassCapTwelve n y / (8 * controlledPrimeEll))
  let M := controlledPrimeClassCapTwelve n y
  let Q := controlledPrimeExtractedFloorTwelve n y
  have hs : 8 * s ≤ M := by
    simpa [s, M] using
      controlledPrime_selectedBlock_eighth M controlledPrimeEll
  have hM : M * (4 * y) ≤ 5 * n := by
    dsimp [M, controlledPrimeClassCapTwelve]
    simpa [mul_comm] using Nat.div_mul_le_self (5 * n) (4 * y)
  have hselected : 32 * (y * s) ≤ 5 * n := by
    calc
      32 * (y * s) = (8 * s) * (4 * y) := by ring
      _ ≤ M * (4 * y) := Nat.mul_le_mul_right (4 * y) hs
      _ ≤ 5 * n := hM
  have hQrem : 6 * n < 5 * y * (Q + 1) := by
    dsimp [Q, controlledPrimeExtractedFloorTwelve]
    exact Nat.lt_mul_div_succ (6 * n) (by positivity : 0 < 5 * y)
  have hQ : 38 * n ≤ 32 * (y * Q) := by
    have hQrem' : 192 * n < 160 * (y * Q) + 160 * y := by
      calc
        192 * n = 32 * (6 * n) := by ring
        _ < 32 * (5 * y * (Q + 1)) :=
          (Nat.mul_lt_mul_left (by norm_num : 0 < 32)).2 hQrem
        _ = 160 * (y * Q) + 160 * y := by ring
    have hySmall : 160 * y ≤ 2 * n := by omega
    omega
  have htotal : n + y * s ≤ y * Q := by
    have hscaled : 32 * (n + y * s) ≤ 32 * (y * Q) := by
      omega
    exact Nat.le_of_mul_le_mul_left hscaled (by norm_num : 0 < 32)
  have hys : y * s ≤ y * Q := (Nat.le_add_left _ _).trans htotal
  have hsQ : s ≤ Q :=
    Nat.le_of_mul_le_mul_left (by simpa [mul_comm] using hys) hy
  have hnsub : n ≤ y * Q - y * s := Nat.le_sub_of_add_le htotal
  simpa [s, Q, Nat.mul_sub_left_distrib, hsQ] using hnsub

/-- The existing unused-reserve estimate in particular says that the full
product `yQ` dominates `n`. -/
lemma controlledPrime_target_le_y_mul_floor
    {n y : ℕ} (hchoice : ControlledPrimeTwelveChoiceNumerics n y) :
    n ≤ y * controlledPrimeExtractedFloorTwelve n y := by
  let Q := controlledPrimeExtractedFloorTwelve n y
  have hseven : 7 * (Q / 8) ≤ Q := by
    calc
      7 * (Q / 8) ≤ 8 * (Q / 8) :=
        Nat.mul_le_mul_right (Q / 8) (by omega)
      _ ≤ Q := Nat.mul_div_le Q 8
  calc
    n ≤ 7 * y * (Q / 8) := by simpa [Q] using hchoice.unused
    _ = y * (7 * (Q / 8)) := by ring
    _ ≤ y * Q := Nat.mul_le_mul_left y hseven

/-- A finite, rounding-safe constructor for all seven scalar rooms.  Its
nontrivial hypotheses are exactly a strong `yU` margin and the one global
real exponential estimate. -/
lemma controlledPrime_scalarRooms_of_growth
    {n y : ℕ}
    (hchoice : ControlledPrimeTwelveChoiceNumerics n y)
    (hlinear : 140 * y ≤ n)
    (hroot : 12 * controlledPrimeEll ^ 2 ≤ fourthRootCeil y)
    (hlog : 1 ≤ Nat.log 2 (controlledPrimeB n y))
    (hloss : 20 * y *
      (controlledPrimeL y * Nat.log 2 (controlledPrimeB n y)) ≤ n)
    (hybig : 2 * controlledPrimeEll ≤ y)
    (hstrong : 4 * controlledPrimeEll * y * controlledPrimeU n ≤ n)
    (hprobability :
      (4 : ℝ) * (controlledPrimeClassCapTwelve n y + 1) * (2 * y + 1) *
        Real.exp (- ((controlledPrimeL y -
            (8 * controlledPrimeEll - 1) : ℕ) : ℝ) /
          (1024 * (controlledPrimeEll : ℝ) ^ 2)) < 1) :
    ControlledPrimeScalarPostRooms n y := by
  have hy : 0 < y := by
    have : 0 < controlledPrimeEll := by norm_num [controlledPrimeEll]
    omega
  have hnQ : n ≤
      y * controlledPrimeExtractedFloorTwelve n y :=
    controlledPrime_target_le_y_mul_floor hchoice
  have hYL : 20 * y * controlledPrimeL y ≤ n := by
    calc
      20 * y * controlledPrimeL y ≤
          20 * y * (controlledPrimeL y *
            Nat.log 2 (controlledPrimeB n y)) := by
        apply Nat.mul_le_mul_left (20 * y)
        calc
          controlledPrimeL y = controlledPrimeL y * 1 := by simp
          _ ≤ controlledPrimeL y *
              Nat.log 2 (controlledPrimeB n y) :=
            Nat.mul_le_mul_left (controlledPrimeL y) hlog
      _ ≤ n := hloss
  have hYU : 20 * y * controlledPrimeU n ≤ n := by
    calc
      20 * y * controlledPrimeU n ≤
          4 * controlledPrimeEll * y * controlledPrimeU n := by
        calc
          20 * y * controlledPrimeU n =
              20 * (y * controlledPrimeU n) := by ring
          _ ≤ (4 * controlledPrimeEll) *
              (y * controlledPrimeU n) :=
            Nat.mul_le_mul_right (y * controlledPrimeU n)
              (by norm_num [controlledPrimeEll])
          _ = 4 * controlledPrimeEll * y * controlledPrimeU n := by ring
      _ ≤ n := hstrong
  have hlargeNumerator :
      5 * y * (controlledPrimeL y + 2 * controlledPrimeU n + 1) ≤
        6 * n := by
    have hLpart : 5 * y * controlledPrimeL y ≤ n := by
      calc
        5 * y * controlledPrimeL y ≤
            20 * y * controlledPrimeL y := by
          calc
            5 * y * controlledPrimeL y =
                5 * (y * controlledPrimeL y) := by ring
            _ ≤ 20 * (y * controlledPrimeL y) :=
              Nat.mul_le_mul_right (y * controlledPrimeL y) (by omega)
            _ = 20 * y * controlledPrimeL y := by ring
        _ ≤ n := hYL
    have hUpart : 10 * y * controlledPrimeU n ≤ n := by
      calc
        10 * y * controlledPrimeU n ≤
            20 * y * controlledPrimeU n := by
          calc
            10 * y * controlledPrimeU n =
                10 * (y * controlledPrimeU n) := by ring
            _ ≤ 20 * (y * controlledPrimeU n) :=
              Nat.mul_le_mul_right (y * controlledPrimeU n) (by omega)
            _ = 20 * y * controlledPrimeU n := by ring
        _ ≤ n := hYU
    have hypart : 5 * y ≤ n :=
      (by omega : 5 * y ≤ 140 * y).trans hlinear
    calc
      5 * y * (controlledPrimeL y + 2 * controlledPrimeU n + 1) =
          5 * y * controlledPrimeL y +
            10 * y * controlledPrimeU n + 5 * y := by ring
      _ ≤ n + n + n := Nat.add_le_add (Nat.add_le_add hLpart hUpart) hypart
      _ ≤ 6 * n := by omega
  have hlarge : controlledPrimeL y + 2 * controlledPrimeU n ≤
      controlledPrimeExtractedFloorTwelve n y := by
    unfold controlledPrimeExtractedFloorTwelve
    apply (Nat.le_div_iff_mul_le (by positivity : 0 < 5 * y)).2
    calc
      (controlledPrimeL y + 2 * controlledPrimeU n) * (5 * y) ≤
          (controlledPrimeL y + 2 * controlledPrimeU n + 1) *
            (5 * y) := Nat.mul_le_mul_right (5 * y) (Nat.le_succ _)
      _ ≤ 6 * n := by
        simpa [mul_comm] using hlargeNumerator
  have hmass0 : 5 * controlledPrimeEll ^ 2 * controlledPrimeU n ≤ n := by
    have hcoeff : 5 * controlledPrimeEll ≤ 4 * y := by
      norm_num [controlledPrimeEll] at hybig ⊢
      omega
    calc
      5 * controlledPrimeEll ^ 2 * controlledPrimeU n =
          (5 * controlledPrimeEll) *
            (controlledPrimeEll * controlledPrimeU n) := by ring
      _ ≤ (4 * y) * (controlledPrimeEll * controlledPrimeU n) :=
        Nat.mul_le_mul_right (controlledPrimeEll * controlledPrimeU n) hcoeff
      _ = 4 * controlledPrimeEll * y * controlledPrimeU n := by ring
      _ ≤ n := hstrong
  have hmass : 5 * controlledPrimeEll ^ 2 * controlledPrimeU n ≤
      y * controlledPrimeExtractedFloorTwelve n y :=
    hmass0.trans hnQ
  have hwidthGrowth :
      controlledPrimeEll * controlledPrimeU n *
          (2 * y + 2 * controlledPrimeEll) ≤
        y * controlledPrimeExtractedFloorTwelve n y := by
    have hparenthesis : 2 * y + 2 * controlledPrimeEll ≤ 4 * y := by
      omega
    calc
      controlledPrimeEll * controlledPrimeU n *
          (2 * y + 2 * controlledPrimeEll) ≤
          controlledPrimeEll * controlledPrimeU n * (4 * y) :=
        Nat.mul_le_mul_left (controlledPrimeEll * controlledPrimeU n)
          hparenthesis
      _ = 4 * controlledPrimeEll * y * controlledPrimeU n := by ring
      _ ≤ n := hstrong
      _ ≤ y * controlledPrimeExtractedFloorTwelve n y := hnQ
  have hden : 0 < controlledPrimeEll ^ 2 * controlledPrimeU n := by
    exact Nat.mul_pos (by norm_num [controlledPrimeEll]) hchoice.U_pos
  let K := 2 * y / controlledPrimeEll + 2
  have hEllK : controlledPrimeEll * K ≤
      2 * y + 2 * controlledPrimeEll := by
    dsimp [K]
    have hdiv : controlledPrimeEll * (2 * y / controlledPrimeEll) ≤
        2 * y := Nat.mul_div_le (2 * y) controlledPrimeEll
    omega
  have hKA : K * (controlledPrimeEll ^ 2 * controlledPrimeU n) ≤
      y * controlledPrimeExtractedFloorTwelve n y := by
    calc
      K * (controlledPrimeEll ^ 2 * controlledPrimeU n) =
          (controlledPrimeEll * K) *
            (controlledPrimeEll * controlledPrimeU n) := by ring
      _ ≤ (2 * y + 2 * controlledPrimeEll) *
          (controlledPrimeEll * controlledPrimeU n) :=
        Nat.mul_le_mul_right (controlledPrimeEll * controlledPrimeU n) hEllK
      _ = controlledPrimeEll * controlledPrimeU n *
          (2 * y + 2 * controlledPrimeEll) := by ring
      _ ≤ y * controlledPrimeExtractedFloorTwelve n y := hwidthGrowth
  have hK : K ≤
      y * controlledPrimeExtractedFloorTwelve n y /
        (controlledPrimeEll ^ 2 * controlledPrimeU n) :=
    (Nat.le_div_iff_mul_le hden).2 hKA
  have hKsub : 2 * y / controlledPrimeEll + 1 ≤
      y * controlledPrimeExtractedFloorTwelve n y /
          (controlledPrimeEll ^ 2 * controlledPrimeU n) - 1 := by
    apply Nat.le_sub_of_add_le
    simpa [K, add_assoc] using hK
  have hround : 2 * y <
      controlledPrimeEll * (2 * y / controlledPrimeEll + 1) := by
    simpa [mul_comm] using Nat.lt_mul_div_succ (2 * y)
      (by norm_num [controlledPrimeEll] : 0 < controlledPrimeEll)
  have hwidth : 2 * y ≤ controlledPrimeEll *
      (y * controlledPrimeExtractedFloorTwelve n y /
        (controlledPrimeEll ^ 2 * controlledPrimeU n) - 1) + 1 := by
    calc
      2 * y ≤ controlledPrimeEll *
          (2 * y / controlledPrimeEll + 1) := hround.le
      _ ≤ controlledPrimeEll *
          (y * controlledPrimeExtractedFloorTwelve n y /
            (controlledPrimeEll ^ 2 * controlledPrimeU n) - 1) :=
        Nat.mul_le_mul_left controlledPrimeEll hKsub
      _ ≤ _ := Nat.le_add_right _ _
  exact ⟨hroot, hlarge, hprobability, hmass, hwidth,
    controlledPrime_sum_room_of_endpoint hchoice.U_le_y hlinear,
    controlledPrime_unused_room_of_endpoint hy hlinear⟩

/-! ## Canonical asymptotic inputs -/

/-- Eventually the canonical window contains two full cutoff lengths.  This
simultaneously makes the binary extraction logarithm positive and supplies
the fixed lower size needed by the width calculation. -/
lemma eventually_controlledPrime_two_mul_U_le_y :
    ∀ᶠ n : ℕ in atTop,
      let y := initialLowerY n (lowerColorCount 1 n)
      2 * controlledPrimeU n ≤ y := by
  have hp19Top : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (19 / 40 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_controlledPrime_endpoint_parameters,
    eventually_initialMissingMertensBounds_lowerColorCount
      (c := (1 : ℝ)) (by norm_num),
    eventually_CFPDiagonalNumericBounds_lowerColorCount
      (c := (1 : ℝ)) (by norm_num),
    eventually_three_le_lowerColorCount (c := (1 : ℝ)) (by norm_num),
    hp19Top.eventually (eventually_ge_atTop (2005 : ℝ))] with
      n hend hMertens hnum hcolors hp19
  dsimp only at hend ⊢
  let colors := lowerColorCount 1 n
  let y := initialLowerY n colors
  have hn : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    norm_num [controlledPrimeU] at hend
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcolor : 0 < colors := by dsimp [colors]; omega
  have hyLower := (initialLowerY_range_of_numeric_bounds hn hcolor
    hMertens hnum.1 hnum.2.1 hnum.2.2).2.1
  have hUcast := (controlledPrimeU_cast_bounds n).2
  have hp8pos := Real.rpow_pos_of_pos hnR (1 / 8 : ℝ)
  have hp8one : (1 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 8 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have htwoU : ((2 * controlledPrimeU n : ℕ) : ℝ) <
      2005 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := by
    push_cast
    nlinarith
  have hsplit : Real.rpow (n : ℝ) (3 / 5 : ℝ) =
      Real.rpow (n : ℝ) (1 / 8 : ℝ) *
        Real.rpow (n : ℝ) (19 / 40 : ℝ) := by
    convert Real.rpow_add hnR (1 / 8 : ℝ) (19 / 40 : ℝ) using 1 <;>
      norm_num
  have htwoUR : ((2 * controlledPrimeU n : ℕ) : ℝ) < (y : ℝ) := by
    calc
      ((2 * controlledPrimeU n : ℕ) : ℝ) <
          2005 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := htwoU
      _ ≤ Real.rpow (n : ℝ) (3 / 5 : ℝ) := by
        rw [hsplit]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hp19 hp8pos.le
      _ ≤ (y : ℝ) := by simpa [y, colors] using hyLower
  exact_mod_cast htwoUR.le

/-- The cutoff-window product has a fixed-power saving: the canonical upper
window is `O(n^(7/10))` and `U = O(n^(1/8))`. -/
lemma eventually_controlledPrime_strong_yU_room :
    ∀ᶠ n : ℕ in atTop,
      let y := initialLowerY n (lowerColorCount 1 n)
      4 * controlledPrimeEll * y * controlledPrimeU n ≤ n := by
  have hpTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (7 / 40 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_controlledPrime_endpoint_parameters,
    eventually_initialLowerY_lt_rpow_seven_tenths,
    hpTop.eventually (eventually_ge_atTop
      ((4 * controlledPrimeEll * 1002 : ℕ) : ℝ))] with
      n hend hyUpper hpLarge
  dsimp only at hend hyUpper ⊢
  let y := initialLowerY n (lowerColorCount 1 n)
  have hn : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    norm_num [controlledPrimeU] at hend
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hy : 0 < y := hend.1.trans_le hend.2.1
  have hUcast := (controlledPrimeU_cast_bounds n).2
  have hp8pos := Real.rpow_pos_of_pos hnR (1 / 8 : ℝ)
  have hp8one : (1 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 8 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hUrough : (controlledPrimeU n : ℝ) <
      1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ) := by
    nlinarith
  have hyU : (y : ℝ) * controlledPrimeU n <
      Real.rpow (n : ℝ) (7 / 10 : ℝ) *
        (1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ)) := by
    exact (mul_lt_mul_of_pos_right hyUpper
      (by exact_mod_cast hend.1 : (0 : ℝ) < controlledPrimeU n)).trans
      (mul_lt_mul_of_pos_left hUrough
        (Real.rpow_pos_of_pos hnR (7 / 10 : ℝ)))
  have hpow : Real.rpow (n : ℝ) (7 / 10 : ℝ) *
      Real.rpow (n : ℝ) (1 / 8 : ℝ) =
        Real.rpow (n : ℝ) (33 / 40 : ℝ) := by
    convert (Real.rpow_add hnR (7 / 10 : ℝ) (1 / 8 : ℝ)).symm using 1 <;>
      norm_num
  have hnSplit : (n : ℝ) =
      Real.rpow (n : ℝ) (33 / 40 : ℝ) *
        Real.rpow (n : ℝ) (7 / 40 : ℝ) := by
    calc
      (n : ℝ) = Real.rpow (n : ℝ) 1 := (Real.rpow_one _).symm
      _ = Real.rpow (n : ℝ)
          ((33 / 40 : ℝ) + (7 / 40 : ℝ)) := by norm_num
      _ = _ := Real.rpow_add hnR _ _
  have hroomR :
      (((4 * controlledPrimeEll * y * controlledPrimeU n : ℕ) : ℝ)) <
        (n : ℝ) := by
    push_cast
    rw [hnSplit]
    have hp33 := Real.rpow_pos_of_pos hnR (33 / 40 : ℝ)
    calc
      (4 : ℝ) * controlledPrimeEll * y * controlledPrimeU n <
          (4 : ℝ) * controlledPrimeEll *
            (Real.rpow (n : ℝ) (7 / 10 : ℝ) *
              (1002 * Real.rpow (n : ℝ) (1 / 8 : ℝ))) := by
        simpa [mul_assoc] using mul_lt_mul_of_pos_left hyU
          (by norm_num [controlledPrimeEll] :
            (0 : ℝ) < (4 : ℝ) * controlledPrimeEll)
      _ = ((4 * controlledPrimeEll * 1002 : ℕ) : ℝ) *
          Real.rpow (n : ℝ) (33 / 40 : ℝ) := by
        push_cast
        rw [← hpow]
        ring
      _ ≤ Real.rpow (n : ℝ) (33 / 40 : ℝ) *
          Real.rpow (n : ℝ) (7 / 40 : ℝ) := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hpLarge hp33.le
  exact_mod_cast hroomR.le

/-- The rounded fourth root is, as a real number, at least the underlying
real fourth root. -/
lemma rpow_one_fourth_le_fourthRootCeil (y : ℕ) :
    Real.rpow (y : ℝ) (1 / 4 : ℝ) ≤ (fourthRootCeil y : ℝ) := by
  simpa [fourthRootCeil] using
    Nat.le_ceil (Real.rpow (y : ℝ) (1 / 4 : ℝ))

/-- The single global split-failure majorant tends to zero at the canonical
parameters.  The proof retains the exact denominator involving the fixed
pool count; the auxiliary denominator below is only a comparison used for
the limit. -/
lemma eventually_controlledPrime_probability_small :
    ∀ᶠ n : ℕ in atTop,
      let y := initialLowerY n (lowerColorCount 1 n)
      (4 : ℝ) * (controlledPrimeClassCapTwelve n y + 1) * (2 * y + 1) *
        Real.exp (- ((controlledPrimeL y -
            (8 * controlledPrimeEll - 1) : ℕ) : ℝ) /
          (1024 * (controlledPrimeEll : ℝ) ^ 2)) < 1 := by
  let p : ℕ → ℝ := fun n ↦ Real.rpow (n : ℝ) (3 / 20 : ℝ)
  let a : ℝ := (2048 * controlledPrimeEll ^ 2 : ℕ)
  let x : ℕ → ℝ := fun n ↦ p n / a
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast (show 0 < 2048 * controlledPrimeEll ^ 2 by
      norm_num [controlledPrimeEll])
  have hpTop : Tendsto p atTop atTop := by
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 20)).comp
      tendsto_natCast_atTop_atTop
  have hxTop : Tendsto x atTop atTop := by
    exact hpTop.atTop_div_const ha
  have hdecay : Tendsto (fun n : ℕ ↦
      (x n) ^ 14 * Real.exp (-(x n))) atTop (nhds 0) := by
    exact Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 14 |>.comp hxTop
  have hscaled : Tendsto (fun n : ℕ ↦
      (192 * a ^ 14) *
        ((x n) ^ 14 * Real.exp (-(x n)))) atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hdecay
  have hsmall := hscaled.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_controlledPrime_endpoint_parameters,
    eventually_initialMissingMertensBounds_lowerColorCount
      (c := (1 : ℝ)) (by norm_num),
    eventually_CFPDiagonalNumericBounds_lowerColorCount
      (c := (1 : ℝ)) (by norm_num),
    eventually_three_le_lowerColorCount (c := (1 : ℝ)) (by norm_num),
    eventually_ge_atTop (1 : ℕ), hsmall] with
      n hend hMertens hnum hcolors hnOne hsmallN
  dsimp only at hend ⊢
  let colors := lowerColorCount 1 n
  let y := initialLowerY n colors
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcolor : 0 < colors := by dsimp [colors]; omega
  have hyLower := (initialLowerY_range_of_numeric_bounds hn hcolor
    hMertens hnum.1 hnum.2.1 hnum.2.2).2.1
  have hy : 0 < y := hend.1.trans_le hend.2.1
  have hlinear : 140 * y ≤ n := by
    simpa [y, colors] using hend.2.2.2.2.2.2
  have hyn : y ≤ n := by omega
  have hpLower : p n ≤ (fourthRootCeil y : ℝ) := by
    have hbase : Real.rpow (n : ℝ) (3 / 5 : ℝ) ≤ (y : ℝ) := by
      simpa [y, colors] using hyLower
    have hquarter := Real.rpow_le_rpow
      (Real.rpow_nonneg hnR.le (3 / 5 : ℝ)) hbase
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have hpow : p n =
        Real.rpow (Real.rpow (n : ℝ) (3 / 5 : ℝ))
          (1 / 4 : ℝ) := by
      dsimp [p]
      convert Real.rpow_mul hnR.le (3 / 5 : ℝ) (1 / 4 : ℝ) using 1 <;>
        norm_num
    rw [hpow]
    exact hquarter.trans (rpow_one_fourth_le_fourthRootCeil y)
  have hexponent : Real.exp (- ((controlledPrimeL y -
          (8 * controlledPrimeEll - 1) : ℕ) : ℝ) /
        (1024 * (controlledPrimeEll : ℝ) ^ 2)) ≤
      Real.exp (-(x n)) := by
    apply Real.exp_le_exp.mpr
    have hcoef : (1 / a : ℝ) ≤
        1000000 / (1024 * (controlledPrimeEll : ℝ) ^ 2) := by
      dsimp [a]
      norm_num [controlledPrimeEll]
    have hpNonneg : 0 ≤ p n := by
      dsimp [p]
      positivity
    have hrootNonneg : (0 : ℝ) ≤ fourthRootCeil y := by positivity
    have hquot : x n ≤
        (1000000 * fourthRootCeil y : ℕ) /
          (1024 * (controlledPrimeEll : ℝ) ^ 2) := by
      dsimp [x]
      push_cast
      calc
        p n / a = p n * (1 / a : ℝ) := by ring
        _ ≤ (fourthRootCeil y : ℝ) * (1 / a : ℝ) :=
          mul_le_mul_of_nonneg_right hpLower (by positivity)
        _ ≤ (fourthRootCeil y : ℝ) *
            (1000000 / (1024 * (controlledPrimeEll : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hcoef hrootNonneg
        _ = (1000000 : ℝ) * fourthRootCeil y /
            (1024 * (controlledPrimeEll : ℝ) ^ 2) := by ring
    rw [show 8 * controlledPrimeEll = controlledPrimeCells by rfl,
      controlledPrimeL_sub_reserve]
    push_cast
    have hneg := neg_le_neg hquot
    norm_num [controlledPrimeEll] at hneg ⊢
    rw [neg_div]
    exact neg_le_neg hneg
  let M := controlledPrimeClassCapTwelve n y
  have hM : M ≤ 5 * n := by
    dsimp [M, controlledPrimeClassCapTwelve]
    exact Nat.div_le_self (5 * n) (4 * y)
  have hMone : M + 1 ≤ 6 * (n + 1) := by omega
  have hyone : 2 * y + 1 ≤ 2 * (n + 1) := by omega
  have hcoefficientNat :
      4 * (M + 1) * (2 * y + 1) ≤ 48 * (n + 1) ^ 2 := by
    calc
      4 * (M + 1) * (2 * y + 1) ≤
          4 * (6 * (n + 1)) * (2 * (n + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4 hMone) hyone
      _ = 48 * (n + 1) ^ 2 := by ring
  have hcoefficient :
      (4 : ℝ) * (M + 1) * (2 * y + 1) ≤
        48 * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hcoefficientNat
  have hnPlus : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast (by omega : n + 1 ≤ 2 * n)
  have hpoly : (n : ℝ) ^ 2 ≤ (p n) ^ 14 := by
    have hmono := Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ n by exact_mod_cast hnOne)
      (by norm_num : (2 : ℝ) ≤ 21 / 10)
    have hsquare : (n : ℝ) ^ 2 = Real.rpow (n : ℝ) 2 := by
      simpa using (Real.rpow_natCast (n : ℝ) 2).symm
    have hp14 : (p n) ^ 14 = Real.rpow (n : ℝ) (21 / 10 : ℝ) := by
      dsimp [p]
      calc
        (Real.rpow (n : ℝ) (3 / 20 : ℝ)) ^ 14 =
            Real.rpow (Real.rpow (n : ℝ) (3 / 20 : ℝ))
              (14 : ℝ) := by
                simpa using (Real.rpow_natCast
                  (Real.rpow (n : ℝ) (3 / 20 : ℝ)) 14).symm
        _ = Real.rpow (n : ℝ) ((3 / 20 : ℝ) * 14) :=
          (Real.rpow_mul hnR.le _ _).symm
        _ = Real.rpow (n : ℝ) (21 / 10 : ℝ) := by norm_num
    rw [hsquare, hp14]
    exact hmono
  have hxp : (p n) ^ 14 = a ^ 14 * (x n) ^ 14 := by
    dsimp [x]
    field_simp [a]
  have hmajorant :
      (4 : ℝ) * (M + 1) * (2 * y + 1) *
          Real.exp (- ((controlledPrimeL y -
              (8 * controlledPrimeEll - 1) : ℕ) : ℝ) /
            (1024 * (controlledPrimeEll : ℝ) ^ 2)) ≤
        (192 * a ^ 14) *
          ((x n) ^ 14 * Real.exp (-(x n))) := by
    have hexpNonneg : 0 ≤ Real.exp (-(x n)) := (Real.exp_pos _).le
    calc
      (4 : ℝ) * (M + 1) * (2 * y + 1) *
          Real.exp (- ((controlledPrimeL y -
              (8 * controlledPrimeEll - 1) : ℕ) : ℝ) /
            (1024 * (controlledPrimeEll : ℝ) ^ 2)) ≤
          (4 : ℝ) * (M + 1) * (2 * y + 1) *
            Real.exp (-(x n)) :=
        mul_le_mul_of_nonneg_left hexponent (by positivity)
      _ ≤ (48 * ((n + 1 : ℕ) : ℝ) ^ 2) *
          Real.exp (-(x n)) :=
        mul_le_mul_of_nonneg_right hcoefficient hexpNonneg
      _ ≤ (192 * (n : ℝ) ^ 2) * Real.exp (-(x n)) := by
        apply mul_le_mul_of_nonneg_right _ hexpNonneg
        calc
          48 * ((n + 1 : ℕ) : ℝ) ^ 2 ≤
              48 * (2 * (n : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by positivity) hnPlus 2) (by norm_num)
          _ = 192 * (n : ℝ) ^ 2 := by ring
      _ ≤ (192 * (p n) ^ 14) * Real.exp (-(x n)) := by
        gcongr
      _ = (192 * a ^ 14) *
          ((x n) ^ 14 * Real.exp (-(x n))) := by rw [hxp]; ring
  exact hmajorant.trans_lt (by simpa [x] using hsmallN)

/-- All seven canonical scalar rooms hold eventually. -/
theorem eventually_controlledPrime_scalarPostRooms :
    ∀ᶠ n : ℕ in atTop,
      ControlledPrimeScalarPostRooms n
        (initialLowerY n (lowerColorCount 1 n)) := by
  have hp8Top : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (1 / 8 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_controlledPrimeTwelve_choice_numerics,
    eventually_controlledPrime_endpoint_parameters,
    eventually_controlledPrime_root_large,
    eventually_controlledPrime_loss_room,
    eventually_controlledPrime_two_mul_U_le_y,
    eventually_controlledPrime_strong_yU_room,
    eventually_controlledPrime_probability_small,
    hp8Top.eventually
      (eventually_ge_atTop (controlledPrimeEll : ℝ))] with
      n hchoice hend hroot hloss htwo hstrong hprob hp8
  dsimp only at hchoice hend hroot hloss htwo hstrong hprob ⊢
  let y := initialLowerY n (lowerColorCount 1 n)
  have hn : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    norm_num at hp8
  have hUlargeR : (controlledPrimeEll : ℝ) ≤ controlledPrimeU n := by
    have hcast := (controlledPrimeU_cast_bounds n).1
    have hpnonneg : (0 : ℝ) ≤ Real.rpow (n : ℝ) (1 / 8 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    nlinarith
  have hUlarge : controlledPrimeEll ≤ controlledPrimeU n := by
    exact_mod_cast hUlargeR
  have hEllU : controlledPrimeEll ≤ controlledPrimeU n := by
    exact hUlarge
  have hybig : 2 * controlledPrimeEll ≤ y :=
    (Nat.mul_le_mul_left 2 hEllU).trans htwo
  have hBtwo : 2 ≤ controlledPrimeB n y := by
    unfold controlledPrimeB
    apply (Nat.le_div_iff_mul_le hchoice.U_pos).2
    simpa [mul_comm] using htwo
  have hlog : 1 ≤ Nat.log 2 (controlledPrimeB n y) := by
    have := Nat.log_pos (by norm_num : 1 < 2) hBtwo
    omega
  exact controlledPrime_scalarRooms_of_growth hchoice
    hend.2.2.2.2.2.2 hroot hlog hloss hybig hstrong hprob

/-- The exact finite controlled-prime ledger is therefore available for all
sufficiently large targets. -/
theorem eventually_canonicalControlledPrimeNumericalLedger :
    ∀ᶠ n : ℕ in atTop, CanonicalControlledPrimeNumericalLedger n :=
  eventually_canonicalControlledPrimeNumericalLedger_of_scalarRooms
    eventually_controlledPrime_scalarPostRooms

end Erdos360

#print axioms Erdos360.controlledPrime_sum_room_of_endpoint
#print axioms Erdos360.controlledPrime_unused_room_of_endpoint
#print axioms Erdos360.controlledPrime_scalarRooms_of_growth
#print axioms Erdos360.eventually_controlledPrime_two_mul_U_le_y
#print axioms Erdos360.eventually_controlledPrime_strong_yU_room
#print axioms Erdos360.eventually_controlledPrime_probability_small
#print axioms Erdos360.eventually_controlledPrime_scalarPostRooms
#print axioms Erdos360.eventually_canonicalControlledPrimeNumericalLedger
