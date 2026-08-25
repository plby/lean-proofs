import ErdosProblems.Erdos232.Intervals

open LeanCert.Core

namespace Erdos232

def dualConstant : ℚ := 1062576034 / 1000000000
def dualTarget : ℚ := 246993028 / 1000000000

def dualWeight (i : Fin 27) : ℚ :=
  match i.val with
  | 0 => 396364993 / 1000000000
  | 1 => 9318060 / 1000000000
  | 2 => 58681140 / 1000000000
  | 3 => -10849291 / 1000000000
  | 4 => 36511746 / 1000000000
  | 5 => -71089641 / 1000000000
  | 6 => 0 / 1000000000
  | 7 => -30844001 / 1000000000
  | 8 => 24168027 / 1000000000
  | 9 => -177687926 / 1000000000
  | 10 => 74091771 / 1000000000
  | 11 => 142155892 / 1000000000
  | 12 => -18053086 / 1000000000
  | 13 => 94562866 / 1000000000
  | 14 => -5060576 / 1000000000
  | 15 => 11547670 / 1000000000
  | 16 => -57226677 / 1000000000
  | 17 => 25603950 / 1000000000
  | 18 => -159892442 / 1000000000
  | 19 => -56599956 / 1000000000
  | 20 => 32555271 / 1000000000
  | 21 => -18465117 / 1000000000
  | 22 => -22686862 / 1000000000
  | 23 => -76638870 / 1000000000
  | 24 => 6028328 / 1000000000
  | 25 => -81401777 / 1000000000
  | _ => -187626527 / 1000000000

noncomputable def dualSquaredDistance (i : Fin 27) : ℝ :=
  match i.val with
  | 0 => 1
  | 1 => 3 / 2 - Real.sqrt 33 / 6
  | 2 => 10 / 3 - Real.sqrt 33 / 3
  | 3 => 29 / 6 - 5 * Real.sqrt 33 / 6
  | 4 => 1 / 3
  | 5 => Real.sqrt 33 / 6 + 3 / 2
  | 6 => 4 / 3
  | 7 => Real.sqrt 33 / 3 + 2
  | 8 => Real.sqrt 33 / 6 + 7 / 6
  | 9 => 5
  | 10 => 5 / 3
  | 11 => Real.sqrt 33 / 3 + 10 / 3
  | 12 => Real.sqrt 33 / 3 + 8 / 3
  | 13 => 7 / 3
  | 14 => 3
  | 15 => 4 - Real.sqrt 33 / 3
  | 16 => 9 / 2 - Real.sqrt 33 / 2
  | 17 => 16 / 3 - Real.sqrt 33 / 3
  | 18 => 35 / 6 - 5 * Real.sqrt 33 / 6
  | 19 => 8 / 3 - Real.sqrt 33 / 3
  | 20 => 19 / 6 - Real.sqrt 33 / 2
  | 21 => 2 - Real.sqrt 33 / 3
  | 22 => 7 / 2 - Real.sqrt 33 / 2
  | 23 => 5 - 2 * Real.sqrt 33 / 3
  | 24 => 7 / 6 - Real.sqrt 33 / 6
  | 25 => Real.sqrt 33 / 6 + 5 / 2
  | _ => 5 / 2 - Real.sqrt 33 / 6

noncomputable def dualDistance (i : Fin 27) : ℝ :=
  Real.sqrt (dualSquaredDistance i)

def dualDistanceInterval (i : Fin 27) : IntervalRat :=
  match i.val with
  | 0 => orderedInterval (1000000000000 / 1000000000000) (1000000000000 / 1000000000000)
  | 1 => orderedInterval (736595473950 / 1000000000000) (736595473951 / 1000000000000)
  | 2 => orderedInterval (1190999209832 / 1000000000000) (1190999209833 / 1000000000000)
  | 3 => orderedInterval (214936722203 / 1000000000000) (214936722204 / 1000000000000)
  | 4 => orderedInterval (577350269189 / 1000000000000) (577350269190 / 1000000000000)
  | 5 => orderedInterval (1567618291471 / 1000000000000) (1567618291472 / 1000000000000)
  | 6 => orderedInterval (1154700538379 / 1000000000000) (1154700538380 / 1000000000000)
  | 7 => orderedInterval (1978599053753 / 1000000000000) (1978599053754 / 1000000000000)
  | 8 => orderedInterval (1457427107756 / 1000000000000) (1457427107757 / 1000000000000)
  | 9 => orderedInterval (2236067977499 / 1000000000000) (2236067977500 / 1000000000000)
  | 10 => orderedInterval (1290994448735 / 1000000000000) (1290994448736 / 1000000000000)
  | 11 => orderedInterval (2290892304069 / 1000000000000) (2290892304070 / 1000000000000)
  | 12 => orderedInterval (2140448757195 / 1000000000000) (2140448757196 / 1000000000000)
  | 13 => orderedInterval (1527525231651 / 1000000000000) (1527525231652 / 1000000000000)
  | 14 => orderedInterval (1732050807568 / 1000000000000) (1732050807569 / 1000000000000)
  | 15 => orderedInterval (1444003387976 / 1000000000000) (1444003387977 / 1000000000000)
  | 16 => orderedInterval (1275820785506 / 1000000000000) (1275820785507 / 1000000000000)
  | 17 => orderedInterval (1848912955717 / 1000000000000) (1848912955718 / 1000000000000)
  | 18 => orderedInterval (1022838107694 / 1000000000000) (1022838107695 / 1000000000000)
  | 19 => orderedInterval (867071191514 / 1000000000000) (867071191515 / 1000000000000)
  | 20 => orderedInterval (542572892243 / 1000000000000) (542572892244 / 1000000000000)
  | 21 => orderedInterval (291797505964 / 1000000000000) (291797505965 / 1000000000000)
  | 22 => orderedInterval (792286991393 / 1000000000000) (792286991394 / 1000000000000)
  | 23 => orderedInterval (1081800152049 / 1000000000000) (1081800152050 / 1000000000000)
  | 24 => orderedInterval (457427107756 / 1000000000000) (457427107757 / 1000000000000)
  | 25 => orderedInterval (1859415797436 / 1000000000000) (1859415797437 / 1000000000000)
  | _ => orderedInterval (1242003579803 / 1000000000000) (1242003579804 / 1000000000000)

private theorem sqrt_mem_orderedInterval {x : ℝ} {a b : ℚ}
    (hx : 0 ≤ x) (ha : 0 ≤ (a : ℝ)) (hb : 0 ≤ (b : ℝ))
    (hla : (a : ℝ) ^ 2 ≤ x) (hub : x ≤ (b : ℝ) ^ 2) :
    Real.sqrt x ∈ orderedInterval a b := by
  simp only [IntervalRat.mem_def, orderedInterval, Rat.cast_min, Rat.cast_max]
  have hs0 := Real.sqrt_nonneg x
  have hs2 := Real.sq_sqrt hx
  have hab : (a : ℝ) ≤ b := by nlinarith
  rw [min_eq_left hab, max_eq_right hab]
  constructor <;> nlinarith

private theorem dualDistance_mem_00 :
    dualDistance (0 : Fin 27) ∈ dualDistanceInterval (0 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_01 :
    dualDistance (1 : Fin 27) ∈ dualDistanceInterval (1 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_02 :
    dualDistance (2 : Fin 27) ∈ dualDistanceInterval (2 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_03 :
    dualDistance (3 : Fin 27) ∈ dualDistanceInterval (3 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_04 :
    dualDistance (4 : Fin 27) ∈ dualDistanceInterval (4 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_05 :
    dualDistance (5 : Fin 27) ∈ dualDistanceInterval (5 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_06 :
    dualDistance (6 : Fin 27) ∈ dualDistanceInterval (6 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_07 :
    dualDistance (7 : Fin 27) ∈ dualDistanceInterval (7 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_08 :
    dualDistance (8 : Fin 27) ∈ dualDistanceInterval (8 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_09 :
    dualDistance (9 : Fin 27) ∈ dualDistanceInterval (9 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_10 :
    dualDistance (10 : Fin 27) ∈ dualDistanceInterval (10 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_11 :
    dualDistance (11 : Fin 27) ∈ dualDistanceInterval (11 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_12 :
    dualDistance (12 : Fin 27) ∈ dualDistanceInterval (12 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_13 :
    dualDistance (13 : Fin 27) ∈ dualDistanceInterval (13 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_14 :
    dualDistance (14 : Fin 27) ∈ dualDistanceInterval (14 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_15 :
    dualDistance (15 : Fin 27) ∈ dualDistanceInterval (15 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_16 :
    dualDistance (16 : Fin 27) ∈ dualDistanceInterval (16 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_17 :
    dualDistance (17 : Fin 27) ∈ dualDistanceInterval (17 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_18 :
    dualDistance (18 : Fin 27) ∈ dualDistanceInterval (18 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_19 :
    dualDistance (19 : Fin 27) ∈ dualDistanceInterval (19 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_20 :
    dualDistance (20 : Fin 27) ∈ dualDistanceInterval (20 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_21 :
    dualDistance (21 : Fin 27) ∈ dualDistanceInterval (21 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_22 :
    dualDistance (22 : Fin 27) ∈ dualDistanceInterval (22 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_23 :
    dualDistance (23 : Fin 27) ∈ dualDistanceInterval (23 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_24 :
    dualDistance (24 : Fin 27) ∈ dualDistanceInterval (24 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_25 :
    dualDistance (25 : Fin 27) ∈ dualDistanceInterval (25 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

private theorem dualDistance_mem_26 :
    dualDistance (26 : Fin 27) ∈ dualDistanceInterval (26 : Fin 27) := by
  have hs0 : 0 ≤ Real.sqrt 33 := Real.sqrt_nonneg 33
  have hs2 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
  simp only [dualDistance, dualSquaredDistance, dualDistanceInterval]
  apply sqrt_mem_orderedInterval <;> norm_num <;> nlinarith

theorem dualDistance_mem (i : Fin 27) : dualDistance i ∈ dualDistanceInterval i := by
  fin_cases i
  · exact dualDistance_mem_00
  · exact dualDistance_mem_01
  · exact dualDistance_mem_02
  · exact dualDistance_mem_03
  · exact dualDistance_mem_04
  · exact dualDistance_mem_05
  · exact dualDistance_mem_06
  · exact dualDistance_mem_07
  · exact dualDistance_mem_08
  · exact dualDistance_mem_09
  · exact dualDistance_mem_10
  · exact dualDistance_mem_11
  · exact dualDistance_mem_12
  · exact dualDistance_mem_13
  · exact dualDistance_mem_14
  · exact dualDistance_mem_15
  · exact dualDistance_mem_16
  · exact dualDistance_mem_17
  · exact dualDistance_mem_18
  · exact dualDistance_mem_19
  · exact dualDistance_mem_20
  · exact dualDistance_mem_21
  · exact dualDistance_mem_22
  · exact dualDistance_mem_23
  · exact dualDistance_mem_24
  · exact dualDistance_mem_25
  · exact dualDistance_mem_26

end Erdos232
