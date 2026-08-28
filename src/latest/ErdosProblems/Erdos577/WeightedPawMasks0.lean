import ErdosProblems.Erdos577.WeightedPawModel
import ErdosProblems.Erdos577.FirstPawMasks0

/-! Kernel coverage of the initial weighted threshold, retaining all twelve patterns. -/

namespace Erdos577.WeightedPaw.D0

def residualGroups : List (List ℕ) := [
  [
    15621, 15625, 15878, 15882, 22277, 23813, 27395, 27402,
    27909, 27916, 29957, 30979, 30981, 31749, 31750, 32001,
    32004, 32005, 38659, 38661, 40458, 40460, 43786, 44554,
    46595, 46602, 47626, 48137, 48138, 48642, 48648, 48650],
  [
    50949, 50950, 51977, 51978, 54021, 54025, 54533, 54789,
    54796, 55041, 55044, 55045, 58118, 58122, 59658, 59660,
    59914, 60162, 60168, 60170]]

def residualMasks : List ℕ := residualGroups.flatten

def exceptional (m : ℕ) : Bool := residualGroups.any fun group ↦ group.contains m

private theorem coverage_0 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (0 * 256 + lo.val) →
    7 + PawNine.rowCount (0 * 256 + lo.val) 1 ≤ PathExchange.crossCount (0 * 256 + lo.val) →
    (FirstPaw.D0.covered (0 * 256 + lo.val) || exceptional (0 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_1 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (1 * 256 + lo.val) →
    7 + PawNine.rowCount (1 * 256 + lo.val) 1 ≤ PathExchange.crossCount (1 * 256 + lo.val) →
    (FirstPaw.D0.covered (1 * 256 + lo.val) || exceptional (1 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_2 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (2 * 256 + lo.val) →
    7 + PawNine.rowCount (2 * 256 + lo.val) 1 ≤ PathExchange.crossCount (2 * 256 + lo.val) →
    (FirstPaw.D0.covered (2 * 256 + lo.val) || exceptional (2 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_3 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (3 * 256 + lo.val) →
    7 + PawNine.rowCount (3 * 256 + lo.val) 1 ≤ PathExchange.crossCount (3 * 256 + lo.val) →
    (FirstPaw.D0.covered (3 * 256 + lo.val) || exceptional (3 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_4 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (4 * 256 + lo.val) →
    7 + PawNine.rowCount (4 * 256 + lo.val) 1 ≤ PathExchange.crossCount (4 * 256 + lo.val) →
    (FirstPaw.D0.covered (4 * 256 + lo.val) || exceptional (4 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_5 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (5 * 256 + lo.val) →
    7 + PawNine.rowCount (5 * 256 + lo.val) 1 ≤ PathExchange.crossCount (5 * 256 + lo.val) →
    (FirstPaw.D0.covered (5 * 256 + lo.val) || exceptional (5 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_6 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (6 * 256 + lo.val) →
    7 + PawNine.rowCount (6 * 256 + lo.val) 1 ≤ PathExchange.crossCount (6 * 256 + lo.val) →
    (FirstPaw.D0.covered (6 * 256 + lo.val) || exceptional (6 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_7 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (7 * 256 + lo.val) →
    7 + PawNine.rowCount (7 * 256 + lo.val) 1 ≤ PathExchange.crossCount (7 * 256 + lo.val) →
    (FirstPaw.D0.covered (7 * 256 + lo.val) || exceptional (7 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_8 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (8 * 256 + lo.val) →
    7 + PawNine.rowCount (8 * 256 + lo.val) 1 ≤ PathExchange.crossCount (8 * 256 + lo.val) →
    (FirstPaw.D0.covered (8 * 256 + lo.val) || exceptional (8 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_9 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (9 * 256 + lo.val) →
    7 + PawNine.rowCount (9 * 256 + lo.val) 1 ≤ PathExchange.crossCount (9 * 256 + lo.val) →
    (FirstPaw.D0.covered (9 * 256 + lo.val) || exceptional (9 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_10 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (10 * 256 + lo.val) →
    7 + PawNine.rowCount (10 * 256 + lo.val) 1 ≤ PathExchange.crossCount (10 * 256 + lo.val) →
    (FirstPaw.D0.covered (10 * 256 + lo.val) || exceptional (10 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_11 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (11 * 256 + lo.val) →
    7 + PawNine.rowCount (11 * 256 + lo.val) 1 ≤ PathExchange.crossCount (11 * 256 + lo.val) →
    (FirstPaw.D0.covered (11 * 256 + lo.val) || exceptional (11 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_12 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (12 * 256 + lo.val) →
    7 + PawNine.rowCount (12 * 256 + lo.val) 1 ≤ PathExchange.crossCount (12 * 256 + lo.val) →
    (FirstPaw.D0.covered (12 * 256 + lo.val) || exceptional (12 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_13 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (13 * 256 + lo.val) →
    7 + PawNine.rowCount (13 * 256 + lo.val) 1 ≤ PathExchange.crossCount (13 * 256 + lo.val) →
    (FirstPaw.D0.covered (13 * 256 + lo.val) || exceptional (13 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_14 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (14 * 256 + lo.val) →
    7 + PawNine.rowCount (14 * 256 + lo.val) 1 ≤ PathExchange.crossCount (14 * 256 + lo.val) →
    (FirstPaw.D0.covered (14 * 256 + lo.val) || exceptional (14 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_15 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (15 * 256 + lo.val) →
    7 + PawNine.rowCount (15 * 256 + lo.val) 1 ≤ PathExchange.crossCount (15 * 256 + lo.val) →
    (FirstPaw.D0.covered (15 * 256 + lo.val) || exceptional (15 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_16 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (16 * 256 + lo.val) →
    7 + PawNine.rowCount (16 * 256 + lo.val) 1 ≤ PathExchange.crossCount (16 * 256 + lo.val) →
    (FirstPaw.D0.covered (16 * 256 + lo.val) || exceptional (16 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_17 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (17 * 256 + lo.val) →
    7 + PawNine.rowCount (17 * 256 + lo.val) 1 ≤ PathExchange.crossCount (17 * 256 + lo.val) →
    (FirstPaw.D0.covered (17 * 256 + lo.val) || exceptional (17 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_18 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (18 * 256 + lo.val) →
    7 + PawNine.rowCount (18 * 256 + lo.val) 1 ≤ PathExchange.crossCount (18 * 256 + lo.val) →
    (FirstPaw.D0.covered (18 * 256 + lo.val) || exceptional (18 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_19 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (19 * 256 + lo.val) →
    7 + PawNine.rowCount (19 * 256 + lo.val) 1 ≤ PathExchange.crossCount (19 * 256 + lo.val) →
    (FirstPaw.D0.covered (19 * 256 + lo.val) || exceptional (19 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_20 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (20 * 256 + lo.val) →
    7 + PawNine.rowCount (20 * 256 + lo.val) 1 ≤ PathExchange.crossCount (20 * 256 + lo.val) →
    (FirstPaw.D0.covered (20 * 256 + lo.val) || exceptional (20 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_21 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (21 * 256 + lo.val) →
    7 + PawNine.rowCount (21 * 256 + lo.val) 1 ≤ PathExchange.crossCount (21 * 256 + lo.val) →
    (FirstPaw.D0.covered (21 * 256 + lo.val) || exceptional (21 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_22 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (22 * 256 + lo.val) →
    7 + PawNine.rowCount (22 * 256 + lo.val) 1 ≤ PathExchange.crossCount (22 * 256 + lo.val) →
    (FirstPaw.D0.covered (22 * 256 + lo.val) || exceptional (22 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_23 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (23 * 256 + lo.val) →
    7 + PawNine.rowCount (23 * 256 + lo.val) 1 ≤ PathExchange.crossCount (23 * 256 + lo.val) →
    (FirstPaw.D0.covered (23 * 256 + lo.val) || exceptional (23 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_24 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (24 * 256 + lo.val) →
    7 + PawNine.rowCount (24 * 256 + lo.val) 1 ≤ PathExchange.crossCount (24 * 256 + lo.val) →
    (FirstPaw.D0.covered (24 * 256 + lo.val) || exceptional (24 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_25 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (25 * 256 + lo.val) →
    7 + PawNine.rowCount (25 * 256 + lo.val) 1 ≤ PathExchange.crossCount (25 * 256 + lo.val) →
    (FirstPaw.D0.covered (25 * 256 + lo.val) || exceptional (25 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_26 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (26 * 256 + lo.val) →
    7 + PawNine.rowCount (26 * 256 + lo.val) 1 ≤ PathExchange.crossCount (26 * 256 + lo.val) →
    (FirstPaw.D0.covered (26 * 256 + lo.val) || exceptional (26 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_27 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (27 * 256 + lo.val) →
    7 + PawNine.rowCount (27 * 256 + lo.val) 1 ≤ PathExchange.crossCount (27 * 256 + lo.val) →
    (FirstPaw.D0.covered (27 * 256 + lo.val) || exceptional (27 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_28 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (28 * 256 + lo.val) →
    7 + PawNine.rowCount (28 * 256 + lo.val) 1 ≤ PathExchange.crossCount (28 * 256 + lo.val) →
    (FirstPaw.D0.covered (28 * 256 + lo.val) || exceptional (28 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_29 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (29 * 256 + lo.val) →
    7 + PawNine.rowCount (29 * 256 + lo.val) 1 ≤ PathExchange.crossCount (29 * 256 + lo.val) →
    (FirstPaw.D0.covered (29 * 256 + lo.val) || exceptional (29 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_30 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (30 * 256 + lo.val) →
    7 + PawNine.rowCount (30 * 256 + lo.val) 1 ≤ PathExchange.crossCount (30 * 256 + lo.val) →
    (FirstPaw.D0.covered (30 * 256 + lo.val) || exceptional (30 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_31 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (31 * 256 + lo.val) →
    7 + PawNine.rowCount (31 * 256 + lo.val) 1 ≤ PathExchange.crossCount (31 * 256 + lo.val) →
    (FirstPaw.D0.covered (31 * 256 + lo.val) || exceptional (31 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_32 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (32 * 256 + lo.val) →
    7 + PawNine.rowCount (32 * 256 + lo.val) 1 ≤ PathExchange.crossCount (32 * 256 + lo.val) →
    (FirstPaw.D0.covered (32 * 256 + lo.val) || exceptional (32 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_33 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (33 * 256 + lo.val) →
    7 + PawNine.rowCount (33 * 256 + lo.val) 1 ≤ PathExchange.crossCount (33 * 256 + lo.val) →
    (FirstPaw.D0.covered (33 * 256 + lo.val) || exceptional (33 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_34 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (34 * 256 + lo.val) →
    7 + PawNine.rowCount (34 * 256 + lo.val) 1 ≤ PathExchange.crossCount (34 * 256 + lo.val) →
    (FirstPaw.D0.covered (34 * 256 + lo.val) || exceptional (34 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_35 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (35 * 256 + lo.val) →
    7 + PawNine.rowCount (35 * 256 + lo.val) 1 ≤ PathExchange.crossCount (35 * 256 + lo.val) →
    (FirstPaw.D0.covered (35 * 256 + lo.val) || exceptional (35 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_36 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (36 * 256 + lo.val) →
    7 + PawNine.rowCount (36 * 256 + lo.val) 1 ≤ PathExchange.crossCount (36 * 256 + lo.val) →
    (FirstPaw.D0.covered (36 * 256 + lo.val) || exceptional (36 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_37 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (37 * 256 + lo.val) →
    7 + PawNine.rowCount (37 * 256 + lo.val) 1 ≤ PathExchange.crossCount (37 * 256 + lo.val) →
    (FirstPaw.D0.covered (37 * 256 + lo.val) || exceptional (37 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_38 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (38 * 256 + lo.val) →
    7 + PawNine.rowCount (38 * 256 + lo.val) 1 ≤ PathExchange.crossCount (38 * 256 + lo.val) →
    (FirstPaw.D0.covered (38 * 256 + lo.val) || exceptional (38 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_39 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (39 * 256 + lo.val) →
    7 + PawNine.rowCount (39 * 256 + lo.val) 1 ≤ PathExchange.crossCount (39 * 256 + lo.val) →
    (FirstPaw.D0.covered (39 * 256 + lo.val) || exceptional (39 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_40 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (40 * 256 + lo.val) →
    7 + PawNine.rowCount (40 * 256 + lo.val) 1 ≤ PathExchange.crossCount (40 * 256 + lo.val) →
    (FirstPaw.D0.covered (40 * 256 + lo.val) || exceptional (40 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_41 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (41 * 256 + lo.val) →
    7 + PawNine.rowCount (41 * 256 + lo.val) 1 ≤ PathExchange.crossCount (41 * 256 + lo.val) →
    (FirstPaw.D0.covered (41 * 256 + lo.val) || exceptional (41 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_42 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (42 * 256 + lo.val) →
    7 + PawNine.rowCount (42 * 256 + lo.val) 1 ≤ PathExchange.crossCount (42 * 256 + lo.val) →
    (FirstPaw.D0.covered (42 * 256 + lo.val) || exceptional (42 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_43 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (43 * 256 + lo.val) →
    7 + PawNine.rowCount (43 * 256 + lo.val) 1 ≤ PathExchange.crossCount (43 * 256 + lo.val) →
    (FirstPaw.D0.covered (43 * 256 + lo.val) || exceptional (43 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_44 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (44 * 256 + lo.val) →
    7 + PawNine.rowCount (44 * 256 + lo.val) 1 ≤ PathExchange.crossCount (44 * 256 + lo.val) →
    (FirstPaw.D0.covered (44 * 256 + lo.val) || exceptional (44 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_45 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (45 * 256 + lo.val) →
    7 + PawNine.rowCount (45 * 256 + lo.val) 1 ≤ PathExchange.crossCount (45 * 256 + lo.val) →
    (FirstPaw.D0.covered (45 * 256 + lo.val) || exceptional (45 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_46 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (46 * 256 + lo.val) →
    7 + PawNine.rowCount (46 * 256 + lo.val) 1 ≤ PathExchange.crossCount (46 * 256 + lo.val) →
    (FirstPaw.D0.covered (46 * 256 + lo.val) || exceptional (46 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_47 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (47 * 256 + lo.val) →
    7 + PawNine.rowCount (47 * 256 + lo.val) 1 ≤ PathExchange.crossCount (47 * 256 + lo.val) →
    (FirstPaw.D0.covered (47 * 256 + lo.val) || exceptional (47 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_48 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (48 * 256 + lo.val) →
    7 + PawNine.rowCount (48 * 256 + lo.val) 1 ≤ PathExchange.crossCount (48 * 256 + lo.val) →
    (FirstPaw.D0.covered (48 * 256 + lo.val) || exceptional (48 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_49 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (49 * 256 + lo.val) →
    7 + PawNine.rowCount (49 * 256 + lo.val) 1 ≤ PathExchange.crossCount (49 * 256 + lo.val) →
    (FirstPaw.D0.covered (49 * 256 + lo.val) || exceptional (49 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_50 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (50 * 256 + lo.val) →
    7 + PawNine.rowCount (50 * 256 + lo.val) 1 ≤ PathExchange.crossCount (50 * 256 + lo.val) →
    (FirstPaw.D0.covered (50 * 256 + lo.val) || exceptional (50 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_51 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (51 * 256 + lo.val) →
    7 + PawNine.rowCount (51 * 256 + lo.val) 1 ≤ PathExchange.crossCount (51 * 256 + lo.val) →
    (FirstPaw.D0.covered (51 * 256 + lo.val) || exceptional (51 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_52 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (52 * 256 + lo.val) →
    7 + PawNine.rowCount (52 * 256 + lo.val) 1 ≤ PathExchange.crossCount (52 * 256 + lo.val) →
    (FirstPaw.D0.covered (52 * 256 + lo.val) || exceptional (52 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_53 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (53 * 256 + lo.val) →
    7 + PawNine.rowCount (53 * 256 + lo.val) 1 ≤ PathExchange.crossCount (53 * 256 + lo.val) →
    (FirstPaw.D0.covered (53 * 256 + lo.val) || exceptional (53 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_54 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (54 * 256 + lo.val) →
    7 + PawNine.rowCount (54 * 256 + lo.val) 1 ≤ PathExchange.crossCount (54 * 256 + lo.val) →
    (FirstPaw.D0.covered (54 * 256 + lo.val) || exceptional (54 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_55 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (55 * 256 + lo.val) →
    7 + PawNine.rowCount (55 * 256 + lo.val) 1 ≤ PathExchange.crossCount (55 * 256 + lo.val) →
    (FirstPaw.D0.covered (55 * 256 + lo.val) || exceptional (55 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_56 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (56 * 256 + lo.val) →
    7 + PawNine.rowCount (56 * 256 + lo.val) 1 ≤ PathExchange.crossCount (56 * 256 + lo.val) →
    (FirstPaw.D0.covered (56 * 256 + lo.val) || exceptional (56 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_57 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (57 * 256 + lo.val) →
    7 + PawNine.rowCount (57 * 256 + lo.val) 1 ≤ PathExchange.crossCount (57 * 256 + lo.val) →
    (FirstPaw.D0.covered (57 * 256 + lo.val) || exceptional (57 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_58 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (58 * 256 + lo.val) →
    7 + PawNine.rowCount (58 * 256 + lo.val) 1 ≤ PathExchange.crossCount (58 * 256 + lo.val) →
    (FirstPaw.D0.covered (58 * 256 + lo.val) || exceptional (58 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_59 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (59 * 256 + lo.val) →
    7 + PawNine.rowCount (59 * 256 + lo.val) 1 ≤ PathExchange.crossCount (59 * 256 + lo.val) →
    (FirstPaw.D0.covered (59 * 256 + lo.val) || exceptional (59 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_60 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (60 * 256 + lo.val) →
    7 + PawNine.rowCount (60 * 256 + lo.val) 1 ≤ PathExchange.crossCount (60 * 256 + lo.val) →
    (FirstPaw.D0.covered (60 * 256 + lo.val) || exceptional (60 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_61 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (61 * 256 + lo.val) →
    7 + PawNine.rowCount (61 * 256 + lo.val) 1 ≤ PathExchange.crossCount (61 * 256 + lo.val) →
    (FirstPaw.D0.covered (61 * 256 + lo.val) || exceptional (61 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_62 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (62 * 256 + lo.val) →
    7 + PawNine.rowCount (62 * 256 + lo.val) 1 ≤ PathExchange.crossCount (62 * 256 + lo.val) →
    (FirstPaw.D0.covered (62 * 256 + lo.val) || exceptional (62 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_63 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (63 * 256 + lo.val) →
    7 + PawNine.rowCount (63 * 256 + lo.val) 1 ≤ PathExchange.crossCount (63 * 256 + lo.val) →
    (FirstPaw.D0.covered (63 * 256 + lo.val) || exceptional (63 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_64 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (64 * 256 + lo.val) →
    7 + PawNine.rowCount (64 * 256 + lo.val) 1 ≤ PathExchange.crossCount (64 * 256 + lo.val) →
    (FirstPaw.D0.covered (64 * 256 + lo.val) || exceptional (64 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_65 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (65 * 256 + lo.val) →
    7 + PawNine.rowCount (65 * 256 + lo.val) 1 ≤ PathExchange.crossCount (65 * 256 + lo.val) →
    (FirstPaw.D0.covered (65 * 256 + lo.val) || exceptional (65 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_66 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (66 * 256 + lo.val) →
    7 + PawNine.rowCount (66 * 256 + lo.val) 1 ≤ PathExchange.crossCount (66 * 256 + lo.val) →
    (FirstPaw.D0.covered (66 * 256 + lo.val) || exceptional (66 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_67 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (67 * 256 + lo.val) →
    7 + PawNine.rowCount (67 * 256 + lo.val) 1 ≤ PathExchange.crossCount (67 * 256 + lo.val) →
    (FirstPaw.D0.covered (67 * 256 + lo.val) || exceptional (67 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_68 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (68 * 256 + lo.val) →
    7 + PawNine.rowCount (68 * 256 + lo.val) 1 ≤ PathExchange.crossCount (68 * 256 + lo.val) →
    (FirstPaw.D0.covered (68 * 256 + lo.val) || exceptional (68 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_69 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (69 * 256 + lo.val) →
    7 + PawNine.rowCount (69 * 256 + lo.val) 1 ≤ PathExchange.crossCount (69 * 256 + lo.val) →
    (FirstPaw.D0.covered (69 * 256 + lo.val) || exceptional (69 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_70 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (70 * 256 + lo.val) →
    7 + PawNine.rowCount (70 * 256 + lo.val) 1 ≤ PathExchange.crossCount (70 * 256 + lo.val) →
    (FirstPaw.D0.covered (70 * 256 + lo.val) || exceptional (70 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_71 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (71 * 256 + lo.val) →
    7 + PawNine.rowCount (71 * 256 + lo.val) 1 ≤ PathExchange.crossCount (71 * 256 + lo.val) →
    (FirstPaw.D0.covered (71 * 256 + lo.val) || exceptional (71 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_72 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (72 * 256 + lo.val) →
    7 + PawNine.rowCount (72 * 256 + lo.val) 1 ≤ PathExchange.crossCount (72 * 256 + lo.val) →
    (FirstPaw.D0.covered (72 * 256 + lo.val) || exceptional (72 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_73 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (73 * 256 + lo.val) →
    7 + PawNine.rowCount (73 * 256 + lo.val) 1 ≤ PathExchange.crossCount (73 * 256 + lo.val) →
    (FirstPaw.D0.covered (73 * 256 + lo.val) || exceptional (73 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_74 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (74 * 256 + lo.val) →
    7 + PawNine.rowCount (74 * 256 + lo.val) 1 ≤ PathExchange.crossCount (74 * 256 + lo.val) →
    (FirstPaw.D0.covered (74 * 256 + lo.val) || exceptional (74 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_75 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (75 * 256 + lo.val) →
    7 + PawNine.rowCount (75 * 256 + lo.val) 1 ≤ PathExchange.crossCount (75 * 256 + lo.val) →
    (FirstPaw.D0.covered (75 * 256 + lo.val) || exceptional (75 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_76 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (76 * 256 + lo.val) →
    7 + PawNine.rowCount (76 * 256 + lo.val) 1 ≤ PathExchange.crossCount (76 * 256 + lo.val) →
    (FirstPaw.D0.covered (76 * 256 + lo.val) || exceptional (76 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_77 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (77 * 256 + lo.val) →
    7 + PawNine.rowCount (77 * 256 + lo.val) 1 ≤ PathExchange.crossCount (77 * 256 + lo.val) →
    (FirstPaw.D0.covered (77 * 256 + lo.val) || exceptional (77 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_78 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (78 * 256 + lo.val) →
    7 + PawNine.rowCount (78 * 256 + lo.val) 1 ≤ PathExchange.crossCount (78 * 256 + lo.val) →
    (FirstPaw.D0.covered (78 * 256 + lo.val) || exceptional (78 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_79 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (79 * 256 + lo.val) →
    7 + PawNine.rowCount (79 * 256 + lo.val) 1 ≤ PathExchange.crossCount (79 * 256 + lo.val) →
    (FirstPaw.D0.covered (79 * 256 + lo.val) || exceptional (79 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_80 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (80 * 256 + lo.val) →
    7 + PawNine.rowCount (80 * 256 + lo.val) 1 ≤ PathExchange.crossCount (80 * 256 + lo.val) →
    (FirstPaw.D0.covered (80 * 256 + lo.val) || exceptional (80 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_81 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (81 * 256 + lo.val) →
    7 + PawNine.rowCount (81 * 256 + lo.val) 1 ≤ PathExchange.crossCount (81 * 256 + lo.val) →
    (FirstPaw.D0.covered (81 * 256 + lo.val) || exceptional (81 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_82 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (82 * 256 + lo.val) →
    7 + PawNine.rowCount (82 * 256 + lo.val) 1 ≤ PathExchange.crossCount (82 * 256 + lo.val) →
    (FirstPaw.D0.covered (82 * 256 + lo.val) || exceptional (82 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_83 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (83 * 256 + lo.val) →
    7 + PawNine.rowCount (83 * 256 + lo.val) 1 ≤ PathExchange.crossCount (83 * 256 + lo.val) →
    (FirstPaw.D0.covered (83 * 256 + lo.val) || exceptional (83 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_84 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (84 * 256 + lo.val) →
    7 + PawNine.rowCount (84 * 256 + lo.val) 1 ≤ PathExchange.crossCount (84 * 256 + lo.val) →
    (FirstPaw.D0.covered (84 * 256 + lo.val) || exceptional (84 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_85 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (85 * 256 + lo.val) →
    7 + PawNine.rowCount (85 * 256 + lo.val) 1 ≤ PathExchange.crossCount (85 * 256 + lo.val) →
    (FirstPaw.D0.covered (85 * 256 + lo.val) || exceptional (85 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_86 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (86 * 256 + lo.val) →
    7 + PawNine.rowCount (86 * 256 + lo.val) 1 ≤ PathExchange.crossCount (86 * 256 + lo.val) →
    (FirstPaw.D0.covered (86 * 256 + lo.val) || exceptional (86 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_87 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (87 * 256 + lo.val) →
    7 + PawNine.rowCount (87 * 256 + lo.val) 1 ≤ PathExchange.crossCount (87 * 256 + lo.val) →
    (FirstPaw.D0.covered (87 * 256 + lo.val) || exceptional (87 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_88 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (88 * 256 + lo.val) →
    7 + PawNine.rowCount (88 * 256 + lo.val) 1 ≤ PathExchange.crossCount (88 * 256 + lo.val) →
    (FirstPaw.D0.covered (88 * 256 + lo.val) || exceptional (88 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_89 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (89 * 256 + lo.val) →
    7 + PawNine.rowCount (89 * 256 + lo.val) 1 ≤ PathExchange.crossCount (89 * 256 + lo.val) →
    (FirstPaw.D0.covered (89 * 256 + lo.val) || exceptional (89 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_90 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (90 * 256 + lo.val) →
    7 + PawNine.rowCount (90 * 256 + lo.val) 1 ≤ PathExchange.crossCount (90 * 256 + lo.val) →
    (FirstPaw.D0.covered (90 * 256 + lo.val) || exceptional (90 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_91 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (91 * 256 + lo.val) →
    7 + PawNine.rowCount (91 * 256 + lo.val) 1 ≤ PathExchange.crossCount (91 * 256 + lo.val) →
    (FirstPaw.D0.covered (91 * 256 + lo.val) || exceptional (91 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_92 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (92 * 256 + lo.val) →
    7 + PawNine.rowCount (92 * 256 + lo.val) 1 ≤ PathExchange.crossCount (92 * 256 + lo.val) →
    (FirstPaw.D0.covered (92 * 256 + lo.val) || exceptional (92 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_93 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (93 * 256 + lo.val) →
    7 + PawNine.rowCount (93 * 256 + lo.val) 1 ≤ PathExchange.crossCount (93 * 256 + lo.val) →
    (FirstPaw.D0.covered (93 * 256 + lo.val) || exceptional (93 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_94 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (94 * 256 + lo.val) →
    7 + PawNine.rowCount (94 * 256 + lo.val) 1 ≤ PathExchange.crossCount (94 * 256 + lo.val) →
    (FirstPaw.D0.covered (94 * 256 + lo.val) || exceptional (94 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_95 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (95 * 256 + lo.val) →
    7 + PawNine.rowCount (95 * 256 + lo.val) 1 ≤ PathExchange.crossCount (95 * 256 + lo.val) →
    (FirstPaw.D0.covered (95 * 256 + lo.val) || exceptional (95 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_96 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (96 * 256 + lo.val) →
    7 + PawNine.rowCount (96 * 256 + lo.val) 1 ≤ PathExchange.crossCount (96 * 256 + lo.val) →
    (FirstPaw.D0.covered (96 * 256 + lo.val) || exceptional (96 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_97 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (97 * 256 + lo.val) →
    7 + PawNine.rowCount (97 * 256 + lo.val) 1 ≤ PathExchange.crossCount (97 * 256 + lo.val) →
    (FirstPaw.D0.covered (97 * 256 + lo.val) || exceptional (97 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_98 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (98 * 256 + lo.val) →
    7 + PawNine.rowCount (98 * 256 + lo.val) 1 ≤ PathExchange.crossCount (98 * 256 + lo.val) →
    (FirstPaw.D0.covered (98 * 256 + lo.val) || exceptional (98 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_99 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (99 * 256 + lo.val) →
    7 + PawNine.rowCount (99 * 256 + lo.val) 1 ≤ PathExchange.crossCount (99 * 256 + lo.val) →
    (FirstPaw.D0.covered (99 * 256 + lo.val) || exceptional (99 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_100 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (100 * 256 + lo.val) →
    7 + PawNine.rowCount (100 * 256 + lo.val) 1 ≤ PathExchange.crossCount (100 * 256 + lo.val) →
    (FirstPaw.D0.covered (100 * 256 + lo.val) || exceptional (100 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_101 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (101 * 256 + lo.val) →
    7 + PawNine.rowCount (101 * 256 + lo.val) 1 ≤ PathExchange.crossCount (101 * 256 + lo.val) →
    (FirstPaw.D0.covered (101 * 256 + lo.val) || exceptional (101 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_102 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (102 * 256 + lo.val) →
    7 + PawNine.rowCount (102 * 256 + lo.val) 1 ≤ PathExchange.crossCount (102 * 256 + lo.val) →
    (FirstPaw.D0.covered (102 * 256 + lo.val) || exceptional (102 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_103 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (103 * 256 + lo.val) →
    7 + PawNine.rowCount (103 * 256 + lo.val) 1 ≤ PathExchange.crossCount (103 * 256 + lo.val) →
    (FirstPaw.D0.covered (103 * 256 + lo.val) || exceptional (103 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_104 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (104 * 256 + lo.val) →
    7 + PawNine.rowCount (104 * 256 + lo.val) 1 ≤ PathExchange.crossCount (104 * 256 + lo.val) →
    (FirstPaw.D0.covered (104 * 256 + lo.val) || exceptional (104 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_105 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (105 * 256 + lo.val) →
    7 + PawNine.rowCount (105 * 256 + lo.val) 1 ≤ PathExchange.crossCount (105 * 256 + lo.val) →
    (FirstPaw.D0.covered (105 * 256 + lo.val) || exceptional (105 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_106 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (106 * 256 + lo.val) →
    7 + PawNine.rowCount (106 * 256 + lo.val) 1 ≤ PathExchange.crossCount (106 * 256 + lo.val) →
    (FirstPaw.D0.covered (106 * 256 + lo.val) || exceptional (106 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_107 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (107 * 256 + lo.val) →
    7 + PawNine.rowCount (107 * 256 + lo.val) 1 ≤ PathExchange.crossCount (107 * 256 + lo.val) →
    (FirstPaw.D0.covered (107 * 256 + lo.val) || exceptional (107 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_108 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (108 * 256 + lo.val) →
    7 + PawNine.rowCount (108 * 256 + lo.val) 1 ≤ PathExchange.crossCount (108 * 256 + lo.val) →
    (FirstPaw.D0.covered (108 * 256 + lo.val) || exceptional (108 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_109 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (109 * 256 + lo.val) →
    7 + PawNine.rowCount (109 * 256 + lo.val) 1 ≤ PathExchange.crossCount (109 * 256 + lo.val) →
    (FirstPaw.D0.covered (109 * 256 + lo.val) || exceptional (109 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_110 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (110 * 256 + lo.val) →
    7 + PawNine.rowCount (110 * 256 + lo.val) 1 ≤ PathExchange.crossCount (110 * 256 + lo.val) →
    (FirstPaw.D0.covered (110 * 256 + lo.val) || exceptional (110 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_111 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (111 * 256 + lo.val) →
    7 + PawNine.rowCount (111 * 256 + lo.val) 1 ≤ PathExchange.crossCount (111 * 256 + lo.val) →
    (FirstPaw.D0.covered (111 * 256 + lo.val) || exceptional (111 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_112 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (112 * 256 + lo.val) →
    7 + PawNine.rowCount (112 * 256 + lo.val) 1 ≤ PathExchange.crossCount (112 * 256 + lo.val) →
    (FirstPaw.D0.covered (112 * 256 + lo.val) || exceptional (112 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_113 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (113 * 256 + lo.val) →
    7 + PawNine.rowCount (113 * 256 + lo.val) 1 ≤ PathExchange.crossCount (113 * 256 + lo.val) →
    (FirstPaw.D0.covered (113 * 256 + lo.val) || exceptional (113 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_114 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (114 * 256 + lo.val) →
    7 + PawNine.rowCount (114 * 256 + lo.val) 1 ≤ PathExchange.crossCount (114 * 256 + lo.val) →
    (FirstPaw.D0.covered (114 * 256 + lo.val) || exceptional (114 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_115 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (115 * 256 + lo.val) →
    7 + PawNine.rowCount (115 * 256 + lo.val) 1 ≤ PathExchange.crossCount (115 * 256 + lo.val) →
    (FirstPaw.D0.covered (115 * 256 + lo.val) || exceptional (115 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_116 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (116 * 256 + lo.val) →
    7 + PawNine.rowCount (116 * 256 + lo.val) 1 ≤ PathExchange.crossCount (116 * 256 + lo.val) →
    (FirstPaw.D0.covered (116 * 256 + lo.val) || exceptional (116 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_117 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (117 * 256 + lo.val) →
    7 + PawNine.rowCount (117 * 256 + lo.val) 1 ≤ PathExchange.crossCount (117 * 256 + lo.val) →
    (FirstPaw.D0.covered (117 * 256 + lo.val) || exceptional (117 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_118 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (118 * 256 + lo.val) →
    7 + PawNine.rowCount (118 * 256 + lo.val) 1 ≤ PathExchange.crossCount (118 * 256 + lo.val) →
    (FirstPaw.D0.covered (118 * 256 + lo.val) || exceptional (118 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_119 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (119 * 256 + lo.val) →
    7 + PawNine.rowCount (119 * 256 + lo.val) 1 ≤ PathExchange.crossCount (119 * 256 + lo.val) →
    (FirstPaw.D0.covered (119 * 256 + lo.val) || exceptional (119 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_120 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (120 * 256 + lo.val) →
    7 + PawNine.rowCount (120 * 256 + lo.val) 1 ≤ PathExchange.crossCount (120 * 256 + lo.val) →
    (FirstPaw.D0.covered (120 * 256 + lo.val) || exceptional (120 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_121 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (121 * 256 + lo.val) →
    7 + PawNine.rowCount (121 * 256 + lo.val) 1 ≤ PathExchange.crossCount (121 * 256 + lo.val) →
    (FirstPaw.D0.covered (121 * 256 + lo.val) || exceptional (121 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_122 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (122 * 256 + lo.val) →
    7 + PawNine.rowCount (122 * 256 + lo.val) 1 ≤ PathExchange.crossCount (122 * 256 + lo.val) →
    (FirstPaw.D0.covered (122 * 256 + lo.val) || exceptional (122 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_123 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (123 * 256 + lo.val) →
    7 + PawNine.rowCount (123 * 256 + lo.val) 1 ≤ PathExchange.crossCount (123 * 256 + lo.val) →
    (FirstPaw.D0.covered (123 * 256 + lo.val) || exceptional (123 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_124 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (124 * 256 + lo.val) →
    7 + PawNine.rowCount (124 * 256 + lo.val) 1 ≤ PathExchange.crossCount (124 * 256 + lo.val) →
    (FirstPaw.D0.covered (124 * 256 + lo.val) || exceptional (124 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_125 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (125 * 256 + lo.val) →
    7 + PawNine.rowCount (125 * 256 + lo.val) 1 ≤ PathExchange.crossCount (125 * 256 + lo.val) →
    (FirstPaw.D0.covered (125 * 256 + lo.val) || exceptional (125 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_126 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (126 * 256 + lo.val) →
    7 + PawNine.rowCount (126 * 256 + lo.val) 1 ≤ PathExchange.crossCount (126 * 256 + lo.val) →
    (FirstPaw.D0.covered (126 * 256 + lo.val) || exceptional (126 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_127 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (127 * 256 + lo.val) →
    7 + PawNine.rowCount (127 * 256 + lo.val) 1 ≤ PathExchange.crossCount (127 * 256 + lo.val) →
    (FirstPaw.D0.covered (127 * 256 + lo.val) || exceptional (127 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_128 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (128 * 256 + lo.val) →
    7 + PawNine.rowCount (128 * 256 + lo.val) 1 ≤ PathExchange.crossCount (128 * 256 + lo.val) →
    (FirstPaw.D0.covered (128 * 256 + lo.val) || exceptional (128 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_129 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (129 * 256 + lo.val) →
    7 + PawNine.rowCount (129 * 256 + lo.val) 1 ≤ PathExchange.crossCount (129 * 256 + lo.val) →
    (FirstPaw.D0.covered (129 * 256 + lo.val) || exceptional (129 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_130 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (130 * 256 + lo.val) →
    7 + PawNine.rowCount (130 * 256 + lo.val) 1 ≤ PathExchange.crossCount (130 * 256 + lo.val) →
    (FirstPaw.D0.covered (130 * 256 + lo.val) || exceptional (130 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_131 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (131 * 256 + lo.val) →
    7 + PawNine.rowCount (131 * 256 + lo.val) 1 ≤ PathExchange.crossCount (131 * 256 + lo.val) →
    (FirstPaw.D0.covered (131 * 256 + lo.val) || exceptional (131 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_132 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (132 * 256 + lo.val) →
    7 + PawNine.rowCount (132 * 256 + lo.val) 1 ≤ PathExchange.crossCount (132 * 256 + lo.val) →
    (FirstPaw.D0.covered (132 * 256 + lo.val) || exceptional (132 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_133 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (133 * 256 + lo.val) →
    7 + PawNine.rowCount (133 * 256 + lo.val) 1 ≤ PathExchange.crossCount (133 * 256 + lo.val) →
    (FirstPaw.D0.covered (133 * 256 + lo.val) || exceptional (133 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_134 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (134 * 256 + lo.val) →
    7 + PawNine.rowCount (134 * 256 + lo.val) 1 ≤ PathExchange.crossCount (134 * 256 + lo.val) →
    (FirstPaw.D0.covered (134 * 256 + lo.val) || exceptional (134 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_135 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (135 * 256 + lo.val) →
    7 + PawNine.rowCount (135 * 256 + lo.val) 1 ≤ PathExchange.crossCount (135 * 256 + lo.val) →
    (FirstPaw.D0.covered (135 * 256 + lo.val) || exceptional (135 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_136 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (136 * 256 + lo.val) →
    7 + PawNine.rowCount (136 * 256 + lo.val) 1 ≤ PathExchange.crossCount (136 * 256 + lo.val) →
    (FirstPaw.D0.covered (136 * 256 + lo.val) || exceptional (136 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_137 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (137 * 256 + lo.val) →
    7 + PawNine.rowCount (137 * 256 + lo.val) 1 ≤ PathExchange.crossCount (137 * 256 + lo.val) →
    (FirstPaw.D0.covered (137 * 256 + lo.val) || exceptional (137 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_138 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (138 * 256 + lo.val) →
    7 + PawNine.rowCount (138 * 256 + lo.val) 1 ≤ PathExchange.crossCount (138 * 256 + lo.val) →
    (FirstPaw.D0.covered (138 * 256 + lo.val) || exceptional (138 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_139 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (139 * 256 + lo.val) →
    7 + PawNine.rowCount (139 * 256 + lo.val) 1 ≤ PathExchange.crossCount (139 * 256 + lo.val) →
    (FirstPaw.D0.covered (139 * 256 + lo.val) || exceptional (139 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_140 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (140 * 256 + lo.val) →
    7 + PawNine.rowCount (140 * 256 + lo.val) 1 ≤ PathExchange.crossCount (140 * 256 + lo.val) →
    (FirstPaw.D0.covered (140 * 256 + lo.val) || exceptional (140 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_141 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (141 * 256 + lo.val) →
    7 + PawNine.rowCount (141 * 256 + lo.val) 1 ≤ PathExchange.crossCount (141 * 256 + lo.val) →
    (FirstPaw.D0.covered (141 * 256 + lo.val) || exceptional (141 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_142 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (142 * 256 + lo.val) →
    7 + PawNine.rowCount (142 * 256 + lo.val) 1 ≤ PathExchange.crossCount (142 * 256 + lo.val) →
    (FirstPaw.D0.covered (142 * 256 + lo.val) || exceptional (142 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_143 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (143 * 256 + lo.val) →
    7 + PawNine.rowCount (143 * 256 + lo.val) 1 ≤ PathExchange.crossCount (143 * 256 + lo.val) →
    (FirstPaw.D0.covered (143 * 256 + lo.val) || exceptional (143 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_144 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (144 * 256 + lo.val) →
    7 + PawNine.rowCount (144 * 256 + lo.val) 1 ≤ PathExchange.crossCount (144 * 256 + lo.val) →
    (FirstPaw.D0.covered (144 * 256 + lo.val) || exceptional (144 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_145 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (145 * 256 + lo.val) →
    7 + PawNine.rowCount (145 * 256 + lo.val) 1 ≤ PathExchange.crossCount (145 * 256 + lo.val) →
    (FirstPaw.D0.covered (145 * 256 + lo.val) || exceptional (145 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_146 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (146 * 256 + lo.val) →
    7 + PawNine.rowCount (146 * 256 + lo.val) 1 ≤ PathExchange.crossCount (146 * 256 + lo.val) →
    (FirstPaw.D0.covered (146 * 256 + lo.val) || exceptional (146 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_147 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (147 * 256 + lo.val) →
    7 + PawNine.rowCount (147 * 256 + lo.val) 1 ≤ PathExchange.crossCount (147 * 256 + lo.val) →
    (FirstPaw.D0.covered (147 * 256 + lo.val) || exceptional (147 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_148 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (148 * 256 + lo.val) →
    7 + PawNine.rowCount (148 * 256 + lo.val) 1 ≤ PathExchange.crossCount (148 * 256 + lo.val) →
    (FirstPaw.D0.covered (148 * 256 + lo.val) || exceptional (148 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_149 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (149 * 256 + lo.val) →
    7 + PawNine.rowCount (149 * 256 + lo.val) 1 ≤ PathExchange.crossCount (149 * 256 + lo.val) →
    (FirstPaw.D0.covered (149 * 256 + lo.val) || exceptional (149 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_150 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (150 * 256 + lo.val) →
    7 + PawNine.rowCount (150 * 256 + lo.val) 1 ≤ PathExchange.crossCount (150 * 256 + lo.val) →
    (FirstPaw.D0.covered (150 * 256 + lo.val) || exceptional (150 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_151 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (151 * 256 + lo.val) →
    7 + PawNine.rowCount (151 * 256 + lo.val) 1 ≤ PathExchange.crossCount (151 * 256 + lo.val) →
    (FirstPaw.D0.covered (151 * 256 + lo.val) || exceptional (151 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_152 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (152 * 256 + lo.val) →
    7 + PawNine.rowCount (152 * 256 + lo.val) 1 ≤ PathExchange.crossCount (152 * 256 + lo.val) →
    (FirstPaw.D0.covered (152 * 256 + lo.val) || exceptional (152 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_153 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (153 * 256 + lo.val) →
    7 + PawNine.rowCount (153 * 256 + lo.val) 1 ≤ PathExchange.crossCount (153 * 256 + lo.val) →
    (FirstPaw.D0.covered (153 * 256 + lo.val) || exceptional (153 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_154 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (154 * 256 + lo.val) →
    7 + PawNine.rowCount (154 * 256 + lo.val) 1 ≤ PathExchange.crossCount (154 * 256 + lo.val) →
    (FirstPaw.D0.covered (154 * 256 + lo.val) || exceptional (154 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_155 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (155 * 256 + lo.val) →
    7 + PawNine.rowCount (155 * 256 + lo.val) 1 ≤ PathExchange.crossCount (155 * 256 + lo.val) →
    (FirstPaw.D0.covered (155 * 256 + lo.val) || exceptional (155 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_156 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (156 * 256 + lo.val) →
    7 + PawNine.rowCount (156 * 256 + lo.val) 1 ≤ PathExchange.crossCount (156 * 256 + lo.val) →
    (FirstPaw.D0.covered (156 * 256 + lo.val) || exceptional (156 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_157 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (157 * 256 + lo.val) →
    7 + PawNine.rowCount (157 * 256 + lo.val) 1 ≤ PathExchange.crossCount (157 * 256 + lo.val) →
    (FirstPaw.D0.covered (157 * 256 + lo.val) || exceptional (157 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_158 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (158 * 256 + lo.val) →
    7 + PawNine.rowCount (158 * 256 + lo.val) 1 ≤ PathExchange.crossCount (158 * 256 + lo.val) →
    (FirstPaw.D0.covered (158 * 256 + lo.val) || exceptional (158 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_159 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (159 * 256 + lo.val) →
    7 + PawNine.rowCount (159 * 256 + lo.val) 1 ≤ PathExchange.crossCount (159 * 256 + lo.val) →
    (FirstPaw.D0.covered (159 * 256 + lo.val) || exceptional (159 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_160 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (160 * 256 + lo.val) →
    7 + PawNine.rowCount (160 * 256 + lo.val) 1 ≤ PathExchange.crossCount (160 * 256 + lo.val) →
    (FirstPaw.D0.covered (160 * 256 + lo.val) || exceptional (160 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_161 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (161 * 256 + lo.val) →
    7 + PawNine.rowCount (161 * 256 + lo.val) 1 ≤ PathExchange.crossCount (161 * 256 + lo.val) →
    (FirstPaw.D0.covered (161 * 256 + lo.val) || exceptional (161 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_162 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (162 * 256 + lo.val) →
    7 + PawNine.rowCount (162 * 256 + lo.val) 1 ≤ PathExchange.crossCount (162 * 256 + lo.val) →
    (FirstPaw.D0.covered (162 * 256 + lo.val) || exceptional (162 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_163 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (163 * 256 + lo.val) →
    7 + PawNine.rowCount (163 * 256 + lo.val) 1 ≤ PathExchange.crossCount (163 * 256 + lo.val) →
    (FirstPaw.D0.covered (163 * 256 + lo.val) || exceptional (163 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_164 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (164 * 256 + lo.val) →
    7 + PawNine.rowCount (164 * 256 + lo.val) 1 ≤ PathExchange.crossCount (164 * 256 + lo.val) →
    (FirstPaw.D0.covered (164 * 256 + lo.val) || exceptional (164 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_165 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (165 * 256 + lo.val) →
    7 + PawNine.rowCount (165 * 256 + lo.val) 1 ≤ PathExchange.crossCount (165 * 256 + lo.val) →
    (FirstPaw.D0.covered (165 * 256 + lo.val) || exceptional (165 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_166 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (166 * 256 + lo.val) →
    7 + PawNine.rowCount (166 * 256 + lo.val) 1 ≤ PathExchange.crossCount (166 * 256 + lo.val) →
    (FirstPaw.D0.covered (166 * 256 + lo.val) || exceptional (166 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_167 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (167 * 256 + lo.val) →
    7 + PawNine.rowCount (167 * 256 + lo.val) 1 ≤ PathExchange.crossCount (167 * 256 + lo.val) →
    (FirstPaw.D0.covered (167 * 256 + lo.val) || exceptional (167 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_168 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (168 * 256 + lo.val) →
    7 + PawNine.rowCount (168 * 256 + lo.val) 1 ≤ PathExchange.crossCount (168 * 256 + lo.val) →
    (FirstPaw.D0.covered (168 * 256 + lo.val) || exceptional (168 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_169 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (169 * 256 + lo.val) →
    7 + PawNine.rowCount (169 * 256 + lo.val) 1 ≤ PathExchange.crossCount (169 * 256 + lo.val) →
    (FirstPaw.D0.covered (169 * 256 + lo.val) || exceptional (169 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_170 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (170 * 256 + lo.val) →
    7 + PawNine.rowCount (170 * 256 + lo.val) 1 ≤ PathExchange.crossCount (170 * 256 + lo.val) →
    (FirstPaw.D0.covered (170 * 256 + lo.val) || exceptional (170 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_171 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (171 * 256 + lo.val) →
    7 + PawNine.rowCount (171 * 256 + lo.val) 1 ≤ PathExchange.crossCount (171 * 256 + lo.val) →
    (FirstPaw.D0.covered (171 * 256 + lo.val) || exceptional (171 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_172 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (172 * 256 + lo.val) →
    7 + PawNine.rowCount (172 * 256 + lo.val) 1 ≤ PathExchange.crossCount (172 * 256 + lo.val) →
    (FirstPaw.D0.covered (172 * 256 + lo.val) || exceptional (172 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_173 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (173 * 256 + lo.val) →
    7 + PawNine.rowCount (173 * 256 + lo.val) 1 ≤ PathExchange.crossCount (173 * 256 + lo.val) →
    (FirstPaw.D0.covered (173 * 256 + lo.val) || exceptional (173 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_174 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (174 * 256 + lo.val) →
    7 + PawNine.rowCount (174 * 256 + lo.val) 1 ≤ PathExchange.crossCount (174 * 256 + lo.val) →
    (FirstPaw.D0.covered (174 * 256 + lo.val) || exceptional (174 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_175 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (175 * 256 + lo.val) →
    7 + PawNine.rowCount (175 * 256 + lo.val) 1 ≤ PathExchange.crossCount (175 * 256 + lo.val) →
    (FirstPaw.D0.covered (175 * 256 + lo.val) || exceptional (175 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_176 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (176 * 256 + lo.val) →
    7 + PawNine.rowCount (176 * 256 + lo.val) 1 ≤ PathExchange.crossCount (176 * 256 + lo.val) →
    (FirstPaw.D0.covered (176 * 256 + lo.val) || exceptional (176 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_177 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (177 * 256 + lo.val) →
    7 + PawNine.rowCount (177 * 256 + lo.val) 1 ≤ PathExchange.crossCount (177 * 256 + lo.val) →
    (FirstPaw.D0.covered (177 * 256 + lo.val) || exceptional (177 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_178 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (178 * 256 + lo.val) →
    7 + PawNine.rowCount (178 * 256 + lo.val) 1 ≤ PathExchange.crossCount (178 * 256 + lo.val) →
    (FirstPaw.D0.covered (178 * 256 + lo.val) || exceptional (178 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_179 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (179 * 256 + lo.val) →
    7 + PawNine.rowCount (179 * 256 + lo.val) 1 ≤ PathExchange.crossCount (179 * 256 + lo.val) →
    (FirstPaw.D0.covered (179 * 256 + lo.val) || exceptional (179 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_180 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (180 * 256 + lo.val) →
    7 + PawNine.rowCount (180 * 256 + lo.val) 1 ≤ PathExchange.crossCount (180 * 256 + lo.val) →
    (FirstPaw.D0.covered (180 * 256 + lo.val) || exceptional (180 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_181 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (181 * 256 + lo.val) →
    7 + PawNine.rowCount (181 * 256 + lo.val) 1 ≤ PathExchange.crossCount (181 * 256 + lo.val) →
    (FirstPaw.D0.covered (181 * 256 + lo.val) || exceptional (181 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_182 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (182 * 256 + lo.val) →
    7 + PawNine.rowCount (182 * 256 + lo.val) 1 ≤ PathExchange.crossCount (182 * 256 + lo.val) →
    (FirstPaw.D0.covered (182 * 256 + lo.val) || exceptional (182 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_183 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (183 * 256 + lo.val) →
    7 + PawNine.rowCount (183 * 256 + lo.val) 1 ≤ PathExchange.crossCount (183 * 256 + lo.val) →
    (FirstPaw.D0.covered (183 * 256 + lo.val) || exceptional (183 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_184 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (184 * 256 + lo.val) →
    7 + PawNine.rowCount (184 * 256 + lo.val) 1 ≤ PathExchange.crossCount (184 * 256 + lo.val) →
    (FirstPaw.D0.covered (184 * 256 + lo.val) || exceptional (184 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_185 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (185 * 256 + lo.val) →
    7 + PawNine.rowCount (185 * 256 + lo.val) 1 ≤ PathExchange.crossCount (185 * 256 + lo.val) →
    (FirstPaw.D0.covered (185 * 256 + lo.val) || exceptional (185 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_186 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (186 * 256 + lo.val) →
    7 + PawNine.rowCount (186 * 256 + lo.val) 1 ≤ PathExchange.crossCount (186 * 256 + lo.val) →
    (FirstPaw.D0.covered (186 * 256 + lo.val) || exceptional (186 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_187 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (187 * 256 + lo.val) →
    7 + PawNine.rowCount (187 * 256 + lo.val) 1 ≤ PathExchange.crossCount (187 * 256 + lo.val) →
    (FirstPaw.D0.covered (187 * 256 + lo.val) || exceptional (187 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_188 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (188 * 256 + lo.val) →
    7 + PawNine.rowCount (188 * 256 + lo.val) 1 ≤ PathExchange.crossCount (188 * 256 + lo.val) →
    (FirstPaw.D0.covered (188 * 256 + lo.val) || exceptional (188 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_189 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (189 * 256 + lo.val) →
    7 + PawNine.rowCount (189 * 256 + lo.val) 1 ≤ PathExchange.crossCount (189 * 256 + lo.val) →
    (FirstPaw.D0.covered (189 * 256 + lo.val) || exceptional (189 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_190 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (190 * 256 + lo.val) →
    7 + PawNine.rowCount (190 * 256 + lo.val) 1 ≤ PathExchange.crossCount (190 * 256 + lo.val) →
    (FirstPaw.D0.covered (190 * 256 + lo.val) || exceptional (190 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_191 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (191 * 256 + lo.val) →
    7 + PawNine.rowCount (191 * 256 + lo.val) 1 ≤ PathExchange.crossCount (191 * 256 + lo.val) →
    (FirstPaw.D0.covered (191 * 256 + lo.val) || exceptional (191 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_192 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (192 * 256 + lo.val) →
    7 + PawNine.rowCount (192 * 256 + lo.val) 1 ≤ PathExchange.crossCount (192 * 256 + lo.val) →
    (FirstPaw.D0.covered (192 * 256 + lo.val) || exceptional (192 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_193 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (193 * 256 + lo.val) →
    7 + PawNine.rowCount (193 * 256 + lo.val) 1 ≤ PathExchange.crossCount (193 * 256 + lo.val) →
    (FirstPaw.D0.covered (193 * 256 + lo.val) || exceptional (193 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_194 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (194 * 256 + lo.val) →
    7 + PawNine.rowCount (194 * 256 + lo.val) 1 ≤ PathExchange.crossCount (194 * 256 + lo.val) →
    (FirstPaw.D0.covered (194 * 256 + lo.val) || exceptional (194 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_195 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (195 * 256 + lo.val) →
    7 + PawNine.rowCount (195 * 256 + lo.val) 1 ≤ PathExchange.crossCount (195 * 256 + lo.val) →
    (FirstPaw.D0.covered (195 * 256 + lo.val) || exceptional (195 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_196 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (196 * 256 + lo.val) →
    7 + PawNine.rowCount (196 * 256 + lo.val) 1 ≤ PathExchange.crossCount (196 * 256 + lo.val) →
    (FirstPaw.D0.covered (196 * 256 + lo.val) || exceptional (196 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_197 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (197 * 256 + lo.val) →
    7 + PawNine.rowCount (197 * 256 + lo.val) 1 ≤ PathExchange.crossCount (197 * 256 + lo.val) →
    (FirstPaw.D0.covered (197 * 256 + lo.val) || exceptional (197 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_198 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (198 * 256 + lo.val) →
    7 + PawNine.rowCount (198 * 256 + lo.val) 1 ≤ PathExchange.crossCount (198 * 256 + lo.val) →
    (FirstPaw.D0.covered (198 * 256 + lo.val) || exceptional (198 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_199 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (199 * 256 + lo.val) →
    7 + PawNine.rowCount (199 * 256 + lo.val) 1 ≤ PathExchange.crossCount (199 * 256 + lo.val) →
    (FirstPaw.D0.covered (199 * 256 + lo.val) || exceptional (199 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_200 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (200 * 256 + lo.val) →
    7 + PawNine.rowCount (200 * 256 + lo.val) 1 ≤ PathExchange.crossCount (200 * 256 + lo.val) →
    (FirstPaw.D0.covered (200 * 256 + lo.val) || exceptional (200 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_201 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (201 * 256 + lo.val) →
    7 + PawNine.rowCount (201 * 256 + lo.val) 1 ≤ PathExchange.crossCount (201 * 256 + lo.val) →
    (FirstPaw.D0.covered (201 * 256 + lo.val) || exceptional (201 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_202 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (202 * 256 + lo.val) →
    7 + PawNine.rowCount (202 * 256 + lo.val) 1 ≤ PathExchange.crossCount (202 * 256 + lo.val) →
    (FirstPaw.D0.covered (202 * 256 + lo.val) || exceptional (202 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_203 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (203 * 256 + lo.val) →
    7 + PawNine.rowCount (203 * 256 + lo.val) 1 ≤ PathExchange.crossCount (203 * 256 + lo.val) →
    (FirstPaw.D0.covered (203 * 256 + lo.val) || exceptional (203 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_204 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (204 * 256 + lo.val) →
    7 + PawNine.rowCount (204 * 256 + lo.val) 1 ≤ PathExchange.crossCount (204 * 256 + lo.val) →
    (FirstPaw.D0.covered (204 * 256 + lo.val) || exceptional (204 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_205 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (205 * 256 + lo.val) →
    7 + PawNine.rowCount (205 * 256 + lo.val) 1 ≤ PathExchange.crossCount (205 * 256 + lo.val) →
    (FirstPaw.D0.covered (205 * 256 + lo.val) || exceptional (205 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_206 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (206 * 256 + lo.val) →
    7 + PawNine.rowCount (206 * 256 + lo.val) 1 ≤ PathExchange.crossCount (206 * 256 + lo.val) →
    (FirstPaw.D0.covered (206 * 256 + lo.val) || exceptional (206 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_207 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (207 * 256 + lo.val) →
    7 + PawNine.rowCount (207 * 256 + lo.val) 1 ≤ PathExchange.crossCount (207 * 256 + lo.val) →
    (FirstPaw.D0.covered (207 * 256 + lo.val) || exceptional (207 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_208 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (208 * 256 + lo.val) →
    7 + PawNine.rowCount (208 * 256 + lo.val) 1 ≤ PathExchange.crossCount (208 * 256 + lo.val) →
    (FirstPaw.D0.covered (208 * 256 + lo.val) || exceptional (208 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_209 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (209 * 256 + lo.val) →
    7 + PawNine.rowCount (209 * 256 + lo.val) 1 ≤ PathExchange.crossCount (209 * 256 + lo.val) →
    (FirstPaw.D0.covered (209 * 256 + lo.val) || exceptional (209 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_210 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (210 * 256 + lo.val) →
    7 + PawNine.rowCount (210 * 256 + lo.val) 1 ≤ PathExchange.crossCount (210 * 256 + lo.val) →
    (FirstPaw.D0.covered (210 * 256 + lo.val) || exceptional (210 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_211 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (211 * 256 + lo.val) →
    7 + PawNine.rowCount (211 * 256 + lo.val) 1 ≤ PathExchange.crossCount (211 * 256 + lo.val) →
    (FirstPaw.D0.covered (211 * 256 + lo.val) || exceptional (211 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_212 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (212 * 256 + lo.val) →
    7 + PawNine.rowCount (212 * 256 + lo.val) 1 ≤ PathExchange.crossCount (212 * 256 + lo.val) →
    (FirstPaw.D0.covered (212 * 256 + lo.val) || exceptional (212 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_213 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (213 * 256 + lo.val) →
    7 + PawNine.rowCount (213 * 256 + lo.val) 1 ≤ PathExchange.crossCount (213 * 256 + lo.val) →
    (FirstPaw.D0.covered (213 * 256 + lo.val) || exceptional (213 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_214 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (214 * 256 + lo.val) →
    7 + PawNine.rowCount (214 * 256 + lo.val) 1 ≤ PathExchange.crossCount (214 * 256 + lo.val) →
    (FirstPaw.D0.covered (214 * 256 + lo.val) || exceptional (214 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_215 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (215 * 256 + lo.val) →
    7 + PawNine.rowCount (215 * 256 + lo.val) 1 ≤ PathExchange.crossCount (215 * 256 + lo.val) →
    (FirstPaw.D0.covered (215 * 256 + lo.val) || exceptional (215 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_216 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (216 * 256 + lo.val) →
    7 + PawNine.rowCount (216 * 256 + lo.val) 1 ≤ PathExchange.crossCount (216 * 256 + lo.val) →
    (FirstPaw.D0.covered (216 * 256 + lo.val) || exceptional (216 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_217 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (217 * 256 + lo.val) →
    7 + PawNine.rowCount (217 * 256 + lo.val) 1 ≤ PathExchange.crossCount (217 * 256 + lo.val) →
    (FirstPaw.D0.covered (217 * 256 + lo.val) || exceptional (217 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_218 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (218 * 256 + lo.val) →
    7 + PawNine.rowCount (218 * 256 + lo.val) 1 ≤ PathExchange.crossCount (218 * 256 + lo.val) →
    (FirstPaw.D0.covered (218 * 256 + lo.val) || exceptional (218 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_219 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (219 * 256 + lo.val) →
    7 + PawNine.rowCount (219 * 256 + lo.val) 1 ≤ PathExchange.crossCount (219 * 256 + lo.val) →
    (FirstPaw.D0.covered (219 * 256 + lo.val) || exceptional (219 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_220 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (220 * 256 + lo.val) →
    7 + PawNine.rowCount (220 * 256 + lo.val) 1 ≤ PathExchange.crossCount (220 * 256 + lo.val) →
    (FirstPaw.D0.covered (220 * 256 + lo.val) || exceptional (220 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_221 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (221 * 256 + lo.val) →
    7 + PawNine.rowCount (221 * 256 + lo.val) 1 ≤ PathExchange.crossCount (221 * 256 + lo.val) →
    (FirstPaw.D0.covered (221 * 256 + lo.val) || exceptional (221 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_222 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (222 * 256 + lo.val) →
    7 + PawNine.rowCount (222 * 256 + lo.val) 1 ≤ PathExchange.crossCount (222 * 256 + lo.val) →
    (FirstPaw.D0.covered (222 * 256 + lo.val) || exceptional (222 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_223 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (223 * 256 + lo.val) →
    7 + PawNine.rowCount (223 * 256 + lo.val) 1 ≤ PathExchange.crossCount (223 * 256 + lo.val) →
    (FirstPaw.D0.covered (223 * 256 + lo.val) || exceptional (223 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_224 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (224 * 256 + lo.val) →
    7 + PawNine.rowCount (224 * 256 + lo.val) 1 ≤ PathExchange.crossCount (224 * 256 + lo.val) →
    (FirstPaw.D0.covered (224 * 256 + lo.val) || exceptional (224 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_225 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (225 * 256 + lo.val) →
    7 + PawNine.rowCount (225 * 256 + lo.val) 1 ≤ PathExchange.crossCount (225 * 256 + lo.val) →
    (FirstPaw.D0.covered (225 * 256 + lo.val) || exceptional (225 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_226 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (226 * 256 + lo.val) →
    7 + PawNine.rowCount (226 * 256 + lo.val) 1 ≤ PathExchange.crossCount (226 * 256 + lo.val) →
    (FirstPaw.D0.covered (226 * 256 + lo.val) || exceptional (226 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_227 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (227 * 256 + lo.val) →
    7 + PawNine.rowCount (227 * 256 + lo.val) 1 ≤ PathExchange.crossCount (227 * 256 + lo.val) →
    (FirstPaw.D0.covered (227 * 256 + lo.val) || exceptional (227 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_228 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (228 * 256 + lo.val) →
    7 + PawNine.rowCount (228 * 256 + lo.val) 1 ≤ PathExchange.crossCount (228 * 256 + lo.val) →
    (FirstPaw.D0.covered (228 * 256 + lo.val) || exceptional (228 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_229 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (229 * 256 + lo.val) →
    7 + PawNine.rowCount (229 * 256 + lo.val) 1 ≤ PathExchange.crossCount (229 * 256 + lo.val) →
    (FirstPaw.D0.covered (229 * 256 + lo.val) || exceptional (229 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_230 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (230 * 256 + lo.val) →
    7 + PawNine.rowCount (230 * 256 + lo.val) 1 ≤ PathExchange.crossCount (230 * 256 + lo.val) →
    (FirstPaw.D0.covered (230 * 256 + lo.val) || exceptional (230 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_231 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (231 * 256 + lo.val) →
    7 + PawNine.rowCount (231 * 256 + lo.val) 1 ≤ PathExchange.crossCount (231 * 256 + lo.val) →
    (FirstPaw.D0.covered (231 * 256 + lo.val) || exceptional (231 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_232 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (232 * 256 + lo.val) →
    7 + PawNine.rowCount (232 * 256 + lo.val) 1 ≤ PathExchange.crossCount (232 * 256 + lo.val) →
    (FirstPaw.D0.covered (232 * 256 + lo.val) || exceptional (232 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_233 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (233 * 256 + lo.val) →
    7 + PawNine.rowCount (233 * 256 + lo.val) 1 ≤ PathExchange.crossCount (233 * 256 + lo.val) →
    (FirstPaw.D0.covered (233 * 256 + lo.val) || exceptional (233 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_234 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (234 * 256 + lo.val) →
    7 + PawNine.rowCount (234 * 256 + lo.val) 1 ≤ PathExchange.crossCount (234 * 256 + lo.val) →
    (FirstPaw.D0.covered (234 * 256 + lo.val) || exceptional (234 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_235 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (235 * 256 + lo.val) →
    7 + PawNine.rowCount (235 * 256 + lo.val) 1 ≤ PathExchange.crossCount (235 * 256 + lo.val) →
    (FirstPaw.D0.covered (235 * 256 + lo.val) || exceptional (235 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_236 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (236 * 256 + lo.val) →
    7 + PawNine.rowCount (236 * 256 + lo.val) 1 ≤ PathExchange.crossCount (236 * 256 + lo.val) →
    (FirstPaw.D0.covered (236 * 256 + lo.val) || exceptional (236 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_237 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (237 * 256 + lo.val) →
    7 + PawNine.rowCount (237 * 256 + lo.val) 1 ≤ PathExchange.crossCount (237 * 256 + lo.val) →
    (FirstPaw.D0.covered (237 * 256 + lo.val) || exceptional (237 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_238 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (238 * 256 + lo.val) →
    7 + PawNine.rowCount (238 * 256 + lo.val) 1 ≤ PathExchange.crossCount (238 * 256 + lo.val) →
    (FirstPaw.D0.covered (238 * 256 + lo.val) || exceptional (238 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_239 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (239 * 256 + lo.val) →
    7 + PawNine.rowCount (239 * 256 + lo.val) 1 ≤ PathExchange.crossCount (239 * 256 + lo.val) →
    (FirstPaw.D0.covered (239 * 256 + lo.val) || exceptional (239 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_240 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (240 * 256 + lo.val) →
    7 + PawNine.rowCount (240 * 256 + lo.val) 1 ≤ PathExchange.crossCount (240 * 256 + lo.val) →
    (FirstPaw.D0.covered (240 * 256 + lo.val) || exceptional (240 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_241 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (241 * 256 + lo.val) →
    7 + PawNine.rowCount (241 * 256 + lo.val) 1 ≤ PathExchange.crossCount (241 * 256 + lo.val) →
    (FirstPaw.D0.covered (241 * 256 + lo.val) || exceptional (241 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_242 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (242 * 256 + lo.val) →
    7 + PawNine.rowCount (242 * 256 + lo.val) 1 ≤ PathExchange.crossCount (242 * 256 + lo.val) →
    (FirstPaw.D0.covered (242 * 256 + lo.val) || exceptional (242 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_243 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (243 * 256 + lo.val) →
    7 + PawNine.rowCount (243 * 256 + lo.val) 1 ≤ PathExchange.crossCount (243 * 256 + lo.val) →
    (FirstPaw.D0.covered (243 * 256 + lo.val) || exceptional (243 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_244 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (244 * 256 + lo.val) →
    7 + PawNine.rowCount (244 * 256 + lo.val) 1 ≤ PathExchange.crossCount (244 * 256 + lo.val) →
    (FirstPaw.D0.covered (244 * 256 + lo.val) || exceptional (244 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_245 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (245 * 256 + lo.val) →
    7 + PawNine.rowCount (245 * 256 + lo.val) 1 ≤ PathExchange.crossCount (245 * 256 + lo.val) →
    (FirstPaw.D0.covered (245 * 256 + lo.val) || exceptional (245 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_246 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (246 * 256 + lo.val) →
    7 + PawNine.rowCount (246 * 256 + lo.val) 1 ≤ PathExchange.crossCount (246 * 256 + lo.val) →
    (FirstPaw.D0.covered (246 * 256 + lo.val) || exceptional (246 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_247 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (247 * 256 + lo.val) →
    7 + PawNine.rowCount (247 * 256 + lo.val) 1 ≤ PathExchange.crossCount (247 * 256 + lo.val) →
    (FirstPaw.D0.covered (247 * 256 + lo.val) || exceptional (247 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_248 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (248 * 256 + lo.val) →
    7 + PawNine.rowCount (248 * 256 + lo.val) 1 ≤ PathExchange.crossCount (248 * 256 + lo.val) →
    (FirstPaw.D0.covered (248 * 256 + lo.val) || exceptional (248 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_249 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (249 * 256 + lo.val) →
    7 + PawNine.rowCount (249 * 256 + lo.val) 1 ≤ PathExchange.crossCount (249 * 256 + lo.val) →
    (FirstPaw.D0.covered (249 * 256 + lo.val) || exceptional (249 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_250 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (250 * 256 + lo.val) →
    7 + PawNine.rowCount (250 * 256 + lo.val) 1 ≤ PathExchange.crossCount (250 * 256 + lo.val) →
    (FirstPaw.D0.covered (250 * 256 + lo.val) || exceptional (250 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_251 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (251 * 256 + lo.val) →
    7 + PawNine.rowCount (251 * 256 + lo.val) 1 ≤ PathExchange.crossCount (251 * 256 + lo.val) →
    (FirstPaw.D0.covered (251 * 256 + lo.val) || exceptional (251 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_252 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (252 * 256 + lo.val) →
    7 + PawNine.rowCount (252 * 256 + lo.val) 1 ≤ PathExchange.crossCount (252 * 256 + lo.val) →
    (FirstPaw.D0.covered (252 * 256 + lo.val) || exceptional (252 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_253 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (253 * 256 + lo.val) →
    7 + PawNine.rowCount (253 * 256 + lo.val) 1 ≤ PathExchange.crossCount (253 * 256 + lo.val) →
    (FirstPaw.D0.covered (253 * 256 + lo.val) || exceptional (253 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_254 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (254 * 256 + lo.val) →
    7 + PawNine.rowCount (254 * 256 + lo.val) 1 ≤ PathExchange.crossCount (254 * 256 + lo.val) →
    (FirstPaw.D0.covered (254 * 256 + lo.val) || exceptional (254 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_255 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (255 * 256 + lo.val) →
    7 + PawNine.rowCount (255 * 256 + lo.val) 1 ≤ PathExchange.crossCount (255 * 256 + lo.val) →
    (FirstPaw.D0.covered (255 * 256 + lo.val) || exceptional (255 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_rows (hi lo : Fin 256)
    (hl : 1 ≤ DenseOutside.terminalCount (hi.val * 256 + lo.val))
    (hh : 7 + PawNine.rowCount (hi.val * 256 + lo.val) 1 ≤
      PathExchange.crossCount (hi.val * 256 + lo.val)) :
    (FirstPaw.D0.covered (hi.val * 256 + lo.val) ||
      exceptional (hi.val * 256 + lo.val)) = true := by
  fin_cases hi
  · exact coverage_0 lo hl hh
  · exact coverage_1 lo hl hh
  · exact coverage_2 lo hl hh
  · exact coverage_3 lo hl hh
  · exact coverage_4 lo hl hh
  · exact coverage_5 lo hl hh
  · exact coverage_6 lo hl hh
  · exact coverage_7 lo hl hh
  · exact coverage_8 lo hl hh
  · exact coverage_9 lo hl hh
  · exact coverage_10 lo hl hh
  · exact coverage_11 lo hl hh
  · exact coverage_12 lo hl hh
  · exact coverage_13 lo hl hh
  · exact coverage_14 lo hl hh
  · exact coverage_15 lo hl hh
  · exact coverage_16 lo hl hh
  · exact coverage_17 lo hl hh
  · exact coverage_18 lo hl hh
  · exact coverage_19 lo hl hh
  · exact coverage_20 lo hl hh
  · exact coverage_21 lo hl hh
  · exact coverage_22 lo hl hh
  · exact coverage_23 lo hl hh
  · exact coverage_24 lo hl hh
  · exact coverage_25 lo hl hh
  · exact coverage_26 lo hl hh
  · exact coverage_27 lo hl hh
  · exact coverage_28 lo hl hh
  · exact coverage_29 lo hl hh
  · exact coverage_30 lo hl hh
  · exact coverage_31 lo hl hh
  · exact coverage_32 lo hl hh
  · exact coverage_33 lo hl hh
  · exact coverage_34 lo hl hh
  · exact coverage_35 lo hl hh
  · exact coverage_36 lo hl hh
  · exact coverage_37 lo hl hh
  · exact coverage_38 lo hl hh
  · exact coverage_39 lo hl hh
  · exact coverage_40 lo hl hh
  · exact coverage_41 lo hl hh
  · exact coverage_42 lo hl hh
  · exact coverage_43 lo hl hh
  · exact coverage_44 lo hl hh
  · exact coverage_45 lo hl hh
  · exact coverage_46 lo hl hh
  · exact coverage_47 lo hl hh
  · exact coverage_48 lo hl hh
  · exact coverage_49 lo hl hh
  · exact coverage_50 lo hl hh
  · exact coverage_51 lo hl hh
  · exact coverage_52 lo hl hh
  · exact coverage_53 lo hl hh
  · exact coverage_54 lo hl hh
  · exact coverage_55 lo hl hh
  · exact coverage_56 lo hl hh
  · exact coverage_57 lo hl hh
  · exact coverage_58 lo hl hh
  · exact coverage_59 lo hl hh
  · exact coverage_60 lo hl hh
  · exact coverage_61 lo hl hh
  · exact coverage_62 lo hl hh
  · exact coverage_63 lo hl hh
  · exact coverage_64 lo hl hh
  · exact coverage_65 lo hl hh
  · exact coverage_66 lo hl hh
  · exact coverage_67 lo hl hh
  · exact coverage_68 lo hl hh
  · exact coverage_69 lo hl hh
  · exact coverage_70 lo hl hh
  · exact coverage_71 lo hl hh
  · exact coverage_72 lo hl hh
  · exact coverage_73 lo hl hh
  · exact coverage_74 lo hl hh
  · exact coverage_75 lo hl hh
  · exact coverage_76 lo hl hh
  · exact coverage_77 lo hl hh
  · exact coverage_78 lo hl hh
  · exact coverage_79 lo hl hh
  · exact coverage_80 lo hl hh
  · exact coverage_81 lo hl hh
  · exact coverage_82 lo hl hh
  · exact coverage_83 lo hl hh
  · exact coverage_84 lo hl hh
  · exact coverage_85 lo hl hh
  · exact coverage_86 lo hl hh
  · exact coverage_87 lo hl hh
  · exact coverage_88 lo hl hh
  · exact coverage_89 lo hl hh
  · exact coverage_90 lo hl hh
  · exact coverage_91 lo hl hh
  · exact coverage_92 lo hl hh
  · exact coverage_93 lo hl hh
  · exact coverage_94 lo hl hh
  · exact coverage_95 lo hl hh
  · exact coverage_96 lo hl hh
  · exact coverage_97 lo hl hh
  · exact coverage_98 lo hl hh
  · exact coverage_99 lo hl hh
  · exact coverage_100 lo hl hh
  · exact coverage_101 lo hl hh
  · exact coverage_102 lo hl hh
  · exact coverage_103 lo hl hh
  · exact coverage_104 lo hl hh
  · exact coverage_105 lo hl hh
  · exact coverage_106 lo hl hh
  · exact coverage_107 lo hl hh
  · exact coverage_108 lo hl hh
  · exact coverage_109 lo hl hh
  · exact coverage_110 lo hl hh
  · exact coverage_111 lo hl hh
  · exact coverage_112 lo hl hh
  · exact coverage_113 lo hl hh
  · exact coverage_114 lo hl hh
  · exact coverage_115 lo hl hh
  · exact coverage_116 lo hl hh
  · exact coverage_117 lo hl hh
  · exact coverage_118 lo hl hh
  · exact coverage_119 lo hl hh
  · exact coverage_120 lo hl hh
  · exact coverage_121 lo hl hh
  · exact coverage_122 lo hl hh
  · exact coverage_123 lo hl hh
  · exact coverage_124 lo hl hh
  · exact coverage_125 lo hl hh
  · exact coverage_126 lo hl hh
  · exact coverage_127 lo hl hh
  · exact coverage_128 lo hl hh
  · exact coverage_129 lo hl hh
  · exact coverage_130 lo hl hh
  · exact coverage_131 lo hl hh
  · exact coverage_132 lo hl hh
  · exact coverage_133 lo hl hh
  · exact coverage_134 lo hl hh
  · exact coverage_135 lo hl hh
  · exact coverage_136 lo hl hh
  · exact coverage_137 lo hl hh
  · exact coverage_138 lo hl hh
  · exact coverage_139 lo hl hh
  · exact coverage_140 lo hl hh
  · exact coverage_141 lo hl hh
  · exact coverage_142 lo hl hh
  · exact coverage_143 lo hl hh
  · exact coverage_144 lo hl hh
  · exact coverage_145 lo hl hh
  · exact coverage_146 lo hl hh
  · exact coverage_147 lo hl hh
  · exact coverage_148 lo hl hh
  · exact coverage_149 lo hl hh
  · exact coverage_150 lo hl hh
  · exact coverage_151 lo hl hh
  · exact coverage_152 lo hl hh
  · exact coverage_153 lo hl hh
  · exact coverage_154 lo hl hh
  · exact coverage_155 lo hl hh
  · exact coverage_156 lo hl hh
  · exact coverage_157 lo hl hh
  · exact coverage_158 lo hl hh
  · exact coverage_159 lo hl hh
  · exact coverage_160 lo hl hh
  · exact coverage_161 lo hl hh
  · exact coverage_162 lo hl hh
  · exact coverage_163 lo hl hh
  · exact coverage_164 lo hl hh
  · exact coverage_165 lo hl hh
  · exact coverage_166 lo hl hh
  · exact coverage_167 lo hl hh
  · exact coverage_168 lo hl hh
  · exact coverage_169 lo hl hh
  · exact coverage_170 lo hl hh
  · exact coverage_171 lo hl hh
  · exact coverage_172 lo hl hh
  · exact coverage_173 lo hl hh
  · exact coverage_174 lo hl hh
  · exact coverage_175 lo hl hh
  · exact coverage_176 lo hl hh
  · exact coverage_177 lo hl hh
  · exact coverage_178 lo hl hh
  · exact coverage_179 lo hl hh
  · exact coverage_180 lo hl hh
  · exact coverage_181 lo hl hh
  · exact coverage_182 lo hl hh
  · exact coverage_183 lo hl hh
  · exact coverage_184 lo hl hh
  · exact coverage_185 lo hl hh
  · exact coverage_186 lo hl hh
  · exact coverage_187 lo hl hh
  · exact coverage_188 lo hl hh
  · exact coverage_189 lo hl hh
  · exact coverage_190 lo hl hh
  · exact coverage_191 lo hl hh
  · exact coverage_192 lo hl hh
  · exact coverage_193 lo hl hh
  · exact coverage_194 lo hl hh
  · exact coverage_195 lo hl hh
  · exact coverage_196 lo hl hh
  · exact coverage_197 lo hl hh
  · exact coverage_198 lo hl hh
  · exact coverage_199 lo hl hh
  · exact coverage_200 lo hl hh
  · exact coverage_201 lo hl hh
  · exact coverage_202 lo hl hh
  · exact coverage_203 lo hl hh
  · exact coverage_204 lo hl hh
  · exact coverage_205 lo hl hh
  · exact coverage_206 lo hl hh
  · exact coverage_207 lo hl hh
  · exact coverage_208 lo hl hh
  · exact coverage_209 lo hl hh
  · exact coverage_210 lo hl hh
  · exact coverage_211 lo hl hh
  · exact coverage_212 lo hl hh
  · exact coverage_213 lo hl hh
  · exact coverage_214 lo hl hh
  · exact coverage_215 lo hl hh
  · exact coverage_216 lo hl hh
  · exact coverage_217 lo hl hh
  · exact coverage_218 lo hl hh
  · exact coverage_219 lo hl hh
  · exact coverage_220 lo hl hh
  · exact coverage_221 lo hl hh
  · exact coverage_222 lo hl hh
  · exact coverage_223 lo hl hh
  · exact coverage_224 lo hl hh
  · exact coverage_225 lo hl hh
  · exact coverage_226 lo hl hh
  · exact coverage_227 lo hl hh
  · exact coverage_228 lo hl hh
  · exact coverage_229 lo hl hh
  · exact coverage_230 lo hl hh
  · exact coverage_231 lo hl hh
  · exact coverage_232 lo hl hh
  · exact coverage_233 lo hl hh
  · exact coverage_234 lo hl hh
  · exact coverage_235 lo hl hh
  · exact coverage_236 lo hl hh
  · exact coverage_237 lo hl hh
  · exact coverage_238 lo hl hh
  · exact coverage_239 lo hl hh
  · exact coverage_240 lo hl hh
  · exact coverage_241 lo hl hh
  · exact coverage_242 lo hl hh
  · exact coverage_243 lo hl hh
  · exact coverage_244 lo hl hh
  · exact coverage_245 lo hl hh
  · exact coverage_246 lo hl hh
  · exact coverage_247 lo hl hh
  · exact coverage_248 lo hl hh
  · exact coverage_249 lo hl hh
  · exact coverage_250 lo hl hh
  · exact coverage_251 lo hl hh
  · exact coverage_252 lo hl hh
  · exact coverage_253 lo hl hh
  · exact coverage_254 lo hl hh
  · exact coverage_255 lo hl hh

theorem coverage (m : Fin 65536) (hl : 1 ≤ DenseOutside.terminalCount m.val)
    (hh : 7 + PawNine.rowCount m.val 1 ≤ PathExchange.crossCount m.val) :
    (FirstPaw.D0.covered m.val || exceptional m.val) = true := by
  let hi : Fin 256 := ⟨m.val / 256, by omega⟩
  let lo : Fin 256 := ⟨m.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : hi.val * 256 + lo.val = m.val := by dsimp [hi, lo]; omega
  rw [← he] at hl hh ⊢
  exact coverage_rows hi lo hl hh

end Erdos577.WeightedPaw.D0
