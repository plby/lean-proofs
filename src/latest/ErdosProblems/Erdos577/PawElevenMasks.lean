import ErdosProblems.Erdos577.PawElevenModel

/-! Kernel-checked factor coverage or exact exceptional rows for Wang 3.4(a). -/

namespace Erdos577.PawEleven

def masks : List ℕ := [
  282, 549, 1098, 2181, 4122, 4362, 4680, 4740, 6180, 6210,
  6657, 8229, 8520, 8580, 8709, 9240, 9345, 9474, 16458, 16920,
  17025, 17418, 18450, 18465, 18948, 20994, 22536, 32901, 33060, 33090,
  33810, 33825, 34056, 34821, 41217, 41988]

def covered (m : ℕ) : Bool := masks.any fun w ↦ m &&& w == w

private theorem coverage_0 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (0 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (0 * 256 + lo.val) →
    (covered (0 * 256 + lo.val) || exceptional (0 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_1 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (1 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (1 * 256 + lo.val) →
    (covered (1 * 256 + lo.val) || exceptional (1 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_2 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (2 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (2 * 256 + lo.val) →
    (covered (2 * 256 + lo.val) || exceptional (2 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_3 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (3 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (3 * 256 + lo.val) →
    (covered (3 * 256 + lo.val) || exceptional (3 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_4 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (4 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (4 * 256 + lo.val) →
    (covered (4 * 256 + lo.val) || exceptional (4 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_5 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (5 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (5 * 256 + lo.val) →
    (covered (5 * 256 + lo.val) || exceptional (5 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_6 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (6 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (6 * 256 + lo.val) →
    (covered (6 * 256 + lo.val) || exceptional (6 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_7 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (7 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (7 * 256 + lo.val) →
    (covered (7 * 256 + lo.val) || exceptional (7 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_8 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (8 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (8 * 256 + lo.val) →
    (covered (8 * 256 + lo.val) || exceptional (8 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_9 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (9 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (9 * 256 + lo.val) →
    (covered (9 * 256 + lo.val) || exceptional (9 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_10 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (10 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (10 * 256 + lo.val) →
    (covered (10 * 256 + lo.val) || exceptional (10 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_11 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (11 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (11 * 256 + lo.val) →
    (covered (11 * 256 + lo.val) || exceptional (11 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_12 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (12 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (12 * 256 + lo.val) →
    (covered (12 * 256 + lo.val) || exceptional (12 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_13 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (13 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (13 * 256 + lo.val) →
    (covered (13 * 256 + lo.val) || exceptional (13 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_14 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (14 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (14 * 256 + lo.val) →
    (covered (14 * 256 + lo.val) || exceptional (14 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_15 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (15 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (15 * 256 + lo.val) →
    (covered (15 * 256 + lo.val) || exceptional (15 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_16 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (16 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (16 * 256 + lo.val) →
    (covered (16 * 256 + lo.val) || exceptional (16 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_17 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (17 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (17 * 256 + lo.val) →
    (covered (17 * 256 + lo.val) || exceptional (17 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_18 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (18 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (18 * 256 + lo.val) →
    (covered (18 * 256 + lo.val) || exceptional (18 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_19 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (19 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (19 * 256 + lo.val) →
    (covered (19 * 256 + lo.val) || exceptional (19 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_20 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (20 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (20 * 256 + lo.val) →
    (covered (20 * 256 + lo.val) || exceptional (20 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_21 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (21 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (21 * 256 + lo.val) →
    (covered (21 * 256 + lo.val) || exceptional (21 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_22 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (22 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (22 * 256 + lo.val) →
    (covered (22 * 256 + lo.val) || exceptional (22 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_23 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (23 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (23 * 256 + lo.val) →
    (covered (23 * 256 + lo.val) || exceptional (23 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_24 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (24 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (24 * 256 + lo.val) →
    (covered (24 * 256 + lo.val) || exceptional (24 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_25 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (25 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (25 * 256 + lo.val) →
    (covered (25 * 256 + lo.val) || exceptional (25 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_26 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (26 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (26 * 256 + lo.val) →
    (covered (26 * 256 + lo.val) || exceptional (26 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_27 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (27 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (27 * 256 + lo.val) →
    (covered (27 * 256 + lo.val) || exceptional (27 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_28 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (28 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (28 * 256 + lo.val) →
    (covered (28 * 256 + lo.val) || exceptional (28 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_29 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (29 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (29 * 256 + lo.val) →
    (covered (29 * 256 + lo.val) || exceptional (29 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_30 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (30 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (30 * 256 + lo.val) →
    (covered (30 * 256 + lo.val) || exceptional (30 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_31 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (31 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (31 * 256 + lo.val) →
    (covered (31 * 256 + lo.val) || exceptional (31 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_32 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (32 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (32 * 256 + lo.val) →
    (covered (32 * 256 + lo.val) || exceptional (32 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_33 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (33 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (33 * 256 + lo.val) →
    (covered (33 * 256 + lo.val) || exceptional (33 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_34 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (34 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (34 * 256 + lo.val) →
    (covered (34 * 256 + lo.val) || exceptional (34 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_35 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (35 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (35 * 256 + lo.val) →
    (covered (35 * 256 + lo.val) || exceptional (35 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_36 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (36 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (36 * 256 + lo.val) →
    (covered (36 * 256 + lo.val) || exceptional (36 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_37 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (37 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (37 * 256 + lo.val) →
    (covered (37 * 256 + lo.val) || exceptional (37 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_38 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (38 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (38 * 256 + lo.val) →
    (covered (38 * 256 + lo.val) || exceptional (38 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_39 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (39 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (39 * 256 + lo.val) →
    (covered (39 * 256 + lo.val) || exceptional (39 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_40 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (40 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (40 * 256 + lo.val) →
    (covered (40 * 256 + lo.val) || exceptional (40 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_41 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (41 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (41 * 256 + lo.val) →
    (covered (41 * 256 + lo.val) || exceptional (41 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_42 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (42 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (42 * 256 + lo.val) →
    (covered (42 * 256 + lo.val) || exceptional (42 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_43 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (43 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (43 * 256 + lo.val) →
    (covered (43 * 256 + lo.val) || exceptional (43 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_44 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (44 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (44 * 256 + lo.val) →
    (covered (44 * 256 + lo.val) || exceptional (44 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_45 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (45 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (45 * 256 + lo.val) →
    (covered (45 * 256 + lo.val) || exceptional (45 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_46 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (46 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (46 * 256 + lo.val) →
    (covered (46 * 256 + lo.val) || exceptional (46 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_47 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (47 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (47 * 256 + lo.val) →
    (covered (47 * 256 + lo.val) || exceptional (47 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_48 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (48 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (48 * 256 + lo.val) →
    (covered (48 * 256 + lo.val) || exceptional (48 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_49 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (49 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (49 * 256 + lo.val) →
    (covered (49 * 256 + lo.val) || exceptional (49 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_50 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (50 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (50 * 256 + lo.val) →
    (covered (50 * 256 + lo.val) || exceptional (50 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_51 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (51 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (51 * 256 + lo.val) →
    (covered (51 * 256 + lo.val) || exceptional (51 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_52 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (52 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (52 * 256 + lo.val) →
    (covered (52 * 256 + lo.val) || exceptional (52 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_53 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (53 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (53 * 256 + lo.val) →
    (covered (53 * 256 + lo.val) || exceptional (53 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_54 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (54 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (54 * 256 + lo.val) →
    (covered (54 * 256 + lo.val) || exceptional (54 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_55 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (55 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (55 * 256 + lo.val) →
    (covered (55 * 256 + lo.val) || exceptional (55 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_56 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (56 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (56 * 256 + lo.val) →
    (covered (56 * 256 + lo.val) || exceptional (56 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_57 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (57 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (57 * 256 + lo.val) →
    (covered (57 * 256 + lo.val) || exceptional (57 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_58 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (58 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (58 * 256 + lo.val) →
    (covered (58 * 256 + lo.val) || exceptional (58 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_59 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (59 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (59 * 256 + lo.val) →
    (covered (59 * 256 + lo.val) || exceptional (59 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_60 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (60 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (60 * 256 + lo.val) →
    (covered (60 * 256 + lo.val) || exceptional (60 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_61 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (61 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (61 * 256 + lo.val) →
    (covered (61 * 256 + lo.val) || exceptional (61 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_62 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (62 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (62 * 256 + lo.val) →
    (covered (62 * 256 + lo.val) || exceptional (62 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_63 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (63 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (63 * 256 + lo.val) →
    (covered (63 * 256 + lo.val) || exceptional (63 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_64 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (64 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (64 * 256 + lo.val) →
    (covered (64 * 256 + lo.val) || exceptional (64 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_65 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (65 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (65 * 256 + lo.val) →
    (covered (65 * 256 + lo.val) || exceptional (65 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_66 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (66 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (66 * 256 + lo.val) →
    (covered (66 * 256 + lo.val) || exceptional (66 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_67 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (67 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (67 * 256 + lo.val) →
    (covered (67 * 256 + lo.val) || exceptional (67 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_68 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (68 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (68 * 256 + lo.val) →
    (covered (68 * 256 + lo.val) || exceptional (68 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_69 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (69 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (69 * 256 + lo.val) →
    (covered (69 * 256 + lo.val) || exceptional (69 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_70 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (70 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (70 * 256 + lo.val) →
    (covered (70 * 256 + lo.val) || exceptional (70 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_71 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (71 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (71 * 256 + lo.val) →
    (covered (71 * 256 + lo.val) || exceptional (71 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_72 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (72 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (72 * 256 + lo.val) →
    (covered (72 * 256 + lo.val) || exceptional (72 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_73 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (73 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (73 * 256 + lo.val) →
    (covered (73 * 256 + lo.val) || exceptional (73 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_74 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (74 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (74 * 256 + lo.val) →
    (covered (74 * 256 + lo.val) || exceptional (74 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_75 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (75 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (75 * 256 + lo.val) →
    (covered (75 * 256 + lo.val) || exceptional (75 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_76 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (76 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (76 * 256 + lo.val) →
    (covered (76 * 256 + lo.val) || exceptional (76 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_77 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (77 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (77 * 256 + lo.val) →
    (covered (77 * 256 + lo.val) || exceptional (77 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_78 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (78 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (78 * 256 + lo.val) →
    (covered (78 * 256 + lo.val) || exceptional (78 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_79 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (79 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (79 * 256 + lo.val) →
    (covered (79 * 256 + lo.val) || exceptional (79 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_80 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (80 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (80 * 256 + lo.val) →
    (covered (80 * 256 + lo.val) || exceptional (80 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_81 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (81 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (81 * 256 + lo.val) →
    (covered (81 * 256 + lo.val) || exceptional (81 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_82 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (82 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (82 * 256 + lo.val) →
    (covered (82 * 256 + lo.val) || exceptional (82 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_83 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (83 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (83 * 256 + lo.val) →
    (covered (83 * 256 + lo.val) || exceptional (83 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_84 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (84 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (84 * 256 + lo.val) →
    (covered (84 * 256 + lo.val) || exceptional (84 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_85 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (85 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (85 * 256 + lo.val) →
    (covered (85 * 256 + lo.val) || exceptional (85 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_86 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (86 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (86 * 256 + lo.val) →
    (covered (86 * 256 + lo.val) || exceptional (86 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_87 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (87 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (87 * 256 + lo.val) →
    (covered (87 * 256 + lo.val) || exceptional (87 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_88 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (88 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (88 * 256 + lo.val) →
    (covered (88 * 256 + lo.val) || exceptional (88 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_89 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (89 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (89 * 256 + lo.val) →
    (covered (89 * 256 + lo.val) || exceptional (89 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_90 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (90 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (90 * 256 + lo.val) →
    (covered (90 * 256 + lo.val) || exceptional (90 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_91 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (91 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (91 * 256 + lo.val) →
    (covered (91 * 256 + lo.val) || exceptional (91 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_92 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (92 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (92 * 256 + lo.val) →
    (covered (92 * 256 + lo.val) || exceptional (92 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_93 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (93 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (93 * 256 + lo.val) →
    (covered (93 * 256 + lo.val) || exceptional (93 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_94 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (94 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (94 * 256 + lo.val) →
    (covered (94 * 256 + lo.val) || exceptional (94 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_95 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (95 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (95 * 256 + lo.val) →
    (covered (95 * 256 + lo.val) || exceptional (95 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_96 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (96 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (96 * 256 + lo.val) →
    (covered (96 * 256 + lo.val) || exceptional (96 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_97 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (97 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (97 * 256 + lo.val) →
    (covered (97 * 256 + lo.val) || exceptional (97 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_98 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (98 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (98 * 256 + lo.val) →
    (covered (98 * 256 + lo.val) || exceptional (98 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_99 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (99 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (99 * 256 + lo.val) →
    (covered (99 * 256 + lo.val) || exceptional (99 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_100 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (100 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (100 * 256 + lo.val) →
    (covered (100 * 256 + lo.val) || exceptional (100 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_101 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (101 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (101 * 256 + lo.val) →
    (covered (101 * 256 + lo.val) || exceptional (101 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_102 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (102 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (102 * 256 + lo.val) →
    (covered (102 * 256 + lo.val) || exceptional (102 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_103 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (103 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (103 * 256 + lo.val) →
    (covered (103 * 256 + lo.val) || exceptional (103 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_104 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (104 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (104 * 256 + lo.val) →
    (covered (104 * 256 + lo.val) || exceptional (104 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_105 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (105 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (105 * 256 + lo.val) →
    (covered (105 * 256 + lo.val) || exceptional (105 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_106 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (106 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (106 * 256 + lo.val) →
    (covered (106 * 256 + lo.val) || exceptional (106 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_107 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (107 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (107 * 256 + lo.val) →
    (covered (107 * 256 + lo.val) || exceptional (107 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_108 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (108 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (108 * 256 + lo.val) →
    (covered (108 * 256 + lo.val) || exceptional (108 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_109 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (109 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (109 * 256 + lo.val) →
    (covered (109 * 256 + lo.val) || exceptional (109 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_110 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (110 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (110 * 256 + lo.val) →
    (covered (110 * 256 + lo.val) || exceptional (110 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_111 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (111 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (111 * 256 + lo.val) →
    (covered (111 * 256 + lo.val) || exceptional (111 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_112 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (112 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (112 * 256 + lo.val) →
    (covered (112 * 256 + lo.val) || exceptional (112 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_113 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (113 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (113 * 256 + lo.val) →
    (covered (113 * 256 + lo.val) || exceptional (113 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_114 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (114 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (114 * 256 + lo.val) →
    (covered (114 * 256 + lo.val) || exceptional (114 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_115 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (115 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (115 * 256 + lo.val) →
    (covered (115 * 256 + lo.val) || exceptional (115 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_116 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (116 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (116 * 256 + lo.val) →
    (covered (116 * 256 + lo.val) || exceptional (116 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_117 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (117 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (117 * 256 + lo.val) →
    (covered (117 * 256 + lo.val) || exceptional (117 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_118 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (118 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (118 * 256 + lo.val) →
    (covered (118 * 256 + lo.val) || exceptional (118 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_119 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (119 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (119 * 256 + lo.val) →
    (covered (119 * 256 + lo.val) || exceptional (119 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_120 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (120 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (120 * 256 + lo.val) →
    (covered (120 * 256 + lo.val) || exceptional (120 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_121 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (121 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (121 * 256 + lo.val) →
    (covered (121 * 256 + lo.val) || exceptional (121 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_122 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (122 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (122 * 256 + lo.val) →
    (covered (122 * 256 + lo.val) || exceptional (122 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_123 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (123 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (123 * 256 + lo.val) →
    (covered (123 * 256 + lo.val) || exceptional (123 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_124 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (124 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (124 * 256 + lo.val) →
    (covered (124 * 256 + lo.val) || exceptional (124 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_125 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (125 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (125 * 256 + lo.val) →
    (covered (125 * 256 + lo.val) || exceptional (125 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_126 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (126 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (126 * 256 + lo.val) →
    (covered (126 * 256 + lo.val) || exceptional (126 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_127 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (127 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (127 * 256 + lo.val) →
    (covered (127 * 256 + lo.val) || exceptional (127 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_128 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (128 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (128 * 256 + lo.val) →
    (covered (128 * 256 + lo.val) || exceptional (128 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_129 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (129 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (129 * 256 + lo.val) →
    (covered (129 * 256 + lo.val) || exceptional (129 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_130 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (130 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (130 * 256 + lo.val) →
    (covered (130 * 256 + lo.val) || exceptional (130 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_131 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (131 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (131 * 256 + lo.val) →
    (covered (131 * 256 + lo.val) || exceptional (131 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_132 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (132 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (132 * 256 + lo.val) →
    (covered (132 * 256 + lo.val) || exceptional (132 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_133 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (133 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (133 * 256 + lo.val) →
    (covered (133 * 256 + lo.val) || exceptional (133 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_134 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (134 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (134 * 256 + lo.val) →
    (covered (134 * 256 + lo.val) || exceptional (134 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_135 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (135 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (135 * 256 + lo.val) →
    (covered (135 * 256 + lo.val) || exceptional (135 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_136 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (136 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (136 * 256 + lo.val) →
    (covered (136 * 256 + lo.val) || exceptional (136 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_137 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (137 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (137 * 256 + lo.val) →
    (covered (137 * 256 + lo.val) || exceptional (137 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_138 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (138 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (138 * 256 + lo.val) →
    (covered (138 * 256 + lo.val) || exceptional (138 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_139 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (139 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (139 * 256 + lo.val) →
    (covered (139 * 256 + lo.val) || exceptional (139 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_140 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (140 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (140 * 256 + lo.val) →
    (covered (140 * 256 + lo.val) || exceptional (140 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_141 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (141 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (141 * 256 + lo.val) →
    (covered (141 * 256 + lo.val) || exceptional (141 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_142 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (142 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (142 * 256 + lo.val) →
    (covered (142 * 256 + lo.val) || exceptional (142 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_143 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (143 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (143 * 256 + lo.val) →
    (covered (143 * 256 + lo.val) || exceptional (143 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_144 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (144 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (144 * 256 + lo.val) →
    (covered (144 * 256 + lo.val) || exceptional (144 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_145 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (145 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (145 * 256 + lo.val) →
    (covered (145 * 256 + lo.val) || exceptional (145 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_146 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (146 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (146 * 256 + lo.val) →
    (covered (146 * 256 + lo.val) || exceptional (146 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_147 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (147 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (147 * 256 + lo.val) →
    (covered (147 * 256 + lo.val) || exceptional (147 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_148 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (148 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (148 * 256 + lo.val) →
    (covered (148 * 256 + lo.val) || exceptional (148 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_149 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (149 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (149 * 256 + lo.val) →
    (covered (149 * 256 + lo.val) || exceptional (149 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_150 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (150 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (150 * 256 + lo.val) →
    (covered (150 * 256 + lo.val) || exceptional (150 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_151 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (151 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (151 * 256 + lo.val) →
    (covered (151 * 256 + lo.val) || exceptional (151 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_152 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (152 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (152 * 256 + lo.val) →
    (covered (152 * 256 + lo.val) || exceptional (152 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_153 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (153 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (153 * 256 + lo.val) →
    (covered (153 * 256 + lo.val) || exceptional (153 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_154 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (154 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (154 * 256 + lo.val) →
    (covered (154 * 256 + lo.val) || exceptional (154 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_155 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (155 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (155 * 256 + lo.val) →
    (covered (155 * 256 + lo.val) || exceptional (155 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_156 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (156 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (156 * 256 + lo.val) →
    (covered (156 * 256 + lo.val) || exceptional (156 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_157 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (157 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (157 * 256 + lo.val) →
    (covered (157 * 256 + lo.val) || exceptional (157 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_158 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (158 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (158 * 256 + lo.val) →
    (covered (158 * 256 + lo.val) || exceptional (158 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_159 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (159 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (159 * 256 + lo.val) →
    (covered (159 * 256 + lo.val) || exceptional (159 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_160 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (160 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (160 * 256 + lo.val) →
    (covered (160 * 256 + lo.val) || exceptional (160 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_161 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (161 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (161 * 256 + lo.val) →
    (covered (161 * 256 + lo.val) || exceptional (161 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_162 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (162 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (162 * 256 + lo.val) →
    (covered (162 * 256 + lo.val) || exceptional (162 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_163 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (163 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (163 * 256 + lo.val) →
    (covered (163 * 256 + lo.val) || exceptional (163 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_164 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (164 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (164 * 256 + lo.val) →
    (covered (164 * 256 + lo.val) || exceptional (164 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_165 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (165 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (165 * 256 + lo.val) →
    (covered (165 * 256 + lo.val) || exceptional (165 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_166 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (166 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (166 * 256 + lo.val) →
    (covered (166 * 256 + lo.val) || exceptional (166 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_167 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (167 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (167 * 256 + lo.val) →
    (covered (167 * 256 + lo.val) || exceptional (167 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_168 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (168 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (168 * 256 + lo.val) →
    (covered (168 * 256 + lo.val) || exceptional (168 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_169 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (169 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (169 * 256 + lo.val) →
    (covered (169 * 256 + lo.val) || exceptional (169 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_170 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (170 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (170 * 256 + lo.val) →
    (covered (170 * 256 + lo.val) || exceptional (170 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_171 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (171 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (171 * 256 + lo.val) →
    (covered (171 * 256 + lo.val) || exceptional (171 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_172 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (172 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (172 * 256 + lo.val) →
    (covered (172 * 256 + lo.val) || exceptional (172 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_173 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (173 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (173 * 256 + lo.val) →
    (covered (173 * 256 + lo.val) || exceptional (173 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_174 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (174 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (174 * 256 + lo.val) →
    (covered (174 * 256 + lo.val) || exceptional (174 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_175 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (175 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (175 * 256 + lo.val) →
    (covered (175 * 256 + lo.val) || exceptional (175 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_176 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (176 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (176 * 256 + lo.val) →
    (covered (176 * 256 + lo.val) || exceptional (176 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_177 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (177 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (177 * 256 + lo.val) →
    (covered (177 * 256 + lo.val) || exceptional (177 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_178 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (178 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (178 * 256 + lo.val) →
    (covered (178 * 256 + lo.val) || exceptional (178 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_179 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (179 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (179 * 256 + lo.val) →
    (covered (179 * 256 + lo.val) || exceptional (179 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_180 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (180 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (180 * 256 + lo.val) →
    (covered (180 * 256 + lo.val) || exceptional (180 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_181 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (181 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (181 * 256 + lo.val) →
    (covered (181 * 256 + lo.val) || exceptional (181 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_182 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (182 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (182 * 256 + lo.val) →
    (covered (182 * 256 + lo.val) || exceptional (182 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_183 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (183 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (183 * 256 + lo.val) →
    (covered (183 * 256 + lo.val) || exceptional (183 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_184 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (184 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (184 * 256 + lo.val) →
    (covered (184 * 256 + lo.val) || exceptional (184 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_185 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (185 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (185 * 256 + lo.val) →
    (covered (185 * 256 + lo.val) || exceptional (185 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_186 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (186 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (186 * 256 + lo.val) →
    (covered (186 * 256 + lo.val) || exceptional (186 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_187 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (187 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (187 * 256 + lo.val) →
    (covered (187 * 256 + lo.val) || exceptional (187 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_188 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (188 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (188 * 256 + lo.val) →
    (covered (188 * 256 + lo.val) || exceptional (188 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_189 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (189 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (189 * 256 + lo.val) →
    (covered (189 * 256 + lo.val) || exceptional (189 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_190 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (190 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (190 * 256 + lo.val) →
    (covered (190 * 256 + lo.val) || exceptional (190 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_191 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (191 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (191 * 256 + lo.val) →
    (covered (191 * 256 + lo.val) || exceptional (191 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_192 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (192 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (192 * 256 + lo.val) →
    (covered (192 * 256 + lo.val) || exceptional (192 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_193 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (193 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (193 * 256 + lo.val) →
    (covered (193 * 256 + lo.val) || exceptional (193 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_194 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (194 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (194 * 256 + lo.val) →
    (covered (194 * 256 + lo.val) || exceptional (194 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_195 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (195 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (195 * 256 + lo.val) →
    (covered (195 * 256 + lo.val) || exceptional (195 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_196 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (196 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (196 * 256 + lo.val) →
    (covered (196 * 256 + lo.val) || exceptional (196 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_197 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (197 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (197 * 256 + lo.val) →
    (covered (197 * 256 + lo.val) || exceptional (197 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_198 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (198 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (198 * 256 + lo.val) →
    (covered (198 * 256 + lo.val) || exceptional (198 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_199 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (199 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (199 * 256 + lo.val) →
    (covered (199 * 256 + lo.val) || exceptional (199 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_200 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (200 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (200 * 256 + lo.val) →
    (covered (200 * 256 + lo.val) || exceptional (200 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_201 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (201 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (201 * 256 + lo.val) →
    (covered (201 * 256 + lo.val) || exceptional (201 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_202 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (202 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (202 * 256 + lo.val) →
    (covered (202 * 256 + lo.val) || exceptional (202 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_203 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (203 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (203 * 256 + lo.val) →
    (covered (203 * 256 + lo.val) || exceptional (203 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_204 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (204 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (204 * 256 + lo.val) →
    (covered (204 * 256 + lo.val) || exceptional (204 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_205 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (205 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (205 * 256 + lo.val) →
    (covered (205 * 256 + lo.val) || exceptional (205 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_206 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (206 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (206 * 256 + lo.val) →
    (covered (206 * 256 + lo.val) || exceptional (206 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_207 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (207 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (207 * 256 + lo.val) →
    (covered (207 * 256 + lo.val) || exceptional (207 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_208 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (208 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (208 * 256 + lo.val) →
    (covered (208 * 256 + lo.val) || exceptional (208 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_209 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (209 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (209 * 256 + lo.val) →
    (covered (209 * 256 + lo.val) || exceptional (209 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_210 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (210 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (210 * 256 + lo.val) →
    (covered (210 * 256 + lo.val) || exceptional (210 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_211 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (211 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (211 * 256 + lo.val) →
    (covered (211 * 256 + lo.val) || exceptional (211 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_212 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (212 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (212 * 256 + lo.val) →
    (covered (212 * 256 + lo.val) || exceptional (212 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_213 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (213 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (213 * 256 + lo.val) →
    (covered (213 * 256 + lo.val) || exceptional (213 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_214 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (214 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (214 * 256 + lo.val) →
    (covered (214 * 256 + lo.val) || exceptional (214 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_215 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (215 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (215 * 256 + lo.val) →
    (covered (215 * 256 + lo.val) || exceptional (215 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_216 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (216 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (216 * 256 + lo.val) →
    (covered (216 * 256 + lo.val) || exceptional (216 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_217 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (217 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (217 * 256 + lo.val) →
    (covered (217 * 256 + lo.val) || exceptional (217 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_218 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (218 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (218 * 256 + lo.val) →
    (covered (218 * 256 + lo.val) || exceptional (218 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_219 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (219 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (219 * 256 + lo.val) →
    (covered (219 * 256 + lo.val) || exceptional (219 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_220 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (220 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (220 * 256 + lo.val) →
    (covered (220 * 256 + lo.val) || exceptional (220 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_221 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (221 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (221 * 256 + lo.val) →
    (covered (221 * 256 + lo.val) || exceptional (221 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_222 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (222 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (222 * 256 + lo.val) →
    (covered (222 * 256 + lo.val) || exceptional (222 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_223 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (223 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (223 * 256 + lo.val) →
    (covered (223 * 256 + lo.val) || exceptional (223 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_224 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (224 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (224 * 256 + lo.val) →
    (covered (224 * 256 + lo.val) || exceptional (224 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_225 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (225 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (225 * 256 + lo.val) →
    (covered (225 * 256 + lo.val) || exceptional (225 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_226 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (226 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (226 * 256 + lo.val) →
    (covered (226 * 256 + lo.val) || exceptional (226 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_227 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (227 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (227 * 256 + lo.val) →
    (covered (227 * 256 + lo.val) || exceptional (227 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_228 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (228 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (228 * 256 + lo.val) →
    (covered (228 * 256 + lo.val) || exceptional (228 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_229 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (229 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (229 * 256 + lo.val) →
    (covered (229 * 256 + lo.val) || exceptional (229 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_230 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (230 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (230 * 256 + lo.val) →
    (covered (230 * 256 + lo.val) || exceptional (230 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_231 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (231 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (231 * 256 + lo.val) →
    (covered (231 * 256 + lo.val) || exceptional (231 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_232 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (232 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (232 * 256 + lo.val) →
    (covered (232 * 256 + lo.val) || exceptional (232 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_233 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (233 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (233 * 256 + lo.val) →
    (covered (233 * 256 + lo.val) || exceptional (233 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_234 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (234 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (234 * 256 + lo.val) →
    (covered (234 * 256 + lo.val) || exceptional (234 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_235 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (235 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (235 * 256 + lo.val) →
    (covered (235 * 256 + lo.val) || exceptional (235 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_236 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (236 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (236 * 256 + lo.val) →
    (covered (236 * 256 + lo.val) || exceptional (236 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_237 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (237 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (237 * 256 + lo.val) →
    (covered (237 * 256 + lo.val) || exceptional (237 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_238 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (238 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (238 * 256 + lo.val) →
    (covered (238 * 256 + lo.val) || exceptional (238 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_239 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (239 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (239 * 256 + lo.val) →
    (covered (239 * 256 + lo.val) || exceptional (239 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_240 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (240 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (240 * 256 + lo.val) →
    (covered (240 * 256 + lo.val) || exceptional (240 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_241 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (241 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (241 * 256 + lo.val) →
    (covered (241 * 256 + lo.val) || exceptional (241 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_242 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (242 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (242 * 256 + lo.val) →
    (covered (242 * 256 + lo.val) || exceptional (242 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_243 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (243 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (243 * 256 + lo.val) →
    (covered (243 * 256 + lo.val) || exceptional (243 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_244 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (244 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (244 * 256 + lo.val) →
    (covered (244 * 256 + lo.val) || exceptional (244 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_245 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (245 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (245 * 256 + lo.val) →
    (covered (245 * 256 + lo.val) || exceptional (245 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_246 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (246 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (246 * 256 + lo.val) →
    (covered (246 * 256 + lo.val) || exceptional (246 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_247 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (247 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (247 * 256 + lo.val) →
    (covered (247 * 256 + lo.val) || exceptional (247 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_248 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (248 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (248 * 256 + lo.val) →
    (covered (248 * 256 + lo.val) || exceptional (248 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_249 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (249 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (249 * 256 + lo.val) →
    (covered (249 * 256 + lo.val) || exceptional (249 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_250 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (250 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (250 * 256 + lo.val) →
    (covered (250 * 256 + lo.val) || exceptional (250 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_251 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (251 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (251 * 256 + lo.val) →
    (covered (251 * 256 + lo.val) || exceptional (251 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_252 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (252 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (252 * 256 + lo.val) →
    (covered (252 * 256 + lo.val) || exceptional (252 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_253 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (253 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (253 * 256 + lo.val) →
    (covered (253 * 256 + lo.val) || exceptional (253 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_254 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (254 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (254 * 256 + lo.val) →
    (covered (254 * 256 + lo.val) || exceptional (254 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_255 : ∀ lo : Fin 256,
    1 ≤ DenseOutside.terminalCount (255 * 256 + lo.val) →
    11 ≤ PathExchange.crossCount (255 * 256 + lo.val) →
    (covered (255 * 256 + lo.val) || exceptional (255 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_rows (hi lo : Fin 256)
    (hz : 1 ≤ DenseOutside.terminalCount (hi.val * 256 + lo.val))
    (ht : 11 ≤ PathExchange.crossCount (hi.val * 256 + lo.val)) :
    (covered (hi.val * 256 + lo.val) || exceptional (hi.val * 256 + lo.val)) = true := by
  fin_cases hi
  · exact coverage_0 lo hz ht
  · exact coverage_1 lo hz ht
  · exact coverage_2 lo hz ht
  · exact coverage_3 lo hz ht
  · exact coverage_4 lo hz ht
  · exact coverage_5 lo hz ht
  · exact coverage_6 lo hz ht
  · exact coverage_7 lo hz ht
  · exact coverage_8 lo hz ht
  · exact coverage_9 lo hz ht
  · exact coverage_10 lo hz ht
  · exact coverage_11 lo hz ht
  · exact coverage_12 lo hz ht
  · exact coverage_13 lo hz ht
  · exact coverage_14 lo hz ht
  · exact coverage_15 lo hz ht
  · exact coverage_16 lo hz ht
  · exact coverage_17 lo hz ht
  · exact coverage_18 lo hz ht
  · exact coverage_19 lo hz ht
  · exact coverage_20 lo hz ht
  · exact coverage_21 lo hz ht
  · exact coverage_22 lo hz ht
  · exact coverage_23 lo hz ht
  · exact coverage_24 lo hz ht
  · exact coverage_25 lo hz ht
  · exact coverage_26 lo hz ht
  · exact coverage_27 lo hz ht
  · exact coverage_28 lo hz ht
  · exact coverage_29 lo hz ht
  · exact coverage_30 lo hz ht
  · exact coverage_31 lo hz ht
  · exact coverage_32 lo hz ht
  · exact coverage_33 lo hz ht
  · exact coverage_34 lo hz ht
  · exact coverage_35 lo hz ht
  · exact coverage_36 lo hz ht
  · exact coverage_37 lo hz ht
  · exact coverage_38 lo hz ht
  · exact coverage_39 lo hz ht
  · exact coverage_40 lo hz ht
  · exact coverage_41 lo hz ht
  · exact coverage_42 lo hz ht
  · exact coverage_43 lo hz ht
  · exact coverage_44 lo hz ht
  · exact coverage_45 lo hz ht
  · exact coverage_46 lo hz ht
  · exact coverage_47 lo hz ht
  · exact coverage_48 lo hz ht
  · exact coverage_49 lo hz ht
  · exact coverage_50 lo hz ht
  · exact coverage_51 lo hz ht
  · exact coverage_52 lo hz ht
  · exact coverage_53 lo hz ht
  · exact coverage_54 lo hz ht
  · exact coverage_55 lo hz ht
  · exact coverage_56 lo hz ht
  · exact coverage_57 lo hz ht
  · exact coverage_58 lo hz ht
  · exact coverage_59 lo hz ht
  · exact coverage_60 lo hz ht
  · exact coverage_61 lo hz ht
  · exact coverage_62 lo hz ht
  · exact coverage_63 lo hz ht
  · exact coverage_64 lo hz ht
  · exact coverage_65 lo hz ht
  · exact coverage_66 lo hz ht
  · exact coverage_67 lo hz ht
  · exact coverage_68 lo hz ht
  · exact coverage_69 lo hz ht
  · exact coverage_70 lo hz ht
  · exact coverage_71 lo hz ht
  · exact coverage_72 lo hz ht
  · exact coverage_73 lo hz ht
  · exact coverage_74 lo hz ht
  · exact coverage_75 lo hz ht
  · exact coverage_76 lo hz ht
  · exact coverage_77 lo hz ht
  · exact coverage_78 lo hz ht
  · exact coverage_79 lo hz ht
  · exact coverage_80 lo hz ht
  · exact coverage_81 lo hz ht
  · exact coverage_82 lo hz ht
  · exact coverage_83 lo hz ht
  · exact coverage_84 lo hz ht
  · exact coverage_85 lo hz ht
  · exact coverage_86 lo hz ht
  · exact coverage_87 lo hz ht
  · exact coverage_88 lo hz ht
  · exact coverage_89 lo hz ht
  · exact coverage_90 lo hz ht
  · exact coverage_91 lo hz ht
  · exact coverage_92 lo hz ht
  · exact coverage_93 lo hz ht
  · exact coverage_94 lo hz ht
  · exact coverage_95 lo hz ht
  · exact coverage_96 lo hz ht
  · exact coverage_97 lo hz ht
  · exact coverage_98 lo hz ht
  · exact coverage_99 lo hz ht
  · exact coverage_100 lo hz ht
  · exact coverage_101 lo hz ht
  · exact coverage_102 lo hz ht
  · exact coverage_103 lo hz ht
  · exact coverage_104 lo hz ht
  · exact coverage_105 lo hz ht
  · exact coverage_106 lo hz ht
  · exact coverage_107 lo hz ht
  · exact coverage_108 lo hz ht
  · exact coverage_109 lo hz ht
  · exact coverage_110 lo hz ht
  · exact coverage_111 lo hz ht
  · exact coverage_112 lo hz ht
  · exact coverage_113 lo hz ht
  · exact coverage_114 lo hz ht
  · exact coverage_115 lo hz ht
  · exact coverage_116 lo hz ht
  · exact coverage_117 lo hz ht
  · exact coverage_118 lo hz ht
  · exact coverage_119 lo hz ht
  · exact coverage_120 lo hz ht
  · exact coverage_121 lo hz ht
  · exact coverage_122 lo hz ht
  · exact coverage_123 lo hz ht
  · exact coverage_124 lo hz ht
  · exact coverage_125 lo hz ht
  · exact coverage_126 lo hz ht
  · exact coverage_127 lo hz ht
  · exact coverage_128 lo hz ht
  · exact coverage_129 lo hz ht
  · exact coverage_130 lo hz ht
  · exact coverage_131 lo hz ht
  · exact coverage_132 lo hz ht
  · exact coverage_133 lo hz ht
  · exact coverage_134 lo hz ht
  · exact coverage_135 lo hz ht
  · exact coverage_136 lo hz ht
  · exact coverage_137 lo hz ht
  · exact coverage_138 lo hz ht
  · exact coverage_139 lo hz ht
  · exact coverage_140 lo hz ht
  · exact coverage_141 lo hz ht
  · exact coverage_142 lo hz ht
  · exact coverage_143 lo hz ht
  · exact coverage_144 lo hz ht
  · exact coverage_145 lo hz ht
  · exact coverage_146 lo hz ht
  · exact coverage_147 lo hz ht
  · exact coverage_148 lo hz ht
  · exact coverage_149 lo hz ht
  · exact coverage_150 lo hz ht
  · exact coverage_151 lo hz ht
  · exact coverage_152 lo hz ht
  · exact coverage_153 lo hz ht
  · exact coverage_154 lo hz ht
  · exact coverage_155 lo hz ht
  · exact coverage_156 lo hz ht
  · exact coverage_157 lo hz ht
  · exact coverage_158 lo hz ht
  · exact coverage_159 lo hz ht
  · exact coverage_160 lo hz ht
  · exact coverage_161 lo hz ht
  · exact coverage_162 lo hz ht
  · exact coverage_163 lo hz ht
  · exact coverage_164 lo hz ht
  · exact coverage_165 lo hz ht
  · exact coverage_166 lo hz ht
  · exact coverage_167 lo hz ht
  · exact coverage_168 lo hz ht
  · exact coverage_169 lo hz ht
  · exact coverage_170 lo hz ht
  · exact coverage_171 lo hz ht
  · exact coverage_172 lo hz ht
  · exact coverage_173 lo hz ht
  · exact coverage_174 lo hz ht
  · exact coverage_175 lo hz ht
  · exact coverage_176 lo hz ht
  · exact coverage_177 lo hz ht
  · exact coverage_178 lo hz ht
  · exact coverage_179 lo hz ht
  · exact coverage_180 lo hz ht
  · exact coverage_181 lo hz ht
  · exact coverage_182 lo hz ht
  · exact coverage_183 lo hz ht
  · exact coverage_184 lo hz ht
  · exact coverage_185 lo hz ht
  · exact coverage_186 lo hz ht
  · exact coverage_187 lo hz ht
  · exact coverage_188 lo hz ht
  · exact coverage_189 lo hz ht
  · exact coverage_190 lo hz ht
  · exact coverage_191 lo hz ht
  · exact coverage_192 lo hz ht
  · exact coverage_193 lo hz ht
  · exact coverage_194 lo hz ht
  · exact coverage_195 lo hz ht
  · exact coverage_196 lo hz ht
  · exact coverage_197 lo hz ht
  · exact coverage_198 lo hz ht
  · exact coverage_199 lo hz ht
  · exact coverage_200 lo hz ht
  · exact coverage_201 lo hz ht
  · exact coverage_202 lo hz ht
  · exact coverage_203 lo hz ht
  · exact coverage_204 lo hz ht
  · exact coverage_205 lo hz ht
  · exact coverage_206 lo hz ht
  · exact coverage_207 lo hz ht
  · exact coverage_208 lo hz ht
  · exact coverage_209 lo hz ht
  · exact coverage_210 lo hz ht
  · exact coverage_211 lo hz ht
  · exact coverage_212 lo hz ht
  · exact coverage_213 lo hz ht
  · exact coverage_214 lo hz ht
  · exact coverage_215 lo hz ht
  · exact coverage_216 lo hz ht
  · exact coverage_217 lo hz ht
  · exact coverage_218 lo hz ht
  · exact coverage_219 lo hz ht
  · exact coverage_220 lo hz ht
  · exact coverage_221 lo hz ht
  · exact coverage_222 lo hz ht
  · exact coverage_223 lo hz ht
  · exact coverage_224 lo hz ht
  · exact coverage_225 lo hz ht
  · exact coverage_226 lo hz ht
  · exact coverage_227 lo hz ht
  · exact coverage_228 lo hz ht
  · exact coverage_229 lo hz ht
  · exact coverage_230 lo hz ht
  · exact coverage_231 lo hz ht
  · exact coverage_232 lo hz ht
  · exact coverage_233 lo hz ht
  · exact coverage_234 lo hz ht
  · exact coverage_235 lo hz ht
  · exact coverage_236 lo hz ht
  · exact coverage_237 lo hz ht
  · exact coverage_238 lo hz ht
  · exact coverage_239 lo hz ht
  · exact coverage_240 lo hz ht
  · exact coverage_241 lo hz ht
  · exact coverage_242 lo hz ht
  · exact coverage_243 lo hz ht
  · exact coverage_244 lo hz ht
  · exact coverage_245 lo hz ht
  · exact coverage_246 lo hz ht
  · exact coverage_247 lo hz ht
  · exact coverage_248 lo hz ht
  · exact coverage_249 lo hz ht
  · exact coverage_250 lo hz ht
  · exact coverage_251 lo hz ht
  · exact coverage_252 lo hz ht
  · exact coverage_253 lo hz ht
  · exact coverage_254 lo hz ht
  · exact coverage_255 lo hz ht

theorem coverage (m : Fin 65536) (hz : 1 ≤ DenseOutside.terminalCount m.val)
    (ht : 11 ≤ PathExchange.crossCount m.val) : (covered m.val || exceptional m.val) = true := by
  let hi : Fin 256 := ⟨m.val / 256, by omega⟩
  let lo : Fin 256 := ⟨m.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : hi.val * 256 + lo.val = m.val := by dsimp [hi, lo]; omega
  rw [← he] at hz ht ⊢
  exact coverage_rows hi lo hz ht

end Erdos577.PawEleven
