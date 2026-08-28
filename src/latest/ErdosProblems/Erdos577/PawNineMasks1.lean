import ErdosProblems.Erdos577.PawNineModel

/-! Kernel-checked nine-contact coverage for diagonal mask 1. -/

namespace Erdos577.PawNine.D1

def masks : List ℕ := [
  282, 549, 553, 556, 1098, 2179, 2181, 2182, 4122, 4362,
  4680, 4740, 6180, 6210, 6657, 8229, 8233, 8236, 8520, 8580,
  8709, 8713, 8716, 9240, 9345, 9474, 10498, 11266, 14344, 16458,
  16920, 17025, 17418, 18450, 18465, 18948, 20994, 22536, 26632, 32899,
  32901, 32902, 33060, 33090, 33544, 33810, 33825, 34056, 34312, 34819,
  34821, 34822, 37378, 41217, 41988, 49666, 5290, 16810, 43540, 43585]

def covered (m : ℕ) : Bool := masks.any fun w ↦ m &&& w == w

private theorem coverage_0 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (0 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (0 * 256 + lo.val) = 9 →
    HasGoodRow 1 (0 * 256 + lo.val) → covered (0 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_1 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (1 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (1 * 256 + lo.val) = 9 →
    HasGoodRow 1 (1 * 256 + lo.val) → covered (1 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_2 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (2 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (2 * 256 + lo.val) = 9 →
    HasGoodRow 1 (2 * 256 + lo.val) → covered (2 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_3 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (3 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (3 * 256 + lo.val) = 9 →
    HasGoodRow 1 (3 * 256 + lo.val) → covered (3 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_4 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (4 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (4 * 256 + lo.val) = 9 →
    HasGoodRow 1 (4 * 256 + lo.val) → covered (4 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_5 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (5 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (5 * 256 + lo.val) = 9 →
    HasGoodRow 1 (5 * 256 + lo.val) → covered (5 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_6 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (6 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (6 * 256 + lo.val) = 9 →
    HasGoodRow 1 (6 * 256 + lo.val) → covered (6 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_7 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (7 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (7 * 256 + lo.val) = 9 →
    HasGoodRow 1 (7 * 256 + lo.val) → covered (7 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_8 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (8 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (8 * 256 + lo.val) = 9 →
    HasGoodRow 1 (8 * 256 + lo.val) → covered (8 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_9 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (9 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (9 * 256 + lo.val) = 9 →
    HasGoodRow 1 (9 * 256 + lo.val) → covered (9 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_10 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (10 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (10 * 256 + lo.val) = 9 →
    HasGoodRow 1 (10 * 256 + lo.val) → covered (10 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_11 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (11 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (11 * 256 + lo.val) = 9 →
    HasGoodRow 1 (11 * 256 + lo.val) → covered (11 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_12 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (12 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (12 * 256 + lo.val) = 9 →
    HasGoodRow 1 (12 * 256 + lo.val) → covered (12 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_13 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (13 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (13 * 256 + lo.val) = 9 →
    HasGoodRow 1 (13 * 256 + lo.val) → covered (13 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_14 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (14 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (14 * 256 + lo.val) = 9 →
    HasGoodRow 1 (14 * 256 + lo.val) → covered (14 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_15 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (15 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (15 * 256 + lo.val) = 9 →
    HasGoodRow 1 (15 * 256 + lo.val) → covered (15 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_16 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (16 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (16 * 256 + lo.val) = 9 →
    HasGoodRow 1 (16 * 256 + lo.val) → covered (16 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_17 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (17 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (17 * 256 + lo.val) = 9 →
    HasGoodRow 1 (17 * 256 + lo.val) → covered (17 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_18 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (18 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (18 * 256 + lo.val) = 9 →
    HasGoodRow 1 (18 * 256 + lo.val) → covered (18 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_19 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (19 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (19 * 256 + lo.val) = 9 →
    HasGoodRow 1 (19 * 256 + lo.val) → covered (19 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_20 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (20 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (20 * 256 + lo.val) = 9 →
    HasGoodRow 1 (20 * 256 + lo.val) → covered (20 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_21 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (21 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (21 * 256 + lo.val) = 9 →
    HasGoodRow 1 (21 * 256 + lo.val) → covered (21 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_22 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (22 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (22 * 256 + lo.val) = 9 →
    HasGoodRow 1 (22 * 256 + lo.val) → covered (22 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_23 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (23 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (23 * 256 + lo.val) = 9 →
    HasGoodRow 1 (23 * 256 + lo.val) → covered (23 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_24 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (24 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (24 * 256 + lo.val) = 9 →
    HasGoodRow 1 (24 * 256 + lo.val) → covered (24 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_25 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (25 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (25 * 256 + lo.val) = 9 →
    HasGoodRow 1 (25 * 256 + lo.val) → covered (25 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_26 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (26 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (26 * 256 + lo.val) = 9 →
    HasGoodRow 1 (26 * 256 + lo.val) → covered (26 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_27 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (27 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (27 * 256 + lo.val) = 9 →
    HasGoodRow 1 (27 * 256 + lo.val) → covered (27 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_28 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (28 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (28 * 256 + lo.val) = 9 →
    HasGoodRow 1 (28 * 256 + lo.val) → covered (28 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_29 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (29 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (29 * 256 + lo.val) = 9 →
    HasGoodRow 1 (29 * 256 + lo.val) → covered (29 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_30 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (30 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (30 * 256 + lo.val) = 9 →
    HasGoodRow 1 (30 * 256 + lo.val) → covered (30 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_31 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (31 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (31 * 256 + lo.val) = 9 →
    HasGoodRow 1 (31 * 256 + lo.val) → covered (31 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_32 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (32 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (32 * 256 + lo.val) = 9 →
    HasGoodRow 1 (32 * 256 + lo.val) → covered (32 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_33 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (33 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (33 * 256 + lo.val) = 9 →
    HasGoodRow 1 (33 * 256 + lo.val) → covered (33 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_34 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (34 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (34 * 256 + lo.val) = 9 →
    HasGoodRow 1 (34 * 256 + lo.val) → covered (34 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_35 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (35 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (35 * 256 + lo.val) = 9 →
    HasGoodRow 1 (35 * 256 + lo.val) → covered (35 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_36 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (36 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (36 * 256 + lo.val) = 9 →
    HasGoodRow 1 (36 * 256 + lo.val) → covered (36 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_37 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (37 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (37 * 256 + lo.val) = 9 →
    HasGoodRow 1 (37 * 256 + lo.val) → covered (37 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_38 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (38 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (38 * 256 + lo.val) = 9 →
    HasGoodRow 1 (38 * 256 + lo.val) → covered (38 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_39 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (39 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (39 * 256 + lo.val) = 9 →
    HasGoodRow 1 (39 * 256 + lo.val) → covered (39 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_40 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (40 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (40 * 256 + lo.val) = 9 →
    HasGoodRow 1 (40 * 256 + lo.val) → covered (40 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_41 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (41 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (41 * 256 + lo.val) = 9 →
    HasGoodRow 1 (41 * 256 + lo.val) → covered (41 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_42 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (42 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (42 * 256 + lo.val) = 9 →
    HasGoodRow 1 (42 * 256 + lo.val) → covered (42 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_43 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (43 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (43 * 256 + lo.val) = 9 →
    HasGoodRow 1 (43 * 256 + lo.val) → covered (43 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_44 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (44 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (44 * 256 + lo.val) = 9 →
    HasGoodRow 1 (44 * 256 + lo.val) → covered (44 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_45 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (45 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (45 * 256 + lo.val) = 9 →
    HasGoodRow 1 (45 * 256 + lo.val) → covered (45 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_46 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (46 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (46 * 256 + lo.val) = 9 →
    HasGoodRow 1 (46 * 256 + lo.val) → covered (46 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_47 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (47 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (47 * 256 + lo.val) = 9 →
    HasGoodRow 1 (47 * 256 + lo.val) → covered (47 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_48 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (48 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (48 * 256 + lo.val) = 9 →
    HasGoodRow 1 (48 * 256 + lo.val) → covered (48 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_49 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (49 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (49 * 256 + lo.val) = 9 →
    HasGoodRow 1 (49 * 256 + lo.val) → covered (49 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_50 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (50 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (50 * 256 + lo.val) = 9 →
    HasGoodRow 1 (50 * 256 + lo.val) → covered (50 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_51 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (51 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (51 * 256 + lo.val) = 9 →
    HasGoodRow 1 (51 * 256 + lo.val) → covered (51 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_52 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (52 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (52 * 256 + lo.val) = 9 →
    HasGoodRow 1 (52 * 256 + lo.val) → covered (52 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_53 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (53 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (53 * 256 + lo.val) = 9 →
    HasGoodRow 1 (53 * 256 + lo.val) → covered (53 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_54 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (54 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (54 * 256 + lo.val) = 9 →
    HasGoodRow 1 (54 * 256 + lo.val) → covered (54 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_55 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (55 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (55 * 256 + lo.val) = 9 →
    HasGoodRow 1 (55 * 256 + lo.val) → covered (55 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_56 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (56 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (56 * 256 + lo.val) = 9 →
    HasGoodRow 1 (56 * 256 + lo.val) → covered (56 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_57 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (57 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (57 * 256 + lo.val) = 9 →
    HasGoodRow 1 (57 * 256 + lo.val) → covered (57 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_58 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (58 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (58 * 256 + lo.val) = 9 →
    HasGoodRow 1 (58 * 256 + lo.val) → covered (58 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_59 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (59 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (59 * 256 + lo.val) = 9 →
    HasGoodRow 1 (59 * 256 + lo.val) → covered (59 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_60 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (60 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (60 * 256 + lo.val) = 9 →
    HasGoodRow 1 (60 * 256 + lo.val) → covered (60 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_61 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (61 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (61 * 256 + lo.val) = 9 →
    HasGoodRow 1 (61 * 256 + lo.val) → covered (61 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_62 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (62 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (62 * 256 + lo.val) = 9 →
    HasGoodRow 1 (62 * 256 + lo.val) → covered (62 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_63 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (63 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (63 * 256 + lo.val) = 9 →
    HasGoodRow 1 (63 * 256 + lo.val) → covered (63 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_64 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (64 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (64 * 256 + lo.val) = 9 →
    HasGoodRow 1 (64 * 256 + lo.val) → covered (64 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_65 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (65 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (65 * 256 + lo.val) = 9 →
    HasGoodRow 1 (65 * 256 + lo.val) → covered (65 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_66 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (66 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (66 * 256 + lo.val) = 9 →
    HasGoodRow 1 (66 * 256 + lo.val) → covered (66 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_67 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (67 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (67 * 256 + lo.val) = 9 →
    HasGoodRow 1 (67 * 256 + lo.val) → covered (67 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_68 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (68 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (68 * 256 + lo.val) = 9 →
    HasGoodRow 1 (68 * 256 + lo.val) → covered (68 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_69 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (69 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (69 * 256 + lo.val) = 9 →
    HasGoodRow 1 (69 * 256 + lo.val) → covered (69 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_70 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (70 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (70 * 256 + lo.val) = 9 →
    HasGoodRow 1 (70 * 256 + lo.val) → covered (70 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_71 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (71 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (71 * 256 + lo.val) = 9 →
    HasGoodRow 1 (71 * 256 + lo.val) → covered (71 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_72 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (72 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (72 * 256 + lo.val) = 9 →
    HasGoodRow 1 (72 * 256 + lo.val) → covered (72 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_73 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (73 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (73 * 256 + lo.val) = 9 →
    HasGoodRow 1 (73 * 256 + lo.val) → covered (73 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_74 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (74 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (74 * 256 + lo.val) = 9 →
    HasGoodRow 1 (74 * 256 + lo.val) → covered (74 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_75 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (75 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (75 * 256 + lo.val) = 9 →
    HasGoodRow 1 (75 * 256 + lo.val) → covered (75 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_76 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (76 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (76 * 256 + lo.val) = 9 →
    HasGoodRow 1 (76 * 256 + lo.val) → covered (76 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_77 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (77 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (77 * 256 + lo.val) = 9 →
    HasGoodRow 1 (77 * 256 + lo.val) → covered (77 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_78 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (78 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (78 * 256 + lo.val) = 9 →
    HasGoodRow 1 (78 * 256 + lo.val) → covered (78 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_79 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (79 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (79 * 256 + lo.val) = 9 →
    HasGoodRow 1 (79 * 256 + lo.val) → covered (79 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_80 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (80 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (80 * 256 + lo.val) = 9 →
    HasGoodRow 1 (80 * 256 + lo.val) → covered (80 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_81 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (81 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (81 * 256 + lo.val) = 9 →
    HasGoodRow 1 (81 * 256 + lo.val) → covered (81 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_82 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (82 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (82 * 256 + lo.val) = 9 →
    HasGoodRow 1 (82 * 256 + lo.val) → covered (82 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_83 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (83 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (83 * 256 + lo.val) = 9 →
    HasGoodRow 1 (83 * 256 + lo.val) → covered (83 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_84 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (84 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (84 * 256 + lo.val) = 9 →
    HasGoodRow 1 (84 * 256 + lo.val) → covered (84 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_85 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (85 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (85 * 256 + lo.val) = 9 →
    HasGoodRow 1 (85 * 256 + lo.val) → covered (85 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_86 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (86 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (86 * 256 + lo.val) = 9 →
    HasGoodRow 1 (86 * 256 + lo.val) → covered (86 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_87 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (87 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (87 * 256 + lo.val) = 9 →
    HasGoodRow 1 (87 * 256 + lo.val) → covered (87 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_88 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (88 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (88 * 256 + lo.val) = 9 →
    HasGoodRow 1 (88 * 256 + lo.val) → covered (88 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_89 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (89 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (89 * 256 + lo.val) = 9 →
    HasGoodRow 1 (89 * 256 + lo.val) → covered (89 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_90 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (90 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (90 * 256 + lo.val) = 9 →
    HasGoodRow 1 (90 * 256 + lo.val) → covered (90 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_91 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (91 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (91 * 256 + lo.val) = 9 →
    HasGoodRow 1 (91 * 256 + lo.val) → covered (91 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_92 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (92 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (92 * 256 + lo.val) = 9 →
    HasGoodRow 1 (92 * 256 + lo.val) → covered (92 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_93 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (93 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (93 * 256 + lo.val) = 9 →
    HasGoodRow 1 (93 * 256 + lo.val) → covered (93 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_94 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (94 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (94 * 256 + lo.val) = 9 →
    HasGoodRow 1 (94 * 256 + lo.val) → covered (94 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_95 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (95 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (95 * 256 + lo.val) = 9 →
    HasGoodRow 1 (95 * 256 + lo.val) → covered (95 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_96 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (96 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (96 * 256 + lo.val) = 9 →
    HasGoodRow 1 (96 * 256 + lo.val) → covered (96 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_97 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (97 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (97 * 256 + lo.val) = 9 →
    HasGoodRow 1 (97 * 256 + lo.val) → covered (97 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_98 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (98 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (98 * 256 + lo.val) = 9 →
    HasGoodRow 1 (98 * 256 + lo.val) → covered (98 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_99 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (99 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (99 * 256 + lo.val) = 9 →
    HasGoodRow 1 (99 * 256 + lo.val) → covered (99 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_100 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (100 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (100 * 256 + lo.val) = 9 →
    HasGoodRow 1 (100 * 256 + lo.val) → covered (100 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_101 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (101 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (101 * 256 + lo.val) = 9 →
    HasGoodRow 1 (101 * 256 + lo.val) → covered (101 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_102 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (102 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (102 * 256 + lo.val) = 9 →
    HasGoodRow 1 (102 * 256 + lo.val) → covered (102 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_103 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (103 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (103 * 256 + lo.val) = 9 →
    HasGoodRow 1 (103 * 256 + lo.val) → covered (103 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_104 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (104 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (104 * 256 + lo.val) = 9 →
    HasGoodRow 1 (104 * 256 + lo.val) → covered (104 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_105 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (105 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (105 * 256 + lo.val) = 9 →
    HasGoodRow 1 (105 * 256 + lo.val) → covered (105 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_106 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (106 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (106 * 256 + lo.val) = 9 →
    HasGoodRow 1 (106 * 256 + lo.val) → covered (106 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_107 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (107 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (107 * 256 + lo.val) = 9 →
    HasGoodRow 1 (107 * 256 + lo.val) → covered (107 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_108 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (108 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (108 * 256 + lo.val) = 9 →
    HasGoodRow 1 (108 * 256 + lo.val) → covered (108 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_109 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (109 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (109 * 256 + lo.val) = 9 →
    HasGoodRow 1 (109 * 256 + lo.val) → covered (109 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_110 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (110 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (110 * 256 + lo.val) = 9 →
    HasGoodRow 1 (110 * 256 + lo.val) → covered (110 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_111 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (111 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (111 * 256 + lo.val) = 9 →
    HasGoodRow 1 (111 * 256 + lo.val) → covered (111 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_112 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (112 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (112 * 256 + lo.val) = 9 →
    HasGoodRow 1 (112 * 256 + lo.val) → covered (112 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_113 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (113 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (113 * 256 + lo.val) = 9 →
    HasGoodRow 1 (113 * 256 + lo.val) → covered (113 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_114 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (114 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (114 * 256 + lo.val) = 9 →
    HasGoodRow 1 (114 * 256 + lo.val) → covered (114 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_115 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (115 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (115 * 256 + lo.val) = 9 →
    HasGoodRow 1 (115 * 256 + lo.val) → covered (115 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_116 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (116 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (116 * 256 + lo.val) = 9 →
    HasGoodRow 1 (116 * 256 + lo.val) → covered (116 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_117 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (117 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (117 * 256 + lo.val) = 9 →
    HasGoodRow 1 (117 * 256 + lo.val) → covered (117 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_118 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (118 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (118 * 256 + lo.val) = 9 →
    HasGoodRow 1 (118 * 256 + lo.val) → covered (118 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_119 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (119 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (119 * 256 + lo.val) = 9 →
    HasGoodRow 1 (119 * 256 + lo.val) → covered (119 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_120 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (120 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (120 * 256 + lo.val) = 9 →
    HasGoodRow 1 (120 * 256 + lo.val) → covered (120 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_121 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (121 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (121 * 256 + lo.val) = 9 →
    HasGoodRow 1 (121 * 256 + lo.val) → covered (121 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_122 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (122 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (122 * 256 + lo.val) = 9 →
    HasGoodRow 1 (122 * 256 + lo.val) → covered (122 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_123 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (123 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (123 * 256 + lo.val) = 9 →
    HasGoodRow 1 (123 * 256 + lo.val) → covered (123 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_124 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (124 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (124 * 256 + lo.val) = 9 →
    HasGoodRow 1 (124 * 256 + lo.val) → covered (124 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_125 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (125 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (125 * 256 + lo.val) = 9 →
    HasGoodRow 1 (125 * 256 + lo.val) → covered (125 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_126 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (126 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (126 * 256 + lo.val) = 9 →
    HasGoodRow 1 (126 * 256 + lo.val) → covered (126 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_127 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (127 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (127 * 256 + lo.val) = 9 →
    HasGoodRow 1 (127 * 256 + lo.val) → covered (127 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_128 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (128 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (128 * 256 + lo.val) = 9 →
    HasGoodRow 1 (128 * 256 + lo.val) → covered (128 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_129 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (129 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (129 * 256 + lo.val) = 9 →
    HasGoodRow 1 (129 * 256 + lo.val) → covered (129 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_130 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (130 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (130 * 256 + lo.val) = 9 →
    HasGoodRow 1 (130 * 256 + lo.val) → covered (130 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_131 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (131 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (131 * 256 + lo.val) = 9 →
    HasGoodRow 1 (131 * 256 + lo.val) → covered (131 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_132 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (132 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (132 * 256 + lo.val) = 9 →
    HasGoodRow 1 (132 * 256 + lo.val) → covered (132 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_133 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (133 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (133 * 256 + lo.val) = 9 →
    HasGoodRow 1 (133 * 256 + lo.val) → covered (133 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_134 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (134 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (134 * 256 + lo.val) = 9 →
    HasGoodRow 1 (134 * 256 + lo.val) → covered (134 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_135 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (135 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (135 * 256 + lo.val) = 9 →
    HasGoodRow 1 (135 * 256 + lo.val) → covered (135 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_136 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (136 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (136 * 256 + lo.val) = 9 →
    HasGoodRow 1 (136 * 256 + lo.val) → covered (136 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_137 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (137 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (137 * 256 + lo.val) = 9 →
    HasGoodRow 1 (137 * 256 + lo.val) → covered (137 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_138 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (138 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (138 * 256 + lo.val) = 9 →
    HasGoodRow 1 (138 * 256 + lo.val) → covered (138 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_139 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (139 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (139 * 256 + lo.val) = 9 →
    HasGoodRow 1 (139 * 256 + lo.val) → covered (139 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_140 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (140 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (140 * 256 + lo.val) = 9 →
    HasGoodRow 1 (140 * 256 + lo.val) → covered (140 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_141 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (141 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (141 * 256 + lo.val) = 9 →
    HasGoodRow 1 (141 * 256 + lo.val) → covered (141 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_142 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (142 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (142 * 256 + lo.val) = 9 →
    HasGoodRow 1 (142 * 256 + lo.val) → covered (142 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_143 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (143 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (143 * 256 + lo.val) = 9 →
    HasGoodRow 1 (143 * 256 + lo.val) → covered (143 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_144 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (144 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (144 * 256 + lo.val) = 9 →
    HasGoodRow 1 (144 * 256 + lo.val) → covered (144 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_145 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (145 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (145 * 256 + lo.val) = 9 →
    HasGoodRow 1 (145 * 256 + lo.val) → covered (145 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_146 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (146 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (146 * 256 + lo.val) = 9 →
    HasGoodRow 1 (146 * 256 + lo.val) → covered (146 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_147 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (147 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (147 * 256 + lo.val) = 9 →
    HasGoodRow 1 (147 * 256 + lo.val) → covered (147 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_148 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (148 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (148 * 256 + lo.val) = 9 →
    HasGoodRow 1 (148 * 256 + lo.val) → covered (148 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_149 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (149 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (149 * 256 + lo.val) = 9 →
    HasGoodRow 1 (149 * 256 + lo.val) → covered (149 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_150 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (150 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (150 * 256 + lo.val) = 9 →
    HasGoodRow 1 (150 * 256 + lo.val) → covered (150 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_151 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (151 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (151 * 256 + lo.val) = 9 →
    HasGoodRow 1 (151 * 256 + lo.val) → covered (151 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_152 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (152 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (152 * 256 + lo.val) = 9 →
    HasGoodRow 1 (152 * 256 + lo.val) → covered (152 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_153 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (153 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (153 * 256 + lo.val) = 9 →
    HasGoodRow 1 (153 * 256 + lo.val) → covered (153 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_154 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (154 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (154 * 256 + lo.val) = 9 →
    HasGoodRow 1 (154 * 256 + lo.val) → covered (154 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_155 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (155 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (155 * 256 + lo.val) = 9 →
    HasGoodRow 1 (155 * 256 + lo.val) → covered (155 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_156 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (156 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (156 * 256 + lo.val) = 9 →
    HasGoodRow 1 (156 * 256 + lo.val) → covered (156 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_157 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (157 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (157 * 256 + lo.val) = 9 →
    HasGoodRow 1 (157 * 256 + lo.val) → covered (157 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_158 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (158 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (158 * 256 + lo.val) = 9 →
    HasGoodRow 1 (158 * 256 + lo.val) → covered (158 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_159 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (159 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (159 * 256 + lo.val) = 9 →
    HasGoodRow 1 (159 * 256 + lo.val) → covered (159 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_160 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (160 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (160 * 256 + lo.val) = 9 →
    HasGoodRow 1 (160 * 256 + lo.val) → covered (160 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_161 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (161 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (161 * 256 + lo.val) = 9 →
    HasGoodRow 1 (161 * 256 + lo.val) → covered (161 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_162 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (162 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (162 * 256 + lo.val) = 9 →
    HasGoodRow 1 (162 * 256 + lo.val) → covered (162 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_163 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (163 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (163 * 256 + lo.val) = 9 →
    HasGoodRow 1 (163 * 256 + lo.val) → covered (163 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_164 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (164 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (164 * 256 + lo.val) = 9 →
    HasGoodRow 1 (164 * 256 + lo.val) → covered (164 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_165 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (165 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (165 * 256 + lo.val) = 9 →
    HasGoodRow 1 (165 * 256 + lo.val) → covered (165 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_166 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (166 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (166 * 256 + lo.val) = 9 →
    HasGoodRow 1 (166 * 256 + lo.val) → covered (166 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_167 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (167 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (167 * 256 + lo.val) = 9 →
    HasGoodRow 1 (167 * 256 + lo.val) → covered (167 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_168 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (168 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (168 * 256 + lo.val) = 9 →
    HasGoodRow 1 (168 * 256 + lo.val) → covered (168 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_169 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (169 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (169 * 256 + lo.val) = 9 →
    HasGoodRow 1 (169 * 256 + lo.val) → covered (169 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_170 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (170 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (170 * 256 + lo.val) = 9 →
    HasGoodRow 1 (170 * 256 + lo.val) → covered (170 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_171 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (171 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (171 * 256 + lo.val) = 9 →
    HasGoodRow 1 (171 * 256 + lo.val) → covered (171 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_172 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (172 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (172 * 256 + lo.val) = 9 →
    HasGoodRow 1 (172 * 256 + lo.val) → covered (172 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_173 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (173 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (173 * 256 + lo.val) = 9 →
    HasGoodRow 1 (173 * 256 + lo.val) → covered (173 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_174 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (174 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (174 * 256 + lo.val) = 9 →
    HasGoodRow 1 (174 * 256 + lo.val) → covered (174 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_175 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (175 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (175 * 256 + lo.val) = 9 →
    HasGoodRow 1 (175 * 256 + lo.val) → covered (175 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_176 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (176 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (176 * 256 + lo.val) = 9 →
    HasGoodRow 1 (176 * 256 + lo.val) → covered (176 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_177 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (177 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (177 * 256 + lo.val) = 9 →
    HasGoodRow 1 (177 * 256 + lo.val) → covered (177 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_178 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (178 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (178 * 256 + lo.val) = 9 →
    HasGoodRow 1 (178 * 256 + lo.val) → covered (178 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_179 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (179 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (179 * 256 + lo.val) = 9 →
    HasGoodRow 1 (179 * 256 + lo.val) → covered (179 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_180 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (180 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (180 * 256 + lo.val) = 9 →
    HasGoodRow 1 (180 * 256 + lo.val) → covered (180 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_181 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (181 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (181 * 256 + lo.val) = 9 →
    HasGoodRow 1 (181 * 256 + lo.val) → covered (181 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_182 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (182 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (182 * 256 + lo.val) = 9 →
    HasGoodRow 1 (182 * 256 + lo.val) → covered (182 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_183 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (183 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (183 * 256 + lo.val) = 9 →
    HasGoodRow 1 (183 * 256 + lo.val) → covered (183 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_184 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (184 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (184 * 256 + lo.val) = 9 →
    HasGoodRow 1 (184 * 256 + lo.val) → covered (184 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_185 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (185 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (185 * 256 + lo.val) = 9 →
    HasGoodRow 1 (185 * 256 + lo.val) → covered (185 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_186 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (186 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (186 * 256 + lo.val) = 9 →
    HasGoodRow 1 (186 * 256 + lo.val) → covered (186 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_187 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (187 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (187 * 256 + lo.val) = 9 →
    HasGoodRow 1 (187 * 256 + lo.val) → covered (187 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_188 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (188 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (188 * 256 + lo.val) = 9 →
    HasGoodRow 1 (188 * 256 + lo.val) → covered (188 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_189 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (189 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (189 * 256 + lo.val) = 9 →
    HasGoodRow 1 (189 * 256 + lo.val) → covered (189 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_190 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (190 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (190 * 256 + lo.val) = 9 →
    HasGoodRow 1 (190 * 256 + lo.val) → covered (190 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_191 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (191 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (191 * 256 + lo.val) = 9 →
    HasGoodRow 1 (191 * 256 + lo.val) → covered (191 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_192 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (192 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (192 * 256 + lo.val) = 9 →
    HasGoodRow 1 (192 * 256 + lo.val) → covered (192 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_193 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (193 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (193 * 256 + lo.val) = 9 →
    HasGoodRow 1 (193 * 256 + lo.val) → covered (193 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_194 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (194 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (194 * 256 + lo.val) = 9 →
    HasGoodRow 1 (194 * 256 + lo.val) → covered (194 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_195 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (195 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (195 * 256 + lo.val) = 9 →
    HasGoodRow 1 (195 * 256 + lo.val) → covered (195 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_196 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (196 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (196 * 256 + lo.val) = 9 →
    HasGoodRow 1 (196 * 256 + lo.val) → covered (196 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_197 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (197 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (197 * 256 + lo.val) = 9 →
    HasGoodRow 1 (197 * 256 + lo.val) → covered (197 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_198 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (198 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (198 * 256 + lo.val) = 9 →
    HasGoodRow 1 (198 * 256 + lo.val) → covered (198 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_199 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (199 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (199 * 256 + lo.val) = 9 →
    HasGoodRow 1 (199 * 256 + lo.val) → covered (199 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_200 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (200 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (200 * 256 + lo.val) = 9 →
    HasGoodRow 1 (200 * 256 + lo.val) → covered (200 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_201 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (201 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (201 * 256 + lo.val) = 9 →
    HasGoodRow 1 (201 * 256 + lo.val) → covered (201 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_202 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (202 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (202 * 256 + lo.val) = 9 →
    HasGoodRow 1 (202 * 256 + lo.val) → covered (202 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_203 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (203 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (203 * 256 + lo.val) = 9 →
    HasGoodRow 1 (203 * 256 + lo.val) → covered (203 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_204 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (204 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (204 * 256 + lo.val) = 9 →
    HasGoodRow 1 (204 * 256 + lo.val) → covered (204 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_205 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (205 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (205 * 256 + lo.val) = 9 →
    HasGoodRow 1 (205 * 256 + lo.val) → covered (205 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_206 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (206 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (206 * 256 + lo.val) = 9 →
    HasGoodRow 1 (206 * 256 + lo.val) → covered (206 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_207 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (207 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (207 * 256 + lo.val) = 9 →
    HasGoodRow 1 (207 * 256 + lo.val) → covered (207 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_208 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (208 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (208 * 256 + lo.val) = 9 →
    HasGoodRow 1 (208 * 256 + lo.val) → covered (208 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_209 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (209 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (209 * 256 + lo.val) = 9 →
    HasGoodRow 1 (209 * 256 + lo.val) → covered (209 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_210 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (210 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (210 * 256 + lo.val) = 9 →
    HasGoodRow 1 (210 * 256 + lo.val) → covered (210 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_211 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (211 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (211 * 256 + lo.val) = 9 →
    HasGoodRow 1 (211 * 256 + lo.val) → covered (211 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_212 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (212 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (212 * 256 + lo.val) = 9 →
    HasGoodRow 1 (212 * 256 + lo.val) → covered (212 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_213 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (213 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (213 * 256 + lo.val) = 9 →
    HasGoodRow 1 (213 * 256 + lo.val) → covered (213 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_214 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (214 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (214 * 256 + lo.val) = 9 →
    HasGoodRow 1 (214 * 256 + lo.val) → covered (214 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_215 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (215 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (215 * 256 + lo.val) = 9 →
    HasGoodRow 1 (215 * 256 + lo.val) → covered (215 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_216 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (216 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (216 * 256 + lo.val) = 9 →
    HasGoodRow 1 (216 * 256 + lo.val) → covered (216 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_217 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (217 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (217 * 256 + lo.val) = 9 →
    HasGoodRow 1 (217 * 256 + lo.val) → covered (217 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_218 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (218 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (218 * 256 + lo.val) = 9 →
    HasGoodRow 1 (218 * 256 + lo.val) → covered (218 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_219 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (219 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (219 * 256 + lo.val) = 9 →
    HasGoodRow 1 (219 * 256 + lo.val) → covered (219 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_220 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (220 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (220 * 256 + lo.val) = 9 →
    HasGoodRow 1 (220 * 256 + lo.val) → covered (220 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_221 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (221 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (221 * 256 + lo.val) = 9 →
    HasGoodRow 1 (221 * 256 + lo.val) → covered (221 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_222 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (222 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (222 * 256 + lo.val) = 9 →
    HasGoodRow 1 (222 * 256 + lo.val) → covered (222 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_223 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (223 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (223 * 256 + lo.val) = 9 →
    HasGoodRow 1 (223 * 256 + lo.val) → covered (223 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_224 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (224 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (224 * 256 + lo.val) = 9 →
    HasGoodRow 1 (224 * 256 + lo.val) → covered (224 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_225 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (225 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (225 * 256 + lo.val) = 9 →
    HasGoodRow 1 (225 * 256 + lo.val) → covered (225 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_226 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (226 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (226 * 256 + lo.val) = 9 →
    HasGoodRow 1 (226 * 256 + lo.val) → covered (226 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_227 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (227 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (227 * 256 + lo.val) = 9 →
    HasGoodRow 1 (227 * 256 + lo.val) → covered (227 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_228 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (228 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (228 * 256 + lo.val) = 9 →
    HasGoodRow 1 (228 * 256 + lo.val) → covered (228 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_229 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (229 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (229 * 256 + lo.val) = 9 →
    HasGoodRow 1 (229 * 256 + lo.val) → covered (229 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_230 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (230 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (230 * 256 + lo.val) = 9 →
    HasGoodRow 1 (230 * 256 + lo.val) → covered (230 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_231 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (231 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (231 * 256 + lo.val) = 9 →
    HasGoodRow 1 (231 * 256 + lo.val) → covered (231 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_232 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (232 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (232 * 256 + lo.val) = 9 →
    HasGoodRow 1 (232 * 256 + lo.val) → covered (232 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_233 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (233 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (233 * 256 + lo.val) = 9 →
    HasGoodRow 1 (233 * 256 + lo.val) → covered (233 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_234 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (234 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (234 * 256 + lo.val) = 9 →
    HasGoodRow 1 (234 * 256 + lo.val) → covered (234 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_235 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (235 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (235 * 256 + lo.val) = 9 →
    HasGoodRow 1 (235 * 256 + lo.val) → covered (235 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_236 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (236 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (236 * 256 + lo.val) = 9 →
    HasGoodRow 1 (236 * 256 + lo.val) → covered (236 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_237 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (237 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (237 * 256 + lo.val) = 9 →
    HasGoodRow 1 (237 * 256 + lo.val) → covered (237 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_238 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (238 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (238 * 256 + lo.val) = 9 →
    HasGoodRow 1 (238 * 256 + lo.val) → covered (238 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_239 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (239 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (239 * 256 + lo.val) = 9 →
    HasGoodRow 1 (239 * 256 + lo.val) → covered (239 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_240 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (240 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (240 * 256 + lo.val) = 9 →
    HasGoodRow 1 (240 * 256 + lo.val) → covered (240 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_241 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (241 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (241 * 256 + lo.val) = 9 →
    HasGoodRow 1 (241 * 256 + lo.val) → covered (241 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_242 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (242 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (242 * 256 + lo.val) = 9 →
    HasGoodRow 1 (242 * 256 + lo.val) → covered (242 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_243 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (243 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (243 * 256 + lo.val) = 9 →
    HasGoodRow 1 (243 * 256 + lo.val) → covered (243 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_244 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (244 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (244 * 256 + lo.val) = 9 →
    HasGoodRow 1 (244 * 256 + lo.val) → covered (244 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_245 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (245 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (245 * 256 + lo.val) = 9 →
    HasGoodRow 1 (245 * 256 + lo.val) → covered (245 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_246 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (246 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (246 * 256 + lo.val) = 9 →
    HasGoodRow 1 (246 * 256 + lo.val) → covered (246 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_247 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (247 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (247 * 256 + lo.val) = 9 →
    HasGoodRow 1 (247 * 256 + lo.val) → covered (247 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_248 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (248 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (248 * 256 + lo.val) = 9 →
    HasGoodRow 1 (248 * 256 + lo.val) → covered (248 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_249 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (249 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (249 * 256 + lo.val) = 9 →
    HasGoodRow 1 (249 * 256 + lo.val) → covered (249 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_250 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (250 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (250 * 256 + lo.val) = 9 →
    HasGoodRow 1 (250 * 256 + lo.val) → covered (250 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_251 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (251 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (251 * 256 + lo.val) = 9 →
    HasGoodRow 1 (251 * 256 + lo.val) → covered (251 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_252 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (252 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (252 * 256 + lo.val) = 9 →
    HasGoodRow 1 (252 * 256 + lo.val) → covered (252 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_253 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (253 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (253 * 256 + lo.val) = 9 →
    HasGoodRow 1 (253 * 256 + lo.val) → covered (253 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_254 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (254 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (254 * 256 + lo.val) = 9 →
    HasGoodRow 1 (254 * 256 + lo.val) → covered (254 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_255 : ∀ lo : Fin 256,
    DenseOutside.terminalCount (255 * 256 + lo.val) = 1 →
    DenseOutside.triangleCount (255 * 256 + lo.val) = 9 →
    HasGoodRow 1 (255 * 256 + lo.val) → covered (255 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_rows (hi lo : Fin 256)
    (hz : DenseOutside.terminalCount (hi.val * 256 + lo.val) = 1)
    (ht : DenseOutside.triangleCount (hi.val * 256 + lo.val) = 9)
    (hg : HasGoodRow 1 (hi.val * 256 + lo.val)) :
    covered (hi.val * 256 + lo.val) = true := by
  fin_cases hi
  · exact coverage_0 lo hz ht hg
  · exact coverage_1 lo hz ht hg
  · exact coverage_2 lo hz ht hg
  · exact coverage_3 lo hz ht hg
  · exact coverage_4 lo hz ht hg
  · exact coverage_5 lo hz ht hg
  · exact coverage_6 lo hz ht hg
  · exact coverage_7 lo hz ht hg
  · exact coverage_8 lo hz ht hg
  · exact coverage_9 lo hz ht hg
  · exact coverage_10 lo hz ht hg
  · exact coverage_11 lo hz ht hg
  · exact coverage_12 lo hz ht hg
  · exact coverage_13 lo hz ht hg
  · exact coverage_14 lo hz ht hg
  · exact coverage_15 lo hz ht hg
  · exact coverage_16 lo hz ht hg
  · exact coverage_17 lo hz ht hg
  · exact coverage_18 lo hz ht hg
  · exact coverage_19 lo hz ht hg
  · exact coverage_20 lo hz ht hg
  · exact coverage_21 lo hz ht hg
  · exact coverage_22 lo hz ht hg
  · exact coverage_23 lo hz ht hg
  · exact coverage_24 lo hz ht hg
  · exact coverage_25 lo hz ht hg
  · exact coverage_26 lo hz ht hg
  · exact coverage_27 lo hz ht hg
  · exact coverage_28 lo hz ht hg
  · exact coverage_29 lo hz ht hg
  · exact coverage_30 lo hz ht hg
  · exact coverage_31 lo hz ht hg
  · exact coverage_32 lo hz ht hg
  · exact coverage_33 lo hz ht hg
  · exact coverage_34 lo hz ht hg
  · exact coverage_35 lo hz ht hg
  · exact coverage_36 lo hz ht hg
  · exact coverage_37 lo hz ht hg
  · exact coverage_38 lo hz ht hg
  · exact coverage_39 lo hz ht hg
  · exact coverage_40 lo hz ht hg
  · exact coverage_41 lo hz ht hg
  · exact coverage_42 lo hz ht hg
  · exact coverage_43 lo hz ht hg
  · exact coverage_44 lo hz ht hg
  · exact coverage_45 lo hz ht hg
  · exact coverage_46 lo hz ht hg
  · exact coverage_47 lo hz ht hg
  · exact coverage_48 lo hz ht hg
  · exact coverage_49 lo hz ht hg
  · exact coverage_50 lo hz ht hg
  · exact coverage_51 lo hz ht hg
  · exact coverage_52 lo hz ht hg
  · exact coverage_53 lo hz ht hg
  · exact coverage_54 lo hz ht hg
  · exact coverage_55 lo hz ht hg
  · exact coverage_56 lo hz ht hg
  · exact coverage_57 lo hz ht hg
  · exact coverage_58 lo hz ht hg
  · exact coverage_59 lo hz ht hg
  · exact coverage_60 lo hz ht hg
  · exact coverage_61 lo hz ht hg
  · exact coverage_62 lo hz ht hg
  · exact coverage_63 lo hz ht hg
  · exact coverage_64 lo hz ht hg
  · exact coverage_65 lo hz ht hg
  · exact coverage_66 lo hz ht hg
  · exact coverage_67 lo hz ht hg
  · exact coverage_68 lo hz ht hg
  · exact coverage_69 lo hz ht hg
  · exact coverage_70 lo hz ht hg
  · exact coverage_71 lo hz ht hg
  · exact coverage_72 lo hz ht hg
  · exact coverage_73 lo hz ht hg
  · exact coverage_74 lo hz ht hg
  · exact coverage_75 lo hz ht hg
  · exact coverage_76 lo hz ht hg
  · exact coverage_77 lo hz ht hg
  · exact coverage_78 lo hz ht hg
  · exact coverage_79 lo hz ht hg
  · exact coverage_80 lo hz ht hg
  · exact coverage_81 lo hz ht hg
  · exact coverage_82 lo hz ht hg
  · exact coverage_83 lo hz ht hg
  · exact coverage_84 lo hz ht hg
  · exact coverage_85 lo hz ht hg
  · exact coverage_86 lo hz ht hg
  · exact coverage_87 lo hz ht hg
  · exact coverage_88 lo hz ht hg
  · exact coverage_89 lo hz ht hg
  · exact coverage_90 lo hz ht hg
  · exact coverage_91 lo hz ht hg
  · exact coverage_92 lo hz ht hg
  · exact coverage_93 lo hz ht hg
  · exact coverage_94 lo hz ht hg
  · exact coverage_95 lo hz ht hg
  · exact coverage_96 lo hz ht hg
  · exact coverage_97 lo hz ht hg
  · exact coverage_98 lo hz ht hg
  · exact coverage_99 lo hz ht hg
  · exact coverage_100 lo hz ht hg
  · exact coverage_101 lo hz ht hg
  · exact coverage_102 lo hz ht hg
  · exact coverage_103 lo hz ht hg
  · exact coverage_104 lo hz ht hg
  · exact coverage_105 lo hz ht hg
  · exact coverage_106 lo hz ht hg
  · exact coverage_107 lo hz ht hg
  · exact coverage_108 lo hz ht hg
  · exact coverage_109 lo hz ht hg
  · exact coverage_110 lo hz ht hg
  · exact coverage_111 lo hz ht hg
  · exact coverage_112 lo hz ht hg
  · exact coverage_113 lo hz ht hg
  · exact coverage_114 lo hz ht hg
  · exact coverage_115 lo hz ht hg
  · exact coverage_116 lo hz ht hg
  · exact coverage_117 lo hz ht hg
  · exact coverage_118 lo hz ht hg
  · exact coverage_119 lo hz ht hg
  · exact coverage_120 lo hz ht hg
  · exact coverage_121 lo hz ht hg
  · exact coverage_122 lo hz ht hg
  · exact coverage_123 lo hz ht hg
  · exact coverage_124 lo hz ht hg
  · exact coverage_125 lo hz ht hg
  · exact coverage_126 lo hz ht hg
  · exact coverage_127 lo hz ht hg
  · exact coverage_128 lo hz ht hg
  · exact coverage_129 lo hz ht hg
  · exact coverage_130 lo hz ht hg
  · exact coverage_131 lo hz ht hg
  · exact coverage_132 lo hz ht hg
  · exact coverage_133 lo hz ht hg
  · exact coverage_134 lo hz ht hg
  · exact coverage_135 lo hz ht hg
  · exact coverage_136 lo hz ht hg
  · exact coverage_137 lo hz ht hg
  · exact coverage_138 lo hz ht hg
  · exact coverage_139 lo hz ht hg
  · exact coverage_140 lo hz ht hg
  · exact coverage_141 lo hz ht hg
  · exact coverage_142 lo hz ht hg
  · exact coverage_143 lo hz ht hg
  · exact coverage_144 lo hz ht hg
  · exact coverage_145 lo hz ht hg
  · exact coverage_146 lo hz ht hg
  · exact coverage_147 lo hz ht hg
  · exact coverage_148 lo hz ht hg
  · exact coverage_149 lo hz ht hg
  · exact coverage_150 lo hz ht hg
  · exact coverage_151 lo hz ht hg
  · exact coverage_152 lo hz ht hg
  · exact coverage_153 lo hz ht hg
  · exact coverage_154 lo hz ht hg
  · exact coverage_155 lo hz ht hg
  · exact coverage_156 lo hz ht hg
  · exact coverage_157 lo hz ht hg
  · exact coverage_158 lo hz ht hg
  · exact coverage_159 lo hz ht hg
  · exact coverage_160 lo hz ht hg
  · exact coverage_161 lo hz ht hg
  · exact coverage_162 lo hz ht hg
  · exact coverage_163 lo hz ht hg
  · exact coverage_164 lo hz ht hg
  · exact coverage_165 lo hz ht hg
  · exact coverage_166 lo hz ht hg
  · exact coverage_167 lo hz ht hg
  · exact coverage_168 lo hz ht hg
  · exact coverage_169 lo hz ht hg
  · exact coverage_170 lo hz ht hg
  · exact coverage_171 lo hz ht hg
  · exact coverage_172 lo hz ht hg
  · exact coverage_173 lo hz ht hg
  · exact coverage_174 lo hz ht hg
  · exact coverage_175 lo hz ht hg
  · exact coverage_176 lo hz ht hg
  · exact coverage_177 lo hz ht hg
  · exact coverage_178 lo hz ht hg
  · exact coverage_179 lo hz ht hg
  · exact coverage_180 lo hz ht hg
  · exact coverage_181 lo hz ht hg
  · exact coverage_182 lo hz ht hg
  · exact coverage_183 lo hz ht hg
  · exact coverage_184 lo hz ht hg
  · exact coverage_185 lo hz ht hg
  · exact coverage_186 lo hz ht hg
  · exact coverage_187 lo hz ht hg
  · exact coverage_188 lo hz ht hg
  · exact coverage_189 lo hz ht hg
  · exact coverage_190 lo hz ht hg
  · exact coverage_191 lo hz ht hg
  · exact coverage_192 lo hz ht hg
  · exact coverage_193 lo hz ht hg
  · exact coverage_194 lo hz ht hg
  · exact coverage_195 lo hz ht hg
  · exact coverage_196 lo hz ht hg
  · exact coverage_197 lo hz ht hg
  · exact coverage_198 lo hz ht hg
  · exact coverage_199 lo hz ht hg
  · exact coverage_200 lo hz ht hg
  · exact coverage_201 lo hz ht hg
  · exact coverage_202 lo hz ht hg
  · exact coverage_203 lo hz ht hg
  · exact coverage_204 lo hz ht hg
  · exact coverage_205 lo hz ht hg
  · exact coverage_206 lo hz ht hg
  · exact coverage_207 lo hz ht hg
  · exact coverage_208 lo hz ht hg
  · exact coverage_209 lo hz ht hg
  · exact coverage_210 lo hz ht hg
  · exact coverage_211 lo hz ht hg
  · exact coverage_212 lo hz ht hg
  · exact coverage_213 lo hz ht hg
  · exact coverage_214 lo hz ht hg
  · exact coverage_215 lo hz ht hg
  · exact coverage_216 lo hz ht hg
  · exact coverage_217 lo hz ht hg
  · exact coverage_218 lo hz ht hg
  · exact coverage_219 lo hz ht hg
  · exact coverage_220 lo hz ht hg
  · exact coverage_221 lo hz ht hg
  · exact coverage_222 lo hz ht hg
  · exact coverage_223 lo hz ht hg
  · exact coverage_224 lo hz ht hg
  · exact coverage_225 lo hz ht hg
  · exact coverage_226 lo hz ht hg
  · exact coverage_227 lo hz ht hg
  · exact coverage_228 lo hz ht hg
  · exact coverage_229 lo hz ht hg
  · exact coverage_230 lo hz ht hg
  · exact coverage_231 lo hz ht hg
  · exact coverage_232 lo hz ht hg
  · exact coverage_233 lo hz ht hg
  · exact coverage_234 lo hz ht hg
  · exact coverage_235 lo hz ht hg
  · exact coverage_236 lo hz ht hg
  · exact coverage_237 lo hz ht hg
  · exact coverage_238 lo hz ht hg
  · exact coverage_239 lo hz ht hg
  · exact coverage_240 lo hz ht hg
  · exact coverage_241 lo hz ht hg
  · exact coverage_242 lo hz ht hg
  · exact coverage_243 lo hz ht hg
  · exact coverage_244 lo hz ht hg
  · exact coverage_245 lo hz ht hg
  · exact coverage_246 lo hz ht hg
  · exact coverage_247 lo hz ht hg
  · exact coverage_248 lo hz ht hg
  · exact coverage_249 lo hz ht hg
  · exact coverage_250 lo hz ht hg
  · exact coverage_251 lo hz ht hg
  · exact coverage_252 lo hz ht hg
  · exact coverage_253 lo hz ht hg
  · exact coverage_254 lo hz ht hg
  · exact coverage_255 lo hz ht hg

theorem coverage (m : Fin 65536) (hz : DenseOutside.terminalCount m.val = 1)
    (ht : DenseOutside.triangleCount m.val = 9) (hg : HasGoodRow 1 m.val) :
    covered m.val = true := by
  let hi : Fin 256 := ⟨m.val / 256, by omega⟩
  let lo : Fin 256 := ⟨m.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : hi.val * 256 + lo.val = m.val := by dsimp [hi, lo]; omega
  rw [← he] at hz ht hg ⊢
  exact coverage_rows hi lo hz ht hg

end Erdos577.PawNine.D1
