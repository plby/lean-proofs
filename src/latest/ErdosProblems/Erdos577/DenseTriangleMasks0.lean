import ErdosProblems.Erdos577.DenseTriangleModel

/-! Kernel-checked ten-contact coverage for diagonal mask 0. -/

namespace Erdos577.DenseTriangle.D0

def masks : List ℕ := [
  4576, 5056, 5776, 6496, 7216, 7696, 8912, 9152,
  9872, 10592, 11312, 11552, 12736, 12992, 13504, 14528,
  15376, 15392, 15424, 15488, 17344, 17584, 18064, 18784,
  19264, 19504, 24976, 25232, 25744, 26768, 26896, 26912,
  26944, 27008, 30848, 33728, 34448, 34688, 34928, 35168,
  35888, 37216, 37472, 37984, 38416, 38432, 38464, 38528,
  39008, 46144, 49456, 49712, 49936, 49952, 49984, 50048,
  50224, 51248, 53792, 57616]

def covered (m : ℕ) : Bool := masks.any fun w ↦ m &&& w == w

private theorem coverage_0 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (0 * 256 + lo.val) →
    (covered (0 * 256 + lo.val) ||
      decide (DiamondRows 0 (0 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_1 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (1 * 256 + lo.val) →
    (covered (1 * 256 + lo.val) ||
      decide (DiamondRows 0 (1 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_2 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (2 * 256 + lo.val) →
    (covered (2 * 256 + lo.val) ||
      decide (DiamondRows 0 (2 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_3 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (3 * 256 + lo.val) →
    (covered (3 * 256 + lo.val) ||
      decide (DiamondRows 0 (3 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_4 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (4 * 256 + lo.val) →
    (covered (4 * 256 + lo.val) ||
      decide (DiamondRows 0 (4 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_5 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (5 * 256 + lo.val) →
    (covered (5 * 256 + lo.val) ||
      decide (DiamondRows 0 (5 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_6 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (6 * 256 + lo.val) →
    (covered (6 * 256 + lo.val) ||
      decide (DiamondRows 0 (6 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_7 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (7 * 256 + lo.val) →
    (covered (7 * 256 + lo.val) ||
      decide (DiamondRows 0 (7 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_8 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (8 * 256 + lo.val) →
    (covered (8 * 256 + lo.val) ||
      decide (DiamondRows 0 (8 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_9 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (9 * 256 + lo.val) →
    (covered (9 * 256 + lo.val) ||
      decide (DiamondRows 0 (9 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_10 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (10 * 256 + lo.val) →
    (covered (10 * 256 + lo.val) ||
      decide (DiamondRows 0 (10 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_11 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (11 * 256 + lo.val) →
    (covered (11 * 256 + lo.val) ||
      decide (DiamondRows 0 (11 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_12 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (12 * 256 + lo.val) →
    (covered (12 * 256 + lo.val) ||
      decide (DiamondRows 0 (12 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_13 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (13 * 256 + lo.val) →
    (covered (13 * 256 + lo.val) ||
      decide (DiamondRows 0 (13 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_14 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (14 * 256 + lo.val) →
    (covered (14 * 256 + lo.val) ||
      decide (DiamondRows 0 (14 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_15 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (15 * 256 + lo.val) →
    (covered (15 * 256 + lo.val) ||
      decide (DiamondRows 0 (15 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_16 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (16 * 256 + lo.val) →
    (covered (16 * 256 + lo.val) ||
      decide (DiamondRows 0 (16 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_17 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (17 * 256 + lo.val) →
    (covered (17 * 256 + lo.val) ||
      decide (DiamondRows 0 (17 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_18 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (18 * 256 + lo.val) →
    (covered (18 * 256 + lo.val) ||
      decide (DiamondRows 0 (18 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_19 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (19 * 256 + lo.val) →
    (covered (19 * 256 + lo.val) ||
      decide (DiamondRows 0 (19 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_20 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (20 * 256 + lo.val) →
    (covered (20 * 256 + lo.val) ||
      decide (DiamondRows 0 (20 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_21 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (21 * 256 + lo.val) →
    (covered (21 * 256 + lo.val) ||
      decide (DiamondRows 0 (21 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_22 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (22 * 256 + lo.val) →
    (covered (22 * 256 + lo.val) ||
      decide (DiamondRows 0 (22 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_23 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (23 * 256 + lo.val) →
    (covered (23 * 256 + lo.val) ||
      decide (DiamondRows 0 (23 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_24 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (24 * 256 + lo.val) →
    (covered (24 * 256 + lo.val) ||
      decide (DiamondRows 0 (24 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_25 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (25 * 256 + lo.val) →
    (covered (25 * 256 + lo.val) ||
      decide (DiamondRows 0 (25 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_26 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (26 * 256 + lo.val) →
    (covered (26 * 256 + lo.val) ||
      decide (DiamondRows 0 (26 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_27 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (27 * 256 + lo.val) →
    (covered (27 * 256 + lo.val) ||
      decide (DiamondRows 0 (27 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_28 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (28 * 256 + lo.val) →
    (covered (28 * 256 + lo.val) ||
      decide (DiamondRows 0 (28 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_29 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (29 * 256 + lo.val) →
    (covered (29 * 256 + lo.val) ||
      decide (DiamondRows 0 (29 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_30 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (30 * 256 + lo.val) →
    (covered (30 * 256 + lo.val) ||
      decide (DiamondRows 0 (30 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_31 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (31 * 256 + lo.val) →
    (covered (31 * 256 + lo.val) ||
      decide (DiamondRows 0 (31 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_32 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (32 * 256 + lo.val) →
    (covered (32 * 256 + lo.val) ||
      decide (DiamondRows 0 (32 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_33 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (33 * 256 + lo.val) →
    (covered (33 * 256 + lo.val) ||
      decide (DiamondRows 0 (33 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_34 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (34 * 256 + lo.val) →
    (covered (34 * 256 + lo.val) ||
      decide (DiamondRows 0 (34 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_35 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (35 * 256 + lo.val) →
    (covered (35 * 256 + lo.val) ||
      decide (DiamondRows 0 (35 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_36 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (36 * 256 + lo.val) →
    (covered (36 * 256 + lo.val) ||
      decide (DiamondRows 0 (36 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_37 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (37 * 256 + lo.val) →
    (covered (37 * 256 + lo.val) ||
      decide (DiamondRows 0 (37 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_38 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (38 * 256 + lo.val) →
    (covered (38 * 256 + lo.val) ||
      decide (DiamondRows 0 (38 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_39 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (39 * 256 + lo.val) →
    (covered (39 * 256 + lo.val) ||
      decide (DiamondRows 0 (39 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_40 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (40 * 256 + lo.val) →
    (covered (40 * 256 + lo.val) ||
      decide (DiamondRows 0 (40 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_41 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (41 * 256 + lo.val) →
    (covered (41 * 256 + lo.val) ||
      decide (DiamondRows 0 (41 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_42 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (42 * 256 + lo.val) →
    (covered (42 * 256 + lo.val) ||
      decide (DiamondRows 0 (42 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_43 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (43 * 256 + lo.val) →
    (covered (43 * 256 + lo.val) ||
      decide (DiamondRows 0 (43 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_44 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (44 * 256 + lo.val) →
    (covered (44 * 256 + lo.val) ||
      decide (DiamondRows 0 (44 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_45 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (45 * 256 + lo.val) →
    (covered (45 * 256 + lo.val) ||
      decide (DiamondRows 0 (45 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_46 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (46 * 256 + lo.val) →
    (covered (46 * 256 + lo.val) ||
      decide (DiamondRows 0 (46 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_47 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (47 * 256 + lo.val) →
    (covered (47 * 256 + lo.val) ||
      decide (DiamondRows 0 (47 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_48 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (48 * 256 + lo.val) →
    (covered (48 * 256 + lo.val) ||
      decide (DiamondRows 0 (48 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_49 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (49 * 256 + lo.val) →
    (covered (49 * 256 + lo.val) ||
      decide (DiamondRows 0 (49 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_50 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (50 * 256 + lo.val) →
    (covered (50 * 256 + lo.val) ||
      decide (DiamondRows 0 (50 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_51 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (51 * 256 + lo.val) →
    (covered (51 * 256 + lo.val) ||
      decide (DiamondRows 0 (51 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_52 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (52 * 256 + lo.val) →
    (covered (52 * 256 + lo.val) ||
      decide (DiamondRows 0 (52 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_53 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (53 * 256 + lo.val) →
    (covered (53 * 256 + lo.val) ||
      decide (DiamondRows 0 (53 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_54 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (54 * 256 + lo.val) →
    (covered (54 * 256 + lo.val) ||
      decide (DiamondRows 0 (54 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_55 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (55 * 256 + lo.val) →
    (covered (55 * 256 + lo.val) ||
      decide (DiamondRows 0 (55 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_56 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (56 * 256 + lo.val) →
    (covered (56 * 256 + lo.val) ||
      decide (DiamondRows 0 (56 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_57 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (57 * 256 + lo.val) →
    (covered (57 * 256 + lo.val) ||
      decide (DiamondRows 0 (57 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_58 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (58 * 256 + lo.val) →
    (covered (58 * 256 + lo.val) ||
      decide (DiamondRows 0 (58 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_59 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (59 * 256 + lo.val) →
    (covered (59 * 256 + lo.val) ||
      decide (DiamondRows 0 (59 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_60 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (60 * 256 + lo.val) →
    (covered (60 * 256 + lo.val) ||
      decide (DiamondRows 0 (60 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_61 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (61 * 256 + lo.val) →
    (covered (61 * 256 + lo.val) ||
      decide (DiamondRows 0 (61 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_62 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (62 * 256 + lo.val) →
    (covered (62 * 256 + lo.val) ||
      decide (DiamondRows 0 (62 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_63 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (63 * 256 + lo.val) →
    (covered (63 * 256 + lo.val) ||
      decide (DiamondRows 0 (63 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_64 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (64 * 256 + lo.val) →
    (covered (64 * 256 + lo.val) ||
      decide (DiamondRows 0 (64 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_65 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (65 * 256 + lo.val) →
    (covered (65 * 256 + lo.val) ||
      decide (DiamondRows 0 (65 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_66 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (66 * 256 + lo.val) →
    (covered (66 * 256 + lo.val) ||
      decide (DiamondRows 0 (66 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_67 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (67 * 256 + lo.val) →
    (covered (67 * 256 + lo.val) ||
      decide (DiamondRows 0 (67 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_68 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (68 * 256 + lo.val) →
    (covered (68 * 256 + lo.val) ||
      decide (DiamondRows 0 (68 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_69 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (69 * 256 + lo.val) →
    (covered (69 * 256 + lo.val) ||
      decide (DiamondRows 0 (69 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_70 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (70 * 256 + lo.val) →
    (covered (70 * 256 + lo.val) ||
      decide (DiamondRows 0 (70 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_71 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (71 * 256 + lo.val) →
    (covered (71 * 256 + lo.val) ||
      decide (DiamondRows 0 (71 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_72 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (72 * 256 + lo.val) →
    (covered (72 * 256 + lo.val) ||
      decide (DiamondRows 0 (72 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_73 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (73 * 256 + lo.val) →
    (covered (73 * 256 + lo.val) ||
      decide (DiamondRows 0 (73 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_74 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (74 * 256 + lo.val) →
    (covered (74 * 256 + lo.val) ||
      decide (DiamondRows 0 (74 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_75 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (75 * 256 + lo.val) →
    (covered (75 * 256 + lo.val) ||
      decide (DiamondRows 0 (75 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_76 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (76 * 256 + lo.val) →
    (covered (76 * 256 + lo.val) ||
      decide (DiamondRows 0 (76 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_77 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (77 * 256 + lo.val) →
    (covered (77 * 256 + lo.val) ||
      decide (DiamondRows 0 (77 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_78 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (78 * 256 + lo.val) →
    (covered (78 * 256 + lo.val) ||
      decide (DiamondRows 0 (78 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_79 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (79 * 256 + lo.val) →
    (covered (79 * 256 + lo.val) ||
      decide (DiamondRows 0 (79 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_80 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (80 * 256 + lo.val) →
    (covered (80 * 256 + lo.val) ||
      decide (DiamondRows 0 (80 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_81 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (81 * 256 + lo.val) →
    (covered (81 * 256 + lo.val) ||
      decide (DiamondRows 0 (81 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_82 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (82 * 256 + lo.val) →
    (covered (82 * 256 + lo.val) ||
      decide (DiamondRows 0 (82 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_83 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (83 * 256 + lo.val) →
    (covered (83 * 256 + lo.val) ||
      decide (DiamondRows 0 (83 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_84 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (84 * 256 + lo.val) →
    (covered (84 * 256 + lo.val) ||
      decide (DiamondRows 0 (84 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_85 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (85 * 256 + lo.val) →
    (covered (85 * 256 + lo.val) ||
      decide (DiamondRows 0 (85 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_86 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (86 * 256 + lo.val) →
    (covered (86 * 256 + lo.val) ||
      decide (DiamondRows 0 (86 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_87 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (87 * 256 + lo.val) →
    (covered (87 * 256 + lo.val) ||
      decide (DiamondRows 0 (87 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_88 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (88 * 256 + lo.val) →
    (covered (88 * 256 + lo.val) ||
      decide (DiamondRows 0 (88 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_89 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (89 * 256 + lo.val) →
    (covered (89 * 256 + lo.val) ||
      decide (DiamondRows 0 (89 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_90 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (90 * 256 + lo.val) →
    (covered (90 * 256 + lo.val) ||
      decide (DiamondRows 0 (90 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_91 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (91 * 256 + lo.val) →
    (covered (91 * 256 + lo.val) ||
      decide (DiamondRows 0 (91 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_92 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (92 * 256 + lo.val) →
    (covered (92 * 256 + lo.val) ||
      decide (DiamondRows 0 (92 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_93 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (93 * 256 + lo.val) →
    (covered (93 * 256 + lo.val) ||
      decide (DiamondRows 0 (93 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_94 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (94 * 256 + lo.val) →
    (covered (94 * 256 + lo.val) ||
      decide (DiamondRows 0 (94 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_95 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (95 * 256 + lo.val) →
    (covered (95 * 256 + lo.val) ||
      decide (DiamondRows 0 (95 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_96 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (96 * 256 + lo.val) →
    (covered (96 * 256 + lo.val) ||
      decide (DiamondRows 0 (96 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_97 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (97 * 256 + lo.val) →
    (covered (97 * 256 + lo.val) ||
      decide (DiamondRows 0 (97 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_98 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (98 * 256 + lo.val) →
    (covered (98 * 256 + lo.val) ||
      decide (DiamondRows 0 (98 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_99 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (99 * 256 + lo.val) →
    (covered (99 * 256 + lo.val) ||
      decide (DiamondRows 0 (99 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_100 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (100 * 256 + lo.val) →
    (covered (100 * 256 + lo.val) ||
      decide (DiamondRows 0 (100 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_101 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (101 * 256 + lo.val) →
    (covered (101 * 256 + lo.val) ||
      decide (DiamondRows 0 (101 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_102 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (102 * 256 + lo.val) →
    (covered (102 * 256 + lo.val) ||
      decide (DiamondRows 0 (102 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_103 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (103 * 256 + lo.val) →
    (covered (103 * 256 + lo.val) ||
      decide (DiamondRows 0 (103 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_104 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (104 * 256 + lo.val) →
    (covered (104 * 256 + lo.val) ||
      decide (DiamondRows 0 (104 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_105 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (105 * 256 + lo.val) →
    (covered (105 * 256 + lo.val) ||
      decide (DiamondRows 0 (105 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_106 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (106 * 256 + lo.val) →
    (covered (106 * 256 + lo.val) ||
      decide (DiamondRows 0 (106 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_107 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (107 * 256 + lo.val) →
    (covered (107 * 256 + lo.val) ||
      decide (DiamondRows 0 (107 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_108 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (108 * 256 + lo.val) →
    (covered (108 * 256 + lo.val) ||
      decide (DiamondRows 0 (108 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_109 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (109 * 256 + lo.val) →
    (covered (109 * 256 + lo.val) ||
      decide (DiamondRows 0 (109 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_110 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (110 * 256 + lo.val) →
    (covered (110 * 256 + lo.val) ||
      decide (DiamondRows 0 (110 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_111 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (111 * 256 + lo.val) →
    (covered (111 * 256 + lo.val) ||
      decide (DiamondRows 0 (111 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_112 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (112 * 256 + lo.val) →
    (covered (112 * 256 + lo.val) ||
      decide (DiamondRows 0 (112 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_113 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (113 * 256 + lo.val) →
    (covered (113 * 256 + lo.val) ||
      decide (DiamondRows 0 (113 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_114 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (114 * 256 + lo.val) →
    (covered (114 * 256 + lo.val) ||
      decide (DiamondRows 0 (114 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_115 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (115 * 256 + lo.val) →
    (covered (115 * 256 + lo.val) ||
      decide (DiamondRows 0 (115 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_116 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (116 * 256 + lo.val) →
    (covered (116 * 256 + lo.val) ||
      decide (DiamondRows 0 (116 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_117 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (117 * 256 + lo.val) →
    (covered (117 * 256 + lo.val) ||
      decide (DiamondRows 0 (117 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_118 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (118 * 256 + lo.val) →
    (covered (118 * 256 + lo.val) ||
      decide (DiamondRows 0 (118 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_119 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (119 * 256 + lo.val) →
    (covered (119 * 256 + lo.val) ||
      decide (DiamondRows 0 (119 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_120 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (120 * 256 + lo.val) →
    (covered (120 * 256 + lo.val) ||
      decide (DiamondRows 0 (120 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_121 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (121 * 256 + lo.val) →
    (covered (121 * 256 + lo.val) ||
      decide (DiamondRows 0 (121 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_122 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (122 * 256 + lo.val) →
    (covered (122 * 256 + lo.val) ||
      decide (DiamondRows 0 (122 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_123 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (123 * 256 + lo.val) →
    (covered (123 * 256 + lo.val) ||
      decide (DiamondRows 0 (123 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_124 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (124 * 256 + lo.val) →
    (covered (124 * 256 + lo.val) ||
      decide (DiamondRows 0 (124 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_125 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (125 * 256 + lo.val) →
    (covered (125 * 256 + lo.val) ||
      decide (DiamondRows 0 (125 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_126 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (126 * 256 + lo.val) →
    (covered (126 * 256 + lo.val) ||
      decide (DiamondRows 0 (126 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_127 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (127 * 256 + lo.val) →
    (covered (127 * 256 + lo.val) ||
      decide (DiamondRows 0 (127 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_128 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (128 * 256 + lo.val) →
    (covered (128 * 256 + lo.val) ||
      decide (DiamondRows 0 (128 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_129 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (129 * 256 + lo.val) →
    (covered (129 * 256 + lo.val) ||
      decide (DiamondRows 0 (129 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_130 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (130 * 256 + lo.val) →
    (covered (130 * 256 + lo.val) ||
      decide (DiamondRows 0 (130 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_131 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (131 * 256 + lo.val) →
    (covered (131 * 256 + lo.val) ||
      decide (DiamondRows 0 (131 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_132 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (132 * 256 + lo.val) →
    (covered (132 * 256 + lo.val) ||
      decide (DiamondRows 0 (132 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_133 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (133 * 256 + lo.val) →
    (covered (133 * 256 + lo.val) ||
      decide (DiamondRows 0 (133 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_134 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (134 * 256 + lo.val) →
    (covered (134 * 256 + lo.val) ||
      decide (DiamondRows 0 (134 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_135 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (135 * 256 + lo.val) →
    (covered (135 * 256 + lo.val) ||
      decide (DiamondRows 0 (135 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_136 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (136 * 256 + lo.val) →
    (covered (136 * 256 + lo.val) ||
      decide (DiamondRows 0 (136 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_137 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (137 * 256 + lo.val) →
    (covered (137 * 256 + lo.val) ||
      decide (DiamondRows 0 (137 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_138 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (138 * 256 + lo.val) →
    (covered (138 * 256 + lo.val) ||
      decide (DiamondRows 0 (138 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_139 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (139 * 256 + lo.val) →
    (covered (139 * 256 + lo.val) ||
      decide (DiamondRows 0 (139 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_140 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (140 * 256 + lo.val) →
    (covered (140 * 256 + lo.val) ||
      decide (DiamondRows 0 (140 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_141 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (141 * 256 + lo.val) →
    (covered (141 * 256 + lo.val) ||
      decide (DiamondRows 0 (141 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_142 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (142 * 256 + lo.val) →
    (covered (142 * 256 + lo.val) ||
      decide (DiamondRows 0 (142 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_143 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (143 * 256 + lo.val) →
    (covered (143 * 256 + lo.val) ||
      decide (DiamondRows 0 (143 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_144 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (144 * 256 + lo.val) →
    (covered (144 * 256 + lo.val) ||
      decide (DiamondRows 0 (144 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_145 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (145 * 256 + lo.val) →
    (covered (145 * 256 + lo.val) ||
      decide (DiamondRows 0 (145 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_146 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (146 * 256 + lo.val) →
    (covered (146 * 256 + lo.val) ||
      decide (DiamondRows 0 (146 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_147 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (147 * 256 + lo.val) →
    (covered (147 * 256 + lo.val) ||
      decide (DiamondRows 0 (147 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_148 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (148 * 256 + lo.val) →
    (covered (148 * 256 + lo.val) ||
      decide (DiamondRows 0 (148 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_149 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (149 * 256 + lo.val) →
    (covered (149 * 256 + lo.val) ||
      decide (DiamondRows 0 (149 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_150 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (150 * 256 + lo.val) →
    (covered (150 * 256 + lo.val) ||
      decide (DiamondRows 0 (150 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_151 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (151 * 256 + lo.val) →
    (covered (151 * 256 + lo.val) ||
      decide (DiamondRows 0 (151 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_152 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (152 * 256 + lo.val) →
    (covered (152 * 256 + lo.val) ||
      decide (DiamondRows 0 (152 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_153 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (153 * 256 + lo.val) →
    (covered (153 * 256 + lo.val) ||
      decide (DiamondRows 0 (153 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_154 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (154 * 256 + lo.val) →
    (covered (154 * 256 + lo.val) ||
      decide (DiamondRows 0 (154 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_155 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (155 * 256 + lo.val) →
    (covered (155 * 256 + lo.val) ||
      decide (DiamondRows 0 (155 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_156 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (156 * 256 + lo.val) →
    (covered (156 * 256 + lo.val) ||
      decide (DiamondRows 0 (156 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_157 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (157 * 256 + lo.val) →
    (covered (157 * 256 + lo.val) ||
      decide (DiamondRows 0 (157 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_158 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (158 * 256 + lo.val) →
    (covered (158 * 256 + lo.val) ||
      decide (DiamondRows 0 (158 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_159 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (159 * 256 + lo.val) →
    (covered (159 * 256 + lo.val) ||
      decide (DiamondRows 0 (159 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_160 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (160 * 256 + lo.val) →
    (covered (160 * 256 + lo.val) ||
      decide (DiamondRows 0 (160 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_161 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (161 * 256 + lo.val) →
    (covered (161 * 256 + lo.val) ||
      decide (DiamondRows 0 (161 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_162 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (162 * 256 + lo.val) →
    (covered (162 * 256 + lo.val) ||
      decide (DiamondRows 0 (162 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_163 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (163 * 256 + lo.val) →
    (covered (163 * 256 + lo.val) ||
      decide (DiamondRows 0 (163 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_164 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (164 * 256 + lo.val) →
    (covered (164 * 256 + lo.val) ||
      decide (DiamondRows 0 (164 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_165 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (165 * 256 + lo.val) →
    (covered (165 * 256 + lo.val) ||
      decide (DiamondRows 0 (165 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_166 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (166 * 256 + lo.val) →
    (covered (166 * 256 + lo.val) ||
      decide (DiamondRows 0 (166 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_167 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (167 * 256 + lo.val) →
    (covered (167 * 256 + lo.val) ||
      decide (DiamondRows 0 (167 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_168 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (168 * 256 + lo.val) →
    (covered (168 * 256 + lo.val) ||
      decide (DiamondRows 0 (168 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_169 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (169 * 256 + lo.val) →
    (covered (169 * 256 + lo.val) ||
      decide (DiamondRows 0 (169 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_170 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (170 * 256 + lo.val) →
    (covered (170 * 256 + lo.val) ||
      decide (DiamondRows 0 (170 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_171 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (171 * 256 + lo.val) →
    (covered (171 * 256 + lo.val) ||
      decide (DiamondRows 0 (171 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_172 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (172 * 256 + lo.val) →
    (covered (172 * 256 + lo.val) ||
      decide (DiamondRows 0 (172 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_173 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (173 * 256 + lo.val) →
    (covered (173 * 256 + lo.val) ||
      decide (DiamondRows 0 (173 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_174 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (174 * 256 + lo.val) →
    (covered (174 * 256 + lo.val) ||
      decide (DiamondRows 0 (174 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_175 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (175 * 256 + lo.val) →
    (covered (175 * 256 + lo.val) ||
      decide (DiamondRows 0 (175 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_176 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (176 * 256 + lo.val) →
    (covered (176 * 256 + lo.val) ||
      decide (DiamondRows 0 (176 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_177 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (177 * 256 + lo.val) →
    (covered (177 * 256 + lo.val) ||
      decide (DiamondRows 0 (177 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_178 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (178 * 256 + lo.val) →
    (covered (178 * 256 + lo.val) ||
      decide (DiamondRows 0 (178 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_179 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (179 * 256 + lo.val) →
    (covered (179 * 256 + lo.val) ||
      decide (DiamondRows 0 (179 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_180 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (180 * 256 + lo.val) →
    (covered (180 * 256 + lo.val) ||
      decide (DiamondRows 0 (180 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_181 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (181 * 256 + lo.val) →
    (covered (181 * 256 + lo.val) ||
      decide (DiamondRows 0 (181 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_182 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (182 * 256 + lo.val) →
    (covered (182 * 256 + lo.val) ||
      decide (DiamondRows 0 (182 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_183 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (183 * 256 + lo.val) →
    (covered (183 * 256 + lo.val) ||
      decide (DiamondRows 0 (183 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_184 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (184 * 256 + lo.val) →
    (covered (184 * 256 + lo.val) ||
      decide (DiamondRows 0 (184 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_185 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (185 * 256 + lo.val) →
    (covered (185 * 256 + lo.val) ||
      decide (DiamondRows 0 (185 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_186 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (186 * 256 + lo.val) →
    (covered (186 * 256 + lo.val) ||
      decide (DiamondRows 0 (186 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_187 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (187 * 256 + lo.val) →
    (covered (187 * 256 + lo.val) ||
      decide (DiamondRows 0 (187 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_188 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (188 * 256 + lo.val) →
    (covered (188 * 256 + lo.val) ||
      decide (DiamondRows 0 (188 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_189 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (189 * 256 + lo.val) →
    (covered (189 * 256 + lo.val) ||
      decide (DiamondRows 0 (189 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_190 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (190 * 256 + lo.val) →
    (covered (190 * 256 + lo.val) ||
      decide (DiamondRows 0 (190 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_191 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (191 * 256 + lo.val) →
    (covered (191 * 256 + lo.val) ||
      decide (DiamondRows 0 (191 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_192 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (192 * 256 + lo.val) →
    (covered (192 * 256 + lo.val) ||
      decide (DiamondRows 0 (192 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_193 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (193 * 256 + lo.val) →
    (covered (193 * 256 + lo.val) ||
      decide (DiamondRows 0 (193 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_194 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (194 * 256 + lo.val) →
    (covered (194 * 256 + lo.val) ||
      decide (DiamondRows 0 (194 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_195 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (195 * 256 + lo.val) →
    (covered (195 * 256 + lo.val) ||
      decide (DiamondRows 0 (195 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_196 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (196 * 256 + lo.val) →
    (covered (196 * 256 + lo.val) ||
      decide (DiamondRows 0 (196 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_197 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (197 * 256 + lo.val) →
    (covered (197 * 256 + lo.val) ||
      decide (DiamondRows 0 (197 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_198 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (198 * 256 + lo.val) →
    (covered (198 * 256 + lo.val) ||
      decide (DiamondRows 0 (198 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_199 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (199 * 256 + lo.val) →
    (covered (199 * 256 + lo.val) ||
      decide (DiamondRows 0 (199 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_200 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (200 * 256 + lo.val) →
    (covered (200 * 256 + lo.val) ||
      decide (DiamondRows 0 (200 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_201 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (201 * 256 + lo.val) →
    (covered (201 * 256 + lo.val) ||
      decide (DiamondRows 0 (201 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_202 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (202 * 256 + lo.val) →
    (covered (202 * 256 + lo.val) ||
      decide (DiamondRows 0 (202 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_203 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (203 * 256 + lo.val) →
    (covered (203 * 256 + lo.val) ||
      decide (DiamondRows 0 (203 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_204 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (204 * 256 + lo.val) →
    (covered (204 * 256 + lo.val) ||
      decide (DiamondRows 0 (204 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_205 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (205 * 256 + lo.val) →
    (covered (205 * 256 + lo.val) ||
      decide (DiamondRows 0 (205 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_206 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (206 * 256 + lo.val) →
    (covered (206 * 256 + lo.val) ||
      decide (DiamondRows 0 (206 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_207 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (207 * 256 + lo.val) →
    (covered (207 * 256 + lo.val) ||
      decide (DiamondRows 0 (207 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_208 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (208 * 256 + lo.val) →
    (covered (208 * 256 + lo.val) ||
      decide (DiamondRows 0 (208 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_209 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (209 * 256 + lo.val) →
    (covered (209 * 256 + lo.val) ||
      decide (DiamondRows 0 (209 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_210 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (210 * 256 + lo.val) →
    (covered (210 * 256 + lo.val) ||
      decide (DiamondRows 0 (210 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_211 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (211 * 256 + lo.val) →
    (covered (211 * 256 + lo.val) ||
      decide (DiamondRows 0 (211 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_212 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (212 * 256 + lo.val) →
    (covered (212 * 256 + lo.val) ||
      decide (DiamondRows 0 (212 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_213 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (213 * 256 + lo.val) →
    (covered (213 * 256 + lo.val) ||
      decide (DiamondRows 0 (213 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_214 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (214 * 256 + lo.val) →
    (covered (214 * 256 + lo.val) ||
      decide (DiamondRows 0 (214 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_215 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (215 * 256 + lo.val) →
    (covered (215 * 256 + lo.val) ||
      decide (DiamondRows 0 (215 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_216 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (216 * 256 + lo.val) →
    (covered (216 * 256 + lo.val) ||
      decide (DiamondRows 0 (216 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_217 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (217 * 256 + lo.val) →
    (covered (217 * 256 + lo.val) ||
      decide (DiamondRows 0 (217 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_218 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (218 * 256 + lo.val) →
    (covered (218 * 256 + lo.val) ||
      decide (DiamondRows 0 (218 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_219 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (219 * 256 + lo.val) →
    (covered (219 * 256 + lo.val) ||
      decide (DiamondRows 0 (219 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_220 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (220 * 256 + lo.val) →
    (covered (220 * 256 + lo.val) ||
      decide (DiamondRows 0 (220 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_221 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (221 * 256 + lo.val) →
    (covered (221 * 256 + lo.val) ||
      decide (DiamondRows 0 (221 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_222 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (222 * 256 + lo.val) →
    (covered (222 * 256 + lo.val) ||
      decide (DiamondRows 0 (222 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_223 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (223 * 256 + lo.val) →
    (covered (223 * 256 + lo.val) ||
      decide (DiamondRows 0 (223 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_224 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (224 * 256 + lo.val) →
    (covered (224 * 256 + lo.val) ||
      decide (DiamondRows 0 (224 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_225 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (225 * 256 + lo.val) →
    (covered (225 * 256 + lo.val) ||
      decide (DiamondRows 0 (225 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_226 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (226 * 256 + lo.val) →
    (covered (226 * 256 + lo.val) ||
      decide (DiamondRows 0 (226 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_227 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (227 * 256 + lo.val) →
    (covered (227 * 256 + lo.val) ||
      decide (DiamondRows 0 (227 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_228 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (228 * 256 + lo.val) →
    (covered (228 * 256 + lo.val) ||
      decide (DiamondRows 0 (228 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_229 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (229 * 256 + lo.val) →
    (covered (229 * 256 + lo.val) ||
      decide (DiamondRows 0 (229 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_230 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (230 * 256 + lo.val) →
    (covered (230 * 256 + lo.val) ||
      decide (DiamondRows 0 (230 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_231 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (231 * 256 + lo.val) →
    (covered (231 * 256 + lo.val) ||
      decide (DiamondRows 0 (231 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_232 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (232 * 256 + lo.val) →
    (covered (232 * 256 + lo.val) ||
      decide (DiamondRows 0 (232 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_233 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (233 * 256 + lo.val) →
    (covered (233 * 256 + lo.val) ||
      decide (DiamondRows 0 (233 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_234 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (234 * 256 + lo.val) →
    (covered (234 * 256 + lo.val) ||
      decide (DiamondRows 0 (234 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_235 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (235 * 256 + lo.val) →
    (covered (235 * 256 + lo.val) ||
      decide (DiamondRows 0 (235 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_236 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (236 * 256 + lo.val) →
    (covered (236 * 256 + lo.val) ||
      decide (DiamondRows 0 (236 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_237 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (237 * 256 + lo.val) →
    (covered (237 * 256 + lo.val) ||
      decide (DiamondRows 0 (237 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_238 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (238 * 256 + lo.val) →
    (covered (238 * 256 + lo.val) ||
      decide (DiamondRows 0 (238 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_239 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (239 * 256 + lo.val) →
    (covered (239 * 256 + lo.val) ||
      decide (DiamondRows 0 (239 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_240 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (240 * 256 + lo.val) →
    (covered (240 * 256 + lo.val) ||
      decide (DiamondRows 0 (240 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_241 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (241 * 256 + lo.val) →
    (covered (241 * 256 + lo.val) ||
      decide (DiamondRows 0 (241 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_242 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (242 * 256 + lo.val) →
    (covered (242 * 256 + lo.val) ||
      decide (DiamondRows 0 (242 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_243 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (243 * 256 + lo.val) →
    (covered (243 * 256 + lo.val) ||
      decide (DiamondRows 0 (243 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_244 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (244 * 256 + lo.val) →
    (covered (244 * 256 + lo.val) ||
      decide (DiamondRows 0 (244 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_245 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (245 * 256 + lo.val) →
    (covered (245 * 256 + lo.val) ||
      decide (DiamondRows 0 (245 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_246 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (246 * 256 + lo.val) →
    (covered (246 * 256 + lo.val) ||
      decide (DiamondRows 0 (246 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_247 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (247 * 256 + lo.val) →
    (covered (247 * 256 + lo.val) ||
      decide (DiamondRows 0 (247 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_248 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (248 * 256 + lo.val) →
    (covered (248 * 256 + lo.val) ||
      decide (DiamondRows 0 (248 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_249 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (249 * 256 + lo.val) →
    (covered (249 * 256 + lo.val) ||
      decide (DiamondRows 0 (249 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_250 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (250 * 256 + lo.val) →
    (covered (250 * 256 + lo.val) ||
      decide (DiamondRows 0 (250 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_251 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (251 * 256 + lo.val) →
    (covered (251 * 256 + lo.val) ||
      decide (DiamondRows 0 (251 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_252 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (252 * 256 + lo.val) →
    (covered (252 * 256 + lo.val) ||
      decide (DiamondRows 0 (252 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_253 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (253 * 256 + lo.val) →
    (covered (253 * 256 + lo.val) ||
      decide (DiamondRows 0 (253 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_254 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (254 * 256 + lo.val) →
    (covered (254 * 256 + lo.val) ||
      decide (DiamondRows 0 (254 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_255 : ∀ lo : Fin 256,
    10 ≤ DenseOutside.triangleCount (255 * 256 + lo.val) →
    (covered (255 * 256 + lo.val) ||
      decide (DiamondRows 0 (255 * 256 + lo.val))) = true := by
  decide +kernel

private theorem coverage_rows (hi lo : Fin 256)
    (hh : 10 ≤ DenseOutside.triangleCount (hi.val * 256 + lo.val)) :
    (covered (hi.val * 256 + lo.val) ||
      decide (DiamondRows 0 (hi.val * 256 + lo.val))) = true := by
  fin_cases hi
  · exact coverage_0 lo hh
  · exact coverage_1 lo hh
  · exact coverage_2 lo hh
  · exact coverage_3 lo hh
  · exact coverage_4 lo hh
  · exact coverage_5 lo hh
  · exact coverage_6 lo hh
  · exact coverage_7 lo hh
  · exact coverage_8 lo hh
  · exact coverage_9 lo hh
  · exact coverage_10 lo hh
  · exact coverage_11 lo hh
  · exact coverage_12 lo hh
  · exact coverage_13 lo hh
  · exact coverage_14 lo hh
  · exact coverage_15 lo hh
  · exact coverage_16 lo hh
  · exact coverage_17 lo hh
  · exact coverage_18 lo hh
  · exact coverage_19 lo hh
  · exact coverage_20 lo hh
  · exact coverage_21 lo hh
  · exact coverage_22 lo hh
  · exact coverage_23 lo hh
  · exact coverage_24 lo hh
  · exact coverage_25 lo hh
  · exact coverage_26 lo hh
  · exact coverage_27 lo hh
  · exact coverage_28 lo hh
  · exact coverage_29 lo hh
  · exact coverage_30 lo hh
  · exact coverage_31 lo hh
  · exact coverage_32 lo hh
  · exact coverage_33 lo hh
  · exact coverage_34 lo hh
  · exact coverage_35 lo hh
  · exact coverage_36 lo hh
  · exact coverage_37 lo hh
  · exact coverage_38 lo hh
  · exact coverage_39 lo hh
  · exact coverage_40 lo hh
  · exact coverage_41 lo hh
  · exact coverage_42 lo hh
  · exact coverage_43 lo hh
  · exact coverage_44 lo hh
  · exact coverage_45 lo hh
  · exact coverage_46 lo hh
  · exact coverage_47 lo hh
  · exact coverage_48 lo hh
  · exact coverage_49 lo hh
  · exact coverage_50 lo hh
  · exact coverage_51 lo hh
  · exact coverage_52 lo hh
  · exact coverage_53 lo hh
  · exact coverage_54 lo hh
  · exact coverage_55 lo hh
  · exact coverage_56 lo hh
  · exact coverage_57 lo hh
  · exact coverage_58 lo hh
  · exact coverage_59 lo hh
  · exact coverage_60 lo hh
  · exact coverage_61 lo hh
  · exact coverage_62 lo hh
  · exact coverage_63 lo hh
  · exact coverage_64 lo hh
  · exact coverage_65 lo hh
  · exact coverage_66 lo hh
  · exact coverage_67 lo hh
  · exact coverage_68 lo hh
  · exact coverage_69 lo hh
  · exact coverage_70 lo hh
  · exact coverage_71 lo hh
  · exact coverage_72 lo hh
  · exact coverage_73 lo hh
  · exact coverage_74 lo hh
  · exact coverage_75 lo hh
  · exact coverage_76 lo hh
  · exact coverage_77 lo hh
  · exact coverage_78 lo hh
  · exact coverage_79 lo hh
  · exact coverage_80 lo hh
  · exact coverage_81 lo hh
  · exact coverage_82 lo hh
  · exact coverage_83 lo hh
  · exact coverage_84 lo hh
  · exact coverage_85 lo hh
  · exact coverage_86 lo hh
  · exact coverage_87 lo hh
  · exact coverage_88 lo hh
  · exact coverage_89 lo hh
  · exact coverage_90 lo hh
  · exact coverage_91 lo hh
  · exact coverage_92 lo hh
  · exact coverage_93 lo hh
  · exact coverage_94 lo hh
  · exact coverage_95 lo hh
  · exact coverage_96 lo hh
  · exact coverage_97 lo hh
  · exact coverage_98 lo hh
  · exact coverage_99 lo hh
  · exact coverage_100 lo hh
  · exact coverage_101 lo hh
  · exact coverage_102 lo hh
  · exact coverage_103 lo hh
  · exact coverage_104 lo hh
  · exact coverage_105 lo hh
  · exact coverage_106 lo hh
  · exact coverage_107 lo hh
  · exact coverage_108 lo hh
  · exact coverage_109 lo hh
  · exact coverage_110 lo hh
  · exact coverage_111 lo hh
  · exact coverage_112 lo hh
  · exact coverage_113 lo hh
  · exact coverage_114 lo hh
  · exact coverage_115 lo hh
  · exact coverage_116 lo hh
  · exact coverage_117 lo hh
  · exact coverage_118 lo hh
  · exact coverage_119 lo hh
  · exact coverage_120 lo hh
  · exact coverage_121 lo hh
  · exact coverage_122 lo hh
  · exact coverage_123 lo hh
  · exact coverage_124 lo hh
  · exact coverage_125 lo hh
  · exact coverage_126 lo hh
  · exact coverage_127 lo hh
  · exact coverage_128 lo hh
  · exact coverage_129 lo hh
  · exact coverage_130 lo hh
  · exact coverage_131 lo hh
  · exact coverage_132 lo hh
  · exact coverage_133 lo hh
  · exact coverage_134 lo hh
  · exact coverage_135 lo hh
  · exact coverage_136 lo hh
  · exact coverage_137 lo hh
  · exact coverage_138 lo hh
  · exact coverage_139 lo hh
  · exact coverage_140 lo hh
  · exact coverage_141 lo hh
  · exact coverage_142 lo hh
  · exact coverage_143 lo hh
  · exact coverage_144 lo hh
  · exact coverage_145 lo hh
  · exact coverage_146 lo hh
  · exact coverage_147 lo hh
  · exact coverage_148 lo hh
  · exact coverage_149 lo hh
  · exact coverage_150 lo hh
  · exact coverage_151 lo hh
  · exact coverage_152 lo hh
  · exact coverage_153 lo hh
  · exact coverage_154 lo hh
  · exact coverage_155 lo hh
  · exact coverage_156 lo hh
  · exact coverage_157 lo hh
  · exact coverage_158 lo hh
  · exact coverage_159 lo hh
  · exact coverage_160 lo hh
  · exact coverage_161 lo hh
  · exact coverage_162 lo hh
  · exact coverage_163 lo hh
  · exact coverage_164 lo hh
  · exact coverage_165 lo hh
  · exact coverage_166 lo hh
  · exact coverage_167 lo hh
  · exact coverage_168 lo hh
  · exact coverage_169 lo hh
  · exact coverage_170 lo hh
  · exact coverage_171 lo hh
  · exact coverage_172 lo hh
  · exact coverage_173 lo hh
  · exact coverage_174 lo hh
  · exact coverage_175 lo hh
  · exact coverage_176 lo hh
  · exact coverage_177 lo hh
  · exact coverage_178 lo hh
  · exact coverage_179 lo hh
  · exact coverage_180 lo hh
  · exact coverage_181 lo hh
  · exact coverage_182 lo hh
  · exact coverage_183 lo hh
  · exact coverage_184 lo hh
  · exact coverage_185 lo hh
  · exact coverage_186 lo hh
  · exact coverage_187 lo hh
  · exact coverage_188 lo hh
  · exact coverage_189 lo hh
  · exact coverage_190 lo hh
  · exact coverage_191 lo hh
  · exact coverage_192 lo hh
  · exact coverage_193 lo hh
  · exact coverage_194 lo hh
  · exact coverage_195 lo hh
  · exact coverage_196 lo hh
  · exact coverage_197 lo hh
  · exact coverage_198 lo hh
  · exact coverage_199 lo hh
  · exact coverage_200 lo hh
  · exact coverage_201 lo hh
  · exact coverage_202 lo hh
  · exact coverage_203 lo hh
  · exact coverage_204 lo hh
  · exact coverage_205 lo hh
  · exact coverage_206 lo hh
  · exact coverage_207 lo hh
  · exact coverage_208 lo hh
  · exact coverage_209 lo hh
  · exact coverage_210 lo hh
  · exact coverage_211 lo hh
  · exact coverage_212 lo hh
  · exact coverage_213 lo hh
  · exact coverage_214 lo hh
  · exact coverage_215 lo hh
  · exact coverage_216 lo hh
  · exact coverage_217 lo hh
  · exact coverage_218 lo hh
  · exact coverage_219 lo hh
  · exact coverage_220 lo hh
  · exact coverage_221 lo hh
  · exact coverage_222 lo hh
  · exact coverage_223 lo hh
  · exact coverage_224 lo hh
  · exact coverage_225 lo hh
  · exact coverage_226 lo hh
  · exact coverage_227 lo hh
  · exact coverage_228 lo hh
  · exact coverage_229 lo hh
  · exact coverage_230 lo hh
  · exact coverage_231 lo hh
  · exact coverage_232 lo hh
  · exact coverage_233 lo hh
  · exact coverage_234 lo hh
  · exact coverage_235 lo hh
  · exact coverage_236 lo hh
  · exact coverage_237 lo hh
  · exact coverage_238 lo hh
  · exact coverage_239 lo hh
  · exact coverage_240 lo hh
  · exact coverage_241 lo hh
  · exact coverage_242 lo hh
  · exact coverage_243 lo hh
  · exact coverage_244 lo hh
  · exact coverage_245 lo hh
  · exact coverage_246 lo hh
  · exact coverage_247 lo hh
  · exact coverage_248 lo hh
  · exact coverage_249 lo hh
  · exact coverage_250 lo hh
  · exact coverage_251 lo hh
  · exact coverage_252 lo hh
  · exact coverage_253 lo hh
  · exact coverage_254 lo hh
  · exact coverage_255 lo hh

theorem coverage (m : Fin 65536) (hh : 10 ≤ DenseOutside.triangleCount m.val) :
    (covered m.val || decide (DiamondRows 0 m.val)) = true := by
  let hi : Fin 256 := ⟨m.val / 256, by omega⟩
  let lo : Fin 256 := ⟨m.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : hi.val * 256 + lo.val = m.val := by dsimp [hi, lo]; omega
  rw [← he] at hh ⊢
  exact coverage_rows hi lo hh

end Erdos577.DenseTriangle.D0
