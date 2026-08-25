/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.Energy

open LeanCert.Core

namespace Erdos232

/-- The generated Bessel grid, split into short arrays to keep kernel reduction shallow. -/
def besselGridStateBlock00 : Array (IntervalRat × IntervalRat) := #[
  besselGridState000,
  besselGridState001,
  besselGridState002,
  besselGridState003,
  besselGridState004,
  besselGridState005,
  besselGridState006,
  besselGridState007,
  besselGridState008,
  besselGridState009,
  besselGridState010,
  besselGridState011,
  besselGridState012,
  besselGridState013,
  besselGridState014,
  besselGridState015,
  besselGridState016,
  besselGridState017,
  besselGridState018,
  besselGridState019,
  besselGridState020,
  besselGridState021,
  besselGridState022,
  besselGridState023,
  besselGridState024
]

def besselGridStateBlock01 : Array (IntervalRat × IntervalRat) := #[
  besselGridState025,
  besselGridState026,
  besselGridState027,
  besselGridState028,
  besselGridState029,
  besselGridState030,
  besselGridState031,
  besselGridState032,
  besselGridState033,
  besselGridState034,
  besselGridState035,
  besselGridState036,
  besselGridState037,
  besselGridState038,
  besselGridState039,
  besselGridState040,
  besselGridState041,
  besselGridState042,
  besselGridState043,
  besselGridState044,
  besselGridState045,
  besselGridState046,
  besselGridState047,
  besselGridState048,
  besselGridState049
]

def besselGridStateBlock02 : Array (IntervalRat × IntervalRat) := #[
  besselGridState050,
  besselGridState051,
  besselGridState052,
  besselGridState053,
  besselGridState054,
  besselGridState055,
  besselGridState056,
  besselGridState057,
  besselGridState058,
  besselGridState059,
  besselGridState060,
  besselGridState061,
  besselGridState062,
  besselGridState063,
  besselGridState064,
  besselGridState065,
  besselGridState066,
  besselGridState067,
  besselGridState068,
  besselGridState069,
  besselGridState070,
  besselGridState071,
  besselGridState072,
  besselGridState073,
  besselGridState074
]

def besselGridStateBlock03 : Array (IntervalRat × IntervalRat) := #[
  besselGridState075,
  besselGridState076,
  besselGridState077,
  besselGridState078,
  besselGridState079,
  besselGridState080,
  besselGridState081,
  besselGridState082,
  besselGridState083,
  besselGridState084,
  besselGridState085,
  besselGridState086,
  besselGridState087,
  besselGridState088,
  besselGridState089,
  besselGridState090,
  besselGridState091,
  besselGridState092,
  besselGridState093,
  besselGridState094,
  besselGridState095,
  besselGridState096,
  besselGridState097,
  besselGridState098,
  besselGridState099
]

def besselGridStateBlock04 : Array (IntervalRat × IntervalRat) := #[
  besselGridState100,
  besselGridState101,
  besselGridState102,
  besselGridState103,
  besselGridState104,
  besselGridState105,
  besselGridState106,
  besselGridState107,
  besselGridState108,
  besselGridState109,
  besselGridState110,
  besselGridState111,
  besselGridState112,
  besselGridState113,
  besselGridState114,
  besselGridState115,
  besselGridState116,
  besselGridState117,
  besselGridState118,
  besselGridState119,
  besselGridState120,
  besselGridState121,
  besselGridState122,
  besselGridState123,
  besselGridState124
]

def besselGridStateBlock05 : Array (IntervalRat × IntervalRat) := #[
  besselGridState125,
  besselGridState126,
  besselGridState127,
  besselGridState128,
  besselGridState129,
  besselGridState130,
  besselGridState131,
  besselGridState132,
  besselGridState133,
  besselGridState134,
  besselGridState135,
  besselGridState136,
  besselGridState137,
  besselGridState138,
  besselGridState139,
  besselGridState140,
  besselGridState141,
  besselGridState142,
  besselGridState143,
  besselGridState144,
  besselGridState145,
  besselGridState146,
  besselGridState147,
  besselGridState148,
  besselGridState149
]

def besselGridStateBlock06 : Array (IntervalRat × IntervalRat) := #[
  besselGridState150,
  besselGridState151,
  besselGridState152,
  besselGridState153,
  besselGridState154,
  besselGridState155,
  besselGridState156,
  besselGridState157,
  besselGridState158,
  besselGridState159,
  besselGridState160,
  besselGridState161,
  besselGridState162,
  besselGridState163,
  besselGridState164,
  besselGridState165,
  besselGridState166,
  besselGridState167,
  besselGridState168,
  besselGridState169,
  besselGridState170,
  besselGridState171,
  besselGridState172,
  besselGridState173,
  besselGridState174
]

def besselGridStateBlock07 : Array (IntervalRat × IntervalRat) := #[
  besselGridState175,
  besselGridState176,
  besselGridState177,
  besselGridState178,
  besselGridState179,
  besselGridState180,
  besselGridState181,
  besselGridState182,
  besselGridState183,
  besselGridState184,
  besselGridState185,
  besselGridState186,
  besselGridState187,
  besselGridState188,
  besselGridState189,
  besselGridState190,
  besselGridState191,
  besselGridState192,
  besselGridState193,
  besselGridState194,
  besselGridState195,
  besselGridState196,
  besselGridState197,
  besselGridState198,
  besselGridState199
]

def besselGridStateBlock08 : Array (IntervalRat × IntervalRat) := #[
  besselGridState200,
  besselGridState201,
  besselGridState202,
  besselGridState203,
  besselGridState204,
  besselGridState205,
  besselGridState206,
  besselGridState207,
  besselGridState208,
  besselGridState209,
  besselGridState210,
  besselGridState211,
  besselGridState212,
  besselGridState213,
  besselGridState214,
  besselGridState215,
  besselGridState216,
  besselGridState217,
  besselGridState218,
  besselGridState219,
  besselGridState220,
  besselGridState221,
  besselGridState222,
  besselGridState223,
  besselGridState224
]

def besselGridStateBlock09 : Array (IntervalRat × IntervalRat) := #[
  besselGridState225,
  besselGridState226,
  besselGridState227,
  besselGridState228,
  besselGridState229,
  besselGridState230,
  besselGridState231,
  besselGridState232,
  besselGridState233,
  besselGridState234,
  besselGridState235,
  besselGridState236,
  besselGridState237,
  besselGridState238,
  besselGridState239,
  besselGridState240,
  besselGridState241,
  besselGridState242,
  besselGridState243,
  besselGridState244,
  besselGridState245,
  besselGridState246,
  besselGridState247,
  besselGridState248,
  besselGridState249
]

def besselGridStateBlock10 : Array (IntervalRat × IntervalRat) := #[
  besselGridState250,
  besselGridState251,
  besselGridState252,
  besselGridState253,
  besselGridState254,
  besselGridState255,
  besselGridState256,
  besselGridState257,
  besselGridState258,
  besselGridState259,
  besselGridState260,
  besselGridState261,
  besselGridState262,
  besselGridState263,
  besselGridState264,
  besselGridState265,
  besselGridState266,
  besselGridState267,
  besselGridState268,
  besselGridState269,
  besselGridState270,
  besselGridState271,
  besselGridState272,
  besselGridState273,
  besselGridState274
]

def besselGridStateBlock11 : Array (IntervalRat × IntervalRat) := #[
  besselGridState275,
  besselGridState276,
  besselGridState277,
  besselGridState278,
  besselGridState279,
  besselGridState280,
  besselGridState281,
  besselGridState282,
  besselGridState283,
  besselGridState284,
  besselGridState285,
  besselGridState286,
  besselGridState287,
  besselGridState288,
  besselGridState289,
  besselGridState290,
  besselGridState291,
  besselGridState292,
  besselGridState293,
  besselGridState294,
  besselGridState295,
  besselGridState296,
  besselGridState297,
  besselGridState298,
  besselGridState299
]

def besselGridStateBlock12 : Array (IntervalRat × IntervalRat) := #[
  besselGridState300,
  besselGridState301,
  besselGridState302,
  besselGridState303,
  besselGridState304,
  besselGridState305,
  besselGridState306,
  besselGridState307,
  besselGridState308,
  besselGridState309,
  besselGridState310,
  besselGridState311,
  besselGridState312,
  besselGridState313,
  besselGridState314,
  besselGridState315,
  besselGridState316,
  besselGridState317,
  besselGridState318,
  besselGridState319,
  besselGridState320,
  besselGridState321,
  besselGridState322,
  besselGridState323,
  besselGridState324
]

def besselGridStateBlock13 : Array (IntervalRat × IntervalRat) := #[
  besselGridState325,
  besselGridState326,
  besselGridState327,
  besselGridState328,
  besselGridState329,
  besselGridState330,
  besselGridState331,
  besselGridState332,
  besselGridState333,
  besselGridState334,
  besselGridState335,
  besselGridState336,
  besselGridState337,
  besselGridState338,
  besselGridState339,
  besselGridState340,
  besselGridState341,
  besselGridState342,
  besselGridState343,
  besselGridState344,
  besselGridState345,
  besselGridState346,
  besselGridState347,
  besselGridState348,
  besselGridState349
]

def besselGridStateBlock14 : Array (IntervalRat × IntervalRat) := #[
  besselGridState350,
  besselGridState351,
  besselGridState352,
  besselGridState353,
  besselGridState354,
  besselGridState355,
  besselGridState356,
  besselGridState357,
  besselGridState358,
  besselGridState359,
  besselGridState360,
  besselGridState361,
  besselGridState362,
  besselGridState363,
  besselGridState364,
  besselGridState365,
  besselGridState366
]

/-- Lookup in the generated Bessel grid. -/
def besselGridStateAt (i : Fin 367) : IntervalRat × IntervalRat :=
  match i.val / 25 with
  | 0 => besselGridStateBlock00[i.val % 25]!
  | 1 => besselGridStateBlock01[i.val % 25]!
  | 2 => besselGridStateBlock02[i.val % 25]!
  | 3 => besselGridStateBlock03[i.val % 25]!
  | 4 => besselGridStateBlock04[i.val % 25]!
  | 5 => besselGridStateBlock05[i.val % 25]!
  | 6 => besselGridStateBlock06[i.val % 25]!
  | 7 => besselGridStateBlock07[i.val % 25]!
  | 8 => besselGridStateBlock08[i.val % 25]!
  | 9 => besselGridStateBlock09[i.val % 25]!
  | 10 => besselGridStateBlock10[i.val % 25]!
  | 11 => besselGridStateBlock11[i.val % 25]!
  | 12 => besselGridStateBlock12[i.val % 25]!
  | 13 => besselGridStateBlock13[i.val % 25]!
  | _ => besselGridStateBlock14[i.val % 25]!

private theorem besselGridStateAt_valid_000_024
    (i : Fin 367) (hlo : 0 ≤ (i : ℕ)) (hhi : (i : ℕ) ≤ 24) :
    BesselStateValid ((i : ℕ) * 157 / 50 : ℚ) (besselGridStateAt i) := by
  rcases i with ⟨i, hi⟩
  simp only [Fin.val_mk] at hlo hhi ⊢
  interval_cases i
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState000_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState001_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState002_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState003_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState004_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState005_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState006_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState007_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState008_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState009_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState010_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState011_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState012_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState013_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState014_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState015_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState016_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState017_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState018_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState019_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState020_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState021_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState022_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState023_valid
  · simpa [besselGridStateAt, besselGridStateBlock00] using besselGridState024_valid

private theorem besselGridStateAt_valid_025_049
    (i : Fin 367) (hlo : 25 ≤ (i : ℕ)) (hhi : (i : ℕ) ≤ 49) :
    BesselStateValid ((i : ℕ) * 157 / 50 : ℚ) (besselGridStateAt i) := by
  rcases i with ⟨i, hi⟩
  simp only [Fin.val_mk] at hlo hhi ⊢
  interval_cases i
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState025_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState026_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState027_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState028_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState029_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState030_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState031_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState032_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState033_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState034_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState035_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState036_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState037_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState038_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState039_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState040_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState041_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState042_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState043_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState044_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState045_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState046_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState047_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState048_valid
  · simpa [besselGridStateAt, besselGridStateBlock01] using besselGridState049_valid

private theorem besselGridStateAt_valid_050_074
    (i : Fin 367) (hlo : 50 ≤ (i : ℕ)) (hhi : (i : ℕ) ≤ 74) :
    BesselStateValid ((i : ℕ) * 157 / 50 : ℚ) (besselGridStateAt i) := by
  rcases i with ⟨i, hi⟩
  simp only [Fin.val_mk] at hlo hhi ⊢
  interval_cases i
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState050_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState051_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState052_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState053_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState054_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState055_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState056_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState057_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState058_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState059_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState060_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState061_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState062_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState063_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState064_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState065_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState066_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState067_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState068_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState069_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState070_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState071_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState072_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState073_valid
  · simpa [besselGridStateAt, besselGridStateBlock02] using besselGridState074_valid

private theorem besselGridStateAt_valid_075_099
    (i : Fin 367) (hlo : 75 ≤ (i : ℕ)) (hhi : (i : ℕ) ≤ 99) :
    BesselStateValid ((i : ℕ) * 157 / 50 : ℚ) (besselGridStateAt i) := by
  rcases i with ⟨i, hi⟩
  simp only [Fin.val_mk] at hlo hhi ⊢
  interval_cases i
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState075_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState076_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState077_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState078_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState079_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState080_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState081_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState082_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState083_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState084_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState085_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState086_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState087_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState088_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState089_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState090_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState091_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState092_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState093_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState094_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState095_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState096_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState097_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState098_valid
  · simpa [besselGridStateAt, besselGridStateBlock03] using besselGridState099_valid

private theorem besselGridStateAt_valid_100_124
    (i : Fin 367) (hlo : 100 ≤ (i : ℕ)) (hhi : (i : ℕ) ≤ 124) :
    BesselStateValid ((i : ℕ) * 157 / 50 : ℚ) (besselGridStateAt i) := by
  rcases i with ⟨i, hi⟩
  simp only [Fin.val_mk] at hlo hhi ⊢
  interval_cases i
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState100_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState101_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState102_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState103_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState104_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState105_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState106_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState107_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState108_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState109_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState110_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState111_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState112_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState113_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState114_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState115_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState116_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState117_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState118_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState119_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState120_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState121_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState122_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState123_valid
  · simpa [besselGridStateAt, besselGridStateBlock04] using besselGridState124_valid

private theorem besselGridStateAt_valid_125_149
    (i : Fin 367) (hlo : 125 ≤ (i : ℕ)) (hhi : (i : ℕ) ≤ 149) :
    BesselStateValid ((i : ℕ) * 157 / 50 : ℚ) (besselGridStateAt i) := by
  rcases i with ⟨i, hi⟩
  simp only [Fin.val_mk] at hlo hhi ⊢
  interval_cases i
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState125_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState126_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState127_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState128_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState129_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState130_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState131_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState132_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState133_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState134_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState135_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState136_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState137_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState138_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState139_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState140_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState141_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState142_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState143_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState144_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState145_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState146_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState147_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState148_valid
  · simpa [besselGridStateAt, besselGridStateBlock05] using besselGridState149_valid

private theorem besselGridStateAt_valid_150_174
    (i : Fin 367) (hlo : 150 ≤ (i : ℕ)) (hhi : (i : ℕ) ≤ 174) :
    BesselStateValid ((i : ℕ) * 157 / 50 : ℚ) (besselGridStateAt i) := by
  rcases i with ⟨i, hi⟩
  simp only [Fin.val_mk] at hlo hhi ⊢
  interval_cases i
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState150_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState151_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState152_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState153_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState154_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState155_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState156_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState157_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState158_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState159_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState160_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState161_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState162_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState163_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState164_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState165_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState166_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState167_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState168_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState169_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState170_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState171_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState172_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState173_valid
  · simpa [besselGridStateAt, besselGridStateBlock06] using besselGridState174_valid

private theorem besselGridStateAt_valid_175_199
    (i : Fin 367) (hlo : 175 ≤ (i : ℕ)) (hhi : (i : ℕ) ≤ 199) :
    BesselStateValid ((i : ℕ) * 157 / 50 : ℚ) (besselGridStateAt i) := by
  rcases i with ⟨i, hi⟩
  simp only [Fin.val_mk] at hlo hhi ⊢
  interval_cases i
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState175_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState176_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState177_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState178_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState179_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState180_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState181_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState182_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState183_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState184_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState185_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState186_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState187_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState188_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState189_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState190_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState191_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState192_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState193_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState194_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState195_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState196_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState197_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState198_valid
  · simpa [besselGridStateAt, besselGridStateBlock07] using besselGridState199_valid

private theorem besselGridStateAt_valid_200_224
    (i : Fin 367) (hlo : 200 ≤ (i : ℕ)) (hhi : (i : ℕ) ≤ 224) :
    BesselStateValid ((i : ℕ) * 157 / 50 : ℚ) (besselGridStateAt i) := by
  rcases i with ⟨i, hi⟩
  simp only [Fin.val_mk] at hlo hhi ⊢
  interval_cases i
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState200_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState201_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState202_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState203_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState204_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState205_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState206_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState207_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState208_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState209_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState210_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState211_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState212_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState213_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState214_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState215_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState216_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState217_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState218_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState219_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState220_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState221_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState222_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState223_valid
  · simpa [besselGridStateAt, besselGridStateBlock08] using besselGridState224_valid

private theorem besselGridStateAt_valid_225_249
    (i : Fin 367) (hlo : 225 ≤ (i : ℕ)) (hhi : (i : ℕ) ≤ 249) :
    BesselStateValid ((i : ℕ) * 157 / 50 : ℚ) (besselGridStateAt i) := by
  rcases i with ⟨i, hi⟩
  simp only [Fin.val_mk] at hlo hhi ⊢
  interval_cases i
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState225_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState226_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState227_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState228_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState229_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState230_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState231_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState232_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState233_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState234_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState235_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState236_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState237_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState238_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState239_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState240_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState241_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState242_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState243_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState244_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState245_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState246_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState247_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState248_valid
  · simpa [besselGridStateAt, besselGridStateBlock09] using besselGridState249_valid

private theorem besselGridStateAt_valid_250_274
    (i : Fin 367) (hlo : 250 ≤ (i : ℕ)) (hhi : (i : ℕ) ≤ 274) :
    BesselStateValid ((i : ℕ) * 157 / 50 : ℚ) (besselGridStateAt i) := by
  rcases i with ⟨i, hi⟩
  simp only [Fin.val_mk] at hlo hhi ⊢
  interval_cases i
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState250_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState251_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState252_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState253_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState254_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState255_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState256_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState257_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState258_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState259_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState260_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState261_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState262_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState263_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState264_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState265_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState266_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState267_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState268_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState269_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState270_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState271_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState272_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState273_valid
  · simpa [besselGridStateAt, besselGridStateBlock10] using besselGridState274_valid

private theorem besselGridStateAt_valid_275_299
    (i : Fin 367) (hlo : 275 ≤ (i : ℕ)) (hhi : (i : ℕ) ≤ 299) :
    BesselStateValid ((i : ℕ) * 157 / 50 : ℚ) (besselGridStateAt i) := by
  rcases i with ⟨i, hi⟩
  simp only [Fin.val_mk] at hlo hhi ⊢
  interval_cases i
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState275_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState276_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState277_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState278_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState279_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState280_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState281_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState282_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState283_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState284_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState285_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState286_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState287_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState288_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState289_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState290_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState291_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState292_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState293_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState294_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState295_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState296_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState297_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState298_valid
  · simpa [besselGridStateAt, besselGridStateBlock11] using besselGridState299_valid

private theorem besselGridStateAt_valid_300_324
    (i : Fin 367) (hlo : 300 ≤ (i : ℕ)) (hhi : (i : ℕ) ≤ 324) :
    BesselStateValid ((i : ℕ) * 157 / 50 : ℚ) (besselGridStateAt i) := by
  rcases i with ⟨i, hi⟩
  simp only [Fin.val_mk] at hlo hhi ⊢
  interval_cases i
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState300_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState301_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState302_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState303_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState304_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState305_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState306_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState307_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState308_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState309_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState310_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState311_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState312_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState313_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState314_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState315_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState316_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState317_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState318_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState319_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState320_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState321_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState322_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState323_valid
  · simpa [besselGridStateAt, besselGridStateBlock12] using besselGridState324_valid

private theorem besselGridStateAt_valid_325_349
    (i : Fin 367) (hlo : 325 ≤ (i : ℕ)) (hhi : (i : ℕ) ≤ 349) :
    BesselStateValid ((i : ℕ) * 157 / 50 : ℚ) (besselGridStateAt i) := by
  rcases i with ⟨i, hi⟩
  simp only [Fin.val_mk] at hlo hhi ⊢
  interval_cases i
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState325_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState326_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState327_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState328_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState329_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState330_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState331_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState332_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState333_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState334_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState335_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState336_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState337_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState338_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState339_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState340_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState341_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState342_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState343_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState344_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState345_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState346_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState347_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState348_valid
  · simpa [besselGridStateAt, besselGridStateBlock13] using besselGridState349_valid

private theorem besselGridStateAt_valid_350_366
    (i : Fin 367) (hlo : 350 ≤ (i : ℕ)) (hhi : (i : ℕ) ≤ 366) :
    BesselStateValid ((i : ℕ) * 157 / 50 : ℚ) (besselGridStateAt i) := by
  rcases i with ⟨i, hi⟩
  simp only [Fin.val_mk] at hlo hhi ⊢
  interval_cases i
  · simpa [besselGridStateAt, besselGridStateBlock14] using besselGridState350_valid
  · simpa [besselGridStateAt, besselGridStateBlock14] using besselGridState351_valid
  · simpa [besselGridStateAt, besselGridStateBlock14] using besselGridState352_valid
  · simpa [besselGridStateAt, besselGridStateBlock14] using besselGridState353_valid
  · simpa [besselGridStateAt, besselGridStateBlock14] using besselGridState354_valid
  · simpa [besselGridStateAt, besselGridStateBlock14] using besselGridState355_valid
  · simpa [besselGridStateAt, besselGridStateBlock14] using besselGridState356_valid
  · simpa [besselGridStateAt, besselGridStateBlock14] using besselGridState357_valid
  · simpa [besselGridStateAt, besselGridStateBlock14] using besselGridState358_valid
  · simpa [besselGridStateAt, besselGridStateBlock14] using besselGridState359_valid
  · simpa [besselGridStateAt, besselGridStateBlock14] using besselGridState360_valid
  · simpa [besselGridStateAt, besselGridStateBlock14] using besselGridState361_valid
  · simpa [besselGridStateAt, besselGridStateBlock14] using besselGridState362_valid
  · simpa [besselGridStateAt, besselGridStateBlock14] using besselGridState363_valid
  · simpa [besselGridStateAt, besselGridStateBlock14] using besselGridState364_valid
  · simpa [besselGridStateAt, besselGridStateBlock14] using besselGridState365_valid
  · simpa [besselGridStateAt, besselGridStateBlock14] using besselGridState366_valid

/-- Every generated grid entry has its certified semantic enclosure. -/
theorem besselGridStateAt_valid (i : Fin 367) :
    BesselStateValid ((i : ℕ) * 157 / 50 : ℚ) (besselGridStateAt i) := by
  by_cases h0 : (i : ℕ) ≤ 24
  · exact besselGridStateAt_valid_000_024 i (by omega) h0
  by_cases h25 : (i : ℕ) ≤ 49
  · exact besselGridStateAt_valid_025_049 i (by omega) h25
  by_cases h50 : (i : ℕ) ≤ 74
  · exact besselGridStateAt_valid_050_074 i (by omega) h50
  by_cases h75 : (i : ℕ) ≤ 99
  · exact besselGridStateAt_valid_075_099 i (by omega) h75
  by_cases h100 : (i : ℕ) ≤ 124
  · exact besselGridStateAt_valid_100_124 i (by omega) h100
  by_cases h125 : (i : ℕ) ≤ 149
  · exact besselGridStateAt_valid_125_149 i (by omega) h125
  by_cases h150 : (i : ℕ) ≤ 174
  · exact besselGridStateAt_valid_150_174 i (by omega) h150
  by_cases h175 : (i : ℕ) ≤ 199
  · exact besselGridStateAt_valid_175_199 i (by omega) h175
  by_cases h200 : (i : ℕ) ≤ 224
  · exact besselGridStateAt_valid_200_224 i (by omega) h200
  by_cases h225 : (i : ℕ) ≤ 249
  · exact besselGridStateAt_valid_225_249 i (by omega) h225
  by_cases h250 : (i : ℕ) ≤ 274
  · exact besselGridStateAt_valid_250_274 i (by omega) h250
  by_cases h275 : (i : ℕ) ≤ 299
  · exact besselGridStateAt_valid_275_299 i (by omega) h275
  by_cases h300 : (i : ℕ) ≤ 324
  · exact besselGridStateAt_valid_300_324 i (by omega) h300
  by_cases h325 : (i : ℕ) ≤ 349
  · exact besselGridStateAt_valid_325_349 i (by omega) h325
  by_cases h350 : (i : ℕ) ≤ 366
  · exact besselGridStateAt_valid_350_366 i (by omega) h350
  omega

end Erdos232
