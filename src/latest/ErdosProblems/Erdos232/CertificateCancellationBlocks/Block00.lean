/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock00_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights00, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt00 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 1 (-15732857) =
      weightedMaskMass a 2 (-15732857) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 2, -15732857) (by decide)]
  have h001 : weightedMaskMass a 1 (-58477368) =
      weightedMaskMass a 4 (-58477368) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 4, -58477368) (by decide)]
  have h002 : weightedMaskMass a 1 (48156884) =
      weightedMaskMass a 8 (48156884) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 8, 48156884) (by decide)]
  have h003 : weightedMaskMass a 1 (228006807) =
      weightedMaskMass a 16 (228006807) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 16, 228006807) (by decide)]
  have h004 : weightedMaskMass a 1 (221564395) =
      weightedMaskMass a 32 (221564395) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 32, 221564395) (by decide)]
  have h005 : weightedMaskMass a 1 (112702458) =
      weightedMaskMass a 64 (112702458) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 64, 112702458) (by decide)]
  have h006 : weightedMaskMass a 1 (246990017) =
      weightedMaskMass a 128 (246990017) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 128, 246990017) (by decide)]
  have h007 : weightedMaskMass a 1 (106228698) =
      weightedMaskMass a 256 (106228698) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 256, 106228698) (by decide)]
  have h008 : weightedMaskMass a 1 (69302092) =
      weightedMaskMass a 512 (69302092) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 512, 69302092) (by decide)]
  have h009 : weightedMaskMass a 1 (175329932) =
      weightedMaskMass a 1024 (175329932) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 1024, 175329932) (by decide)]
  have h010 : weightedMaskMass a 1 (-7365588) =
      weightedMaskMass a 2048 (-7365588) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 2048, -7365588) (by decide)]
  have h011 : weightedMaskMass a 1 (6806735) =
      weightedMaskMass a 4096 (6806735) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 4096, 6806735) (by decide)]
  have h012 : weightedMaskMass a 1 (127139804) =
      weightedMaskMass a 8192 (127139804) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 8192, 127139804) (by decide)]
  have h013 : weightedMaskMass a 1 (-115628564) =
      weightedMaskMass a 16384 (-115628564) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 16384, -115628564) (by decide)]
  have h014 : weightedMaskMass a 1 (-72563851) =
      weightedMaskMass a 32768 (-72563851) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 32768, -72563851) (by decide)]
  have h015 : weightedMaskMass a 1 (-14412378) =
      weightedMaskMass a 65536 (-14412378) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 65536, -14412378) (by decide)]
  have h016 : weightedMaskMass a 1 (84439803) =
      weightedMaskMass a 131072 (84439803) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 131072, 84439803) (by decide)]
  have h017 : weightedMaskMass a 1 (-102498938) =
      weightedMaskMass a 262144 (-102498938) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 262144, -102498938) (by decide)]
  have h018 : weightedMaskMass a 1 (-67369485) =
      weightedMaskMass a 524288 (-67369485) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 524288, -67369485) (by decide)]
  have h019 : weightedMaskMass a 1 (88270778) =
      weightedMaskMass a 1048576 (88270778) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 1048576, 88270778) (by decide)]
  have h020 : weightedMaskMass a 1 (-141210688) =
      weightedMaskMass a 2097152 (-141210688) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 2097152, -141210688) (by decide)]
  have h021 : weightedMaskMass a 1 (30885029) =
      weightedMaskMass a 4194304 (30885029) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1, 4194304, 30885029) (by decide)]
  have h022 : weightedMaskMass a 9 (-67155277) =
      weightedMaskMass a 65 (-67155277) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9, 65, -67155277) (by decide)]
  have h023 : weightedMaskMass a 9 (-48148733) =
      weightedMaskMass a 264 (-48148733) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9, 264, -48148733) (by decide)]
  have h024 : weightedMaskMass a 9 (83203748) =
      weightedMaskMass a 4104 (83203748) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9, 4104, 83203748) (by decide)]
  have h025 : weightedMaskMass a 9 (-41872921) =
      weightedMaskMass a 4224 (-41872921) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9, 4224, -41872921) (by decide)]
  have h026 : weightedMaskMass a 9 (22716257) =
      weightedMaskMass a 81920 (22716257) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9, 81920, 22716257) (by decide)]
  have h027 : weightedMaskMass a 9 (8083140) =
      weightedMaskMass a 655360 (8083140) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9, 655360, 8083140) (by decide)]
  have h028 : weightedMaskMass a 9 (36619114) =
      weightedMaskMass a 2097280 (36619114) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9, 2097280, 36619114) (by decide)]
  have h029 : weightedMaskMass a 9 (31343761) =
      weightedMaskMass a 2113536 (31343761) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9, 2113536, 31343761) (by decide)]
  have h030 : weightedMaskMass a 18 (51277579) =
      weightedMaskMass a 36 (51277579) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 36, 51277579) (by decide)]
  have h031 : weightedMaskMass a 18 (15732857) =
      weightedMaskMass a 130 (15732857) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 130, 15732857) (by decide)]
  have h032 : weightedMaskMass a 18 (17904465) =
      weightedMaskMass a 514 (17904465) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 514, 17904465) (by decide)]
  have h033 : weightedMaskMass a 18 (17689100) =
      weightedMaskMass a 1028 (17689100) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 1028, 17689100) (by decide)]
  have h034 : weightedMaskMass a 18 (95683504) =
      weightedMaskMass a 2052 (95683504) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 2052, 95683504) (by decide)]
  have h035 : weightedMaskMass a 18 (-122180429) =
      weightedMaskMass a 2080 (-122180429) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 2080, -122180429) (by decide)]
  have h036 : weightedMaskMass a 18 (70963344) =
      weightedMaskMass a 3072 (70963344) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 3072, 70963344) (by decide)]
  have h037 : weightedMaskMass a 18 (37701375) =
      weightedMaskMass a 8196 (37701375) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 8196, 37701375) (by decide)]
  have h038 : weightedMaskMass a 18 (-55479718) =
      weightedMaskMass a 9216 (-55479718) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 9216, -55479718) (by decide)]
  have h039 : weightedMaskMass a 18 (66015617) =
      weightedMaskMass a 16385 (66015617) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 16385, 66015617) (by decide)]
  have h040 : weightedMaskMass a 18 (96323645) =
      weightedMaskMass a 34816 (96323645) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 34816, 96323645) (by decide)]
  have h041 : weightedMaskMass a 18 (103086056) =
      weightedMaskMass a 65544 (103086056) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 65544, 103086056) (by decide)]
  have h042 : weightedMaskMass a 18 (90068946) =
      weightedMaskMass a 131076 (90068946) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 131076, 90068946) (by decide)]
  have h043 : weightedMaskMass a 18 (-96547370) =
      weightedMaskMass a 131104 (-96547370) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 131104, -96547370) (by decide)]
  have h044 : weightedMaskMass a 18 (37176508) =
      weightedMaskMass a 262160 (37176508) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 262160, 37176508) (by decide)]
  have h045 : weightedMaskMass a 18 (68309587) =
      weightedMaskMass a 266240 (68309587) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 266240, 68309587) (by decide)]
  have h046 : weightedMaskMass a 18 (67369485) =
      weightedMaskMass a 524800 (67369485) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 524800, 67369485) (by decide)]
  have h047 : weightedMaskMass a 18 (-72038359) =
      weightedMaskMass a 528384 (-72038359) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 528384, -72038359) (by decide)]
  have h048 : weightedMaskMass a 18 (-116430953) =
      weightedMaskMass a 1048578 (-116430953) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 1048578, -116430953) (by decide)]
  have h049 : weightedMaskMass a 18 (-110362217) =
      weightedMaskMass a 1048704 (-110362217) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 1048704, -110362217) (by decide)]
  have h050 : weightedMaskMass a 18 (-111893960) =
      weightedMaskMass a 1049088 (-111893960) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 1049088, -111893960) (by decide)]
  have h051 : weightedMaskMass a 18 (-113702501) =
      weightedMaskMass a 2097216 (-113702501) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (18, 2097216, -113702501) (by decide)]
  have h052 : weightedMaskMass a 20 (87392942) =
      weightedMaskMass a 1026 (87392942) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20, 1026, 87392942) (by decide)]
  have h053 : weightedMaskMass a 20 (-24979123) =
      weightedMaskMass a 2049 (-24979123) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20, 2049, -24979123) (by decide)]
  have h054 : weightedMaskMass a 20 (-2190421) =
      weightedMaskMass a 8200 (-2190421) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20, 8200, -2190421) (by decide)]
  have h055 : weightedMaskMass a 20 (-53506305) =
      weightedMaskMass a 49152 (-53506305) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20, 49152, -53506305) (by decide)]
  have h056 : weightedMaskMass a 20 (17617461) =
      weightedMaskMass a 65538 (17617461) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20, 65538, 17617461) (by decide)]
  have h057 : weightedMaskMass a 20 (-14014990) =
      weightedMaskMass a 66560 (-14014990) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20, 66560, -14014990) (by decide)]
  have h058 : weightedMaskMass a 20 (-121143676) =
      weightedMaskMass a 131136 (-121143676) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20, 131136, -121143676) (by decide)]
  have h059 : weightedMaskMass a 20 (36277962) =
      weightedMaskMass a 262176 (36277962) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20, 262176, 36277962) (by decide)]
  have h060 : weightedMaskMass a 20 (-171454871) =
      weightedMaskMass a 540672 (-171454871) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20, 540672, -171454871) (by decide)]
  have h061 : weightedMaskMass a 20 (150054276) =
      weightedMaskMass a 557056 (150054276) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20, 557056, 150054276) (by decide)]
  have h062 : weightedMaskMass a 20 (-106272308) =
      weightedMaskMass a 1048832 (-106272308) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20, 1048832, -106272308) (by decide)]
  have h063 : weightedMaskMass a 20 (43600700) =
      weightedMaskMass a 2097184 (43600700) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20, 2097184, 43600700) (by decide)]
  have h064 : weightedMaskMass a 20 (110304834) =
      weightedMaskMass a 2359296 (110304834) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20, 2359296, 110304834) (by decide)]
  have h065 : weightedMaskMass a 20 (27417457) =
      weightedMaskMass a 4227072 (27417457) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20, 4227072, 27417457) (by decide)]
  have h066 : weightedMaskMass a 20 (-35060072) =
      weightedMaskMass a 4718592 (-35060072) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20, 4718592, -35060072) (by decide)]
  have h067 : weightedMaskMass a 24 (10027360) =
      weightedMaskMass a 68 (10027360) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24, 68, 10027360) (by decide)]
  have h068 : weightedMaskMass a 24 (56669362) =
      weightedMaskMass a 258 (56669362) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24, 258, 56669362) (by decide)]
  have h069 : weightedMaskMass a 24 (-12300765) =
      weightedMaskMass a 513 (-12300765) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24, 513, -12300765) (by decide)]
  have h070 : weightedMaskMass a 24 (-96821365) =
      weightedMaskMass a 1025 (-96821365) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24, 1025, -96821365) (by decide)]
  have h071 : weightedMaskMass a 24 (-139391629) =
      weightedMaskMass a 1536 (-139391629) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24, 1536, -139391629) (by decide)]
  have h072 : weightedMaskMass a 24 (-31573077) =
      weightedMaskMass a 2064 (-31573077) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24, 2064, -31573077) (by decide)]
  have h073 : weightedMaskMass a 24 (-108968755) =
      weightedMaskMass a 4128 (-108968755) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24, 4128, -108968755) (by decide)]
  have h074 : weightedMaskMass a 24 (88650669) =
      weightedMaskMass a 8194 (88650669) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24, 8194, 88650669) (by decide)]
  have h075 : weightedMaskMass a 24 (-37260511) =
      weightedMaskMass a 20480 (-37260511) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24, 20480, -37260511) (by decide)]
  have h076 : weightedMaskMass a 24 (16119159) =
      weightedMaskMass a 65540 (16119159) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24, 65540, 16119159) (by decide)]
  have h077 : weightedMaskMass a 24 (2007444) =
      weightedMaskMass a 65664 (2007444) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24, 65664, 2007444) (by decide)]
  have h078 : weightedMaskMass a 24 (13778019) =
      weightedMaskMass a 262145 (13778019) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24, 262145, 13778019) (by decide)]
  have h079 : weightedMaskMass a 24 (58209423) =
      weightedMaskMass a 393216 (58209423) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24, 393216, 58209423) (by decide)]
  have h080 : weightedMaskMass a 24 (24649187) =
      weightedMaskMass a 526336 (24649187) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24, 526336, 24649187) (by decide)]
  have h081 : weightedMaskMass a 24 (115606739) =
      weightedMaskMass a 2097168 (115606739) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24, 2097168, 115606739) (by decide)]
  have h082 : weightedMaskMass a 24 (56985527) =
      weightedMaskMass a 2099200 (56985527) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24, 2099200, 56985527) (by decide)]
  have h083 : weightedMaskMass a 24 (12786886) =
      weightedMaskMass a 4194816 (12786886) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24, 4194816, 12786886) (by decide)]
  have h084 : weightedMaskMass a 34 (8951650) =
      weightedMaskMass a 132 (8951650) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34, 132, 8951650) (by decide)]
  have h085 : weightedMaskMass a 34 (32989682) =
      weightedMaskMass a 2056 (32989682) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34, 2056, 32989682) (by decide)]
  have h086 : weightedMaskMass a 34 (-56031968) =
      weightedMaskMass a 8448 (-56031968) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34, 8448, -56031968) (by decide)]
  have h087 : weightedMaskMass a 34 (-18875990) =
      weightedMaskMass a 16386 (-18875990) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34, 16386, -18875990) (by decide)]
  have h088 : weightedMaskMass a 34 (-25399375) =
      weightedMaskMass a 16416 (-25399375) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34, 16416, -25399375) (by decide)]
  have h089 : weightedMaskMass a 34 (6516685) =
      weightedMaskMass a 98304 (6516685) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34, 98304, 6516685) (by decide)]
  have h090 : weightedMaskMass a 34 (-25332059) =
      weightedMaskMass a 131073 (-25332059) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34, 131073, -25332059) (by decide)]
  have h091 : weightedMaskMass a 34 (-7213425) =
      weightedMaskMass a 1048584 (-7213425) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34, 1048584, -7213425) (by decide)]
  have h092 : weightedMaskMass a 34 (57648026) =
      weightedMaskMass a 1050624 (57648026) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34, 1050624, 57648026) (by decide)]
  have h093 : weightedMaskMass a 34 (62227164) =
      weightedMaskMass a 2621440 (62227164) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34, 2621440, 62227164) (by decide)]
  have h094 : weightedMaskMass a 40 (30785632) =
      weightedMaskMass a 66 (30785632) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40, 66, 30785632) (by decide)]
  have h095 : weightedMaskMass a 40 (-112009317) =
      weightedMaskMass a 129 (-112009317) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40, 129, -112009317) (by decide)]
  have h096 : weightedMaskMass a 40 (12776477) =
      weightedMaskMass a 260 (12776477) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40, 260, 12776477) (by decide)]
  have h097 : weightedMaskMass a 40 (82750628) =
      weightedMaskMass a 520 (82750628) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40, 520, 82750628) (by decide)]
  have h098 : weightedMaskMass a 40 (-65804659) =
      weightedMaskMass a 544 (-65804659) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40, 544, -65804659) (by decide)]
  have h099 : weightedMaskMass a 40 (-13565989) =
      weightedMaskMass a 2176 (-13565989) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40, 2176, -13565989) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt00 s.val : ℝ)) = (((((((weightedMaskMass a 1 (-15732857) + (-weightedMaskMass a 2 (-15732857) + weightedMaskMass a 1 (-58477368))) + (-weightedMaskMass a 4 (-58477368) + (weightedMaskMass a 1 (48156884) + -weightedMaskMass a 8 (48156884)))) + ((weightedMaskMass a 1 (228006807) + (-weightedMaskMass a 16 (228006807) + weightedMaskMass a 1 (221564395))) + (-weightedMaskMass a 32 (221564395) + (weightedMaskMass a 1 (112702458) + -weightedMaskMass a 64 (112702458))))) + (((weightedMaskMass a 1 (246990017) + (-weightedMaskMass a 128 (246990017) + weightedMaskMass a 1 (106228698))) + (-weightedMaskMass a 256 (106228698) + (weightedMaskMass a 1 (69302092) + -weightedMaskMass a 512 (69302092)))) + ((weightedMaskMass a 1 (175329932) + (-weightedMaskMass a 1024 (175329932) + weightedMaskMass a 1 (-7365588))) + ((-weightedMaskMass a 2048 (-7365588) + weightedMaskMass a 1 (6806735)) + (-weightedMaskMass a 4096 (6806735) + weightedMaskMass a 1 (127139804)))))) + ((((-weightedMaskMass a 8192 (127139804) + (weightedMaskMass a 1 (-115628564) + -weightedMaskMass a 16384 (-115628564))) + (weightedMaskMass a 1 (-72563851) + (-weightedMaskMass a 32768 (-72563851) + weightedMaskMass a 1 (-14412378)))) + ((-weightedMaskMass a 65536 (-14412378) + (weightedMaskMass a 1 (84439803) + -weightedMaskMass a 131072 (84439803))) + (weightedMaskMass a 1 (-102498938) + (-weightedMaskMass a 262144 (-102498938) + weightedMaskMass a 1 (-67369485))))) + (((-weightedMaskMass a 524288 (-67369485) + (weightedMaskMass a 1 (88270778) + -weightedMaskMass a 1048576 (88270778))) + (weightedMaskMass a 1 (-141210688) + (-weightedMaskMass a 2097152 (-141210688) + weightedMaskMass a 1 (30885029)))) + ((-weightedMaskMass a 4194304 (30885029) + (weightedMaskMass a 9 (-67155277) + -weightedMaskMass a 65 (-67155277))) + ((weightedMaskMass a 9 (-48148733) + -weightedMaskMass a 264 (-48148733)) + (weightedMaskMass a 9 (83203748) + -weightedMaskMass a 4104 (83203748))))))) + (((((weightedMaskMass a 9 (-41872921) + (-weightedMaskMass a 4224 (-41872921) + weightedMaskMass a 9 (22716257))) + (-weightedMaskMass a 81920 (22716257) + (weightedMaskMass a 9 (8083140) + -weightedMaskMass a 655360 (8083140)))) + ((weightedMaskMass a 9 (36619114) + (-weightedMaskMass a 2097280 (36619114) + weightedMaskMass a 9 (31343761))) + (-weightedMaskMass a 2113536 (31343761) + (weightedMaskMass a 18 (51277579) + -weightedMaskMass a 36 (51277579))))) + (((weightedMaskMass a 18 (15732857) + (-weightedMaskMass a 130 (15732857) + weightedMaskMass a 18 (17904465))) + (-weightedMaskMass a 514 (17904465) + (weightedMaskMass a 18 (17689100) + -weightedMaskMass a 1028 (17689100)))) + ((weightedMaskMass a 18 (95683504) + (-weightedMaskMass a 2052 (95683504) + weightedMaskMass a 18 (-122180429))) + ((-weightedMaskMass a 2080 (-122180429) + weightedMaskMass a 18 (70963344)) + (-weightedMaskMass a 3072 (70963344) + weightedMaskMass a 18 (37701375)))))) + ((((-weightedMaskMass a 8196 (37701375) + (weightedMaskMass a 18 (-55479718) + -weightedMaskMass a 9216 (-55479718))) + (weightedMaskMass a 18 (66015617) + (-weightedMaskMass a 16385 (66015617) + weightedMaskMass a 18 (96323645)))) + ((-weightedMaskMass a 34816 (96323645) + (weightedMaskMass a 18 (103086056) + -weightedMaskMass a 65544 (103086056))) + (weightedMaskMass a 18 (90068946) + (-weightedMaskMass a 131076 (90068946) + weightedMaskMass a 18 (-96547370))))) + (((-weightedMaskMass a 131104 (-96547370) + (weightedMaskMass a 18 (37176508) + -weightedMaskMass a 262160 (37176508))) + (weightedMaskMass a 18 (68309587) + (-weightedMaskMass a 266240 (68309587) + weightedMaskMass a 18 (67369485)))) + ((-weightedMaskMass a 524800 (67369485) + (weightedMaskMass a 18 (-72038359) + -weightedMaskMass a 528384 (-72038359))) + ((weightedMaskMass a 18 (-116430953) + -weightedMaskMass a 1048578 (-116430953)) + (weightedMaskMass a 18 (-110362217) + -weightedMaskMass a 1048704 (-110362217)))))))) + ((((((weightedMaskMass a 18 (-111893960) + (-weightedMaskMass a 1049088 (-111893960) + weightedMaskMass a 18 (-113702501))) + (-weightedMaskMass a 2097216 (-113702501) + (weightedMaskMass a 20 (87392942) + -weightedMaskMass a 1026 (87392942)))) + ((weightedMaskMass a 20 (-24979123) + (-weightedMaskMass a 2049 (-24979123) + weightedMaskMass a 20 (-2190421))) + (-weightedMaskMass a 8200 (-2190421) + (weightedMaskMass a 20 (-53506305) + -weightedMaskMass a 49152 (-53506305))))) + (((weightedMaskMass a 20 (17617461) + (-weightedMaskMass a 65538 (17617461) + weightedMaskMass a 20 (-14014990))) + (-weightedMaskMass a 66560 (-14014990) + (weightedMaskMass a 20 (-121143676) + -weightedMaskMass a 131136 (-121143676)))) + ((weightedMaskMass a 20 (36277962) + (-weightedMaskMass a 262176 (36277962) + weightedMaskMass a 20 (-171454871))) + ((-weightedMaskMass a 540672 (-171454871) + weightedMaskMass a 20 (150054276)) + (-weightedMaskMass a 557056 (150054276) + weightedMaskMass a 20 (-106272308)))))) + ((((-weightedMaskMass a 1048832 (-106272308) + (weightedMaskMass a 20 (43600700) + -weightedMaskMass a 2097184 (43600700))) + (weightedMaskMass a 20 (110304834) + (-weightedMaskMass a 2359296 (110304834) + weightedMaskMass a 20 (27417457)))) + ((-weightedMaskMass a 4227072 (27417457) + (weightedMaskMass a 20 (-35060072) + -weightedMaskMass a 4718592 (-35060072))) + (weightedMaskMass a 24 (10027360) + (-weightedMaskMass a 68 (10027360) + weightedMaskMass a 24 (56669362))))) + (((-weightedMaskMass a 258 (56669362) + (weightedMaskMass a 24 (-12300765) + -weightedMaskMass a 513 (-12300765))) + (weightedMaskMass a 24 (-96821365) + (-weightedMaskMass a 1025 (-96821365) + weightedMaskMass a 24 (-139391629)))) + ((-weightedMaskMass a 1536 (-139391629) + (weightedMaskMass a 24 (-31573077) + -weightedMaskMass a 2064 (-31573077))) + ((weightedMaskMass a 24 (-108968755) + -weightedMaskMass a 4128 (-108968755)) + (weightedMaskMass a 24 (88650669) + -weightedMaskMass a 8194 (88650669))))))) + (((((weightedMaskMass a 24 (-37260511) + (-weightedMaskMass a 20480 (-37260511) + weightedMaskMass a 24 (16119159))) + (-weightedMaskMass a 65540 (16119159) + (weightedMaskMass a 24 (2007444) + -weightedMaskMass a 65664 (2007444)))) + ((weightedMaskMass a 24 (13778019) + (-weightedMaskMass a 262145 (13778019) + weightedMaskMass a 24 (58209423))) + (-weightedMaskMass a 393216 (58209423) + (weightedMaskMass a 24 (24649187) + -weightedMaskMass a 526336 (24649187))))) + (((weightedMaskMass a 24 (115606739) + (-weightedMaskMass a 2097168 (115606739) + weightedMaskMass a 24 (56985527))) + (-weightedMaskMass a 2099200 (56985527) + (weightedMaskMass a 24 (12786886) + -weightedMaskMass a 4194816 (12786886)))) + ((weightedMaskMass a 34 (8951650) + (-weightedMaskMass a 132 (8951650) + weightedMaskMass a 34 (32989682))) + ((-weightedMaskMass a 2056 (32989682) + weightedMaskMass a 34 (-56031968)) + (-weightedMaskMass a 8448 (-56031968) + weightedMaskMass a 34 (-18875990)))))) + ((((-weightedMaskMass a 16386 (-18875990) + (weightedMaskMass a 34 (-25399375) + -weightedMaskMass a 16416 (-25399375))) + (weightedMaskMass a 34 (6516685) + (-weightedMaskMass a 98304 (6516685) + weightedMaskMass a 34 (-25332059)))) + ((-weightedMaskMass a 131073 (-25332059) + (weightedMaskMass a 34 (-7213425) + -weightedMaskMass a 1048584 (-7213425))) + (weightedMaskMass a 34 (57648026) + (-weightedMaskMass a 1050624 (57648026) + weightedMaskMass a 34 (62227164))))) + (((-weightedMaskMass a 2621440 (62227164) + (weightedMaskMass a 40 (30785632) + -weightedMaskMass a 66 (30785632))) + (weightedMaskMass a 40 (-112009317) + (-weightedMaskMass a 129 (-112009317) + weightedMaskMass a 40 (12776477)))) + ((-weightedMaskMass a 260 (12776477) + (weightedMaskMass a 40 (82750628) + -weightedMaskMass a 520 (82750628))) + ((weightedMaskMass a 40 (-65804659) + -weightedMaskMass a 544 (-65804659)) + (weightedMaskMass a 40 (-13565989) + -weightedMaskMass a 2176 (-13565989))))))))) := by
      simp only [atomCongruenceContributionInt00, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
