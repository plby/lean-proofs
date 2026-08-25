/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate558 : CompactCertificate where
  left := 429
  right := 430
  center := 859 / 2
  grid := fun i =>
    match i.val with
    | 0 => 137
    | 1 => 101
    | 2 => 163
    | 3 => 29
    | 4 => 79
    | 5 => 214
    | 6 => 158
    | 7 => 271
    | 8 => 199
    | 9 => 306
    | 10 => 177
    | 11 => 313
    | 12 => 293
    | 13 => 209
    | 14 => 237
    | 15 => 198
    | 16 => 175
    | 17 => 253
    | 18 => 140
    | 19 => 119
    | 20 => 74
    | 21 => 40
    | 22 => 108
    | 23 => 148
    | 24 => 63
    | 25 => 254
    | _ => 170
  point := fun i =>
    match i.val with
    | 0 => 859 / 2
    | 1 => 1265471024246959 / 4000000000000
    | 2 => 409227328498447 / 800000000000
    | 3 => 369261288745613 / 4000000000000
    | 4 => 991887762467561 / 4000000000000
    | 5 => 2693168224748037 / 4000000000000
    | 6 => 1983775524935981 / 4000000000000
    | 7 => 3399233174348513 / 4000000000000
    | 8 => 2503859771125667 / 4000000000000
    | 9 => 3841564785344141 / 4000000000000
    | 10 => 2217928462927589 / 4000000000000
    | 11 => 3935752978391401 / 4000000000000
    | 12 => 3677290964861869 / 4000000000000
    | 13 => 2624288347977277 / 4000000000000
    | 14 => 2975663287402683 / 4000000000000
    | 15 => 2480797820543627 / 4000000000000
    | 16 => 2191860109500167 / 4000000000000
    | 17 => 635286491584533 / 800000000000
    | 18 => 1757235869019151 / 4000000000000
    | 19 => 1489628307021911 / 4000000000000
    | 20 => 932140228874333 / 4000000000000
    | 21 => 501308115247011 / 4000000000000
    | 22 => 1361149051214033 / 4000000000000
    | 23 => 1858532661221041 / 4000000000000
    | 24 => 785859771125667 / 4000000000000
    | 25 => 3194476339995907 / 4000000000000
    | _ => 2133762150102413 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (4344529009 / 1000000000000) (4344529012 / 1000000000000), orderedInterval (-38258955150 / 1000000000000) (-38258955147 / 1000000000000))
    | 1 => (orderedInterval (6619219077 / 1000000000000) (6619219089 / 1000000000000), orderedInterval (-44377859380 / 1000000000000) (-44377859368 / 1000000000000))
    | 2 => (orderedInterval (-8375774807 / 1000000000000) (-8375774806 / 1000000000000), orderedInterval (-34261001052 / 1000000000000) (-34261001051 / 1000000000000))
    | 3 => (orderedInterval (-75744205391 / 1000000000000) (-75744199216 / 1000000000000), orderedInterval (34452747025 / 1000000000000) (34452753200 / 1000000000000))
    | 4 => (orderedInterval (-27385651778 / 1000000000000) (-27385651777 / 1000000000000), orderedInterval (-42574980705 / 1000000000000) (-42574980704 / 1000000000000))
    | 5 => (orderedInterval (30101602055 / 1000000000000) (30101615408 / 1000000000000), orderedInterval (-6301355386 / 1000000000000) (-6301342033 / 1000000000000))
    | 6 => (orderedInterval (12533689625 / 1000000000000) (12533689626 / 1000000000000), orderedInterval (33551629911 / 1000000000000) (33551629912 / 1000000000000))
    | 7 => (orderedInterval (19211269613 / 1000000000000) (19211271218 / 1000000000000), orderedInterval (-19506444136 / 1000000000000) (-19506442531 / 1000000000000))
    | 8 => (orderedInterval (-31890676824 / 1000000000000) (-31890675647 / 1000000000000), orderedInterval (102229235 / 1000000000000) (102230411 / 1000000000000))
    | 9 => (orderedInterval (-3870084655 / 1000000000000) (-3870084654 / 1000000000000), orderedInterval (25455855570 / 1000000000000) (25455855571 / 1000000000000))
    | 10 => (orderedInterval (24179407740 / 1000000000000) (24179417265 / 1000000000000), orderedInterval (-23759752600 / 1000000000000) (-23759743075 / 1000000000000))
    | 11 => (orderedInterval (-25087688080 / 1000000000000) (-25087686705 / 1000000000000), orderedInterval (-4184844381 / 1000000000000) (-4184843007 / 1000000000000))
    | 12 => (orderedInterval (9727687210 / 1000000000000) (9727687214 / 1000000000000), orderedInterval (-24456465804 / 1000000000000) (-24456465800 / 1000000000000))
    | 13 => (orderedInterval (-8141453185 / 1000000000000) (-8141453184 / 1000000000000), orderedInterval (-30061507609 / 1000000000000) (-30061507608 / 1000000000000))
    | 14 => (orderedInterval (-4186182508 / 1000000000000) (-4186182507 / 1000000000000), orderedInterval (-28949640903 / 1000000000000) (-28949640902 / 1000000000000))
    | 15 => (orderedInterval (-27802162537 / 1000000000000) (-27802087936 / 1000000000000), orderedInterval (15944607969 / 1000000000000) (15944682570 / 1000000000000))
    | 16 => (orderedInterval (29194953517 / 1000000000000) (29195037863 / 1000000000000), orderedInterval (-17617615679 / 1000000000000) (-17617531333 / 1000000000000))
    | 17 => (orderedInterval (-1992046709 / 1000000000000) (-1992046708 / 1000000000000), orderedInterval (-28242521572 / 1000000000000) (-28242521571 / 1000000000000))
    | 18 => (orderedInterval (10194506426 / 1000000000000) (10194506427 / 1000000000000), orderedInterval (36665527282 / 1000000000000) (36665527283 / 1000000000000))
    | 19 => (orderedInterval (25264324251 / 1000000000000) (25264330274 / 1000000000000), orderedInterval (-32762915909 / 1000000000000) (-32762909886 / 1000000000000))
    | 20 => (orderedInterval (50905828657 / 1000000000000) (50905828660 / 1000000000000), orderedInterval (11742090465 / 1000000000000) (11742090467 / 1000000000000))
    | 21 => (orderedInterval (30854471476 / 1000000000000) (30854471477 / 1000000000000), orderedInterval (64124049678 / 1000000000000) (64124049679 / 1000000000000))
    | 22 => (orderedInterval (42307428972 / 1000000000000) (42307431372 / 1000000000000), orderedInterval (-9057161274 / 1000000000000) (-9057158875 / 1000000000000))
    | 23 => (orderedInterval (16518582084 / 1000000000000) (16518582085 / 1000000000000), orderedInterval (33107631356 / 1000000000000) (33107631357 / 1000000000000))
    | 24 => (orderedInterval (35377325468 / 1000000000000) (35377342149 / 1000000000000), orderedInterval (-44686230403 / 1000000000000) (-44686213722 / 1000000000000))
    | 25 => (orderedInterval (27991926467 / 1000000000000) (27991927146 / 1000000000000), orderedInterval (3670643993 / 1000000000000) (3670644671 / 1000000000000))
    | _ => (orderedInterval (5331506937 / 1000000000000) (5331506938 / 1000000000000), orderedInterval (34127065638 / 1000000000000) (34127065639 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (1292197462 / 1000000000000) (1292197493 / 1000000000000)
      | 1 => orderedInterval (-2318040162 / 1000000000000) (-2318039094 / 1000000000000)
      | 2 => orderedInterval (-1363287220 / 1000000000000) (-1363287117 / 1000000000000)
      | 3 => orderedInterval (-1087200306 / 1000000000000) (-1087199234 / 1000000000000)
      | 4 => orderedInterval (-924309451 / 1000000000000) (-924309400 / 1000000000000)
      | 5 => orderedInterval (-2042789485 / 1000000000000) (-2042783755 / 1000000000000)
      | 6 => orderedInterval (-1402731516 / 1000000000000) (-1402731067 / 1000000000000)
      | 7 => orderedInterval (-2795519774 / 1000000000000) (-2795519668 / 1000000000000)
      | _ => orderedInterval (-3065658680 / 1000000000000) (-3065658405 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-17863577854 / 1000000000000) (-17863577818 / 1000000000000)
      | 1 => orderedInterval (-275593691 / 1000000000000) (-275592129 / 1000000000000)
      | 2 => orderedInterval (1194038256 / 1000000000000) (1194038437 / 1000000000000)
      | 3 => orderedInterval (-13749700673 / 1000000000000) (-13749698961 / 1000000000000)
      | 4 => orderedInterval (-3143511345 / 1000000000000) (-3143511261 / 1000000000000)
      | 5 => orderedInterval (215161467 / 1000000000000) (215168929 / 1000000000000)
      | 6 => orderedInterval (-4181143570 / 1000000000000) (-4181143174 / 1000000000000)
      | 7 => orderedInterval (-2927592819 / 1000000000000) (-2927592729 / 1000000000000)
      | _ => orderedInterval (-8631537429 / 1000000000000) (-8631537113 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-1016710121 / 1000000000000) (-1016710081 / 1000000000000)
      | 1 => orderedInterval (5554654896 / 1000000000000) (5554657317 / 1000000000000)
      | 2 => orderedInterval (3954089032 / 1000000000000) (3954089361 / 1000000000000)
      | 3 => orderedInterval (12324789072 / 1000000000000) (12324792034 / 1000000000000)
      | 4 => orderedInterval (2544732877 / 1000000000000) (2544733016 / 1000000000000)
      | 5 => orderedInterval (3562769373 / 1000000000000) (3562779133 / 1000000000000)
      | 6 => orderedInterval (2302253382 / 1000000000000) (2302253734 / 1000000000000)
      | 7 => orderedInterval (2139373897 / 1000000000000) (2139373978 / 1000000000000)
      | _ => orderedInterval (9396625755 / 1000000000000) (9396626215 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (18728555985 / 1000000000000) (18728556032 / 1000000000000)
      | 1 => orderedInterval (-1435745653 / 1000000000000) (-1435741869 / 1000000000000)
      | 2 => orderedInterval (-4677237878 / 1000000000000) (-4677237270 / 1000000000000)
      | 3 => orderedInterval (61482405922 / 1000000000000) (61482411453 / 1000000000000)
      | 4 => orderedInterval (5035125755 / 1000000000000) (5035125989 / 1000000000000)
      | 5 => orderedInterval (1914074676 / 1000000000000) (1914087453 / 1000000000000)
      | 6 => orderedInterval (4998187520 / 1000000000000) (4998187836 / 1000000000000)
      | 7 => orderedInterval (3134546416 / 1000000000000) (3134546491 / 1000000000000)
      | _ => orderedInterval (14192422276 / 1000000000000) (14192423021 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (664021282 / 1000000000000) (664021336 / 1000000000000)
      | 1 => orderedInterval (-13025453764 / 1000000000000) (-13025447827 / 1000000000000)
      | 2 => orderedInterval (-12537088651 / 1000000000000) (-12537087511 / 1000000000000)
      | 3 => orderedInterval (-76348186672 / 1000000000000) (-76348175627 / 1000000000000)
      | 4 => orderedInterval (-7710549298 / 1000000000000) (-7710548892 / 1000000000000)
      | 5 => orderedInterval (-6427361403 / 1000000000000) (-6427344594 / 1000000000000)
      | 6 => orderedInterval (-2471995134 / 1000000000000) (-2471994849 / 1000000000000)
      | 7 => orderedInterval (-2130758763 / 1000000000000) (-2130758691 / 1000000000000)
      | _ => orderedInterval (-29674867154 / 1000000000000) (-29674865876 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-13707339132 / 1000000000000) (-13707330247 / 1000000000000)
    | 1 => orderedInterval (-49363457658 / 1000000000000) (-49363445819 / 1000000000000)
    | 2 => orderedInterval (40762578163 / 1000000000000) (40762594707 / 1000000000000)
    | 3 => orderedInterval (103372335019 / 1000000000000) (103372359136 / 1000000000000)
    | _ => orderedInterval (-149662239557 / 1000000000000) (-149662202531 / 1000000000000)

theorem compactCertificate558_stateChecks0 :
    compactCertificate558.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (859 / 2)) (orderedInterval (4344529009 / 1000000000000) (4344529012 / 1000000000000), orderedInterval (-38258955150 / 1000000000000) (-38258955147 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1265471024246959 / 4000000000000)) (orderedInterval (6619219077 / 1000000000000) (6619219089 / 1000000000000), orderedInterval (-44377859380 / 1000000000000) (-44377859368 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (409227328498447 / 800000000000)) (orderedInterval (-8375774807 / 1000000000000) (-8375774806 / 1000000000000), orderedInterval (-34261001052 / 1000000000000) (-34261001051 / 1000000000000))) = true
  rfl'

theorem compactCertificate558_stateChecks1 :
    compactCertificate558.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (369261288745613 / 4000000000000)) (orderedInterval (-75744205391 / 1000000000000) (-75744199216 / 1000000000000), orderedInterval (34452747025 / 1000000000000) (34452753200 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (991887762467561 / 4000000000000)) (orderedInterval (-27385651778 / 1000000000000) (-27385651777 / 1000000000000), orderedInterval (-42574980705 / 1000000000000) (-42574980704 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 214 12 (2693168224748037 / 4000000000000)) (orderedInterval (30101602055 / 1000000000000) (30101615408 / 1000000000000), orderedInterval (-6301355386 / 1000000000000) (-6301342033 / 1000000000000))) = true
  rfl'

theorem compactCertificate558_stateChecks2 :
    compactCertificate558.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1983775524935981 / 4000000000000)) (orderedInterval (12533689625 / 1000000000000) (12533689626 / 1000000000000), orderedInterval (33551629911 / 1000000000000) (33551629912 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 271 12 (3399233174348513 / 4000000000000)) (orderedInterval (19211269613 / 1000000000000) (19211271218 / 1000000000000), orderedInterval (-19506444136 / 1000000000000) (-19506442531 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (2503859771125667 / 4000000000000)) (orderedInterval (-31890676824 / 1000000000000) (-31890675647 / 1000000000000), orderedInterval (102229235 / 1000000000000) (102230411 / 1000000000000))) = true
  rfl'

theorem compactCertificate558_stateChecks3 :
    compactCertificate558.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 306 12 (3841564785344141 / 4000000000000)) (orderedInterval (-3870084655 / 1000000000000) (-3870084654 / 1000000000000), orderedInterval (25455855570 / 1000000000000) (25455855571 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2217928462927589 / 4000000000000)) (orderedInterval (24179407740 / 1000000000000) (24179417265 / 1000000000000), orderedInterval (-23759752600 / 1000000000000) (-23759743075 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 313 12 (3935752978391401 / 4000000000000)) (orderedInterval (-25087688080 / 1000000000000) (-25087686705 / 1000000000000), orderedInterval (-4184844381 / 1000000000000) (-4184843007 / 1000000000000))) = true
  rfl'

theorem compactCertificate558_stateChecks4 :
    compactCertificate558.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 293 12 (3677290964861869 / 4000000000000)) (orderedInterval (9727687210 / 1000000000000) (9727687214 / 1000000000000), orderedInterval (-24456465804 / 1000000000000) (-24456465800 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 209 12 (2624288347977277 / 4000000000000)) (orderedInterval (-8141453185 / 1000000000000) (-8141453184 / 1000000000000), orderedInterval (-30061507609 / 1000000000000) (-30061507608 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 237 12 (2975663287402683 / 4000000000000)) (orderedInterval (-4186182508 / 1000000000000) (-4186182507 / 1000000000000), orderedInterval (-28949640903 / 1000000000000) (-28949640902 / 1000000000000))) = true
  rfl'

theorem compactCertificate558_stateChecks5 :
    compactCertificate558.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (2480797820543627 / 4000000000000)) (orderedInterval (-27802162537 / 1000000000000) (-27802087936 / 1000000000000), orderedInterval (15944607969 / 1000000000000) (15944682570 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2191860109500167 / 4000000000000)) (orderedInterval (29194953517 / 1000000000000) (29195037863 / 1000000000000), orderedInterval (-17617615679 / 1000000000000) (-17617531333 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 253 12 (635286491584533 / 800000000000)) (orderedInterval (-1992046709 / 1000000000000) (-1992046708 / 1000000000000), orderedInterval (-28242521572 / 1000000000000) (-28242521571 / 1000000000000))) = true
  rfl'

theorem compactCertificate558_stateChecks6 :
    compactCertificate558.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1757235869019151 / 4000000000000)) (orderedInterval (10194506426 / 1000000000000) (10194506427 / 1000000000000), orderedInterval (36665527282 / 1000000000000) (36665527283 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1489628307021911 / 4000000000000)) (orderedInterval (25264324251 / 1000000000000) (25264330274 / 1000000000000), orderedInterval (-32762915909 / 1000000000000) (-32762909886 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (932140228874333 / 4000000000000)) (orderedInterval (50905828657 / 1000000000000) (50905828660 / 1000000000000), orderedInterval (11742090465 / 1000000000000) (11742090467 / 1000000000000))) = true
  rfl'

theorem compactCertificate558_stateChecks7 :
    compactCertificate558.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (501308115247011 / 4000000000000)) (orderedInterval (30854471476 / 1000000000000) (30854471477 / 1000000000000), orderedInterval (64124049678 / 1000000000000) (64124049679 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1361149051214033 / 4000000000000)) (orderedInterval (42307428972 / 1000000000000) (42307431372 / 1000000000000), orderedInterval (-9057161274 / 1000000000000) (-9057158875 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1858532661221041 / 4000000000000)) (orderedInterval (16518582084 / 1000000000000) (16518582085 / 1000000000000), orderedInterval (33107631356 / 1000000000000) (33107631357 / 1000000000000))) = true
  rfl'

theorem compactCertificate558_stateChecks8 :
    compactCertificate558.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (785859771125667 / 4000000000000)) (orderedInterval (35377325468 / 1000000000000) (35377342149 / 1000000000000), orderedInterval (-44686230403 / 1000000000000) (-44686213722 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 254 12 (3194476339995907 / 4000000000000)) (orderedInterval (27991926467 / 1000000000000) (27991927146 / 1000000000000), orderedInterval (3670643993 / 1000000000000) (3670644671 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2133762150102413 / 4000000000000)) (orderedInterval (5331506937 / 1000000000000) (5331506938 / 1000000000000), orderedInterval (34127065638 / 1000000000000) (34127065639 / 1000000000000))) = true
  rfl'

theorem compactCertificate558_states : ∀ j,
    BesselStateValid (compactCertificate558.point j) (compactCertificate558.state j) :=
  compactCertificate558.statesValid_of_checks3 compactCertificate558_stateChecks0
    compactCertificate558_stateChecks1 compactCertificate558_stateChecks2
    compactCertificate558_stateChecks3 compactCertificate558_stateChecks4
    compactCertificate558_stateChecks5 compactCertificate558_stateChecks6
    compactCertificate558_stateChecks7 compactCertificate558_stateChecks8

theorem compactCertificate558_chunkChecks0_0 :
    compactCertificate558.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (859 / 2) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4344529009 / 1000000000000) (4344529012 / 1000000000000), orderedInterval (-38258955150 / 1000000000000) (-38258955147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1265471024246959 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (6619219077 / 1000000000000) (6619219089 / 1000000000000), orderedInterval (-44377859380 / 1000000000000) (-44377859368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (409227328498447 / 800000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8375774807 / 1000000000000) (-8375774806 / 1000000000000), orderedInterval (-34261001052 / 1000000000000) (-34261001051 / 1000000000000)))) (orderedInterval (1292197462 / 1000000000000) (1292197493 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (369261288745613 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-75744205391 / 1000000000000) (-75744199216 / 1000000000000), orderedInterval (34452747025 / 1000000000000) (34452753200 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (991887762467561 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-27385651778 / 1000000000000) (-27385651777 / 1000000000000), orderedInterval (-42574980705 / 1000000000000) (-42574980704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2693168224748037 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30101602055 / 1000000000000) (30101615408 / 1000000000000), orderedInterval (-6301355386 / 1000000000000) (-6301342033 / 1000000000000)))) (orderedInterval (-2318040162 / 1000000000000) (-2318039094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1983775524935981 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12533689625 / 1000000000000) (12533689626 / 1000000000000), orderedInterval (33551629911 / 1000000000000) (33551629912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3399233174348513 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19211269613 / 1000000000000) (19211271218 / 1000000000000), orderedInterval (-19506444136 / 1000000000000) (-19506442531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2503859771125667 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31890676824 / 1000000000000) (-31890675647 / 1000000000000), orderedInterval (102229235 / 1000000000000) (102230411 / 1000000000000)))) (orderedInterval (-1363287220 / 1000000000000) (-1363287117 / 1000000000000))) = true
  rfl'

theorem compactCertificate558_chunkChecks0_1 :
    compactCertificate558.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3841564785344141 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3870084655 / 1000000000000) (-3870084654 / 1000000000000), orderedInterval (25455855570 / 1000000000000) (25455855571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2217928462927589 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24179407740 / 1000000000000) (24179417265 / 1000000000000), orderedInterval (-23759752600 / 1000000000000) (-23759743075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3935752978391401 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25087688080 / 1000000000000) (-25087686705 / 1000000000000), orderedInterval (-4184844381 / 1000000000000) (-4184843007 / 1000000000000)))) (orderedInterval (-1087200306 / 1000000000000) (-1087199234 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3677290964861869 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9727687210 / 1000000000000) (9727687214 / 1000000000000), orderedInterval (-24456465804 / 1000000000000) (-24456465800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2624288347977277 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8141453185 / 1000000000000) (-8141453184 / 1000000000000), orderedInterval (-30061507609 / 1000000000000) (-30061507608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2975663287402683 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4186182508 / 1000000000000) (-4186182507 / 1000000000000), orderedInterval (-28949640903 / 1000000000000) (-28949640902 / 1000000000000)))) (orderedInterval (-924309451 / 1000000000000) (-924309400 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2480797820543627 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27802162537 / 1000000000000) (-27802087936 / 1000000000000), orderedInterval (15944607969 / 1000000000000) (15944682570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2191860109500167 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29194953517 / 1000000000000) (29195037863 / 1000000000000), orderedInterval (-17617615679 / 1000000000000) (-17617531333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (635286491584533 / 800000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1992046709 / 1000000000000) (-1992046708 / 1000000000000), orderedInterval (-28242521572 / 1000000000000) (-28242521571 / 1000000000000)))) (orderedInterval (-2042789485 / 1000000000000) (-2042783755 / 1000000000000))) = true
  rfl'

theorem compactCertificate558_chunkChecks0_2 :
    compactCertificate558.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1757235869019151 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (10194506426 / 1000000000000) (10194506427 / 1000000000000), orderedInterval (36665527282 / 1000000000000) (36665527283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1489628307021911 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (25264324251 / 1000000000000) (25264330274 / 1000000000000), orderedInterval (-32762915909 / 1000000000000) (-32762909886 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (932140228874333 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50905828657 / 1000000000000) (50905828660 / 1000000000000), orderedInterval (11742090465 / 1000000000000) (11742090467 / 1000000000000)))) (orderedInterval (-1402731516 / 1000000000000) (-1402731067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (501308115247011 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (30854471476 / 1000000000000) (30854471477 / 1000000000000), orderedInterval (64124049678 / 1000000000000) (64124049679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1361149051214033 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (42307428972 / 1000000000000) (42307431372 / 1000000000000), orderedInterval (-9057161274 / 1000000000000) (-9057158875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1858532661221041 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (16518582084 / 1000000000000) (16518582085 / 1000000000000), orderedInterval (33107631356 / 1000000000000) (33107631357 / 1000000000000)))) (orderedInterval (-2795519774 / 1000000000000) (-2795519668 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (785859771125667 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (35377325468 / 1000000000000) (35377342149 / 1000000000000), orderedInterval (-44686230403 / 1000000000000) (-44686213722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3194476339995907 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27991926467 / 1000000000000) (27991927146 / 1000000000000), orderedInterval (3670643993 / 1000000000000) (3670644671 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2133762150102413 / 4000000000000) 0 (IntervalRat.scale (859 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (5331506937 / 1000000000000) (5331506938 / 1000000000000), orderedInterval (34127065638 / 1000000000000) (34127065639 / 1000000000000)))) (orderedInterval (-3065658680 / 1000000000000) (-3065658405 / 1000000000000))) = true
  rfl'

theorem compactCertificate558_chunkChecks0 :
    compactCertificate558.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate558.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate558_chunkChecks0_0
    compactCertificate558_chunkChecks0_1 compactCertificate558_chunkChecks0_2

theorem compactCertificate558_chunkChecks1_0 :
    compactCertificate558.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (859 / 2) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4344529009 / 1000000000000) (4344529012 / 1000000000000), orderedInterval (-38258955150 / 1000000000000) (-38258955147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1265471024246959 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (6619219077 / 1000000000000) (6619219089 / 1000000000000), orderedInterval (-44377859380 / 1000000000000) (-44377859368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (409227328498447 / 800000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8375774807 / 1000000000000) (-8375774806 / 1000000000000), orderedInterval (-34261001052 / 1000000000000) (-34261001051 / 1000000000000)))) (orderedInterval (-17863577854 / 1000000000000) (-17863577818 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (369261288745613 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-75744205391 / 1000000000000) (-75744199216 / 1000000000000), orderedInterval (34452747025 / 1000000000000) (34452753200 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (991887762467561 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-27385651778 / 1000000000000) (-27385651777 / 1000000000000), orderedInterval (-42574980705 / 1000000000000) (-42574980704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2693168224748037 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30101602055 / 1000000000000) (30101615408 / 1000000000000), orderedInterval (-6301355386 / 1000000000000) (-6301342033 / 1000000000000)))) (orderedInterval (-275593691 / 1000000000000) (-275592129 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1983775524935981 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12533689625 / 1000000000000) (12533689626 / 1000000000000), orderedInterval (33551629911 / 1000000000000) (33551629912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3399233174348513 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19211269613 / 1000000000000) (19211271218 / 1000000000000), orderedInterval (-19506444136 / 1000000000000) (-19506442531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2503859771125667 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31890676824 / 1000000000000) (-31890675647 / 1000000000000), orderedInterval (102229235 / 1000000000000) (102230411 / 1000000000000)))) (orderedInterval (1194038256 / 1000000000000) (1194038437 / 1000000000000))) = true
  rfl'

theorem compactCertificate558_chunkChecks1_1 :
    compactCertificate558.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3841564785344141 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3870084655 / 1000000000000) (-3870084654 / 1000000000000), orderedInterval (25455855570 / 1000000000000) (25455855571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2217928462927589 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24179407740 / 1000000000000) (24179417265 / 1000000000000), orderedInterval (-23759752600 / 1000000000000) (-23759743075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3935752978391401 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25087688080 / 1000000000000) (-25087686705 / 1000000000000), orderedInterval (-4184844381 / 1000000000000) (-4184843007 / 1000000000000)))) (orderedInterval (-13749700673 / 1000000000000) (-13749698961 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3677290964861869 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9727687210 / 1000000000000) (9727687214 / 1000000000000), orderedInterval (-24456465804 / 1000000000000) (-24456465800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2624288347977277 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8141453185 / 1000000000000) (-8141453184 / 1000000000000), orderedInterval (-30061507609 / 1000000000000) (-30061507608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2975663287402683 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4186182508 / 1000000000000) (-4186182507 / 1000000000000), orderedInterval (-28949640903 / 1000000000000) (-28949640902 / 1000000000000)))) (orderedInterval (-3143511345 / 1000000000000) (-3143511261 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2480797820543627 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27802162537 / 1000000000000) (-27802087936 / 1000000000000), orderedInterval (15944607969 / 1000000000000) (15944682570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2191860109500167 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29194953517 / 1000000000000) (29195037863 / 1000000000000), orderedInterval (-17617615679 / 1000000000000) (-17617531333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (635286491584533 / 800000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1992046709 / 1000000000000) (-1992046708 / 1000000000000), orderedInterval (-28242521572 / 1000000000000) (-28242521571 / 1000000000000)))) (orderedInterval (215161467 / 1000000000000) (215168929 / 1000000000000))) = true
  rfl'

theorem compactCertificate558_chunkChecks1_2 :
    compactCertificate558.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1757235869019151 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (10194506426 / 1000000000000) (10194506427 / 1000000000000), orderedInterval (36665527282 / 1000000000000) (36665527283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1489628307021911 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (25264324251 / 1000000000000) (25264330274 / 1000000000000), orderedInterval (-32762915909 / 1000000000000) (-32762909886 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (932140228874333 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50905828657 / 1000000000000) (50905828660 / 1000000000000), orderedInterval (11742090465 / 1000000000000) (11742090467 / 1000000000000)))) (orderedInterval (-4181143570 / 1000000000000) (-4181143174 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (501308115247011 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (30854471476 / 1000000000000) (30854471477 / 1000000000000), orderedInterval (64124049678 / 1000000000000) (64124049679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1361149051214033 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (42307428972 / 1000000000000) (42307431372 / 1000000000000), orderedInterval (-9057161274 / 1000000000000) (-9057158875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1858532661221041 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (16518582084 / 1000000000000) (16518582085 / 1000000000000), orderedInterval (33107631356 / 1000000000000) (33107631357 / 1000000000000)))) (orderedInterval (-2927592819 / 1000000000000) (-2927592729 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (785859771125667 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (35377325468 / 1000000000000) (35377342149 / 1000000000000), orderedInterval (-44686230403 / 1000000000000) (-44686213722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3194476339995907 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27991926467 / 1000000000000) (27991927146 / 1000000000000), orderedInterval (3670643993 / 1000000000000) (3670644671 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2133762150102413 / 4000000000000) 1 (IntervalRat.scale (859 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (5331506937 / 1000000000000) (5331506938 / 1000000000000), orderedInterval (34127065638 / 1000000000000) (34127065639 / 1000000000000)))) (orderedInterval (-8631537429 / 1000000000000) (-8631537113 / 1000000000000))) = true
  rfl'

theorem compactCertificate558_chunkChecks1 :
    compactCertificate558.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate558.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate558_chunkChecks1_0
    compactCertificate558_chunkChecks1_1 compactCertificate558_chunkChecks1_2

theorem compactCertificate558_chunkChecks2_0 :
    compactCertificate558.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (859 / 2) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4344529009 / 1000000000000) (4344529012 / 1000000000000), orderedInterval (-38258955150 / 1000000000000) (-38258955147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1265471024246959 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (6619219077 / 1000000000000) (6619219089 / 1000000000000), orderedInterval (-44377859380 / 1000000000000) (-44377859368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (409227328498447 / 800000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8375774807 / 1000000000000) (-8375774806 / 1000000000000), orderedInterval (-34261001052 / 1000000000000) (-34261001051 / 1000000000000)))) (orderedInterval (-1016710121 / 1000000000000) (-1016710081 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (369261288745613 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-75744205391 / 1000000000000) (-75744199216 / 1000000000000), orderedInterval (34452747025 / 1000000000000) (34452753200 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (991887762467561 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-27385651778 / 1000000000000) (-27385651777 / 1000000000000), orderedInterval (-42574980705 / 1000000000000) (-42574980704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2693168224748037 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30101602055 / 1000000000000) (30101615408 / 1000000000000), orderedInterval (-6301355386 / 1000000000000) (-6301342033 / 1000000000000)))) (orderedInterval (5554654896 / 1000000000000) (5554657317 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1983775524935981 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12533689625 / 1000000000000) (12533689626 / 1000000000000), orderedInterval (33551629911 / 1000000000000) (33551629912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3399233174348513 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19211269613 / 1000000000000) (19211271218 / 1000000000000), orderedInterval (-19506444136 / 1000000000000) (-19506442531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2503859771125667 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31890676824 / 1000000000000) (-31890675647 / 1000000000000), orderedInterval (102229235 / 1000000000000) (102230411 / 1000000000000)))) (orderedInterval (3954089032 / 1000000000000) (3954089361 / 1000000000000))) = true
  rfl'

theorem compactCertificate558_chunkChecks2_1 :
    compactCertificate558.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3841564785344141 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3870084655 / 1000000000000) (-3870084654 / 1000000000000), orderedInterval (25455855570 / 1000000000000) (25455855571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2217928462927589 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24179407740 / 1000000000000) (24179417265 / 1000000000000), orderedInterval (-23759752600 / 1000000000000) (-23759743075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3935752978391401 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25087688080 / 1000000000000) (-25087686705 / 1000000000000), orderedInterval (-4184844381 / 1000000000000) (-4184843007 / 1000000000000)))) (orderedInterval (12324789072 / 1000000000000) (12324792034 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3677290964861869 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9727687210 / 1000000000000) (9727687214 / 1000000000000), orderedInterval (-24456465804 / 1000000000000) (-24456465800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2624288347977277 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8141453185 / 1000000000000) (-8141453184 / 1000000000000), orderedInterval (-30061507609 / 1000000000000) (-30061507608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2975663287402683 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4186182508 / 1000000000000) (-4186182507 / 1000000000000), orderedInterval (-28949640903 / 1000000000000) (-28949640902 / 1000000000000)))) (orderedInterval (2544732877 / 1000000000000) (2544733016 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2480797820543627 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27802162537 / 1000000000000) (-27802087936 / 1000000000000), orderedInterval (15944607969 / 1000000000000) (15944682570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2191860109500167 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29194953517 / 1000000000000) (29195037863 / 1000000000000), orderedInterval (-17617615679 / 1000000000000) (-17617531333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (635286491584533 / 800000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1992046709 / 1000000000000) (-1992046708 / 1000000000000), orderedInterval (-28242521572 / 1000000000000) (-28242521571 / 1000000000000)))) (orderedInterval (3562769373 / 1000000000000) (3562779133 / 1000000000000))) = true
  rfl'

theorem compactCertificate558_chunkChecks2_2 :
    compactCertificate558.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1757235869019151 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (10194506426 / 1000000000000) (10194506427 / 1000000000000), orderedInterval (36665527282 / 1000000000000) (36665527283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1489628307021911 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (25264324251 / 1000000000000) (25264330274 / 1000000000000), orderedInterval (-32762915909 / 1000000000000) (-32762909886 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (932140228874333 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50905828657 / 1000000000000) (50905828660 / 1000000000000), orderedInterval (11742090465 / 1000000000000) (11742090467 / 1000000000000)))) (orderedInterval (2302253382 / 1000000000000) (2302253734 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (501308115247011 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (30854471476 / 1000000000000) (30854471477 / 1000000000000), orderedInterval (64124049678 / 1000000000000) (64124049679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1361149051214033 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (42307428972 / 1000000000000) (42307431372 / 1000000000000), orderedInterval (-9057161274 / 1000000000000) (-9057158875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1858532661221041 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (16518582084 / 1000000000000) (16518582085 / 1000000000000), orderedInterval (33107631356 / 1000000000000) (33107631357 / 1000000000000)))) (orderedInterval (2139373897 / 1000000000000) (2139373978 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (785859771125667 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (35377325468 / 1000000000000) (35377342149 / 1000000000000), orderedInterval (-44686230403 / 1000000000000) (-44686213722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3194476339995907 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27991926467 / 1000000000000) (27991927146 / 1000000000000), orderedInterval (3670643993 / 1000000000000) (3670644671 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2133762150102413 / 4000000000000) 2 (IntervalRat.scale (859 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (5331506937 / 1000000000000) (5331506938 / 1000000000000), orderedInterval (34127065638 / 1000000000000) (34127065639 / 1000000000000)))) (orderedInterval (9396625755 / 1000000000000) (9396626215 / 1000000000000))) = true
  rfl'

theorem compactCertificate558_chunkChecks2 :
    compactCertificate558.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate558.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate558_chunkChecks2_0
    compactCertificate558_chunkChecks2_1 compactCertificate558_chunkChecks2_2

theorem compactCertificate558_chunkChecks3_0 :
    compactCertificate558.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (859 / 2) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4344529009 / 1000000000000) (4344529012 / 1000000000000), orderedInterval (-38258955150 / 1000000000000) (-38258955147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1265471024246959 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (6619219077 / 1000000000000) (6619219089 / 1000000000000), orderedInterval (-44377859380 / 1000000000000) (-44377859368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (409227328498447 / 800000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8375774807 / 1000000000000) (-8375774806 / 1000000000000), orderedInterval (-34261001052 / 1000000000000) (-34261001051 / 1000000000000)))) (orderedInterval (18728555985 / 1000000000000) (18728556032 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (369261288745613 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-75744205391 / 1000000000000) (-75744199216 / 1000000000000), orderedInterval (34452747025 / 1000000000000) (34452753200 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (991887762467561 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-27385651778 / 1000000000000) (-27385651777 / 1000000000000), orderedInterval (-42574980705 / 1000000000000) (-42574980704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2693168224748037 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30101602055 / 1000000000000) (30101615408 / 1000000000000), orderedInterval (-6301355386 / 1000000000000) (-6301342033 / 1000000000000)))) (orderedInterval (-1435745653 / 1000000000000) (-1435741869 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1983775524935981 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12533689625 / 1000000000000) (12533689626 / 1000000000000), orderedInterval (33551629911 / 1000000000000) (33551629912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3399233174348513 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19211269613 / 1000000000000) (19211271218 / 1000000000000), orderedInterval (-19506444136 / 1000000000000) (-19506442531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2503859771125667 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31890676824 / 1000000000000) (-31890675647 / 1000000000000), orderedInterval (102229235 / 1000000000000) (102230411 / 1000000000000)))) (orderedInterval (-4677237878 / 1000000000000) (-4677237270 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate558_chunkChecks3_1 :
    compactCertificate558.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3841564785344141 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3870084655 / 1000000000000) (-3870084654 / 1000000000000), orderedInterval (25455855570 / 1000000000000) (25455855571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2217928462927589 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24179407740 / 1000000000000) (24179417265 / 1000000000000), orderedInterval (-23759752600 / 1000000000000) (-23759743075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3935752978391401 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25087688080 / 1000000000000) (-25087686705 / 1000000000000), orderedInterval (-4184844381 / 1000000000000) (-4184843007 / 1000000000000)))) (orderedInterval (61482405922 / 1000000000000) (61482411453 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3677290964861869 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9727687210 / 1000000000000) (9727687214 / 1000000000000), orderedInterval (-24456465804 / 1000000000000) (-24456465800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2624288347977277 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8141453185 / 1000000000000) (-8141453184 / 1000000000000), orderedInterval (-30061507609 / 1000000000000) (-30061507608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2975663287402683 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4186182508 / 1000000000000) (-4186182507 / 1000000000000), orderedInterval (-28949640903 / 1000000000000) (-28949640902 / 1000000000000)))) (orderedInterval (5035125755 / 1000000000000) (5035125989 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2480797820543627 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27802162537 / 1000000000000) (-27802087936 / 1000000000000), orderedInterval (15944607969 / 1000000000000) (15944682570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2191860109500167 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29194953517 / 1000000000000) (29195037863 / 1000000000000), orderedInterval (-17617615679 / 1000000000000) (-17617531333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (635286491584533 / 800000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1992046709 / 1000000000000) (-1992046708 / 1000000000000), orderedInterval (-28242521572 / 1000000000000) (-28242521571 / 1000000000000)))) (orderedInterval (1914074676 / 1000000000000) (1914087453 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate558_chunkChecks3_2 :
    compactCertificate558.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1757235869019151 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (10194506426 / 1000000000000) (10194506427 / 1000000000000), orderedInterval (36665527282 / 1000000000000) (36665527283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1489628307021911 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (25264324251 / 1000000000000) (25264330274 / 1000000000000), orderedInterval (-32762915909 / 1000000000000) (-32762909886 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (932140228874333 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50905828657 / 1000000000000) (50905828660 / 1000000000000), orderedInterval (11742090465 / 1000000000000) (11742090467 / 1000000000000)))) (orderedInterval (4998187520 / 1000000000000) (4998187836 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (501308115247011 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (30854471476 / 1000000000000) (30854471477 / 1000000000000), orderedInterval (64124049678 / 1000000000000) (64124049679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1361149051214033 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (42307428972 / 1000000000000) (42307431372 / 1000000000000), orderedInterval (-9057161274 / 1000000000000) (-9057158875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1858532661221041 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (16518582084 / 1000000000000) (16518582085 / 1000000000000), orderedInterval (33107631356 / 1000000000000) (33107631357 / 1000000000000)))) (orderedInterval (3134546416 / 1000000000000) (3134546491 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (785859771125667 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (35377325468 / 1000000000000) (35377342149 / 1000000000000), orderedInterval (-44686230403 / 1000000000000) (-44686213722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3194476339995907 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27991926467 / 1000000000000) (27991927146 / 1000000000000), orderedInterval (3670643993 / 1000000000000) (3670644671 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2133762150102413 / 4000000000000) 3 (IntervalRat.scale (859 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (5331506937 / 1000000000000) (5331506938 / 1000000000000), orderedInterval (34127065638 / 1000000000000) (34127065639 / 1000000000000)))) (orderedInterval (14192422276 / 1000000000000) (14192423021 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate558_chunkChecks3 :
    compactCertificate558.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate558.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate558_chunkChecks3_0
    compactCertificate558_chunkChecks3_1 compactCertificate558_chunkChecks3_2

theorem compactCertificate558_chunkChecks4_0 :
    compactCertificate558.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (859 / 2) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4344529009 / 1000000000000) (4344529012 / 1000000000000), orderedInterval (-38258955150 / 1000000000000) (-38258955147 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1265471024246959 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (6619219077 / 1000000000000) (6619219089 / 1000000000000), orderedInterval (-44377859380 / 1000000000000) (-44377859368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (409227328498447 / 800000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8375774807 / 1000000000000) (-8375774806 / 1000000000000), orderedInterval (-34261001052 / 1000000000000) (-34261001051 / 1000000000000)))) (orderedInterval (664021282 / 1000000000000) (664021336 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (369261288745613 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-75744205391 / 1000000000000) (-75744199216 / 1000000000000), orderedInterval (34452747025 / 1000000000000) (34452753200 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (991887762467561 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-27385651778 / 1000000000000) (-27385651777 / 1000000000000), orderedInterval (-42574980705 / 1000000000000) (-42574980704 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2693168224748037 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30101602055 / 1000000000000) (30101615408 / 1000000000000), orderedInterval (-6301355386 / 1000000000000) (-6301342033 / 1000000000000)))) (orderedInterval (-13025453764 / 1000000000000) (-13025447827 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1983775524935981 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12533689625 / 1000000000000) (12533689626 / 1000000000000), orderedInterval (33551629911 / 1000000000000) (33551629912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3399233174348513 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19211269613 / 1000000000000) (19211271218 / 1000000000000), orderedInterval (-19506444136 / 1000000000000) (-19506442531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2503859771125667 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31890676824 / 1000000000000) (-31890675647 / 1000000000000), orderedInterval (102229235 / 1000000000000) (102230411 / 1000000000000)))) (orderedInterval (-12537088651 / 1000000000000) (-12537087511 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate558_chunkChecks4_1 :
    compactCertificate558.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3841564785344141 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3870084655 / 1000000000000) (-3870084654 / 1000000000000), orderedInterval (25455855570 / 1000000000000) (25455855571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2217928462927589 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24179407740 / 1000000000000) (24179417265 / 1000000000000), orderedInterval (-23759752600 / 1000000000000) (-23759743075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3935752978391401 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25087688080 / 1000000000000) (-25087686705 / 1000000000000), orderedInterval (-4184844381 / 1000000000000) (-4184843007 / 1000000000000)))) (orderedInterval (-76348186672 / 1000000000000) (-76348175627 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3677290964861869 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (9727687210 / 1000000000000) (9727687214 / 1000000000000), orderedInterval (-24456465804 / 1000000000000) (-24456465800 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2624288347977277 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8141453185 / 1000000000000) (-8141453184 / 1000000000000), orderedInterval (-30061507609 / 1000000000000) (-30061507608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2975663287402683 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4186182508 / 1000000000000) (-4186182507 / 1000000000000), orderedInterval (-28949640903 / 1000000000000) (-28949640902 / 1000000000000)))) (orderedInterval (-7710549298 / 1000000000000) (-7710548892 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2480797820543627 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27802162537 / 1000000000000) (-27802087936 / 1000000000000), orderedInterval (15944607969 / 1000000000000) (15944682570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2191860109500167 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (29194953517 / 1000000000000) (29195037863 / 1000000000000), orderedInterval (-17617615679 / 1000000000000) (-17617531333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (635286491584533 / 800000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1992046709 / 1000000000000) (-1992046708 / 1000000000000), orderedInterval (-28242521572 / 1000000000000) (-28242521571 / 1000000000000)))) (orderedInterval (-6427361403 / 1000000000000) (-6427344594 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate558_chunkChecks4_2 :
    compactCertificate558.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1757235869019151 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (10194506426 / 1000000000000) (10194506427 / 1000000000000), orderedInterval (36665527282 / 1000000000000) (36665527283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1489628307021911 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (25264324251 / 1000000000000) (25264330274 / 1000000000000), orderedInterval (-32762915909 / 1000000000000) (-32762909886 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (932140228874333 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (50905828657 / 1000000000000) (50905828660 / 1000000000000), orderedInterval (11742090465 / 1000000000000) (11742090467 / 1000000000000)))) (orderedInterval (-2471995134 / 1000000000000) (-2471994849 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (501308115247011 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (30854471476 / 1000000000000) (30854471477 / 1000000000000), orderedInterval (64124049678 / 1000000000000) (64124049679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1361149051214033 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (42307428972 / 1000000000000) (42307431372 / 1000000000000), orderedInterval (-9057161274 / 1000000000000) (-9057158875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1858532661221041 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (16518582084 / 1000000000000) (16518582085 / 1000000000000), orderedInterval (33107631356 / 1000000000000) (33107631357 / 1000000000000)))) (orderedInterval (-2130758763 / 1000000000000) (-2130758691 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (785859771125667 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (35377325468 / 1000000000000) (35377342149 / 1000000000000), orderedInterval (-44686230403 / 1000000000000) (-44686213722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3194476339995907 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27991926467 / 1000000000000) (27991927146 / 1000000000000), orderedInterval (3670643993 / 1000000000000) (3670644671 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2133762150102413 / 4000000000000) 4 (IntervalRat.scale (859 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (5331506937 / 1000000000000) (5331506938 / 1000000000000), orderedInterval (34127065638 / 1000000000000) (34127065639 / 1000000000000)))) (orderedInterval (-29674867154 / 1000000000000) (-29674865876 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate558_chunkChecks4 :
    compactCertificate558.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate558.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate558_chunkChecks4_0
    compactCertificate558_chunkChecks4_1 compactCertificate558_chunkChecks4_2

theorem compactCertificate558_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate558.chunkCheck r b = true :=
  compactCertificate558.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate558_chunkChecks0
    · exact compactCertificate558_chunkChecks1
    · exact compactCertificate558_chunkChecks2
    · exact compactCertificate558_chunkChecks3
    · exact compactCertificate558_chunkChecks4)

theorem compactCertificate558_coefficient0 :
    compactCertificate558.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate558_coefficient1 :
    compactCertificate558.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate558_coefficient2 :
    compactCertificate558.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate558_coefficient3 :
    compactCertificate558.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate558_coefficient4 :
    compactCertificate558.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate558_coefficients : ∀ r : Fin 5,
    compactCertificate558.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate558_coefficient0
  · exact compactCertificate558_coefficient1
  · exact compactCertificate558_coefficient2
  · exact compactCertificate558_coefficient3
  · exact compactCertificate558_coefficient4

theorem compactCertificate558_lower : (1 : ℚ) ≤ compactCertificate558.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate558, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate558_proves {t : ℝ} (ht : t ∈ compactCertificate558.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate558.proves compactCertificate558_states compactCertificate558_chunks
    compactCertificate558_coefficients compactCertificate558_lower ht

end Erdos232
