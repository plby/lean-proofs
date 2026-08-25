/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate555 : CompactCertificate where
  left := 426
  right := 427
  center := 853 / 2
  grid := fun i =>
    match i.val with
    | 0 => 136
    | 1 => 100
    | 2 => 162
    | 3 => 29
    | 4 => 78
    | 5 => 213
    | 6 => 157
    | 7 => 269
    | 8 => 198
    | 9 => 304
    | 10 => 175
    | 11 => 311
    | 12 => 291
    | 13 => 207
    | 14 => 235
    | 15 => 196
    | 16 => 173
    | 17 => 251
    | 18 => 139
    | 19 => 118
    | 20 => 74
    | 21 => 40
    | 22 => 108
    | 23 => 147
    | 24 => 62
    | 25 => 253
    | _ => 169
  point := fun i =>
    match i.val with
    | 0 => 853 / 2
    | 1 => 1256631878559553 / 4000000000000
    | 2 => 406368930394849 / 800000000000
    | 3 => 366682048079171 / 4000000000000
    | 4 => 984959559237287 / 4000000000000
    | 5 => 2674356805250379 / 4000000000000
    | 6 => 1969919118475427 / 4000000000000
    | 7 => 3375489985703471 / 4000000000000
    | 8 => 2486370645832589 / 4000000000000
    | 9 => 3814731969614147 / 4000000000000
    | 10 => 2202436529542763 / 4000000000000
    | 11 => 3908262270742567 / 4000000000000
    | 12 => 3651605579775523 / 4000000000000
    | 13 => 2605958045197459 / 4000000000000
    | 14 => 2954878677711861 / 4000000000000
    | 15 => 2463469779887909 / 4000000000000
    | 16 => 2176550260074089 / 4000000000000
    | 17 => 630849100490811 / 800000000000
    | 18 => 1744961811726817 / 4000000000000
    | 19 => 1479223452723737 / 4000000000000
    | 20 => 925629354167411 / 4000000000000
    | 21 => 497806545175437 / 4000000000000
    | 22 => 1351641607317311 / 4000000000000
    | 23 => 1845551059396447 / 4000000000000
    | 24 => 780370645832589 / 4000000000000
    | 25 => 3172163350426669 / 4000000000000
    | _ => 2118858107144771 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (1101109043 / 1000000000000) (1101109045 / 1000000000000), orderedInterval (38617995055 / 1000000000000) (38617995056 / 1000000000000))
    | 1 => (orderedInterval (31777079248 / 1000000000000) (31777079249 / 1000000000000), orderedInterval (31834363166 / 1000000000000) (31834363167 / 1000000000000))
    | 2 => (orderedInterval (-6744844672 / 1000000000000) (-6744844667 / 1000000000000), orderedInterval (34759940786 / 1000000000000) (34759940791 / 1000000000000))
    | 3 => (orderedInterval (-81280842870 / 1000000000000) (-81280842869 / 1000000000000), orderedInterval (-17940995797 / 1000000000000) (-17940995795 / 1000000000000))
    | 4 => (orderedInterval (46637230552 / 1000000000000) (46637242403 / 1000000000000), orderedInterval (-20351273932 / 1000000000000) (-20351262081 / 1000000000000))
    | 5 => (orderedInterval (-6588706952 / 1000000000000) (-6588706951 / 1000000000000), orderedInterval (-30140933624 / 1000000000000) (-30140933623 / 1000000000000))
    | 6 => (orderedInterval (-1253721855 / 1000000000000) (-1253721854 / 1000000000000), orderedInterval (-35930758788 / 1000000000000) (-35930758787 / 1000000000000))
    | 7 => (orderedInterval (11466844854 / 1000000000000) (11466844869 / 1000000000000), orderedInterval (-24965046390 / 1000000000000) (-24965046375 / 1000000000000))
    | 8 => (orderedInterval (10748286679 / 1000000000000) (10748286680 / 1000000000000), orderedInterval (30135172253 / 1000000000000) (30135172254 / 1000000000000))
    | 9 => (orderedInterval (-14070591786 / 1000000000000) (-14070591726 / 1000000000000), orderedInterval (21676632272 / 1000000000000) (21676632331 / 1000000000000))
    | 10 => (orderedInterval (-33968975213 / 1000000000000) (-33968973977 / 1000000000000), orderedInterval (1553431408 / 1000000000000) (1553432644 / 1000000000000))
    | 11 => (orderedInterval (-18584875090 / 1000000000000) (-18584875088 / 1000000000000), orderedInterval (-17488072499 / 1000000000000) (-17488072498 / 1000000000000))
    | 12 => (orderedInterval (13048123222 / 1000000000000) (13048123256 / 1000000000000), orderedInterval (-22965920011 / 1000000000000) (-22965919977 / 1000000000000))
    | 13 => (orderedInterval (-28861836931 / 1000000000000) (-28861769069 / 1000000000000), orderedInterval (12029274601 / 1000000000000) (12029342463 / 1000000000000))
    | 14 => (orderedInterval (-27674036574 / 1000000000000) (-27674036548 / 1000000000000), orderedInterval (-9775940042 / 1000000000000) (-9775940017 / 1000000000000))
    | 15 => (orderedInterval (25194443977 / 1000000000000) (25194443978 / 1000000000000), orderedInterval (19952928090 / 1000000000000) (19952928091 / 1000000000000))
    | 16 => (orderedInterval (-33852664979 / 1000000000000) (-33852664873 / 1000000000000), orderedInterval (-4863551881 / 1000000000000) (-4863551775 / 1000000000000))
    | 17 => (orderedInterval (-20517784270 / 1000000000000) (-20517784269 / 1000000000000), orderedInterval (-19642485688 / 1000000000000) (-19642485687 / 1000000000000))
    | 18 => (orderedInterval (-12890239032 / 1000000000000) (-12890239031 / 1000000000000), orderedInterval (-35945964825 / 1000000000000) (-35945964824 / 1000000000000))
    | 19 => (orderedInterval (-4843772277 / 1000000000000) (-4843772272 / 1000000000000), orderedInterval (41213789195 / 1000000000000) (41213789200 / 1000000000000))
    | 20 => (orderedInterval (-14780104269 / 1000000000000) (-14780104097 / 1000000000000), orderedInterval (50357202052 / 1000000000000) (50357202224 / 1000000000000))
    | 21 => (orderedInterval (-29664159741 / 1000000000000) (-29664157800 / 1000000000000), orderedInterval (65199616994 / 1000000000000) (65199618935 / 1000000000000))
    | 22 => (orderedInterval (-24385482827 / 1000000000000) (-24385479014 / 1000000000000), orderedInterval (35943446864 / 1000000000000) (35943450677 / 1000000000000))
    | 23 => (orderedInterval (-13042723204 / 1000000000000) (-13042723203 / 1000000000000), orderedInterval (-34766339296 / 1000000000000) (-34766339295 / 1000000000000))
    | 24 => (orderedInterval (50874968014 / 1000000000000) (50874968015 / 1000000000000), orderedInterval (25848403859 / 1000000000000) (25848403860 / 1000000000000))
    | 25 => (orderedInterval (23793232734 / 1000000000000) (23793253712 / 1000000000000), orderedInterval (-15398098694 / 1000000000000) (-15398077716 / 1000000000000))
    | _ => (orderedInterval (14435032633 / 1000000000000) (14435032789 / 1000000000000), orderedInterval (-31532617968 / 1000000000000) (-31532617812 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (336746620 / 1000000000000) (336746651 / 1000000000000)
      | 1 => orderedInterval (3053035019 / 1000000000000) (3053035503 / 1000000000000)
      | 2 => orderedInterval (-93918504 / 1000000000000) (-93918479 / 1000000000000)
      | 3 => orderedInterval (-2658596852 / 1000000000000) (-2658596580 / 1000000000000)
      | 4 => orderedInterval (-2824770370 / 1000000000000) (-2824763901 / 1000000000000)
      | 5 => orderedInterval (1702876300 / 1000000000000) (1702876347 / 1000000000000)
      | 6 => orderedInterval (1854038741 / 1000000000000) (1854038854 / 1000000000000)
      | 7 => orderedInterval (2100561684 / 1000000000000) (2100561858 / 1000000000000)
      | _ => orderedInterval (-4338517267 / 1000000000000) (-4338515412 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (17954665111 / 1000000000000) (17954665146 / 1000000000000)
      | 1 => orderedInterval (2971779062 / 1000000000000) (2971779370 / 1000000000000)
      | 2 => orderedInterval (2585019934 / 1000000000000) (2585019977 / 1000000000000)
      | 3 => orderedInterval (-14159253088 / 1000000000000) (-14159252596 / 1000000000000)
      | 4 => orderedInterval (2710724696 / 1000000000000) (2710734583 / 1000000000000)
      | 5 => orderedInterval (-242059713 / 1000000000000) (-242059645 / 1000000000000)
      | 6 => orderedInterval (4745623850 / 1000000000000) (4745623952 / 1000000000000)
      | 7 => orderedInterval (1885039392 / 1000000000000) (1885039518 / 1000000000000)
      | _ => orderedInterval (9750061413 / 1000000000000) (9750064791 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-77767830 / 1000000000000) (-77767790 / 1000000000000)
      | 1 => orderedInterval (-1766340657 / 1000000000000) (-1766340431 / 1000000000000)
      | 2 => orderedInterval (826792833 / 1000000000000) (826792909 / 1000000000000)
      | 3 => orderedInterval (5592475832 / 1000000000000) (5592476790 / 1000000000000)
      | 4 => orderedInterval (7020976181 / 1000000000000) (7020991318 / 1000000000000)
      | 5 => orderedInterval (-1963567119 / 1000000000000) (-1963567021 / 1000000000000)
      | 6 => orderedInterval (-2231860182 / 1000000000000) (-2231860085 / 1000000000000)
      | 7 => orderedInterval (-1568130997 / 1000000000000) (-1568130893 / 1000000000000)
      | _ => orderedInterval (10787248439 / 1000000000000) (10787254641 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-18871066249 / 1000000000000) (-18871066203 / 1000000000000)
      | 1 => orderedInterval (-8109144102 / 1000000000000) (-8109143897 / 1000000000000)
      | 2 => orderedInterval (-8221088480 / 1000000000000) (-8221088342 / 1000000000000)
      | 3 => orderedInterval (72691855380 / 1000000000000) (72691857342 / 1000000000000)
      | 4 => orderedInterval (-8393756339 / 1000000000000) (-8393733193 / 1000000000000)
      | 5 => orderedInterval (1911581196 / 1000000000000) (1911581344 / 1000000000000)
      | 6 => orderedInterval (-4886301150 / 1000000000000) (-4886301056 / 1000000000000)
      | 7 => orderedInterval (-2934108657 / 1000000000000) (-2934108566 / 1000000000000)
      | _ => orderedInterval (-19433247452 / 1000000000000) (-19433236026 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-184271946 / 1000000000000) (-184271892 / 1000000000000)
      | 1 => orderedInterval (3057675098 / 1000000000000) (3057675333 / 1000000000000)
      | 2 => orderedInterval (-4210024606 / 1000000000000) (-4210024349 / 1000000000000)
      | 3 => orderedInterval (-17596124941 / 1000000000000) (-17596120757 / 1000000000000)
      | 4 => orderedInterval (-18503934915 / 1000000000000) (-18503899454 / 1000000000000)
      | 5 => orderedInterval (249640755 / 1000000000000) (249640986 / 1000000000000)
      | 6 => orderedInterval (2392043967 / 1000000000000) (2392044059 / 1000000000000)
      | 7 => orderedInterval (1604717599 / 1000000000000) (1604717683 / 1000000000000)
      | _ => orderedInterval (-29492376409 / 1000000000000) (-29492355268 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-868544629 / 1000000000000) (-868535159 / 1000000000000)
    | 1 => orderedInterval (28201600657 / 1000000000000) (28201615096 / 1000000000000)
    | 2 => orderedInterval (16619826500 / 1000000000000) (16619849438 / 1000000000000)
    | 3 => orderedInterval (3754724147 / 1000000000000) (3754761403 / 1000000000000)
    | _ => orderedInterval (-62682655398 / 1000000000000) (-62682593659 / 1000000000000)

theorem compactCertificate555_stateChecks0 :
    compactCertificate555.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (853 / 2)) (orderedInterval (1101109043 / 1000000000000) (1101109045 / 1000000000000), orderedInterval (38617995055 / 1000000000000) (38617995056 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1256631878559553 / 4000000000000)) (orderedInterval (31777079248 / 1000000000000) (31777079249 / 1000000000000), orderedInterval (31834363166 / 1000000000000) (31834363167 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (406368930394849 / 800000000000)) (orderedInterval (-6744844672 / 1000000000000) (-6744844667 / 1000000000000), orderedInterval (34759940786 / 1000000000000) (34759940791 / 1000000000000))) = true
  rfl'

theorem compactCertificate555_stateChecks1 :
    compactCertificate555.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (366682048079171 / 4000000000000)) (orderedInterval (-81280842870 / 1000000000000) (-81280842869 / 1000000000000), orderedInterval (-17940995797 / 1000000000000) (-17940995795 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (984959559237287 / 4000000000000)) (orderedInterval (46637230552 / 1000000000000) (46637242403 / 1000000000000), orderedInterval (-20351273932 / 1000000000000) (-20351262081 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (2674356805250379 / 4000000000000)) (orderedInterval (-6588706952 / 1000000000000) (-6588706951 / 1000000000000), orderedInterval (-30140933624 / 1000000000000) (-30140933623 / 1000000000000))) = true
  rfl'

theorem compactCertificate555_stateChecks2 :
    compactCertificate555.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1969919118475427 / 4000000000000)) (orderedInterval (-1253721855 / 1000000000000) (-1253721854 / 1000000000000), orderedInterval (-35930758788 / 1000000000000) (-35930758787 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 269 12 (3375489985703471 / 4000000000000)) (orderedInterval (11466844854 / 1000000000000) (11466844869 / 1000000000000), orderedInterval (-24965046390 / 1000000000000) (-24965046375 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (2486370645832589 / 4000000000000)) (orderedInterval (10748286679 / 1000000000000) (10748286680 / 1000000000000), orderedInterval (30135172253 / 1000000000000) (30135172254 / 1000000000000))) = true
  rfl'

theorem compactCertificate555_stateChecks3 :
    compactCertificate555.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 304 12 (3814731969614147 / 4000000000000)) (orderedInterval (-14070591786 / 1000000000000) (-14070591726 / 1000000000000), orderedInterval (21676632272 / 1000000000000) (21676632331 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2202436529542763 / 4000000000000)) (orderedInterval (-33968975213 / 1000000000000) (-33968973977 / 1000000000000), orderedInterval (1553431408 / 1000000000000) (1553432644 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 311 12 (3908262270742567 / 4000000000000)) (orderedInterval (-18584875090 / 1000000000000) (-18584875088 / 1000000000000), orderedInterval (-17488072499 / 1000000000000) (-17488072498 / 1000000000000))) = true
  rfl'

theorem compactCertificate555_stateChecks4 :
    compactCertificate555.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 291 12 (3651605579775523 / 4000000000000)) (orderedInterval (13048123222 / 1000000000000) (13048123256 / 1000000000000), orderedInterval (-22965920011 / 1000000000000) (-22965919977 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 207 12 (2605958045197459 / 4000000000000)) (orderedInterval (-28861836931 / 1000000000000) (-28861769069 / 1000000000000), orderedInterval (12029274601 / 1000000000000) (12029342463 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 235 12 (2954878677711861 / 4000000000000)) (orderedInterval (-27674036574 / 1000000000000) (-27674036548 / 1000000000000), orderedInterval (-9775940042 / 1000000000000) (-9775940017 / 1000000000000))) = true
  rfl'

theorem compactCertificate555_stateChecks5 :
    compactCertificate555.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (2463469779887909 / 4000000000000)) (orderedInterval (25194443977 / 1000000000000) (25194443978 / 1000000000000), orderedInterval (19952928090 / 1000000000000) (19952928091 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2176550260074089 / 4000000000000)) (orderedInterval (-33852664979 / 1000000000000) (-33852664873 / 1000000000000), orderedInterval (-4863551881 / 1000000000000) (-4863551775 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 251 12 (630849100490811 / 800000000000)) (orderedInterval (-20517784270 / 1000000000000) (-20517784269 / 1000000000000), orderedInterval (-19642485688 / 1000000000000) (-19642485687 / 1000000000000))) = true
  rfl'

theorem compactCertificate555_stateChecks6 :
    compactCertificate555.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1744961811726817 / 4000000000000)) (orderedInterval (-12890239032 / 1000000000000) (-12890239031 / 1000000000000), orderedInterval (-35945964825 / 1000000000000) (-35945964824 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1479223452723737 / 4000000000000)) (orderedInterval (-4843772277 / 1000000000000) (-4843772272 / 1000000000000), orderedInterval (41213789195 / 1000000000000) (41213789200 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (925629354167411 / 4000000000000)) (orderedInterval (-14780104269 / 1000000000000) (-14780104097 / 1000000000000), orderedInterval (50357202052 / 1000000000000) (50357202224 / 1000000000000))) = true
  rfl'

theorem compactCertificate555_stateChecks7 :
    compactCertificate555.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (497806545175437 / 4000000000000)) (orderedInterval (-29664159741 / 1000000000000) (-29664157800 / 1000000000000), orderedInterval (65199616994 / 1000000000000) (65199618935 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1351641607317311 / 4000000000000)) (orderedInterval (-24385482827 / 1000000000000) (-24385479014 / 1000000000000), orderedInterval (35943446864 / 1000000000000) (35943450677 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1845551059396447 / 4000000000000)) (orderedInterval (-13042723204 / 1000000000000) (-13042723203 / 1000000000000), orderedInterval (-34766339296 / 1000000000000) (-34766339295 / 1000000000000))) = true
  rfl'

theorem compactCertificate555_stateChecks8 :
    compactCertificate555.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (780370645832589 / 4000000000000)) (orderedInterval (50874968014 / 1000000000000) (50874968015 / 1000000000000), orderedInterval (25848403859 / 1000000000000) (25848403860 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 253 12 (3172163350426669 / 4000000000000)) (orderedInterval (23793232734 / 1000000000000) (23793253712 / 1000000000000), orderedInterval (-15398098694 / 1000000000000) (-15398077716 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2118858107144771 / 4000000000000)) (orderedInterval (14435032633 / 1000000000000) (14435032789 / 1000000000000), orderedInterval (-31532617968 / 1000000000000) (-31532617812 / 1000000000000))) = true
  rfl'

theorem compactCertificate555_states : ∀ j,
    BesselStateValid (compactCertificate555.point j) (compactCertificate555.state j) :=
  compactCertificate555.statesValid_of_checks3 compactCertificate555_stateChecks0
    compactCertificate555_stateChecks1 compactCertificate555_stateChecks2
    compactCertificate555_stateChecks3 compactCertificate555_stateChecks4
    compactCertificate555_stateChecks5 compactCertificate555_stateChecks6
    compactCertificate555_stateChecks7 compactCertificate555_stateChecks8

theorem compactCertificate555_chunkChecks0_0 :
    compactCertificate555.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (853 / 2) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (1101109043 / 1000000000000) (1101109045 / 1000000000000), orderedInterval (38617995055 / 1000000000000) (38617995056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1256631878559553 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (31777079248 / 1000000000000) (31777079249 / 1000000000000), orderedInterval (31834363166 / 1000000000000) (31834363167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (406368930394849 / 800000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6744844672 / 1000000000000) (-6744844667 / 1000000000000), orderedInterval (34759940786 / 1000000000000) (34759940791 / 1000000000000)))) (orderedInterval (336746620 / 1000000000000) (336746651 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (366682048079171 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-81280842870 / 1000000000000) (-81280842869 / 1000000000000), orderedInterval (-17940995797 / 1000000000000) (-17940995795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (984959559237287 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46637230552 / 1000000000000) (46637242403 / 1000000000000), orderedInterval (-20351273932 / 1000000000000) (-20351262081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2674356805250379 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-6588706952 / 1000000000000) (-6588706951 / 1000000000000), orderedInterval (-30140933624 / 1000000000000) (-30140933623 / 1000000000000)))) (orderedInterval (3053035019 / 1000000000000) (3053035503 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1969919118475427 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-1253721855 / 1000000000000) (-1253721854 / 1000000000000), orderedInterval (-35930758788 / 1000000000000) (-35930758787 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3375489985703471 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (11466844854 / 1000000000000) (11466844869 / 1000000000000), orderedInterval (-24965046390 / 1000000000000) (-24965046375 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2486370645832589 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10748286679 / 1000000000000) (10748286680 / 1000000000000), orderedInterval (30135172253 / 1000000000000) (30135172254 / 1000000000000)))) (orderedInterval (-93918504 / 1000000000000) (-93918479 / 1000000000000))) = true
  rfl'

theorem compactCertificate555_chunkChecks0_1 :
    compactCertificate555.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3814731969614147 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14070591786 / 1000000000000) (-14070591726 / 1000000000000), orderedInterval (21676632272 / 1000000000000) (21676632331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2202436529542763 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33968975213 / 1000000000000) (-33968973977 / 1000000000000), orderedInterval (1553431408 / 1000000000000) (1553432644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3908262270742567 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18584875090 / 1000000000000) (-18584875088 / 1000000000000), orderedInterval (-17488072499 / 1000000000000) (-17488072498 / 1000000000000)))) (orderedInterval (-2658596852 / 1000000000000) (-2658596580 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3651605579775523 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13048123222 / 1000000000000) (13048123256 / 1000000000000), orderedInterval (-22965920011 / 1000000000000) (-22965919977 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2605958045197459 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28861836931 / 1000000000000) (-28861769069 / 1000000000000), orderedInterval (12029274601 / 1000000000000) (12029342463 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2954878677711861 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27674036574 / 1000000000000) (-27674036548 / 1000000000000), orderedInterval (-9775940042 / 1000000000000) (-9775940017 / 1000000000000)))) (orderedInterval (-2824770370 / 1000000000000) (-2824763901 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2463469779887909 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25194443977 / 1000000000000) (25194443978 / 1000000000000), orderedInterval (19952928090 / 1000000000000) (19952928091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2176550260074089 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33852664979 / 1000000000000) (-33852664873 / 1000000000000), orderedInterval (-4863551881 / 1000000000000) (-4863551775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (630849100490811 / 800000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20517784270 / 1000000000000) (-20517784269 / 1000000000000), orderedInterval (-19642485688 / 1000000000000) (-19642485687 / 1000000000000)))) (orderedInterval (1702876300 / 1000000000000) (1702876347 / 1000000000000))) = true
  rfl'

theorem compactCertificate555_chunkChecks0_2 :
    compactCertificate555.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1744961811726817 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12890239032 / 1000000000000) (-12890239031 / 1000000000000), orderedInterval (-35945964825 / 1000000000000) (-35945964824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1479223452723737 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-4843772277 / 1000000000000) (-4843772272 / 1000000000000), orderedInterval (41213789195 / 1000000000000) (41213789200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (925629354167411 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14780104269 / 1000000000000) (-14780104097 / 1000000000000), orderedInterval (50357202052 / 1000000000000) (50357202224 / 1000000000000)))) (orderedInterval (1854038741 / 1000000000000) (1854038854 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (497806545175437 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29664159741 / 1000000000000) (-29664157800 / 1000000000000), orderedInterval (65199616994 / 1000000000000) (65199618935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1351641607317311 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24385482827 / 1000000000000) (-24385479014 / 1000000000000), orderedInterval (35943446864 / 1000000000000) (35943450677 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1845551059396447 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13042723204 / 1000000000000) (-13042723203 / 1000000000000), orderedInterval (-34766339296 / 1000000000000) (-34766339295 / 1000000000000)))) (orderedInterval (2100561684 / 1000000000000) (2100561858 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (780370645832589 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50874968014 / 1000000000000) (50874968015 / 1000000000000), orderedInterval (25848403859 / 1000000000000) (25848403860 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3172163350426669 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23793232734 / 1000000000000) (23793253712 / 1000000000000), orderedInterval (-15398098694 / 1000000000000) (-15398077716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2118858107144771 / 4000000000000) 0 (IntervalRat.scale (853 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (14435032633 / 1000000000000) (14435032789 / 1000000000000), orderedInterval (-31532617968 / 1000000000000) (-31532617812 / 1000000000000)))) (orderedInterval (-4338517267 / 1000000000000) (-4338515412 / 1000000000000))) = true
  rfl'

theorem compactCertificate555_chunkChecks0 :
    compactCertificate555.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate555.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate555_chunkChecks0_0
    compactCertificate555_chunkChecks0_1 compactCertificate555_chunkChecks0_2

theorem compactCertificate555_chunkChecks1_0 :
    compactCertificate555.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (853 / 2) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (1101109043 / 1000000000000) (1101109045 / 1000000000000), orderedInterval (38617995055 / 1000000000000) (38617995056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1256631878559553 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (31777079248 / 1000000000000) (31777079249 / 1000000000000), orderedInterval (31834363166 / 1000000000000) (31834363167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (406368930394849 / 800000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6744844672 / 1000000000000) (-6744844667 / 1000000000000), orderedInterval (34759940786 / 1000000000000) (34759940791 / 1000000000000)))) (orderedInterval (17954665111 / 1000000000000) (17954665146 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (366682048079171 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-81280842870 / 1000000000000) (-81280842869 / 1000000000000), orderedInterval (-17940995797 / 1000000000000) (-17940995795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (984959559237287 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46637230552 / 1000000000000) (46637242403 / 1000000000000), orderedInterval (-20351273932 / 1000000000000) (-20351262081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2674356805250379 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-6588706952 / 1000000000000) (-6588706951 / 1000000000000), orderedInterval (-30140933624 / 1000000000000) (-30140933623 / 1000000000000)))) (orderedInterval (2971779062 / 1000000000000) (2971779370 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1969919118475427 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-1253721855 / 1000000000000) (-1253721854 / 1000000000000), orderedInterval (-35930758788 / 1000000000000) (-35930758787 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3375489985703471 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (11466844854 / 1000000000000) (11466844869 / 1000000000000), orderedInterval (-24965046390 / 1000000000000) (-24965046375 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2486370645832589 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10748286679 / 1000000000000) (10748286680 / 1000000000000), orderedInterval (30135172253 / 1000000000000) (30135172254 / 1000000000000)))) (orderedInterval (2585019934 / 1000000000000) (2585019977 / 1000000000000))) = true
  rfl'

theorem compactCertificate555_chunkChecks1_1 :
    compactCertificate555.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3814731969614147 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14070591786 / 1000000000000) (-14070591726 / 1000000000000), orderedInterval (21676632272 / 1000000000000) (21676632331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2202436529542763 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33968975213 / 1000000000000) (-33968973977 / 1000000000000), orderedInterval (1553431408 / 1000000000000) (1553432644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3908262270742567 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18584875090 / 1000000000000) (-18584875088 / 1000000000000), orderedInterval (-17488072499 / 1000000000000) (-17488072498 / 1000000000000)))) (orderedInterval (-14159253088 / 1000000000000) (-14159252596 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3651605579775523 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13048123222 / 1000000000000) (13048123256 / 1000000000000), orderedInterval (-22965920011 / 1000000000000) (-22965919977 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2605958045197459 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28861836931 / 1000000000000) (-28861769069 / 1000000000000), orderedInterval (12029274601 / 1000000000000) (12029342463 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2954878677711861 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27674036574 / 1000000000000) (-27674036548 / 1000000000000), orderedInterval (-9775940042 / 1000000000000) (-9775940017 / 1000000000000)))) (orderedInterval (2710724696 / 1000000000000) (2710734583 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2463469779887909 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25194443977 / 1000000000000) (25194443978 / 1000000000000), orderedInterval (19952928090 / 1000000000000) (19952928091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2176550260074089 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33852664979 / 1000000000000) (-33852664873 / 1000000000000), orderedInterval (-4863551881 / 1000000000000) (-4863551775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (630849100490811 / 800000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20517784270 / 1000000000000) (-20517784269 / 1000000000000), orderedInterval (-19642485688 / 1000000000000) (-19642485687 / 1000000000000)))) (orderedInterval (-242059713 / 1000000000000) (-242059645 / 1000000000000))) = true
  rfl'

theorem compactCertificate555_chunkChecks1_2 :
    compactCertificate555.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1744961811726817 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12890239032 / 1000000000000) (-12890239031 / 1000000000000), orderedInterval (-35945964825 / 1000000000000) (-35945964824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1479223452723737 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-4843772277 / 1000000000000) (-4843772272 / 1000000000000), orderedInterval (41213789195 / 1000000000000) (41213789200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (925629354167411 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14780104269 / 1000000000000) (-14780104097 / 1000000000000), orderedInterval (50357202052 / 1000000000000) (50357202224 / 1000000000000)))) (orderedInterval (4745623850 / 1000000000000) (4745623952 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (497806545175437 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29664159741 / 1000000000000) (-29664157800 / 1000000000000), orderedInterval (65199616994 / 1000000000000) (65199618935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1351641607317311 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24385482827 / 1000000000000) (-24385479014 / 1000000000000), orderedInterval (35943446864 / 1000000000000) (35943450677 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1845551059396447 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13042723204 / 1000000000000) (-13042723203 / 1000000000000), orderedInterval (-34766339296 / 1000000000000) (-34766339295 / 1000000000000)))) (orderedInterval (1885039392 / 1000000000000) (1885039518 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (780370645832589 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50874968014 / 1000000000000) (50874968015 / 1000000000000), orderedInterval (25848403859 / 1000000000000) (25848403860 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3172163350426669 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23793232734 / 1000000000000) (23793253712 / 1000000000000), orderedInterval (-15398098694 / 1000000000000) (-15398077716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2118858107144771 / 4000000000000) 1 (IntervalRat.scale (853 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (14435032633 / 1000000000000) (14435032789 / 1000000000000), orderedInterval (-31532617968 / 1000000000000) (-31532617812 / 1000000000000)))) (orderedInterval (9750061413 / 1000000000000) (9750064791 / 1000000000000))) = true
  rfl'

theorem compactCertificate555_chunkChecks1 :
    compactCertificate555.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate555.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate555_chunkChecks1_0
    compactCertificate555_chunkChecks1_1 compactCertificate555_chunkChecks1_2

theorem compactCertificate555_chunkChecks2_0 :
    compactCertificate555.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (853 / 2) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (1101109043 / 1000000000000) (1101109045 / 1000000000000), orderedInterval (38617995055 / 1000000000000) (38617995056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1256631878559553 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (31777079248 / 1000000000000) (31777079249 / 1000000000000), orderedInterval (31834363166 / 1000000000000) (31834363167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (406368930394849 / 800000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6744844672 / 1000000000000) (-6744844667 / 1000000000000), orderedInterval (34759940786 / 1000000000000) (34759940791 / 1000000000000)))) (orderedInterval (-77767830 / 1000000000000) (-77767790 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (366682048079171 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-81280842870 / 1000000000000) (-81280842869 / 1000000000000), orderedInterval (-17940995797 / 1000000000000) (-17940995795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (984959559237287 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46637230552 / 1000000000000) (46637242403 / 1000000000000), orderedInterval (-20351273932 / 1000000000000) (-20351262081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2674356805250379 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-6588706952 / 1000000000000) (-6588706951 / 1000000000000), orderedInterval (-30140933624 / 1000000000000) (-30140933623 / 1000000000000)))) (orderedInterval (-1766340657 / 1000000000000) (-1766340431 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1969919118475427 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-1253721855 / 1000000000000) (-1253721854 / 1000000000000), orderedInterval (-35930758788 / 1000000000000) (-35930758787 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3375489985703471 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (11466844854 / 1000000000000) (11466844869 / 1000000000000), orderedInterval (-24965046390 / 1000000000000) (-24965046375 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2486370645832589 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10748286679 / 1000000000000) (10748286680 / 1000000000000), orderedInterval (30135172253 / 1000000000000) (30135172254 / 1000000000000)))) (orderedInterval (826792833 / 1000000000000) (826792909 / 1000000000000))) = true
  rfl'

theorem compactCertificate555_chunkChecks2_1 :
    compactCertificate555.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3814731969614147 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14070591786 / 1000000000000) (-14070591726 / 1000000000000), orderedInterval (21676632272 / 1000000000000) (21676632331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2202436529542763 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33968975213 / 1000000000000) (-33968973977 / 1000000000000), orderedInterval (1553431408 / 1000000000000) (1553432644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3908262270742567 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18584875090 / 1000000000000) (-18584875088 / 1000000000000), orderedInterval (-17488072499 / 1000000000000) (-17488072498 / 1000000000000)))) (orderedInterval (5592475832 / 1000000000000) (5592476790 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3651605579775523 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13048123222 / 1000000000000) (13048123256 / 1000000000000), orderedInterval (-22965920011 / 1000000000000) (-22965919977 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2605958045197459 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28861836931 / 1000000000000) (-28861769069 / 1000000000000), orderedInterval (12029274601 / 1000000000000) (12029342463 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2954878677711861 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27674036574 / 1000000000000) (-27674036548 / 1000000000000), orderedInterval (-9775940042 / 1000000000000) (-9775940017 / 1000000000000)))) (orderedInterval (7020976181 / 1000000000000) (7020991318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2463469779887909 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25194443977 / 1000000000000) (25194443978 / 1000000000000), orderedInterval (19952928090 / 1000000000000) (19952928091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2176550260074089 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33852664979 / 1000000000000) (-33852664873 / 1000000000000), orderedInterval (-4863551881 / 1000000000000) (-4863551775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (630849100490811 / 800000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20517784270 / 1000000000000) (-20517784269 / 1000000000000), orderedInterval (-19642485688 / 1000000000000) (-19642485687 / 1000000000000)))) (orderedInterval (-1963567119 / 1000000000000) (-1963567021 / 1000000000000))) = true
  rfl'

theorem compactCertificate555_chunkChecks2_2 :
    compactCertificate555.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1744961811726817 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12890239032 / 1000000000000) (-12890239031 / 1000000000000), orderedInterval (-35945964825 / 1000000000000) (-35945964824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1479223452723737 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-4843772277 / 1000000000000) (-4843772272 / 1000000000000), orderedInterval (41213789195 / 1000000000000) (41213789200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (925629354167411 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14780104269 / 1000000000000) (-14780104097 / 1000000000000), orderedInterval (50357202052 / 1000000000000) (50357202224 / 1000000000000)))) (orderedInterval (-2231860182 / 1000000000000) (-2231860085 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (497806545175437 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29664159741 / 1000000000000) (-29664157800 / 1000000000000), orderedInterval (65199616994 / 1000000000000) (65199618935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1351641607317311 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24385482827 / 1000000000000) (-24385479014 / 1000000000000), orderedInterval (35943446864 / 1000000000000) (35943450677 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1845551059396447 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13042723204 / 1000000000000) (-13042723203 / 1000000000000), orderedInterval (-34766339296 / 1000000000000) (-34766339295 / 1000000000000)))) (orderedInterval (-1568130997 / 1000000000000) (-1568130893 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (780370645832589 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50874968014 / 1000000000000) (50874968015 / 1000000000000), orderedInterval (25848403859 / 1000000000000) (25848403860 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3172163350426669 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23793232734 / 1000000000000) (23793253712 / 1000000000000), orderedInterval (-15398098694 / 1000000000000) (-15398077716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2118858107144771 / 4000000000000) 2 (IntervalRat.scale (853 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (14435032633 / 1000000000000) (14435032789 / 1000000000000), orderedInterval (-31532617968 / 1000000000000) (-31532617812 / 1000000000000)))) (orderedInterval (10787248439 / 1000000000000) (10787254641 / 1000000000000))) = true
  rfl'

theorem compactCertificate555_chunkChecks2 :
    compactCertificate555.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate555.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate555_chunkChecks2_0
    compactCertificate555_chunkChecks2_1 compactCertificate555_chunkChecks2_2

theorem compactCertificate555_chunkChecks3_0 :
    compactCertificate555.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (853 / 2) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (1101109043 / 1000000000000) (1101109045 / 1000000000000), orderedInterval (38617995055 / 1000000000000) (38617995056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1256631878559553 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (31777079248 / 1000000000000) (31777079249 / 1000000000000), orderedInterval (31834363166 / 1000000000000) (31834363167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (406368930394849 / 800000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6744844672 / 1000000000000) (-6744844667 / 1000000000000), orderedInterval (34759940786 / 1000000000000) (34759940791 / 1000000000000)))) (orderedInterval (-18871066249 / 1000000000000) (-18871066203 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (366682048079171 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-81280842870 / 1000000000000) (-81280842869 / 1000000000000), orderedInterval (-17940995797 / 1000000000000) (-17940995795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (984959559237287 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46637230552 / 1000000000000) (46637242403 / 1000000000000), orderedInterval (-20351273932 / 1000000000000) (-20351262081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2674356805250379 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-6588706952 / 1000000000000) (-6588706951 / 1000000000000), orderedInterval (-30140933624 / 1000000000000) (-30140933623 / 1000000000000)))) (orderedInterval (-8109144102 / 1000000000000) (-8109143897 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1969919118475427 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-1253721855 / 1000000000000) (-1253721854 / 1000000000000), orderedInterval (-35930758788 / 1000000000000) (-35930758787 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3375489985703471 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (11466844854 / 1000000000000) (11466844869 / 1000000000000), orderedInterval (-24965046390 / 1000000000000) (-24965046375 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2486370645832589 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10748286679 / 1000000000000) (10748286680 / 1000000000000), orderedInterval (30135172253 / 1000000000000) (30135172254 / 1000000000000)))) (orderedInterval (-8221088480 / 1000000000000) (-8221088342 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate555_chunkChecks3_1 :
    compactCertificate555.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3814731969614147 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14070591786 / 1000000000000) (-14070591726 / 1000000000000), orderedInterval (21676632272 / 1000000000000) (21676632331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2202436529542763 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33968975213 / 1000000000000) (-33968973977 / 1000000000000), orderedInterval (1553431408 / 1000000000000) (1553432644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3908262270742567 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18584875090 / 1000000000000) (-18584875088 / 1000000000000), orderedInterval (-17488072499 / 1000000000000) (-17488072498 / 1000000000000)))) (orderedInterval (72691855380 / 1000000000000) (72691857342 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3651605579775523 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13048123222 / 1000000000000) (13048123256 / 1000000000000), orderedInterval (-22965920011 / 1000000000000) (-22965919977 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2605958045197459 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28861836931 / 1000000000000) (-28861769069 / 1000000000000), orderedInterval (12029274601 / 1000000000000) (12029342463 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2954878677711861 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27674036574 / 1000000000000) (-27674036548 / 1000000000000), orderedInterval (-9775940042 / 1000000000000) (-9775940017 / 1000000000000)))) (orderedInterval (-8393756339 / 1000000000000) (-8393733193 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2463469779887909 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25194443977 / 1000000000000) (25194443978 / 1000000000000), orderedInterval (19952928090 / 1000000000000) (19952928091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2176550260074089 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33852664979 / 1000000000000) (-33852664873 / 1000000000000), orderedInterval (-4863551881 / 1000000000000) (-4863551775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (630849100490811 / 800000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20517784270 / 1000000000000) (-20517784269 / 1000000000000), orderedInterval (-19642485688 / 1000000000000) (-19642485687 / 1000000000000)))) (orderedInterval (1911581196 / 1000000000000) (1911581344 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate555_chunkChecks3_2 :
    compactCertificate555.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1744961811726817 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12890239032 / 1000000000000) (-12890239031 / 1000000000000), orderedInterval (-35945964825 / 1000000000000) (-35945964824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1479223452723737 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-4843772277 / 1000000000000) (-4843772272 / 1000000000000), orderedInterval (41213789195 / 1000000000000) (41213789200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (925629354167411 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14780104269 / 1000000000000) (-14780104097 / 1000000000000), orderedInterval (50357202052 / 1000000000000) (50357202224 / 1000000000000)))) (orderedInterval (-4886301150 / 1000000000000) (-4886301056 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (497806545175437 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29664159741 / 1000000000000) (-29664157800 / 1000000000000), orderedInterval (65199616994 / 1000000000000) (65199618935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1351641607317311 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24385482827 / 1000000000000) (-24385479014 / 1000000000000), orderedInterval (35943446864 / 1000000000000) (35943450677 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1845551059396447 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13042723204 / 1000000000000) (-13042723203 / 1000000000000), orderedInterval (-34766339296 / 1000000000000) (-34766339295 / 1000000000000)))) (orderedInterval (-2934108657 / 1000000000000) (-2934108566 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (780370645832589 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50874968014 / 1000000000000) (50874968015 / 1000000000000), orderedInterval (25848403859 / 1000000000000) (25848403860 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3172163350426669 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23793232734 / 1000000000000) (23793253712 / 1000000000000), orderedInterval (-15398098694 / 1000000000000) (-15398077716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2118858107144771 / 4000000000000) 3 (IntervalRat.scale (853 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (14435032633 / 1000000000000) (14435032789 / 1000000000000), orderedInterval (-31532617968 / 1000000000000) (-31532617812 / 1000000000000)))) (orderedInterval (-19433247452 / 1000000000000) (-19433236026 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate555_chunkChecks3 :
    compactCertificate555.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate555.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate555_chunkChecks3_0
    compactCertificate555_chunkChecks3_1 compactCertificate555_chunkChecks3_2

theorem compactCertificate555_chunkChecks4_0 :
    compactCertificate555.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (853 / 2) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (1101109043 / 1000000000000) (1101109045 / 1000000000000), orderedInterval (38617995055 / 1000000000000) (38617995056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1256631878559553 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (31777079248 / 1000000000000) (31777079249 / 1000000000000), orderedInterval (31834363166 / 1000000000000) (31834363167 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (406368930394849 / 800000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6744844672 / 1000000000000) (-6744844667 / 1000000000000), orderedInterval (34759940786 / 1000000000000) (34759940791 / 1000000000000)))) (orderedInterval (-184271946 / 1000000000000) (-184271892 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (366682048079171 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-81280842870 / 1000000000000) (-81280842869 / 1000000000000), orderedInterval (-17940995797 / 1000000000000) (-17940995795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (984959559237287 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46637230552 / 1000000000000) (46637242403 / 1000000000000), orderedInterval (-20351273932 / 1000000000000) (-20351262081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2674356805250379 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-6588706952 / 1000000000000) (-6588706951 / 1000000000000), orderedInterval (-30140933624 / 1000000000000) (-30140933623 / 1000000000000)))) (orderedInterval (3057675098 / 1000000000000) (3057675333 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1969919118475427 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-1253721855 / 1000000000000) (-1253721854 / 1000000000000), orderedInterval (-35930758788 / 1000000000000) (-35930758787 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3375489985703471 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (11466844854 / 1000000000000) (11466844869 / 1000000000000), orderedInterval (-24965046390 / 1000000000000) (-24965046375 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2486370645832589 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10748286679 / 1000000000000) (10748286680 / 1000000000000), orderedInterval (30135172253 / 1000000000000) (30135172254 / 1000000000000)))) (orderedInterval (-4210024606 / 1000000000000) (-4210024349 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate555_chunkChecks4_1 :
    compactCertificate555.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3814731969614147 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14070591786 / 1000000000000) (-14070591726 / 1000000000000), orderedInterval (21676632272 / 1000000000000) (21676632331 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2202436529542763 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33968975213 / 1000000000000) (-33968973977 / 1000000000000), orderedInterval (1553431408 / 1000000000000) (1553432644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3908262270742567 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18584875090 / 1000000000000) (-18584875088 / 1000000000000), orderedInterval (-17488072499 / 1000000000000) (-17488072498 / 1000000000000)))) (orderedInterval (-17596124941 / 1000000000000) (-17596120757 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3651605579775523 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13048123222 / 1000000000000) (13048123256 / 1000000000000), orderedInterval (-22965920011 / 1000000000000) (-22965919977 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2605958045197459 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28861836931 / 1000000000000) (-28861769069 / 1000000000000), orderedInterval (12029274601 / 1000000000000) (12029342463 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2954878677711861 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27674036574 / 1000000000000) (-27674036548 / 1000000000000), orderedInterval (-9775940042 / 1000000000000) (-9775940017 / 1000000000000)))) (orderedInterval (-18503934915 / 1000000000000) (-18503899454 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2463469779887909 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25194443977 / 1000000000000) (25194443978 / 1000000000000), orderedInterval (19952928090 / 1000000000000) (19952928091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2176550260074089 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33852664979 / 1000000000000) (-33852664873 / 1000000000000), orderedInterval (-4863551881 / 1000000000000) (-4863551775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (630849100490811 / 800000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20517784270 / 1000000000000) (-20517784269 / 1000000000000), orderedInterval (-19642485688 / 1000000000000) (-19642485687 / 1000000000000)))) (orderedInterval (249640755 / 1000000000000) (249640986 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate555_chunkChecks4_2 :
    compactCertificate555.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1744961811726817 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12890239032 / 1000000000000) (-12890239031 / 1000000000000), orderedInterval (-35945964825 / 1000000000000) (-35945964824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1479223452723737 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-4843772277 / 1000000000000) (-4843772272 / 1000000000000), orderedInterval (41213789195 / 1000000000000) (41213789200 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (925629354167411 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14780104269 / 1000000000000) (-14780104097 / 1000000000000), orderedInterval (50357202052 / 1000000000000) (50357202224 / 1000000000000)))) (orderedInterval (2392043967 / 1000000000000) (2392044059 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (497806545175437 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29664159741 / 1000000000000) (-29664157800 / 1000000000000), orderedInterval (65199616994 / 1000000000000) (65199618935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1351641607317311 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24385482827 / 1000000000000) (-24385479014 / 1000000000000), orderedInterval (35943446864 / 1000000000000) (35943450677 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1845551059396447 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13042723204 / 1000000000000) (-13042723203 / 1000000000000), orderedInterval (-34766339296 / 1000000000000) (-34766339295 / 1000000000000)))) (orderedInterval (1604717599 / 1000000000000) (1604717683 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (780370645832589 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50874968014 / 1000000000000) (50874968015 / 1000000000000), orderedInterval (25848403859 / 1000000000000) (25848403860 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3172163350426669 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23793232734 / 1000000000000) (23793253712 / 1000000000000), orderedInterval (-15398098694 / 1000000000000) (-15398077716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2118858107144771 / 4000000000000) 4 (IntervalRat.scale (853 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (14435032633 / 1000000000000) (14435032789 / 1000000000000), orderedInterval (-31532617968 / 1000000000000) (-31532617812 / 1000000000000)))) (orderedInterval (-29492376409 / 1000000000000) (-29492355268 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate555_chunkChecks4 :
    compactCertificate555.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate555.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate555_chunkChecks4_0
    compactCertificate555_chunkChecks4_1 compactCertificate555_chunkChecks4_2

theorem compactCertificate555_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate555.chunkCheck r b = true :=
  compactCertificate555.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate555_chunkChecks0
    · exact compactCertificate555_chunkChecks1
    · exact compactCertificate555_chunkChecks2
    · exact compactCertificate555_chunkChecks3
    · exact compactCertificate555_chunkChecks4)

theorem compactCertificate555_coefficient0 :
    compactCertificate555.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate555_coefficient1 :
    compactCertificate555.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate555_coefficient2 :
    compactCertificate555.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate555_coefficient3 :
    compactCertificate555.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate555_coefficient4 :
    compactCertificate555.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate555_coefficients : ∀ r : Fin 5,
    compactCertificate555.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate555_coefficient0
  · exact compactCertificate555_coefficient1
  · exact compactCertificate555_coefficient2
  · exact compactCertificate555_coefficient3
  · exact compactCertificate555_coefficient4

theorem compactCertificate555_lower : (1 : ℚ) ≤ compactCertificate555.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate555, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate555_proves {t : ℝ} (ht : t ∈ compactCertificate555.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate555.proves compactCertificate555_states compactCertificate555_chunks
    compactCertificate555_coefficients compactCertificate555_lower ht

end Erdos232
