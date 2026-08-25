/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate616 : CompactCertificate where
  left := 487
  right := 488
  center := 975 / 2
  grid := fun i =>
    match i.val with
    | 0 => 155
    | 1 => 114
    | 2 => 185
    | 3 => 33
    | 4 => 90
    | 5 => 243
    | 6 => 179
    | 7 => 307
    | 8 => 226
    | 9 => 347
    | 10 => 200
    | 11 => 356
    | 12 => 332
    | 13 => 237
    | 14 => 269
    | 15 => 224
    | 16 => 198
    | 17 => 287
    | 18 => 159
    | 19 => 135
    | 20 => 84
    | 21 => 45
    | 22 => 123
    | 23 => 168
    | 24 => 71
    | 25 => 289
    | _ => 193
  point := fun i =>
    match i.val with
    | 0 => 975 / 2
    | 1 => 57454446968139 / 160000000000
    | 2 => 18579587673387 / 32000000000
    | 3 => 16765064331873 / 160000000000
    | 4 => 45033320996781 / 160000000000
    | 5 => 122274226734777 / 160000000000
    | 6 => 90066641993601 / 160000000000
    | 7 => 154330726192773 / 160000000000
    | 8 => 113679314405007 / 160000000000
    | 9 => 174413302244961 / 160000000000
    | 10 => 100697567001369 / 160000000000
    | 11 => 178689599717421 / 160000000000
    | 12 => 166955003061249 / 160000000000
    | 13 => 119146968068817 / 160000000000
    | 14 => 135099962990343 / 160000000000
    | 15 => 112632264262167 / 160000000000
    | 16 => 99514021269507 / 160000000000
    | 17 => 28843042109193 / 32000000000
    | 18 => 79781372400171 / 160000000000
    | 19 => 67631552938131 / 160000000000
    | 20 => 42320685594993 / 160000000000
    | 21 => 22760205465231 / 160000000000
    | 22 => 61798385328693 / 160000000000
    | 23 => 84380411859861 / 160000000000
    | 24 => 35679314405007 / 160000000000
    | 25 => 145034432200047 / 160000000000
    | _ => 96876279224673 / 160000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-35164588158 / 1000000000000) (-35164588139 / 1000000000000), orderedInterval (-8290868350 / 1000000000000) (-8290868332 / 1000000000000))
    | 1 => (orderedInterval (41547412447 / 1000000000000) (41547414026 / 1000000000000), orderedInterval (-6890058475 / 1000000000000) (-6890056895 / 1000000000000))
    | 2 => (orderedInterval (-6664709214 / 1000000000000) (-6664709213 / 1000000000000), orderedInterval (-32429506071 / 1000000000000) (-32429506070 / 1000000000000))
    | 3 => (orderedInterval (-73927684085 / 1000000000000) (-73927681831 / 1000000000000), orderedInterval (25057462306 / 1000000000000) (25057464560 / 1000000000000))
    | 4 => (orderedInterval (-22806365267 / 1000000000000) (-22806363466 / 1000000000000), orderedInterval (41774598052 / 1000000000000) (41774599853 / 1000000000000))
    | 5 => (orderedInterval (-28855836398 / 1000000000000) (-28855833180 / 1000000000000), orderedInterval (634770513 / 1000000000000) (634773730 / 1000000000000))
    | 6 => (orderedInterval (-32860825007 / 1000000000000) (-32860824963 / 1000000000000), orderedInterval (-7119017616 / 1000000000000) (-7119017572 / 1000000000000))
    | 7 => (orderedInterval (-19855654942 / 1000000000000) (-19855654940 / 1000000000000), orderedInterval (-16291814077 / 1000000000000) (-16291814075 / 1000000000000))
    | 8 => (orderedInterval (28685432139 / 1000000000000) (28685432183 / 1000000000000), orderedInterval (8533629125 / 1000000000000) (8533629168 / 1000000000000))
    | 9 => (orderedInterval (-16219442996 / 1000000000000) (-16219442995 / 1000000000000), orderedInterval (-17907357890 / 1000000000000) (-17907357889 / 1000000000000))
    | 10 => (orderedInterval (30770822635 / 1000000000000) (30770840091 / 1000000000000), orderedInterval (-8067535109 / 1000000000000) (-8067517654 / 1000000000000))
    | 11 => (orderedInterval (-17320599614 / 1000000000000) (-17320599141 / 1000000000000), orderedInterval (16440371980 / 1000000000000) (16440372453 / 1000000000000))
    | 12 => (orderedInterval (23403129713 / 1000000000000) (23403129992 / 1000000000000), orderedInterval (7887706916 / 1000000000000) (7887707194 / 1000000000000))
    | 13 => (orderedInterval (-22836478301 / 1000000000000) (-22836478300 / 1000000000000), orderedInterval (-18243876594 / 1000000000000) (-18243876593 / 1000000000000))
    | 14 => (orderedInterval (-1964192293 / 1000000000000) (-1964192292 / 1000000000000), orderedInterval (-27386719700 / 1000000000000) (-27386719699 / 1000000000000))
    | 15 => (orderedInterval (25626817171 / 1000000000000) (25626817172 / 1000000000000), orderedInterval (15717670786 / 1000000000000) (15717670788 / 1000000000000))
    | 16 => (orderedInterval (20914476749 / 1000000000000) (20914476750 / 1000000000000), orderedInterval (24193735226 / 1000000000000) (24193735227 / 1000000000000))
    | 17 => (orderedInterval (-12583258488 / 1000000000000) (-12583258487 / 1000000000000), orderedInterval (-23401594895 / 1000000000000) (-23401594894 / 1000000000000))
    | 18 => (orderedInterval (3371834245 / 1000000000000) (3371834247 / 1000000000000), orderedInterval (-35575280241 / 1000000000000) (-35575280239 / 1000000000000))
    | 19 => (orderedInterval (22948317842 / 1000000000000) (22948321385 / 1000000000000), orderedInterval (-31323541488 / 1000000000000) (-31323537945 / 1000000000000))
    | 20 => (orderedInterval (48307061481 / 1000000000000) (48307061489 / 1000000000000), orderedInterval (8468171684 / 1000000000000) (8468171692 / 1000000000000))
    | 21 => (orderedInterval (-66606420017 / 1000000000000) (-66606419848 / 1000000000000), orderedInterval (6469169767 / 1000000000000) (6469169935 / 1000000000000))
    | 22 => (orderedInterval (-23227220501 / 1000000000000) (-23227220500 / 1000000000000), orderedInterval (-33267773933 / 1000000000000) (-33267773932 / 1000000000000))
    | 23 => (orderedInterval (12731231253 / 1000000000000) (12731231254 / 1000000000000), orderedInterval (32315293291 / 1000000000000) (32315293292 / 1000000000000))
    | 24 => (orderedInterval (-35530666648 / 1000000000000) (-35530666647 / 1000000000000), orderedInterval (-39825528835 / 1000000000000) (-39825528834 / 1000000000000))
    | 25 => (orderedInterval (16452997379 / 1000000000000) (16452997680 / 1000000000000), orderedInterval (-20784279811 / 1000000000000) (-20784279510 / 1000000000000))
    | _ => (orderedInterval (2120603522 / 1000000000000) (2120603523 / 1000000000000), orderedInterval (-32358187059 / 1000000000000) (-32358187058 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-13941963209 / 1000000000000) (-13941963152 / 1000000000000)
      | 1 => orderedInterval (2020713509 / 1000000000000) (2020713887 / 1000000000000)
      | 2 => orderedInterval (1305698125 / 1000000000000) (1305698154 / 1000000000000)
      | 3 => orderedInterval (2699638546 / 1000000000000) (2699640100 / 1000000000000)
      | 4 => orderedInterval (-2572041641 / 1000000000000) (-2572041577 / 1000000000000)
      | 5 => orderedInterval (-1223117122 / 1000000000000) (-1223117075 / 1000000000000)
      | 6 => orderedInterval (-265355376 / 1000000000000) (-265355052 / 1000000000000)
      | 7 => orderedInterval (781140875 / 1000000000000) (781140937 / 1000000000000)
      | _ => orderedInterval (-1951375302 / 1000000000000) (-1951375143 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-5599972837 / 1000000000000) (-5599972781 / 1000000000000)
      | 1 => orderedInterval (751439401 / 1000000000000) (751439870 / 1000000000000)
      | 2 => orderedInterval (1294836552 / 1000000000000) (1294836602 / 1000000000000)
      | 3 => orderedInterval (11697350349 / 1000000000000) (11697352573 / 1000000000000)
      | 4 => orderedInterval (-2700021352 / 1000000000000) (-2700021247 / 1000000000000)
      | 5 => orderedInterval (-2612137474 / 1000000000000) (-2612137406 / 1000000000000)
      | 6 => orderedInterval (7504944922 / 1000000000000) (7504945210 / 1000000000000)
      | 7 => orderedInterval (-2116079046 / 1000000000000) (-2116078993 / 1000000000000)
      | _ => orderedInterval (10576603062 / 1000000000000) (10576603297 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (14294203337 / 1000000000000) (14294203397 / 1000000000000)
      | 1 => orderedInterval (-4802073963 / 1000000000000) (-4802073284 / 1000000000000)
      | 2 => orderedInterval (-3872792959 / 1000000000000) (-3872792872 / 1000000000000)
      | 3 => orderedInterval (-5311547915 / 1000000000000) (-5311544544 / 1000000000000)
      | 4 => orderedInterval (6950198559 / 1000000000000) (6950198739 / 1000000000000)
      | 5 => orderedInterval (2437831516 / 1000000000000) (2437831617 / 1000000000000)
      | 6 => orderedInterval (1062187176 / 1000000000000) (1062187436 / 1000000000000)
      | 7 => orderedInterval (710704048 / 1000000000000) (710704101 / 1000000000000)
      | _ => orderedInterval (5267425839 / 1000000000000) (5267426204 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (6497466824 / 1000000000000) (6497466889 / 1000000000000)
      | 1 => orderedInterval (-107146468 / 1000000000000) (-107145435 / 1000000000000)
      | 2 => orderedInterval (-4522877960 / 1000000000000) (-4522877802 / 1000000000000)
      | 3 => orderedInterval (-62376871961 / 1000000000000) (-62376866482 / 1000000000000)
      | 4 => orderedInterval (6810983535 / 1000000000000) (6810983849 / 1000000000000)
      | 5 => orderedInterval (6110764814 / 1000000000000) (6110764969 / 1000000000000)
      | 6 => orderedInterval (-7288808478 / 1000000000000) (-7288808242 / 1000000000000)
      | 7 => orderedInterval (2761581688 / 1000000000000) (2761581742 / 1000000000000)
      | _ => orderedInterval (-22496314755 / 1000000000000) (-22496314165 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-14637550175 / 1000000000000) (-14637550103 / 1000000000000)
      | 1 => orderedInterval (12297609719 / 1000000000000) (12297611323 / 1000000000000)
      | 2 => orderedInterval (12532538350 / 1000000000000) (12532538640 / 1000000000000)
      | 3 => orderedInterval (10820583218 / 1000000000000) (10820592858 / 1000000000000)
      | 4 => orderedInterval (-20564027339 / 1000000000000) (-20564026774 / 1000000000000)
      | 5 => orderedInterval (-5674472028 / 1000000000000) (-5674471782 / 1000000000000)
      | 6 => orderedInterval (-1158049599 / 1000000000000) (-1158049381 / 1000000000000)
      | 7 => orderedInterval (-1131085840 / 1000000000000) (-1131085784 / 1000000000000)
      | _ => orderedInterval (-16873600692 / 1000000000000) (-16873599705 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-13146661595 / 1000000000000) (-13146658921 / 1000000000000)
    | 1 => orderedInterval (18796963577 / 1000000000000) (18796967125 / 1000000000000)
    | 2 => orderedInterval (16736135638 / 1000000000000) (16736140794 / 1000000000000)
    | 3 => orderedInterval (-74611222761 / 1000000000000) (-74611214677 / 1000000000000)
    | _ => orderedInterval (-24388054386 / 1000000000000) (-24388040708 / 1000000000000)

theorem compactCertificate616_stateChecks0 :
    compactCertificate616.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (975 / 2)) (orderedInterval (-35164588158 / 1000000000000) (-35164588139 / 1000000000000), orderedInterval (-8290868350 / 1000000000000) (-8290868332 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (57454446968139 / 160000000000)) (orderedInterval (41547412447 / 1000000000000) (41547414026 / 1000000000000), orderedInterval (-6890058475 / 1000000000000) (-6890056895 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (18579587673387 / 32000000000)) (orderedInterval (-6664709214 / 1000000000000) (-6664709213 / 1000000000000), orderedInterval (-32429506071 / 1000000000000) (-32429506070 / 1000000000000))) = true
  rfl'

theorem compactCertificate616_stateChecks1 :
    compactCertificate616.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (16765064331873 / 160000000000)) (orderedInterval (-73927684085 / 1000000000000) (-73927681831 / 1000000000000), orderedInterval (25057462306 / 1000000000000) (25057464560 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (45033320996781 / 160000000000)) (orderedInterval (-22806365267 / 1000000000000) (-22806363466 / 1000000000000), orderedInterval (41774598052 / 1000000000000) (41774599853 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 243 12 (122274226734777 / 160000000000)) (orderedInterval (-28855836398 / 1000000000000) (-28855833180 / 1000000000000), orderedInterval (634770513 / 1000000000000) (634773730 / 1000000000000))) = true
  rfl'

theorem compactCertificate616_stateChecks2 :
    compactCertificate616.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (90066641993601 / 160000000000)) (orderedInterval (-32860825007 / 1000000000000) (-32860824963 / 1000000000000), orderedInterval (-7119017616 / 1000000000000) (-7119017572 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 307 12 (154330726192773 / 160000000000)) (orderedInterval (-19855654942 / 1000000000000) (-19855654940 / 1000000000000), orderedInterval (-16291814077 / 1000000000000) (-16291814075 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 226 12 (113679314405007 / 160000000000)) (orderedInterval (28685432139 / 1000000000000) (28685432183 / 1000000000000), orderedInterval (8533629125 / 1000000000000) (8533629168 / 1000000000000))) = true
  rfl'

theorem compactCertificate616_stateChecks3 :
    compactCertificate616.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 347 12 (174413302244961 / 160000000000)) (orderedInterval (-16219442996 / 1000000000000) (-16219442995 / 1000000000000), orderedInterval (-17907357890 / 1000000000000) (-17907357889 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (100697567001369 / 160000000000)) (orderedInterval (30770822635 / 1000000000000) (30770840091 / 1000000000000), orderedInterval (-8067535109 / 1000000000000) (-8067517654 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 356 12 (178689599717421 / 160000000000)) (orderedInterval (-17320599614 / 1000000000000) (-17320599141 / 1000000000000), orderedInterval (16440371980 / 1000000000000) (16440372453 / 1000000000000))) = true
  rfl'

theorem compactCertificate616_stateChecks4 :
    compactCertificate616.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 332 12 (166955003061249 / 160000000000)) (orderedInterval (23403129713 / 1000000000000) (23403129992 / 1000000000000), orderedInterval (7887706916 / 1000000000000) (7887707194 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 237 12 (119146968068817 / 160000000000)) (orderedInterval (-22836478301 / 1000000000000) (-22836478300 / 1000000000000), orderedInterval (-18243876594 / 1000000000000) (-18243876593 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 269 12 (135099962990343 / 160000000000)) (orderedInterval (-1964192293 / 1000000000000) (-1964192292 / 1000000000000), orderedInterval (-27386719700 / 1000000000000) (-27386719699 / 1000000000000))) = true
  rfl'

theorem compactCertificate616_stateChecks5 :
    compactCertificate616.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 224 12 (112632264262167 / 160000000000)) (orderedInterval (25626817171 / 1000000000000) (25626817172 / 1000000000000), orderedInterval (15717670786 / 1000000000000) (15717670788 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (99514021269507 / 160000000000)) (orderedInterval (20914476749 / 1000000000000) (20914476750 / 1000000000000), orderedInterval (24193735226 / 1000000000000) (24193735227 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 287 12 (28843042109193 / 32000000000)) (orderedInterval (-12583258488 / 1000000000000) (-12583258487 / 1000000000000), orderedInterval (-23401594895 / 1000000000000) (-23401594894 / 1000000000000))) = true
  rfl'

theorem compactCertificate616_stateChecks6 :
    compactCertificate616.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (79781372400171 / 160000000000)) (orderedInterval (3371834245 / 1000000000000) (3371834247 / 1000000000000), orderedInterval (-35575280241 / 1000000000000) (-35575280239 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (67631552938131 / 160000000000)) (orderedInterval (22948317842 / 1000000000000) (22948321385 / 1000000000000), orderedInterval (-31323541488 / 1000000000000) (-31323537945 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (42320685594993 / 160000000000)) (orderedInterval (48307061481 / 1000000000000) (48307061489 / 1000000000000), orderedInterval (8468171684 / 1000000000000) (8468171692 / 1000000000000))) = true
  rfl'

theorem compactCertificate616_stateChecks7 :
    compactCertificate616.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (22760205465231 / 160000000000)) (orderedInterval (-66606420017 / 1000000000000) (-66606419848 / 1000000000000), orderedInterval (6469169767 / 1000000000000) (6469169935 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (61798385328693 / 160000000000)) (orderedInterval (-23227220501 / 1000000000000) (-23227220500 / 1000000000000), orderedInterval (-33267773933 / 1000000000000) (-33267773932 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (84380411859861 / 160000000000)) (orderedInterval (12731231253 / 1000000000000) (12731231254 / 1000000000000), orderedInterval (32315293291 / 1000000000000) (32315293292 / 1000000000000))) = true
  rfl'

theorem compactCertificate616_stateChecks8 :
    compactCertificate616.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (35679314405007 / 160000000000)) (orderedInterval (-35530666648 / 1000000000000) (-35530666647 / 1000000000000), orderedInterval (-39825528835 / 1000000000000) (-39825528834 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 289 12 (145034432200047 / 160000000000)) (orderedInterval (16452997379 / 1000000000000) (16452997680 / 1000000000000), orderedInterval (-20784279811 / 1000000000000) (-20784279510 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (96876279224673 / 160000000000)) (orderedInterval (2120603522 / 1000000000000) (2120603523 / 1000000000000), orderedInterval (-32358187059 / 1000000000000) (-32358187058 / 1000000000000))) = true
  rfl'

theorem compactCertificate616_states : ∀ j,
    BesselStateValid (compactCertificate616.point j) (compactCertificate616.state j) :=
  compactCertificate616.statesValid_of_checks3 compactCertificate616_stateChecks0
    compactCertificate616_stateChecks1 compactCertificate616_stateChecks2
    compactCertificate616_stateChecks3 compactCertificate616_stateChecks4
    compactCertificate616_stateChecks5 compactCertificate616_stateChecks6
    compactCertificate616_stateChecks7 compactCertificate616_stateChecks8

theorem compactCertificate616_chunkChecks0_0 :
    compactCertificate616.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (975 / 2) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35164588158 / 1000000000000) (-35164588139 / 1000000000000), orderedInterval (-8290868350 / 1000000000000) (-8290868332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (57454446968139 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41547412447 / 1000000000000) (41547414026 / 1000000000000), orderedInterval (-6890058475 / 1000000000000) (-6890056895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (18579587673387 / 32000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6664709214 / 1000000000000) (-6664709213 / 1000000000000), orderedInterval (-32429506071 / 1000000000000) (-32429506070 / 1000000000000)))) (orderedInterval (-13941963209 / 1000000000000) (-13941963152 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (16765064331873 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-73927684085 / 1000000000000) (-73927681831 / 1000000000000), orderedInterval (25057462306 / 1000000000000) (25057464560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (45033320996781 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-22806365267 / 1000000000000) (-22806363466 / 1000000000000), orderedInterval (41774598052 / 1000000000000) (41774599853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (122274226734777 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28855836398 / 1000000000000) (-28855833180 / 1000000000000), orderedInterval (634770513 / 1000000000000) (634773730 / 1000000000000)))) (orderedInterval (2020713509 / 1000000000000) (2020713887 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (90066641993601 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32860825007 / 1000000000000) (-32860824963 / 1000000000000), orderedInterval (-7119017616 / 1000000000000) (-7119017572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (154330726192773 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19855654942 / 1000000000000) (-19855654940 / 1000000000000), orderedInterval (-16291814077 / 1000000000000) (-16291814075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (113679314405007 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28685432139 / 1000000000000) (28685432183 / 1000000000000), orderedInterval (8533629125 / 1000000000000) (8533629168 / 1000000000000)))) (orderedInterval (1305698125 / 1000000000000) (1305698154 / 1000000000000))) = true
  rfl'

theorem compactCertificate616_chunkChecks0_1 :
    compactCertificate616.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (174413302244961 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16219442996 / 1000000000000) (-16219442995 / 1000000000000), orderedInterval (-17907357890 / 1000000000000) (-17907357889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (100697567001369 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (30770822635 / 1000000000000) (30770840091 / 1000000000000), orderedInterval (-8067535109 / 1000000000000) (-8067517654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (178689599717421 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17320599614 / 1000000000000) (-17320599141 / 1000000000000), orderedInterval (16440371980 / 1000000000000) (16440372453 / 1000000000000)))) (orderedInterval (2699638546 / 1000000000000) (2699640100 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (166955003061249 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23403129713 / 1000000000000) (23403129992 / 1000000000000), orderedInterval (7887706916 / 1000000000000) (7887707194 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (119146968068817 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22836478301 / 1000000000000) (-22836478300 / 1000000000000), orderedInterval (-18243876594 / 1000000000000) (-18243876593 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (135099962990343 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1964192293 / 1000000000000) (-1964192292 / 1000000000000), orderedInterval (-27386719700 / 1000000000000) (-27386719699 / 1000000000000)))) (orderedInterval (-2572041641 / 1000000000000) (-2572041577 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (112632264262167 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25626817171 / 1000000000000) (25626817172 / 1000000000000), orderedInterval (15717670786 / 1000000000000) (15717670788 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (99514021269507 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20914476749 / 1000000000000) (20914476750 / 1000000000000), orderedInterval (24193735226 / 1000000000000) (24193735227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (28843042109193 / 32000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12583258488 / 1000000000000) (-12583258487 / 1000000000000), orderedInterval (-23401594895 / 1000000000000) (-23401594894 / 1000000000000)))) (orderedInterval (-1223117122 / 1000000000000) (-1223117075 / 1000000000000))) = true
  rfl'

theorem compactCertificate616_chunkChecks0_2 :
    compactCertificate616.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (79781372400171 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3371834245 / 1000000000000) (3371834247 / 1000000000000), orderedInterval (-35575280241 / 1000000000000) (-35575280239 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (67631552938131 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (22948317842 / 1000000000000) (22948321385 / 1000000000000), orderedInterval (-31323541488 / 1000000000000) (-31323537945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (42320685594993 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48307061481 / 1000000000000) (48307061489 / 1000000000000), orderedInterval (8468171684 / 1000000000000) (8468171692 / 1000000000000)))) (orderedInterval (-265355376 / 1000000000000) (-265355052 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (22760205465231 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66606420017 / 1000000000000) (-66606419848 / 1000000000000), orderedInterval (6469169767 / 1000000000000) (6469169935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (61798385328693 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-23227220501 / 1000000000000) (-23227220500 / 1000000000000), orderedInterval (-33267773933 / 1000000000000) (-33267773932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (84380411859861 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (12731231253 / 1000000000000) (12731231254 / 1000000000000), orderedInterval (32315293291 / 1000000000000) (32315293292 / 1000000000000)))) (orderedInterval (781140875 / 1000000000000) (781140937 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (35679314405007 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-35530666648 / 1000000000000) (-35530666647 / 1000000000000), orderedInterval (-39825528835 / 1000000000000) (-39825528834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (145034432200047 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16452997379 / 1000000000000) (16452997680 / 1000000000000), orderedInterval (-20784279811 / 1000000000000) (-20784279510 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (96876279224673 / 160000000000) 0 (IntervalRat.scale (975 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2120603522 / 1000000000000) (2120603523 / 1000000000000), orderedInterval (-32358187059 / 1000000000000) (-32358187058 / 1000000000000)))) (orderedInterval (-1951375302 / 1000000000000) (-1951375143 / 1000000000000))) = true
  rfl'

theorem compactCertificate616_chunkChecks0 :
    compactCertificate616.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate616.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate616_chunkChecks0_0
    compactCertificate616_chunkChecks0_1 compactCertificate616_chunkChecks0_2

theorem compactCertificate616_chunkChecks1_0 :
    compactCertificate616.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (975 / 2) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35164588158 / 1000000000000) (-35164588139 / 1000000000000), orderedInterval (-8290868350 / 1000000000000) (-8290868332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (57454446968139 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41547412447 / 1000000000000) (41547414026 / 1000000000000), orderedInterval (-6890058475 / 1000000000000) (-6890056895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (18579587673387 / 32000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6664709214 / 1000000000000) (-6664709213 / 1000000000000), orderedInterval (-32429506071 / 1000000000000) (-32429506070 / 1000000000000)))) (orderedInterval (-5599972837 / 1000000000000) (-5599972781 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (16765064331873 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-73927684085 / 1000000000000) (-73927681831 / 1000000000000), orderedInterval (25057462306 / 1000000000000) (25057464560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (45033320996781 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-22806365267 / 1000000000000) (-22806363466 / 1000000000000), orderedInterval (41774598052 / 1000000000000) (41774599853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (122274226734777 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28855836398 / 1000000000000) (-28855833180 / 1000000000000), orderedInterval (634770513 / 1000000000000) (634773730 / 1000000000000)))) (orderedInterval (751439401 / 1000000000000) (751439870 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (90066641993601 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32860825007 / 1000000000000) (-32860824963 / 1000000000000), orderedInterval (-7119017616 / 1000000000000) (-7119017572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (154330726192773 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19855654942 / 1000000000000) (-19855654940 / 1000000000000), orderedInterval (-16291814077 / 1000000000000) (-16291814075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (113679314405007 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28685432139 / 1000000000000) (28685432183 / 1000000000000), orderedInterval (8533629125 / 1000000000000) (8533629168 / 1000000000000)))) (orderedInterval (1294836552 / 1000000000000) (1294836602 / 1000000000000))) = true
  rfl'

theorem compactCertificate616_chunkChecks1_1 :
    compactCertificate616.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (174413302244961 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16219442996 / 1000000000000) (-16219442995 / 1000000000000), orderedInterval (-17907357890 / 1000000000000) (-17907357889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (100697567001369 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (30770822635 / 1000000000000) (30770840091 / 1000000000000), orderedInterval (-8067535109 / 1000000000000) (-8067517654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (178689599717421 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17320599614 / 1000000000000) (-17320599141 / 1000000000000), orderedInterval (16440371980 / 1000000000000) (16440372453 / 1000000000000)))) (orderedInterval (11697350349 / 1000000000000) (11697352573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (166955003061249 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23403129713 / 1000000000000) (23403129992 / 1000000000000), orderedInterval (7887706916 / 1000000000000) (7887707194 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (119146968068817 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22836478301 / 1000000000000) (-22836478300 / 1000000000000), orderedInterval (-18243876594 / 1000000000000) (-18243876593 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (135099962990343 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1964192293 / 1000000000000) (-1964192292 / 1000000000000), orderedInterval (-27386719700 / 1000000000000) (-27386719699 / 1000000000000)))) (orderedInterval (-2700021352 / 1000000000000) (-2700021247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (112632264262167 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25626817171 / 1000000000000) (25626817172 / 1000000000000), orderedInterval (15717670786 / 1000000000000) (15717670788 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (99514021269507 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20914476749 / 1000000000000) (20914476750 / 1000000000000), orderedInterval (24193735226 / 1000000000000) (24193735227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (28843042109193 / 32000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12583258488 / 1000000000000) (-12583258487 / 1000000000000), orderedInterval (-23401594895 / 1000000000000) (-23401594894 / 1000000000000)))) (orderedInterval (-2612137474 / 1000000000000) (-2612137406 / 1000000000000))) = true
  rfl'

theorem compactCertificate616_chunkChecks1_2 :
    compactCertificate616.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (79781372400171 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3371834245 / 1000000000000) (3371834247 / 1000000000000), orderedInterval (-35575280241 / 1000000000000) (-35575280239 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (67631552938131 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (22948317842 / 1000000000000) (22948321385 / 1000000000000), orderedInterval (-31323541488 / 1000000000000) (-31323537945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (42320685594993 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48307061481 / 1000000000000) (48307061489 / 1000000000000), orderedInterval (8468171684 / 1000000000000) (8468171692 / 1000000000000)))) (orderedInterval (7504944922 / 1000000000000) (7504945210 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (22760205465231 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66606420017 / 1000000000000) (-66606419848 / 1000000000000), orderedInterval (6469169767 / 1000000000000) (6469169935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (61798385328693 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-23227220501 / 1000000000000) (-23227220500 / 1000000000000), orderedInterval (-33267773933 / 1000000000000) (-33267773932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (84380411859861 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (12731231253 / 1000000000000) (12731231254 / 1000000000000), orderedInterval (32315293291 / 1000000000000) (32315293292 / 1000000000000)))) (orderedInterval (-2116079046 / 1000000000000) (-2116078993 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (35679314405007 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-35530666648 / 1000000000000) (-35530666647 / 1000000000000), orderedInterval (-39825528835 / 1000000000000) (-39825528834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (145034432200047 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16452997379 / 1000000000000) (16452997680 / 1000000000000), orderedInterval (-20784279811 / 1000000000000) (-20784279510 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (96876279224673 / 160000000000) 1 (IntervalRat.scale (975 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2120603522 / 1000000000000) (2120603523 / 1000000000000), orderedInterval (-32358187059 / 1000000000000) (-32358187058 / 1000000000000)))) (orderedInterval (10576603062 / 1000000000000) (10576603297 / 1000000000000))) = true
  rfl'

theorem compactCertificate616_chunkChecks1 :
    compactCertificate616.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate616.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate616_chunkChecks1_0
    compactCertificate616_chunkChecks1_1 compactCertificate616_chunkChecks1_2

theorem compactCertificate616_chunkChecks2_0 :
    compactCertificate616.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (975 / 2) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35164588158 / 1000000000000) (-35164588139 / 1000000000000), orderedInterval (-8290868350 / 1000000000000) (-8290868332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (57454446968139 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41547412447 / 1000000000000) (41547414026 / 1000000000000), orderedInterval (-6890058475 / 1000000000000) (-6890056895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (18579587673387 / 32000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6664709214 / 1000000000000) (-6664709213 / 1000000000000), orderedInterval (-32429506071 / 1000000000000) (-32429506070 / 1000000000000)))) (orderedInterval (14294203337 / 1000000000000) (14294203397 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (16765064331873 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-73927684085 / 1000000000000) (-73927681831 / 1000000000000), orderedInterval (25057462306 / 1000000000000) (25057464560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (45033320996781 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-22806365267 / 1000000000000) (-22806363466 / 1000000000000), orderedInterval (41774598052 / 1000000000000) (41774599853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (122274226734777 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28855836398 / 1000000000000) (-28855833180 / 1000000000000), orderedInterval (634770513 / 1000000000000) (634773730 / 1000000000000)))) (orderedInterval (-4802073963 / 1000000000000) (-4802073284 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (90066641993601 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32860825007 / 1000000000000) (-32860824963 / 1000000000000), orderedInterval (-7119017616 / 1000000000000) (-7119017572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (154330726192773 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19855654942 / 1000000000000) (-19855654940 / 1000000000000), orderedInterval (-16291814077 / 1000000000000) (-16291814075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (113679314405007 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28685432139 / 1000000000000) (28685432183 / 1000000000000), orderedInterval (8533629125 / 1000000000000) (8533629168 / 1000000000000)))) (orderedInterval (-3872792959 / 1000000000000) (-3872792872 / 1000000000000))) = true
  rfl'

theorem compactCertificate616_chunkChecks2_1 :
    compactCertificate616.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (174413302244961 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16219442996 / 1000000000000) (-16219442995 / 1000000000000), orderedInterval (-17907357890 / 1000000000000) (-17907357889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (100697567001369 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (30770822635 / 1000000000000) (30770840091 / 1000000000000), orderedInterval (-8067535109 / 1000000000000) (-8067517654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (178689599717421 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17320599614 / 1000000000000) (-17320599141 / 1000000000000), orderedInterval (16440371980 / 1000000000000) (16440372453 / 1000000000000)))) (orderedInterval (-5311547915 / 1000000000000) (-5311544544 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (166955003061249 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23403129713 / 1000000000000) (23403129992 / 1000000000000), orderedInterval (7887706916 / 1000000000000) (7887707194 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (119146968068817 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22836478301 / 1000000000000) (-22836478300 / 1000000000000), orderedInterval (-18243876594 / 1000000000000) (-18243876593 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (135099962990343 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1964192293 / 1000000000000) (-1964192292 / 1000000000000), orderedInterval (-27386719700 / 1000000000000) (-27386719699 / 1000000000000)))) (orderedInterval (6950198559 / 1000000000000) (6950198739 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (112632264262167 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25626817171 / 1000000000000) (25626817172 / 1000000000000), orderedInterval (15717670786 / 1000000000000) (15717670788 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (99514021269507 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20914476749 / 1000000000000) (20914476750 / 1000000000000), orderedInterval (24193735226 / 1000000000000) (24193735227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (28843042109193 / 32000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12583258488 / 1000000000000) (-12583258487 / 1000000000000), orderedInterval (-23401594895 / 1000000000000) (-23401594894 / 1000000000000)))) (orderedInterval (2437831516 / 1000000000000) (2437831617 / 1000000000000))) = true
  rfl'

theorem compactCertificate616_chunkChecks2_2 :
    compactCertificate616.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (79781372400171 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3371834245 / 1000000000000) (3371834247 / 1000000000000), orderedInterval (-35575280241 / 1000000000000) (-35575280239 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (67631552938131 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (22948317842 / 1000000000000) (22948321385 / 1000000000000), orderedInterval (-31323541488 / 1000000000000) (-31323537945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (42320685594993 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48307061481 / 1000000000000) (48307061489 / 1000000000000), orderedInterval (8468171684 / 1000000000000) (8468171692 / 1000000000000)))) (orderedInterval (1062187176 / 1000000000000) (1062187436 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (22760205465231 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66606420017 / 1000000000000) (-66606419848 / 1000000000000), orderedInterval (6469169767 / 1000000000000) (6469169935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (61798385328693 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-23227220501 / 1000000000000) (-23227220500 / 1000000000000), orderedInterval (-33267773933 / 1000000000000) (-33267773932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (84380411859861 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (12731231253 / 1000000000000) (12731231254 / 1000000000000), orderedInterval (32315293291 / 1000000000000) (32315293292 / 1000000000000)))) (orderedInterval (710704048 / 1000000000000) (710704101 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (35679314405007 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-35530666648 / 1000000000000) (-35530666647 / 1000000000000), orderedInterval (-39825528835 / 1000000000000) (-39825528834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (145034432200047 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16452997379 / 1000000000000) (16452997680 / 1000000000000), orderedInterval (-20784279811 / 1000000000000) (-20784279510 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (96876279224673 / 160000000000) 2 (IntervalRat.scale (975 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2120603522 / 1000000000000) (2120603523 / 1000000000000), orderedInterval (-32358187059 / 1000000000000) (-32358187058 / 1000000000000)))) (orderedInterval (5267425839 / 1000000000000) (5267426204 / 1000000000000))) = true
  rfl'

theorem compactCertificate616_chunkChecks2 :
    compactCertificate616.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate616.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate616_chunkChecks2_0
    compactCertificate616_chunkChecks2_1 compactCertificate616_chunkChecks2_2

theorem compactCertificate616_chunkChecks3_0 :
    compactCertificate616.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (975 / 2) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35164588158 / 1000000000000) (-35164588139 / 1000000000000), orderedInterval (-8290868350 / 1000000000000) (-8290868332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (57454446968139 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41547412447 / 1000000000000) (41547414026 / 1000000000000), orderedInterval (-6890058475 / 1000000000000) (-6890056895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (18579587673387 / 32000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6664709214 / 1000000000000) (-6664709213 / 1000000000000), orderedInterval (-32429506071 / 1000000000000) (-32429506070 / 1000000000000)))) (orderedInterval (6497466824 / 1000000000000) (6497466889 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (16765064331873 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-73927684085 / 1000000000000) (-73927681831 / 1000000000000), orderedInterval (25057462306 / 1000000000000) (25057464560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (45033320996781 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-22806365267 / 1000000000000) (-22806363466 / 1000000000000), orderedInterval (41774598052 / 1000000000000) (41774599853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (122274226734777 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28855836398 / 1000000000000) (-28855833180 / 1000000000000), orderedInterval (634770513 / 1000000000000) (634773730 / 1000000000000)))) (orderedInterval (-107146468 / 1000000000000) (-107145435 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (90066641993601 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32860825007 / 1000000000000) (-32860824963 / 1000000000000), orderedInterval (-7119017616 / 1000000000000) (-7119017572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (154330726192773 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19855654942 / 1000000000000) (-19855654940 / 1000000000000), orderedInterval (-16291814077 / 1000000000000) (-16291814075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (113679314405007 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28685432139 / 1000000000000) (28685432183 / 1000000000000), orderedInterval (8533629125 / 1000000000000) (8533629168 / 1000000000000)))) (orderedInterval (-4522877960 / 1000000000000) (-4522877802 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate616_chunkChecks3_1 :
    compactCertificate616.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (174413302244961 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16219442996 / 1000000000000) (-16219442995 / 1000000000000), orderedInterval (-17907357890 / 1000000000000) (-17907357889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (100697567001369 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (30770822635 / 1000000000000) (30770840091 / 1000000000000), orderedInterval (-8067535109 / 1000000000000) (-8067517654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (178689599717421 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17320599614 / 1000000000000) (-17320599141 / 1000000000000), orderedInterval (16440371980 / 1000000000000) (16440372453 / 1000000000000)))) (orderedInterval (-62376871961 / 1000000000000) (-62376866482 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (166955003061249 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23403129713 / 1000000000000) (23403129992 / 1000000000000), orderedInterval (7887706916 / 1000000000000) (7887707194 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (119146968068817 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22836478301 / 1000000000000) (-22836478300 / 1000000000000), orderedInterval (-18243876594 / 1000000000000) (-18243876593 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (135099962990343 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1964192293 / 1000000000000) (-1964192292 / 1000000000000), orderedInterval (-27386719700 / 1000000000000) (-27386719699 / 1000000000000)))) (orderedInterval (6810983535 / 1000000000000) (6810983849 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (112632264262167 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25626817171 / 1000000000000) (25626817172 / 1000000000000), orderedInterval (15717670786 / 1000000000000) (15717670788 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (99514021269507 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20914476749 / 1000000000000) (20914476750 / 1000000000000), orderedInterval (24193735226 / 1000000000000) (24193735227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (28843042109193 / 32000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12583258488 / 1000000000000) (-12583258487 / 1000000000000), orderedInterval (-23401594895 / 1000000000000) (-23401594894 / 1000000000000)))) (orderedInterval (6110764814 / 1000000000000) (6110764969 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate616_chunkChecks3_2 :
    compactCertificate616.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (79781372400171 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3371834245 / 1000000000000) (3371834247 / 1000000000000), orderedInterval (-35575280241 / 1000000000000) (-35575280239 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (67631552938131 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (22948317842 / 1000000000000) (22948321385 / 1000000000000), orderedInterval (-31323541488 / 1000000000000) (-31323537945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (42320685594993 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48307061481 / 1000000000000) (48307061489 / 1000000000000), orderedInterval (8468171684 / 1000000000000) (8468171692 / 1000000000000)))) (orderedInterval (-7288808478 / 1000000000000) (-7288808242 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (22760205465231 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66606420017 / 1000000000000) (-66606419848 / 1000000000000), orderedInterval (6469169767 / 1000000000000) (6469169935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (61798385328693 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-23227220501 / 1000000000000) (-23227220500 / 1000000000000), orderedInterval (-33267773933 / 1000000000000) (-33267773932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (84380411859861 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (12731231253 / 1000000000000) (12731231254 / 1000000000000), orderedInterval (32315293291 / 1000000000000) (32315293292 / 1000000000000)))) (orderedInterval (2761581688 / 1000000000000) (2761581742 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (35679314405007 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-35530666648 / 1000000000000) (-35530666647 / 1000000000000), orderedInterval (-39825528835 / 1000000000000) (-39825528834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (145034432200047 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16452997379 / 1000000000000) (16452997680 / 1000000000000), orderedInterval (-20784279811 / 1000000000000) (-20784279510 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (96876279224673 / 160000000000) 3 (IntervalRat.scale (975 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2120603522 / 1000000000000) (2120603523 / 1000000000000), orderedInterval (-32358187059 / 1000000000000) (-32358187058 / 1000000000000)))) (orderedInterval (-22496314755 / 1000000000000) (-22496314165 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate616_chunkChecks3 :
    compactCertificate616.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate616.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate616_chunkChecks3_0
    compactCertificate616_chunkChecks3_1 compactCertificate616_chunkChecks3_2

theorem compactCertificate616_chunkChecks4_0 :
    compactCertificate616.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (975 / 2) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35164588158 / 1000000000000) (-35164588139 / 1000000000000), orderedInterval (-8290868350 / 1000000000000) (-8290868332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (57454446968139 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41547412447 / 1000000000000) (41547414026 / 1000000000000), orderedInterval (-6890058475 / 1000000000000) (-6890056895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (18579587673387 / 32000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6664709214 / 1000000000000) (-6664709213 / 1000000000000), orderedInterval (-32429506071 / 1000000000000) (-32429506070 / 1000000000000)))) (orderedInterval (-14637550175 / 1000000000000) (-14637550103 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (16765064331873 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-73927684085 / 1000000000000) (-73927681831 / 1000000000000), orderedInterval (25057462306 / 1000000000000) (25057464560 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (45033320996781 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-22806365267 / 1000000000000) (-22806363466 / 1000000000000), orderedInterval (41774598052 / 1000000000000) (41774599853 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (122274226734777 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28855836398 / 1000000000000) (-28855833180 / 1000000000000), orderedInterval (634770513 / 1000000000000) (634773730 / 1000000000000)))) (orderedInterval (12297609719 / 1000000000000) (12297611323 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (90066641993601 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32860825007 / 1000000000000) (-32860824963 / 1000000000000), orderedInterval (-7119017616 / 1000000000000) (-7119017572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (154330726192773 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19855654942 / 1000000000000) (-19855654940 / 1000000000000), orderedInterval (-16291814077 / 1000000000000) (-16291814075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (113679314405007 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28685432139 / 1000000000000) (28685432183 / 1000000000000), orderedInterval (8533629125 / 1000000000000) (8533629168 / 1000000000000)))) (orderedInterval (12532538350 / 1000000000000) (12532538640 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate616_chunkChecks4_1 :
    compactCertificate616.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (174413302244961 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16219442996 / 1000000000000) (-16219442995 / 1000000000000), orderedInterval (-17907357890 / 1000000000000) (-17907357889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (100697567001369 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (30770822635 / 1000000000000) (30770840091 / 1000000000000), orderedInterval (-8067535109 / 1000000000000) (-8067517654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (178689599717421 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17320599614 / 1000000000000) (-17320599141 / 1000000000000), orderedInterval (16440371980 / 1000000000000) (16440372453 / 1000000000000)))) (orderedInterval (10820583218 / 1000000000000) (10820592858 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (166955003061249 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23403129713 / 1000000000000) (23403129992 / 1000000000000), orderedInterval (7887706916 / 1000000000000) (7887707194 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (119146968068817 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22836478301 / 1000000000000) (-22836478300 / 1000000000000), orderedInterval (-18243876594 / 1000000000000) (-18243876593 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (135099962990343 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1964192293 / 1000000000000) (-1964192292 / 1000000000000), orderedInterval (-27386719700 / 1000000000000) (-27386719699 / 1000000000000)))) (orderedInterval (-20564027339 / 1000000000000) (-20564026774 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (112632264262167 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25626817171 / 1000000000000) (25626817172 / 1000000000000), orderedInterval (15717670786 / 1000000000000) (15717670788 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (99514021269507 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20914476749 / 1000000000000) (20914476750 / 1000000000000), orderedInterval (24193735226 / 1000000000000) (24193735227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (28843042109193 / 32000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12583258488 / 1000000000000) (-12583258487 / 1000000000000), orderedInterval (-23401594895 / 1000000000000) (-23401594894 / 1000000000000)))) (orderedInterval (-5674472028 / 1000000000000) (-5674471782 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate616_chunkChecks4_2 :
    compactCertificate616.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (79781372400171 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3371834245 / 1000000000000) (3371834247 / 1000000000000), orderedInterval (-35575280241 / 1000000000000) (-35575280239 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (67631552938131 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (22948317842 / 1000000000000) (22948321385 / 1000000000000), orderedInterval (-31323541488 / 1000000000000) (-31323537945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (42320685594993 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48307061481 / 1000000000000) (48307061489 / 1000000000000), orderedInterval (8468171684 / 1000000000000) (8468171692 / 1000000000000)))) (orderedInterval (-1158049599 / 1000000000000) (-1158049381 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (22760205465231 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66606420017 / 1000000000000) (-66606419848 / 1000000000000), orderedInterval (6469169767 / 1000000000000) (6469169935 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (61798385328693 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-23227220501 / 1000000000000) (-23227220500 / 1000000000000), orderedInterval (-33267773933 / 1000000000000) (-33267773932 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (84380411859861 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (12731231253 / 1000000000000) (12731231254 / 1000000000000), orderedInterval (32315293291 / 1000000000000) (32315293292 / 1000000000000)))) (orderedInterval (-1131085840 / 1000000000000) (-1131085784 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (35679314405007 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-35530666648 / 1000000000000) (-35530666647 / 1000000000000), orderedInterval (-39825528835 / 1000000000000) (-39825528834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (145034432200047 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16452997379 / 1000000000000) (16452997680 / 1000000000000), orderedInterval (-20784279811 / 1000000000000) (-20784279510 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (96876279224673 / 160000000000) 4 (IntervalRat.scale (975 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2120603522 / 1000000000000) (2120603523 / 1000000000000), orderedInterval (-32358187059 / 1000000000000) (-32358187058 / 1000000000000)))) (orderedInterval (-16873600692 / 1000000000000) (-16873599705 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate616_chunkChecks4 :
    compactCertificate616.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate616.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate616_chunkChecks4_0
    compactCertificate616_chunkChecks4_1 compactCertificate616_chunkChecks4_2

theorem compactCertificate616_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate616.chunkCheck r b = true :=
  compactCertificate616.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate616_chunkChecks0
    · exact compactCertificate616_chunkChecks1
    · exact compactCertificate616_chunkChecks2
    · exact compactCertificate616_chunkChecks3
    · exact compactCertificate616_chunkChecks4)

theorem compactCertificate616_coefficient0 :
    compactCertificate616.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate616_coefficient1 :
    compactCertificate616.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate616_coefficient2 :
    compactCertificate616.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate616_coefficient3 :
    compactCertificate616.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate616_coefficient4 :
    compactCertificate616.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate616_coefficients : ∀ r : Fin 5,
    compactCertificate616.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate616_coefficient0
  · exact compactCertificate616_coefficient1
  · exact compactCertificate616_coefficient2
  · exact compactCertificate616_coefficient3
  · exact compactCertificate616_coefficient4

theorem compactCertificate616_lower : (1 : ℚ) ≤ compactCertificate616.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate616, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate616_proves {t : ℝ} (ht : t ∈ compactCertificate616.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate616.proves compactCertificate616_states compactCertificate616_chunks
    compactCertificate616_coefficients compactCertificate616_lower ht

end Erdos232
