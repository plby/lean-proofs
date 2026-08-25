/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate583 : CompactCertificate where
  left := 454
  right := 455
  center := 909 / 2
  grid := fun i =>
    match i.val with
    | 0 => 145
    | 1 => 107
    | 2 => 172
    | 3 => 31
    | 4 => 84
    | 5 => 227
    | 6 => 167
    | 7 => 286
    | 8 => 211
    | 9 => 324
    | 10 => 187
    | 11 => 332
    | 12 => 310
    | 13 => 221
    | 14 => 251
    | 15 => 209
    | 16 => 185
    | 17 => 268
    | 18 => 148
    | 19 => 126
    | 20 => 79
    | 21 => 42
    | 22 => 115
    | 23 => 157
    | 24 => 66
    | 25 => 269
    | _ => 180
  point := fun i =>
    match i.val with
    | 0 => 909 / 2
    | 1 => 1339130571642009 / 4000000000000
    | 2 => 433047312695097 / 800000000000
    | 3 => 390754960965963 / 4000000000000
    | 4 => 1049622789386511 / 4000000000000
    | 5 => 2849930053895187 / 4000000000000
    | 6 => 2099245578773931 / 4000000000000
    | 7 => 3597093079723863 / 4000000000000
    | 8 => 2649602481901317 / 4000000000000
    | 9 => 4065171583094091 / 4000000000000
    | 10 => 2347027907801139 / 4000000000000
    | 11 => 4164842208798351 / 4000000000000
    | 12 => 3891335840581419 / 4000000000000
    | 13 => 2777040871142427 / 4000000000000
    | 14 => 3148868368159533 / 4000000000000
    | 15 => 2625198159341277 / 4000000000000
    | 16 => 2319442188050817 / 4000000000000
    | 17 => 672264750698883 / 800000000000
    | 18 => 1859519679788601 / 4000000000000
    | 19 => 1576335426173361 / 4000000000000
    | 20 => 986397518098683 / 4000000000000
    | 21 => 530487865843461 / 4000000000000
    | 22 => 1440377750353383 / 4000000000000
    | 23 => 1966712676425991 / 4000000000000
    | 24 => 831602481901317 / 4000000000000
    | 25 => 3380417919739557 / 4000000000000
    | _ => 2257962508082763 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (9107370152 / 1000000000000) (9107370171 / 1000000000000), orderedInterval (-36310985009 / 1000000000000) (-36310984991 / 1000000000000))
    | 1 => (orderedInterval (23997876882 / 1000000000000) (23997880222 / 1000000000000), orderedInterval (-36445923445 / 1000000000000) (-36445920105 / 1000000000000))
    | 2 => (orderedInterval (33802035676 / 1000000000000) (33802040371 / 1000000000000), orderedInterval (-5818802343 / 1000000000000) (-5818797647 / 1000000000000))
    | 3 => (orderedInterval (-71329405331 / 1000000000000) (-71329405330 / 1000000000000), orderedInterval (-37435537410 / 1000000000000) (-37435537409 / 1000000000000))
    | 4 => (orderedInterval (-31850175875 / 1000000000000) (-31850159314 / 1000000000000), orderedInterval (37632707860 / 1000000000000) (37632724420 / 1000000000000))
    | 5 => (orderedInterval (-3762460592 / 1000000000000) (-3762460591 / 1000000000000), orderedInterval (-29651490313 / 1000000000000) (-29651490312 / 1000000000000))
    | 6 => (orderedInterval (-28342050974 / 1000000000000) (-28342050973 / 1000000000000), orderedInterval (-20215844593 / 1000000000000) (-20215844592 / 1000000000000))
    | 7 => (orderedInterval (26606089498 / 1000000000000) (26606094403 / 1000000000000), orderedInterval (191835830 / 1000000000000) (191840734 / 1000000000000))
    | 8 => (orderedInterval (-9450713690 / 1000000000000) (-9450713689 / 1000000000000), orderedInterval (-29518514622 / 1000000000000) (-29518514621 / 1000000000000))
    | 9 => (orderedInterval (-17916619965 / 1000000000000) (-17916619217 / 1000000000000), orderedInterval (17484752624 / 1000000000000) (17484753372 / 1000000000000))
    | 10 => (orderedInterval (-2117699356 / 1000000000000) (-2117699355 / 1000000000000), orderedInterval (-32869095314 / 1000000000000) (-32869095313 / 1000000000000))
    | 11 => (orderedInterval (-20978034356 / 1000000000000) (-20978027214 / 1000000000000), orderedInterval (13099947848 / 1000000000000) (13099954990 / 1000000000000))
    | 12 => (orderedInterval (-6934004359 / 1000000000000) (-6934004358 / 1000000000000), orderedInterval (24627064963 / 1000000000000) (24627064964 / 1000000000000))
    | 13 => (orderedInterval (-20717641043 / 1000000000000) (-20717641042 / 1000000000000), orderedInterval (-22070257596 / 1000000000000) (-22070257595 / 1000000000000))
    | 14 => (orderedInterval (14557922949 / 1000000000000) (14557923063 / 1000000000000), orderedInterval (-24437990600 / 1000000000000) (-24437990486 / 1000000000000))
    | 15 => (orderedInterval (-14709381637 / 1000000000000) (-14709381636 / 1000000000000), orderedInterval (-27441449211 / 1000000000000) (-27441449210 / 1000000000000))
    | 16 => (orderedInterval (17288127658 / 1000000000000) (17288128190 / 1000000000000), orderedInterval (-28281585423 / 1000000000000) (-28281584891 / 1000000000000))
    | 17 => (orderedInterval (-20322925523 / 1000000000000) (-20322922471 / 1000000000000), orderedInterval (18574443971 / 1000000000000) (18574447023 / 1000000000000))
    | 18 => (orderedInterval (24102990176 / 1000000000000) (24102990177 / 1000000000000), orderedInterval (28053862474 / 1000000000000) (28053862475 / 1000000000000))
    | 19 => (orderedInterval (-33193721507 / 1000000000000) (-33193620721 / 1000000000000), orderedInterval (22705293934 / 1000000000000) (22705394720 / 1000000000000))
    | 20 => (orderedInterval (36503156346 / 1000000000000) (36503200579 / 1000000000000), orderedInterval (-35416825862 / 1000000000000) (-35416781629 / 1000000000000))
    | 21 => (orderedInterval (68855229277 / 1000000000000) (68855229284 / 1000000000000), orderedInterval (7433461149 / 1000000000000) (7433461157 / 1000000000000))
    | 22 => (orderedInterval (16515631606 / 1000000000000) (16515631952 / 1000000000000), orderedInterval (-38690225746 / 1000000000000) (-38690225400 / 1000000000000))
    | 23 => (orderedInterval (24964637223 / 1000000000000) (24964647131 / 1000000000000), orderedInterval (-25939794253 / 1000000000000) (-25939784344 / 1000000000000))
    | 24 => (orderedInterval (53873032890 / 1000000000000) (53873032892 / 1000000000000), orderedInterval (12512565316 / 1000000000000) (12512565318 / 1000000000000))
    | 25 => (orderedInterval (-19713780239 / 1000000000000) (-19713780238 / 1000000000000), orderedInterval (-19084668669 / 1000000000000) (-19084668668 / 1000000000000))
    | _ => (orderedInterval (-7029282027 / 1000000000000) (-7029282023 / 1000000000000), orderedInterval (32844724943 / 1000000000000) (32844724948 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (5816998335 / 1000000000000) (5816998681 / 1000000000000)
      | 1 => orderedInterval (-121560111 / 1000000000000) (-121559451 / 1000000000000)
      | 2 => orderedInterval (-1049043519 / 1000000000000) (-1049043342 / 1000000000000)
      | 3 => orderedInterval (44511538 / 1000000000000) (44512866 / 1000000000000)
      | 4 => orderedInterval (-1907610840 / 1000000000000) (-1907610785 / 1000000000000)
      | 5 => orderedInterval (-1679548404 / 1000000000000) (-1679548251 / 1000000000000)
      | 6 => orderedInterval (-786758397 / 1000000000000) (-786751138 / 1000000000000)
      | 7 => orderedInterval (-3559370101 / 1000000000000) (-3559369279 / 1000000000000)
      | _ => orderedInterval (3248380766 / 1000000000000) (3248380893 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-15049226455 / 1000000000000) (-15049226061 / 1000000000000)
      | 1 => orderedInterval (4185000524 / 1000000000000) (4185000935 / 1000000000000)
      | 2 => orderedInterval (-1051442367 / 1000000000000) (-1051442023 / 1000000000000)
      | 3 => orderedInterval (-5824899822 / 1000000000000) (-5824896825 / 1000000000000)
      | 4 => orderedInterval (-3925414692 / 1000000000000) (-3925414603 / 1000000000000)
      | 5 => orderedInterval (2486588010 / 1000000000000) (2486588256 / 1000000000000)
      | 6 => orderedInterval (-6327926468 / 1000000000000) (-6327920634 / 1000000000000)
      | 7 => orderedInterval (2805999719 / 1000000000000) (2806000596 / 1000000000000)
      | _ => orderedInterval (-4730744569 / 1000000000000) (-4730744390 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-6511671131 / 1000000000000) (-6511670674 / 1000000000000)
      | 1 => orderedInterval (-314617114 / 1000000000000) (-314616826 / 1000000000000)
      | 2 => orderedInterval (3700146340 / 1000000000000) (3700147012 / 1000000000000)
      | 3 => orderedInterval (7370665 / 1000000000000) (7377464 / 1000000000000)
      | 4 => orderedInterval (4227414400 / 1000000000000) (4227414548 / 1000000000000)
      | 5 => orderedInterval (3737876140 / 1000000000000) (3737876552 / 1000000000000)
      | 6 => orderedInterval (2283533031 / 1000000000000) (2283537857 / 1000000000000)
      | 7 => orderedInterval (2576354667 / 1000000000000) (2576355612 / 1000000000000)
      | _ => orderedInterval (-7640273496 / 1000000000000) (-7640273234 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (15119237487 / 1000000000000) (15119238021 / 1000000000000)
      | 1 => orderedInterval (-8388086455 / 1000000000000) (-8388086209 / 1000000000000)
      | 2 => orderedInterval (2246180244 / 1000000000000) (2246181560 / 1000000000000)
      | 3 => orderedInterval (17585637113 / 1000000000000) (17585652573 / 1000000000000)
      | 4 => orderedInterval (11146625048 / 1000000000000) (11146625298 / 1000000000000)
      | 5 => orderedInterval (-5420991374 / 1000000000000) (-5420990672 / 1000000000000)
      | 6 => orderedInterval (5816846300 / 1000000000000) (5816850357 / 1000000000000)
      | 7 => orderedInterval (-2955630477 / 1000000000000) (-2955629460 / 1000000000000)
      | _ => orderedInterval (1828965317 / 1000000000000) (1828965722 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (7600159728 / 1000000000000) (7600160357 / 1000000000000)
      | 1 => orderedInterval (1524598839 / 1000000000000) (1524599105 / 1000000000000)
      | 2 => orderedInterval (-13617551389 / 1000000000000) (-13617548799 / 1000000000000)
      | 3 => orderedInterval (-3062857758 / 1000000000000) (-3062822517 / 1000000000000)
      | 4 => orderedInterval (-8750816726 / 1000000000000) (-8750816292 / 1000000000000)
      | 5 => orderedInterval (-9416653370 / 1000000000000) (-9416652145 / 1000000000000)
      | 6 => orderedInterval (-3078876367 / 1000000000000) (-3078872904 / 1000000000000)
      | 7 => orderedInterval (-2764207947 / 1000000000000) (-2764206847 / 1000000000000)
      | _ => orderedInterval (22327154146 / 1000000000000) (22327154795 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (5999267 / 1000000000000) (6010194 / 1000000000000)
    | 1 => orderedInterval (-27432066120 / 1000000000000) (-27432054749 / 1000000000000)
    | 2 => orderedInterval (2066133502 / 1000000000000) (2066148311 / 1000000000000)
    | 3 => orderedInterval (36978783203 / 1000000000000) (36978807190 / 1000000000000)
    | _ => orderedInterval (-9239050844 / 1000000000000) (-9239005247 / 1000000000000)

theorem compactCertificate583_stateChecks0 :
    compactCertificate583.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (909 / 2)) (orderedInterval (9107370152 / 1000000000000) (9107370171 / 1000000000000), orderedInterval (-36310985009 / 1000000000000) (-36310984991 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1339130571642009 / 4000000000000)) (orderedInterval (23997876882 / 1000000000000) (23997880222 / 1000000000000), orderedInterval (-36445923445 / 1000000000000) (-36445920105 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (433047312695097 / 800000000000)) (orderedInterval (33802035676 / 1000000000000) (33802040371 / 1000000000000), orderedInterval (-5818802343 / 1000000000000) (-5818797647 / 1000000000000))) = true
  rfl'

theorem compactCertificate583_stateChecks1 :
    compactCertificate583.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (390754960965963 / 4000000000000)) (orderedInterval (-71329405331 / 1000000000000) (-71329405330 / 1000000000000), orderedInterval (-37435537410 / 1000000000000) (-37435537409 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1049622789386511 / 4000000000000)) (orderedInterval (-31850175875 / 1000000000000) (-31850159314 / 1000000000000), orderedInterval (37632707860 / 1000000000000) (37632724420 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 227 12 (2849930053895187 / 4000000000000)) (orderedInterval (-3762460592 / 1000000000000) (-3762460591 / 1000000000000), orderedInterval (-29651490313 / 1000000000000) (-29651490312 / 1000000000000))) = true
  rfl'

theorem compactCertificate583_stateChecks2 :
    compactCertificate583.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2099245578773931 / 4000000000000)) (orderedInterval (-28342050974 / 1000000000000) (-28342050973 / 1000000000000), orderedInterval (-20215844593 / 1000000000000) (-20215844592 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 286 12 (3597093079723863 / 4000000000000)) (orderedInterval (26606089498 / 1000000000000) (26606094403 / 1000000000000), orderedInterval (191835830 / 1000000000000) (191840734 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 211 12 (2649602481901317 / 4000000000000)) (orderedInterval (-9450713690 / 1000000000000) (-9450713689 / 1000000000000), orderedInterval (-29518514622 / 1000000000000) (-29518514621 / 1000000000000))) = true
  rfl'

theorem compactCertificate583_stateChecks3 :
    compactCertificate583.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 324 12 (4065171583094091 / 4000000000000)) (orderedInterval (-17916619965 / 1000000000000) (-17916619217 / 1000000000000), orderedInterval (17484752624 / 1000000000000) (17484753372 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (2347027907801139 / 4000000000000)) (orderedInterval (-2117699356 / 1000000000000) (-2117699355 / 1000000000000), orderedInterval (-32869095314 / 1000000000000) (-32869095313 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 332 12 (4164842208798351 / 4000000000000)) (orderedInterval (-20978034356 / 1000000000000) (-20978027214 / 1000000000000), orderedInterval (13099947848 / 1000000000000) (13099954990 / 1000000000000))) = true
  rfl'

theorem compactCertificate583_stateChecks4 :
    compactCertificate583.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 310 12 (3891335840581419 / 4000000000000)) (orderedInterval (-6934004359 / 1000000000000) (-6934004358 / 1000000000000), orderedInterval (24627064963 / 1000000000000) (24627064964 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (2777040871142427 / 4000000000000)) (orderedInterval (-20717641043 / 1000000000000) (-20717641042 / 1000000000000), orderedInterval (-22070257596 / 1000000000000) (-22070257595 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 251 12 (3148868368159533 / 4000000000000)) (orderedInterval (14557922949 / 1000000000000) (14557923063 / 1000000000000), orderedInterval (-24437990600 / 1000000000000) (-24437990486 / 1000000000000))) = true
  rfl'

theorem compactCertificate583_stateChecks5 :
    compactCertificate583.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 209 12 (2625198159341277 / 4000000000000)) (orderedInterval (-14709381637 / 1000000000000) (-14709381636 / 1000000000000), orderedInterval (-27441449211 / 1000000000000) (-27441449210 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2319442188050817 / 4000000000000)) (orderedInterval (17288127658 / 1000000000000) (17288128190 / 1000000000000), orderedInterval (-28281585423 / 1000000000000) (-28281584891 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 268 12 (672264750698883 / 800000000000)) (orderedInterval (-20322925523 / 1000000000000) (-20322922471 / 1000000000000), orderedInterval (18574443971 / 1000000000000) (18574447023 / 1000000000000))) = true
  rfl'

theorem compactCertificate583_stateChecks6 :
    compactCertificate583.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1859519679788601 / 4000000000000)) (orderedInterval (24102990176 / 1000000000000) (24102990177 / 1000000000000), orderedInterval (28053862474 / 1000000000000) (28053862475 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1576335426173361 / 4000000000000)) (orderedInterval (-33193721507 / 1000000000000) (-33193620721 / 1000000000000), orderedInterval (22705293934 / 1000000000000) (22705394720 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (986397518098683 / 4000000000000)) (orderedInterval (36503156346 / 1000000000000) (36503200579 / 1000000000000), orderedInterval (-35416825862 / 1000000000000) (-35416781629 / 1000000000000))) = true
  rfl'

theorem compactCertificate583_stateChecks7 :
    compactCertificate583.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (530487865843461 / 4000000000000)) (orderedInterval (68855229277 / 1000000000000) (68855229284 / 1000000000000), orderedInterval (7433461149 / 1000000000000) (7433461157 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1440377750353383 / 4000000000000)) (orderedInterval (16515631606 / 1000000000000) (16515631952 / 1000000000000), orderedInterval (-38690225746 / 1000000000000) (-38690225400 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1966712676425991 / 4000000000000)) (orderedInterval (24964637223 / 1000000000000) (24964647131 / 1000000000000), orderedInterval (-25939794253 / 1000000000000) (-25939784344 / 1000000000000))) = true
  rfl'

theorem compactCertificate583_stateChecks8 :
    compactCertificate583.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (831602481901317 / 4000000000000)) (orderedInterval (53873032890 / 1000000000000) (53873032892 / 1000000000000), orderedInterval (12512565316 / 1000000000000) (12512565318 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 269 12 (3380417919739557 / 4000000000000)) (orderedInterval (-19713780239 / 1000000000000) (-19713780238 / 1000000000000), orderedInterval (-19084668669 / 1000000000000) (-19084668668 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2257962508082763 / 4000000000000)) (orderedInterval (-7029282027 / 1000000000000) (-7029282023 / 1000000000000), orderedInterval (32844724943 / 1000000000000) (32844724948 / 1000000000000))) = true
  rfl'

theorem compactCertificate583_states : ∀ j,
    BesselStateValid (compactCertificate583.point j) (compactCertificate583.state j) :=
  compactCertificate583.statesValid_of_checks3 compactCertificate583_stateChecks0
    compactCertificate583_stateChecks1 compactCertificate583_stateChecks2
    compactCertificate583_stateChecks3 compactCertificate583_stateChecks4
    compactCertificate583_stateChecks5 compactCertificate583_stateChecks6
    compactCertificate583_stateChecks7 compactCertificate583_stateChecks8

theorem compactCertificate583_chunkChecks0_0 :
    compactCertificate583.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (909 / 2) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (9107370152 / 1000000000000) (9107370171 / 1000000000000), orderedInterval (-36310985009 / 1000000000000) (-36310984991 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1339130571642009 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23997876882 / 1000000000000) (23997880222 / 1000000000000), orderedInterval (-36445923445 / 1000000000000) (-36445920105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (433047312695097 / 800000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33802035676 / 1000000000000) (33802040371 / 1000000000000), orderedInterval (-5818802343 / 1000000000000) (-5818797647 / 1000000000000)))) (orderedInterval (5816998335 / 1000000000000) (5816998681 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (390754960965963 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-71329405331 / 1000000000000) (-71329405330 / 1000000000000), orderedInterval (-37435537410 / 1000000000000) (-37435537409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1049622789386511 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-31850175875 / 1000000000000) (-31850159314 / 1000000000000), orderedInterval (37632707860 / 1000000000000) (37632724420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2849930053895187 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-3762460592 / 1000000000000) (-3762460591 / 1000000000000), orderedInterval (-29651490313 / 1000000000000) (-29651490312 / 1000000000000)))) (orderedInterval (-121560111 / 1000000000000) (-121559451 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2099245578773931 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28342050974 / 1000000000000) (-28342050973 / 1000000000000), orderedInterval (-20215844593 / 1000000000000) (-20215844592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3597093079723863 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26606089498 / 1000000000000) (26606094403 / 1000000000000), orderedInterval (191835830 / 1000000000000) (191840734 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2649602481901317 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9450713690 / 1000000000000) (-9450713689 / 1000000000000), orderedInterval (-29518514622 / 1000000000000) (-29518514621 / 1000000000000)))) (orderedInterval (-1049043519 / 1000000000000) (-1049043342 / 1000000000000))) = true
  rfl'

theorem compactCertificate583_chunkChecks0_1 :
    compactCertificate583.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4065171583094091 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17916619965 / 1000000000000) (-17916619217 / 1000000000000), orderedInterval (17484752624 / 1000000000000) (17484753372 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2347027907801139 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2117699356 / 1000000000000) (-2117699355 / 1000000000000), orderedInterval (-32869095314 / 1000000000000) (-32869095313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4164842208798351 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20978034356 / 1000000000000) (-20978027214 / 1000000000000), orderedInterval (13099947848 / 1000000000000) (13099954990 / 1000000000000)))) (orderedInterval (44511538 / 1000000000000) (44512866 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3891335840581419 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6934004359 / 1000000000000) (-6934004358 / 1000000000000), orderedInterval (24627064963 / 1000000000000) (24627064964 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2777040871142427 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20717641043 / 1000000000000) (-20717641042 / 1000000000000), orderedInterval (-22070257596 / 1000000000000) (-22070257595 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3148868368159533 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14557922949 / 1000000000000) (14557923063 / 1000000000000), orderedInterval (-24437990600 / 1000000000000) (-24437990486 / 1000000000000)))) (orderedInterval (-1907610840 / 1000000000000) (-1907610785 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2625198159341277 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14709381637 / 1000000000000) (-14709381636 / 1000000000000), orderedInterval (-27441449211 / 1000000000000) (-27441449210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2319442188050817 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17288127658 / 1000000000000) (17288128190 / 1000000000000), orderedInterval (-28281585423 / 1000000000000) (-28281584891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (672264750698883 / 800000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20322925523 / 1000000000000) (-20322922471 / 1000000000000), orderedInterval (18574443971 / 1000000000000) (18574447023 / 1000000000000)))) (orderedInterval (-1679548404 / 1000000000000) (-1679548251 / 1000000000000))) = true
  rfl'

theorem compactCertificate583_chunkChecks0_2 :
    compactCertificate583.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1859519679788601 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24102990176 / 1000000000000) (24102990177 / 1000000000000), orderedInterval (28053862474 / 1000000000000) (28053862475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1576335426173361 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-33193721507 / 1000000000000) (-33193620721 / 1000000000000), orderedInterval (22705293934 / 1000000000000) (22705394720 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (986397518098683 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36503156346 / 1000000000000) (36503200579 / 1000000000000), orderedInterval (-35416825862 / 1000000000000) (-35416781629 / 1000000000000)))) (orderedInterval (-786758397 / 1000000000000) (-786751138 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (530487865843461 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68855229277 / 1000000000000) (68855229284 / 1000000000000), orderedInterval (7433461149 / 1000000000000) (7433461157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1440377750353383 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (16515631606 / 1000000000000) (16515631952 / 1000000000000), orderedInterval (-38690225746 / 1000000000000) (-38690225400 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1966712676425991 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24964637223 / 1000000000000) (24964647131 / 1000000000000), orderedInterval (-25939794253 / 1000000000000) (-25939784344 / 1000000000000)))) (orderedInterval (-3559370101 / 1000000000000) (-3559369279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (831602481901317 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53873032890 / 1000000000000) (53873032892 / 1000000000000), orderedInterval (12512565316 / 1000000000000) (12512565318 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3380417919739557 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19713780239 / 1000000000000) (-19713780238 / 1000000000000), orderedInterval (-19084668669 / 1000000000000) (-19084668668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2257962508082763 / 4000000000000) 0 (IntervalRat.scale (909 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7029282027 / 1000000000000) (-7029282023 / 1000000000000), orderedInterval (32844724943 / 1000000000000) (32844724948 / 1000000000000)))) (orderedInterval (3248380766 / 1000000000000) (3248380893 / 1000000000000))) = true
  rfl'

theorem compactCertificate583_chunkChecks0 :
    compactCertificate583.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate583.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate583_chunkChecks0_0
    compactCertificate583_chunkChecks0_1 compactCertificate583_chunkChecks0_2

theorem compactCertificate583_chunkChecks1_0 :
    compactCertificate583.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (909 / 2) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (9107370152 / 1000000000000) (9107370171 / 1000000000000), orderedInterval (-36310985009 / 1000000000000) (-36310984991 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1339130571642009 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23997876882 / 1000000000000) (23997880222 / 1000000000000), orderedInterval (-36445923445 / 1000000000000) (-36445920105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (433047312695097 / 800000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33802035676 / 1000000000000) (33802040371 / 1000000000000), orderedInterval (-5818802343 / 1000000000000) (-5818797647 / 1000000000000)))) (orderedInterval (-15049226455 / 1000000000000) (-15049226061 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (390754960965963 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-71329405331 / 1000000000000) (-71329405330 / 1000000000000), orderedInterval (-37435537410 / 1000000000000) (-37435537409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1049622789386511 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-31850175875 / 1000000000000) (-31850159314 / 1000000000000), orderedInterval (37632707860 / 1000000000000) (37632724420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2849930053895187 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-3762460592 / 1000000000000) (-3762460591 / 1000000000000), orderedInterval (-29651490313 / 1000000000000) (-29651490312 / 1000000000000)))) (orderedInterval (4185000524 / 1000000000000) (4185000935 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2099245578773931 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28342050974 / 1000000000000) (-28342050973 / 1000000000000), orderedInterval (-20215844593 / 1000000000000) (-20215844592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3597093079723863 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26606089498 / 1000000000000) (26606094403 / 1000000000000), orderedInterval (191835830 / 1000000000000) (191840734 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2649602481901317 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9450713690 / 1000000000000) (-9450713689 / 1000000000000), orderedInterval (-29518514622 / 1000000000000) (-29518514621 / 1000000000000)))) (orderedInterval (-1051442367 / 1000000000000) (-1051442023 / 1000000000000))) = true
  rfl'

theorem compactCertificate583_chunkChecks1_1 :
    compactCertificate583.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4065171583094091 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17916619965 / 1000000000000) (-17916619217 / 1000000000000), orderedInterval (17484752624 / 1000000000000) (17484753372 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2347027907801139 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2117699356 / 1000000000000) (-2117699355 / 1000000000000), orderedInterval (-32869095314 / 1000000000000) (-32869095313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4164842208798351 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20978034356 / 1000000000000) (-20978027214 / 1000000000000), orderedInterval (13099947848 / 1000000000000) (13099954990 / 1000000000000)))) (orderedInterval (-5824899822 / 1000000000000) (-5824896825 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3891335840581419 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6934004359 / 1000000000000) (-6934004358 / 1000000000000), orderedInterval (24627064963 / 1000000000000) (24627064964 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2777040871142427 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20717641043 / 1000000000000) (-20717641042 / 1000000000000), orderedInterval (-22070257596 / 1000000000000) (-22070257595 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3148868368159533 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14557922949 / 1000000000000) (14557923063 / 1000000000000), orderedInterval (-24437990600 / 1000000000000) (-24437990486 / 1000000000000)))) (orderedInterval (-3925414692 / 1000000000000) (-3925414603 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2625198159341277 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14709381637 / 1000000000000) (-14709381636 / 1000000000000), orderedInterval (-27441449211 / 1000000000000) (-27441449210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2319442188050817 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17288127658 / 1000000000000) (17288128190 / 1000000000000), orderedInterval (-28281585423 / 1000000000000) (-28281584891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (672264750698883 / 800000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20322925523 / 1000000000000) (-20322922471 / 1000000000000), orderedInterval (18574443971 / 1000000000000) (18574447023 / 1000000000000)))) (orderedInterval (2486588010 / 1000000000000) (2486588256 / 1000000000000))) = true
  rfl'

theorem compactCertificate583_chunkChecks1_2 :
    compactCertificate583.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1859519679788601 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24102990176 / 1000000000000) (24102990177 / 1000000000000), orderedInterval (28053862474 / 1000000000000) (28053862475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1576335426173361 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-33193721507 / 1000000000000) (-33193620721 / 1000000000000), orderedInterval (22705293934 / 1000000000000) (22705394720 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (986397518098683 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36503156346 / 1000000000000) (36503200579 / 1000000000000), orderedInterval (-35416825862 / 1000000000000) (-35416781629 / 1000000000000)))) (orderedInterval (-6327926468 / 1000000000000) (-6327920634 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (530487865843461 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68855229277 / 1000000000000) (68855229284 / 1000000000000), orderedInterval (7433461149 / 1000000000000) (7433461157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1440377750353383 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (16515631606 / 1000000000000) (16515631952 / 1000000000000), orderedInterval (-38690225746 / 1000000000000) (-38690225400 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1966712676425991 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24964637223 / 1000000000000) (24964647131 / 1000000000000), orderedInterval (-25939794253 / 1000000000000) (-25939784344 / 1000000000000)))) (orderedInterval (2805999719 / 1000000000000) (2806000596 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (831602481901317 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53873032890 / 1000000000000) (53873032892 / 1000000000000), orderedInterval (12512565316 / 1000000000000) (12512565318 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3380417919739557 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19713780239 / 1000000000000) (-19713780238 / 1000000000000), orderedInterval (-19084668669 / 1000000000000) (-19084668668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2257962508082763 / 4000000000000) 1 (IntervalRat.scale (909 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7029282027 / 1000000000000) (-7029282023 / 1000000000000), orderedInterval (32844724943 / 1000000000000) (32844724948 / 1000000000000)))) (orderedInterval (-4730744569 / 1000000000000) (-4730744390 / 1000000000000))) = true
  rfl'

theorem compactCertificate583_chunkChecks1 :
    compactCertificate583.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate583.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate583_chunkChecks1_0
    compactCertificate583_chunkChecks1_1 compactCertificate583_chunkChecks1_2

theorem compactCertificate583_chunkChecks2_0 :
    compactCertificate583.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (909 / 2) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (9107370152 / 1000000000000) (9107370171 / 1000000000000), orderedInterval (-36310985009 / 1000000000000) (-36310984991 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1339130571642009 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23997876882 / 1000000000000) (23997880222 / 1000000000000), orderedInterval (-36445923445 / 1000000000000) (-36445920105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (433047312695097 / 800000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33802035676 / 1000000000000) (33802040371 / 1000000000000), orderedInterval (-5818802343 / 1000000000000) (-5818797647 / 1000000000000)))) (orderedInterval (-6511671131 / 1000000000000) (-6511670674 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (390754960965963 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-71329405331 / 1000000000000) (-71329405330 / 1000000000000), orderedInterval (-37435537410 / 1000000000000) (-37435537409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1049622789386511 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-31850175875 / 1000000000000) (-31850159314 / 1000000000000), orderedInterval (37632707860 / 1000000000000) (37632724420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2849930053895187 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-3762460592 / 1000000000000) (-3762460591 / 1000000000000), orderedInterval (-29651490313 / 1000000000000) (-29651490312 / 1000000000000)))) (orderedInterval (-314617114 / 1000000000000) (-314616826 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2099245578773931 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28342050974 / 1000000000000) (-28342050973 / 1000000000000), orderedInterval (-20215844593 / 1000000000000) (-20215844592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3597093079723863 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26606089498 / 1000000000000) (26606094403 / 1000000000000), orderedInterval (191835830 / 1000000000000) (191840734 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2649602481901317 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9450713690 / 1000000000000) (-9450713689 / 1000000000000), orderedInterval (-29518514622 / 1000000000000) (-29518514621 / 1000000000000)))) (orderedInterval (3700146340 / 1000000000000) (3700147012 / 1000000000000))) = true
  rfl'

theorem compactCertificate583_chunkChecks2_1 :
    compactCertificate583.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4065171583094091 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17916619965 / 1000000000000) (-17916619217 / 1000000000000), orderedInterval (17484752624 / 1000000000000) (17484753372 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2347027907801139 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2117699356 / 1000000000000) (-2117699355 / 1000000000000), orderedInterval (-32869095314 / 1000000000000) (-32869095313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4164842208798351 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20978034356 / 1000000000000) (-20978027214 / 1000000000000), orderedInterval (13099947848 / 1000000000000) (13099954990 / 1000000000000)))) (orderedInterval (7370665 / 1000000000000) (7377464 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3891335840581419 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6934004359 / 1000000000000) (-6934004358 / 1000000000000), orderedInterval (24627064963 / 1000000000000) (24627064964 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2777040871142427 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20717641043 / 1000000000000) (-20717641042 / 1000000000000), orderedInterval (-22070257596 / 1000000000000) (-22070257595 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3148868368159533 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14557922949 / 1000000000000) (14557923063 / 1000000000000), orderedInterval (-24437990600 / 1000000000000) (-24437990486 / 1000000000000)))) (orderedInterval (4227414400 / 1000000000000) (4227414548 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2625198159341277 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14709381637 / 1000000000000) (-14709381636 / 1000000000000), orderedInterval (-27441449211 / 1000000000000) (-27441449210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2319442188050817 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17288127658 / 1000000000000) (17288128190 / 1000000000000), orderedInterval (-28281585423 / 1000000000000) (-28281584891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (672264750698883 / 800000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20322925523 / 1000000000000) (-20322922471 / 1000000000000), orderedInterval (18574443971 / 1000000000000) (18574447023 / 1000000000000)))) (orderedInterval (3737876140 / 1000000000000) (3737876552 / 1000000000000))) = true
  rfl'

theorem compactCertificate583_chunkChecks2_2 :
    compactCertificate583.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1859519679788601 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24102990176 / 1000000000000) (24102990177 / 1000000000000), orderedInterval (28053862474 / 1000000000000) (28053862475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1576335426173361 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-33193721507 / 1000000000000) (-33193620721 / 1000000000000), orderedInterval (22705293934 / 1000000000000) (22705394720 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (986397518098683 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36503156346 / 1000000000000) (36503200579 / 1000000000000), orderedInterval (-35416825862 / 1000000000000) (-35416781629 / 1000000000000)))) (orderedInterval (2283533031 / 1000000000000) (2283537857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (530487865843461 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68855229277 / 1000000000000) (68855229284 / 1000000000000), orderedInterval (7433461149 / 1000000000000) (7433461157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1440377750353383 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (16515631606 / 1000000000000) (16515631952 / 1000000000000), orderedInterval (-38690225746 / 1000000000000) (-38690225400 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1966712676425991 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24964637223 / 1000000000000) (24964647131 / 1000000000000), orderedInterval (-25939794253 / 1000000000000) (-25939784344 / 1000000000000)))) (orderedInterval (2576354667 / 1000000000000) (2576355612 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (831602481901317 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53873032890 / 1000000000000) (53873032892 / 1000000000000), orderedInterval (12512565316 / 1000000000000) (12512565318 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3380417919739557 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19713780239 / 1000000000000) (-19713780238 / 1000000000000), orderedInterval (-19084668669 / 1000000000000) (-19084668668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2257962508082763 / 4000000000000) 2 (IntervalRat.scale (909 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7029282027 / 1000000000000) (-7029282023 / 1000000000000), orderedInterval (32844724943 / 1000000000000) (32844724948 / 1000000000000)))) (orderedInterval (-7640273496 / 1000000000000) (-7640273234 / 1000000000000))) = true
  rfl'

theorem compactCertificate583_chunkChecks2 :
    compactCertificate583.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate583.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate583_chunkChecks2_0
    compactCertificate583_chunkChecks2_1 compactCertificate583_chunkChecks2_2

theorem compactCertificate583_chunkChecks3_0 :
    compactCertificate583.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (909 / 2) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (9107370152 / 1000000000000) (9107370171 / 1000000000000), orderedInterval (-36310985009 / 1000000000000) (-36310984991 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1339130571642009 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23997876882 / 1000000000000) (23997880222 / 1000000000000), orderedInterval (-36445923445 / 1000000000000) (-36445920105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (433047312695097 / 800000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33802035676 / 1000000000000) (33802040371 / 1000000000000), orderedInterval (-5818802343 / 1000000000000) (-5818797647 / 1000000000000)))) (orderedInterval (15119237487 / 1000000000000) (15119238021 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (390754960965963 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-71329405331 / 1000000000000) (-71329405330 / 1000000000000), orderedInterval (-37435537410 / 1000000000000) (-37435537409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1049622789386511 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-31850175875 / 1000000000000) (-31850159314 / 1000000000000), orderedInterval (37632707860 / 1000000000000) (37632724420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2849930053895187 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-3762460592 / 1000000000000) (-3762460591 / 1000000000000), orderedInterval (-29651490313 / 1000000000000) (-29651490312 / 1000000000000)))) (orderedInterval (-8388086455 / 1000000000000) (-8388086209 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2099245578773931 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28342050974 / 1000000000000) (-28342050973 / 1000000000000), orderedInterval (-20215844593 / 1000000000000) (-20215844592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3597093079723863 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26606089498 / 1000000000000) (26606094403 / 1000000000000), orderedInterval (191835830 / 1000000000000) (191840734 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2649602481901317 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9450713690 / 1000000000000) (-9450713689 / 1000000000000), orderedInterval (-29518514622 / 1000000000000) (-29518514621 / 1000000000000)))) (orderedInterval (2246180244 / 1000000000000) (2246181560 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate583_chunkChecks3_1 :
    compactCertificate583.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4065171583094091 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17916619965 / 1000000000000) (-17916619217 / 1000000000000), orderedInterval (17484752624 / 1000000000000) (17484753372 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2347027907801139 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2117699356 / 1000000000000) (-2117699355 / 1000000000000), orderedInterval (-32869095314 / 1000000000000) (-32869095313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4164842208798351 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20978034356 / 1000000000000) (-20978027214 / 1000000000000), orderedInterval (13099947848 / 1000000000000) (13099954990 / 1000000000000)))) (orderedInterval (17585637113 / 1000000000000) (17585652573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3891335840581419 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6934004359 / 1000000000000) (-6934004358 / 1000000000000), orderedInterval (24627064963 / 1000000000000) (24627064964 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2777040871142427 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20717641043 / 1000000000000) (-20717641042 / 1000000000000), orderedInterval (-22070257596 / 1000000000000) (-22070257595 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3148868368159533 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14557922949 / 1000000000000) (14557923063 / 1000000000000), orderedInterval (-24437990600 / 1000000000000) (-24437990486 / 1000000000000)))) (orderedInterval (11146625048 / 1000000000000) (11146625298 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2625198159341277 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14709381637 / 1000000000000) (-14709381636 / 1000000000000), orderedInterval (-27441449211 / 1000000000000) (-27441449210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2319442188050817 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17288127658 / 1000000000000) (17288128190 / 1000000000000), orderedInterval (-28281585423 / 1000000000000) (-28281584891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (672264750698883 / 800000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20322925523 / 1000000000000) (-20322922471 / 1000000000000), orderedInterval (18574443971 / 1000000000000) (18574447023 / 1000000000000)))) (orderedInterval (-5420991374 / 1000000000000) (-5420990672 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate583_chunkChecks3_2 :
    compactCertificate583.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1859519679788601 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24102990176 / 1000000000000) (24102990177 / 1000000000000), orderedInterval (28053862474 / 1000000000000) (28053862475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1576335426173361 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-33193721507 / 1000000000000) (-33193620721 / 1000000000000), orderedInterval (22705293934 / 1000000000000) (22705394720 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (986397518098683 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36503156346 / 1000000000000) (36503200579 / 1000000000000), orderedInterval (-35416825862 / 1000000000000) (-35416781629 / 1000000000000)))) (orderedInterval (5816846300 / 1000000000000) (5816850357 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (530487865843461 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68855229277 / 1000000000000) (68855229284 / 1000000000000), orderedInterval (7433461149 / 1000000000000) (7433461157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1440377750353383 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (16515631606 / 1000000000000) (16515631952 / 1000000000000), orderedInterval (-38690225746 / 1000000000000) (-38690225400 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1966712676425991 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24964637223 / 1000000000000) (24964647131 / 1000000000000), orderedInterval (-25939794253 / 1000000000000) (-25939784344 / 1000000000000)))) (orderedInterval (-2955630477 / 1000000000000) (-2955629460 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (831602481901317 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53873032890 / 1000000000000) (53873032892 / 1000000000000), orderedInterval (12512565316 / 1000000000000) (12512565318 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3380417919739557 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19713780239 / 1000000000000) (-19713780238 / 1000000000000), orderedInterval (-19084668669 / 1000000000000) (-19084668668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2257962508082763 / 4000000000000) 3 (IntervalRat.scale (909 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7029282027 / 1000000000000) (-7029282023 / 1000000000000), orderedInterval (32844724943 / 1000000000000) (32844724948 / 1000000000000)))) (orderedInterval (1828965317 / 1000000000000) (1828965722 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate583_chunkChecks3 :
    compactCertificate583.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate583.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate583_chunkChecks3_0
    compactCertificate583_chunkChecks3_1 compactCertificate583_chunkChecks3_2

theorem compactCertificate583_chunkChecks4_0 :
    compactCertificate583.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (909 / 2) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (9107370152 / 1000000000000) (9107370171 / 1000000000000), orderedInterval (-36310985009 / 1000000000000) (-36310984991 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1339130571642009 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23997876882 / 1000000000000) (23997880222 / 1000000000000), orderedInterval (-36445923445 / 1000000000000) (-36445920105 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (433047312695097 / 800000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33802035676 / 1000000000000) (33802040371 / 1000000000000), orderedInterval (-5818802343 / 1000000000000) (-5818797647 / 1000000000000)))) (orderedInterval (7600159728 / 1000000000000) (7600160357 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (390754960965963 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-71329405331 / 1000000000000) (-71329405330 / 1000000000000), orderedInterval (-37435537410 / 1000000000000) (-37435537409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1049622789386511 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-31850175875 / 1000000000000) (-31850159314 / 1000000000000), orderedInterval (37632707860 / 1000000000000) (37632724420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2849930053895187 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-3762460592 / 1000000000000) (-3762460591 / 1000000000000), orderedInterval (-29651490313 / 1000000000000) (-29651490312 / 1000000000000)))) (orderedInterval (1524598839 / 1000000000000) (1524599105 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2099245578773931 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28342050974 / 1000000000000) (-28342050973 / 1000000000000), orderedInterval (-20215844593 / 1000000000000) (-20215844592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3597093079723863 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26606089498 / 1000000000000) (26606094403 / 1000000000000), orderedInterval (191835830 / 1000000000000) (191840734 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2649602481901317 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9450713690 / 1000000000000) (-9450713689 / 1000000000000), orderedInterval (-29518514622 / 1000000000000) (-29518514621 / 1000000000000)))) (orderedInterval (-13617551389 / 1000000000000) (-13617548799 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate583_chunkChecks4_1 :
    compactCertificate583.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4065171583094091 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17916619965 / 1000000000000) (-17916619217 / 1000000000000), orderedInterval (17484752624 / 1000000000000) (17484753372 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2347027907801139 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2117699356 / 1000000000000) (-2117699355 / 1000000000000), orderedInterval (-32869095314 / 1000000000000) (-32869095313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4164842208798351 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20978034356 / 1000000000000) (-20978027214 / 1000000000000), orderedInterval (13099947848 / 1000000000000) (13099954990 / 1000000000000)))) (orderedInterval (-3062857758 / 1000000000000) (-3062822517 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3891335840581419 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6934004359 / 1000000000000) (-6934004358 / 1000000000000), orderedInterval (24627064963 / 1000000000000) (24627064964 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2777040871142427 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20717641043 / 1000000000000) (-20717641042 / 1000000000000), orderedInterval (-22070257596 / 1000000000000) (-22070257595 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3148868368159533 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14557922949 / 1000000000000) (14557923063 / 1000000000000), orderedInterval (-24437990600 / 1000000000000) (-24437990486 / 1000000000000)))) (orderedInterval (-8750816726 / 1000000000000) (-8750816292 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2625198159341277 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-14709381637 / 1000000000000) (-14709381636 / 1000000000000), orderedInterval (-27441449211 / 1000000000000) (-27441449210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2319442188050817 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17288127658 / 1000000000000) (17288128190 / 1000000000000), orderedInterval (-28281585423 / 1000000000000) (-28281584891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (672264750698883 / 800000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20322925523 / 1000000000000) (-20322922471 / 1000000000000), orderedInterval (18574443971 / 1000000000000) (18574447023 / 1000000000000)))) (orderedInterval (-9416653370 / 1000000000000) (-9416652145 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate583_chunkChecks4_2 :
    compactCertificate583.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1859519679788601 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24102990176 / 1000000000000) (24102990177 / 1000000000000), orderedInterval (28053862474 / 1000000000000) (28053862475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1576335426173361 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-33193721507 / 1000000000000) (-33193620721 / 1000000000000), orderedInterval (22705293934 / 1000000000000) (22705394720 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (986397518098683 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36503156346 / 1000000000000) (36503200579 / 1000000000000), orderedInterval (-35416825862 / 1000000000000) (-35416781629 / 1000000000000)))) (orderedInterval (-3078876367 / 1000000000000) (-3078872904 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (530487865843461 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68855229277 / 1000000000000) (68855229284 / 1000000000000), orderedInterval (7433461149 / 1000000000000) (7433461157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1440377750353383 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (16515631606 / 1000000000000) (16515631952 / 1000000000000), orderedInterval (-38690225746 / 1000000000000) (-38690225400 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1966712676425991 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24964637223 / 1000000000000) (24964647131 / 1000000000000), orderedInterval (-25939794253 / 1000000000000) (-25939784344 / 1000000000000)))) (orderedInterval (-2764207947 / 1000000000000) (-2764206847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (831602481901317 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53873032890 / 1000000000000) (53873032892 / 1000000000000), orderedInterval (12512565316 / 1000000000000) (12512565318 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3380417919739557 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-19713780239 / 1000000000000) (-19713780238 / 1000000000000), orderedInterval (-19084668669 / 1000000000000) (-19084668668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2257962508082763 / 4000000000000) 4 (IntervalRat.scale (909 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7029282027 / 1000000000000) (-7029282023 / 1000000000000), orderedInterval (32844724943 / 1000000000000) (32844724948 / 1000000000000)))) (orderedInterval (22327154146 / 1000000000000) (22327154795 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate583_chunkChecks4 :
    compactCertificate583.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate583.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate583_chunkChecks4_0
    compactCertificate583_chunkChecks4_1 compactCertificate583_chunkChecks4_2

theorem compactCertificate583_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate583.chunkCheck r b = true :=
  compactCertificate583.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate583_chunkChecks0
    · exact compactCertificate583_chunkChecks1
    · exact compactCertificate583_chunkChecks2
    · exact compactCertificate583_chunkChecks3
    · exact compactCertificate583_chunkChecks4)

theorem compactCertificate583_coefficient0 :
    compactCertificate583.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate583_coefficient1 :
    compactCertificate583.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate583_coefficient2 :
    compactCertificate583.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate583_coefficient3 :
    compactCertificate583.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate583_coefficient4 :
    compactCertificate583.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate583_coefficients : ∀ r : Fin 5,
    compactCertificate583.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate583_coefficient0
  · exact compactCertificate583_coefficient1
  · exact compactCertificate583_coefficient2
  · exact compactCertificate583_coefficient3
  · exact compactCertificate583_coefficient4

theorem compactCertificate583_lower : (1 : ℚ) ≤ compactCertificate583.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate583, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate583_proves {t : ℝ} (ht : t ∈ compactCertificate583.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate583.proves compactCertificate583_states compactCertificate583_chunks
    compactCertificate583_coefficients compactCertificate583_lower ht

end Erdos232
