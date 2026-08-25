/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate543 : CompactCertificate where
  left := 414
  right := 415
  center := 829 / 2
  grid := fun i =>
    match i.val with
    | 0 => 132
    | 1 => 97
    | 2 => 157
    | 3 => 28
    | 4 => 76
    | 5 => 207
    | 6 => 152
    | 7 => 261
    | 8 => 192
    | 9 => 295
    | 10 => 170
    | 11 => 302
    | 12 => 283
    | 13 => 202
    | 14 => 229
    | 15 => 191
    | 16 => 168
    | 17 => 244
    | 18 => 135
    | 19 => 114
    | 20 => 72
    | 21 => 39
    | 22 => 105
    | 23 => 143
    | 24 => 60
    | 25 => 245
    | _ => 164
  point := fun i =>
    match i.val with
    | 0 => 829 / 2
    | 1 => 1221275295809929 / 4000000000000
    | 2 => 394935337980457 / 800000000000
    | 3 => 356365085413403 / 4000000000000
    | 4 => 957246746316191 / 4000000000000
    | 5 => 2599111127259747 / 4000000000000
    | 6 => 1914493492633211 / 4000000000000
    | 7 => 3280517231123303 / 4000000000000
    | 8 => 2416414144660277 / 4000000000000
    | 9 => 3707400706694171 / 4000000000000
    | 10 => 2140468796003459 / 4000000000000
    | 11 => 3798299440147231 / 4000000000000
    | 12 => 3548864039430139 / 4000000000000
    | 13 => 2532636834078187 / 4000000000000
    | 14 => 2871740238948573 / 4000000000000
    | 15 => 2394157617265037 / 4000000000000
    | 16 => 2115310862369777 / 4000000000000
    | 17 => 613099536115923 / 800000000000
    | 18 => 1695865582557481 / 4000000000000
    | 19 => 1437604035531041 / 4000000000000
    | 20 => 899585855339723 / 4000000000000
    | 21 => 483800264889141 / 4000000000000
    | 22 => 1313611831730423 / 4000000000000
    | 23 => 1793624652098071 / 4000000000000
    | 24 => 758414144660277 / 4000000000000
    | 25 => 3082911392149717 / 4000000000000
    | _ => 2059241935314203 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (21962119344 / 1000000000000) (21962119345 / 1000000000000), orderedInterval (32431784460 / 1000000000000) (32431784461 / 1000000000000))
    | 1 => (orderedInterval (-44739236438 / 1000000000000) (-44739236431 / 1000000000000), orderedInterval (-9064375115 / 1000000000000) (-9064375108 / 1000000000000))
    | 2 => (orderedInterval (-33775962146 / 1000000000000) (-33775962143 / 1000000000000), orderedInterval (-12162162411 / 1000000000000) (-12162162408 / 1000000000000))
    | 3 => (orderedInterval (79696051416 / 1000000000000) (79696053925 / 1000000000000), orderedInterval (-28628010600 / 1000000000000) (-28628008092 / 1000000000000))
    | 4 => (orderedInterval (50156240418 / 1000000000000) (50156240421 / 1000000000000), orderedInterval (11918442387 / 1000000000000) (11918442390 / 1000000000000))
    | 5 => (orderedInterval (-7844271384 / 1000000000000) (-7844271383 / 1000000000000), orderedInterval (-30296070177 / 1000000000000) (-30296070176 / 1000000000000))
    | 6 => (orderedInterval (34668982536 / 1000000000000) (34668997441 / 1000000000000), orderedInterval (-11357286086 / 1000000000000) (-11357271181 / 1000000000000))
    | 7 => (orderedInterval (-22805553868 / 1000000000000) (-22805553866 / 1000000000000), orderedInterval (-15990777943 / 1000000000000) (-15990777942 / 1000000000000))
    | 8 => (orderedInterval (32179662585 / 1000000000000) (32179667010 / 1000000000000), orderedInterval (-4303834386 / 1000000000000) (-4303829962 / 1000000000000))
    | 9 => (orderedInterval (-19957165965 / 1000000000000) (-19957165963 / 1000000000000), orderedInterval (-16976736458 / 1000000000000) (-16976736457 / 1000000000000))
    | 10 => (orderedInterval (33325249363 / 1000000000000) (33325260905 / 1000000000000), orderedInterval (-8925512507 / 1000000000000) (-8925500965 / 1000000000000))
    | 11 => (orderedInterval (25882177577 / 1000000000000) (25882186818 / 1000000000000), orderedInterval (-747559734 / 1000000000000) (-747550493 / 1000000000000))
    | 12 => (orderedInterval (23490596942 / 1000000000000) (23490623397 / 1000000000000), orderedInterval (-12887210397 / 1000000000000) (-12887183942 / 1000000000000))
    | 13 => (orderedInterval (-19373831237 / 1000000000000) (-19373829822 / 1000000000000), orderedInterval (25117496125 / 1000000000000) (25117497541 / 1000000000000))
    | 14 => (orderedInterval (19284392836 / 1000000000000) (19284394321 / 1000000000000), orderedInterval (-22703725690 / 1000000000000) (-22703724205 / 1000000000000))
    | 15 => (orderedInterval (21494921410 / 1000000000000) (21494924870 / 1000000000000), orderedInterval (-24545299379 / 1000000000000) (-24545295919 / 1000000000000))
    | 16 => (orderedInterval (33578545644 / 1000000000000) (33578556150 / 1000000000000), orderedInterval (-8767457347 / 1000000000000) (-8767446840 / 1000000000000))
    | 17 => (orderedInterval (16535753156 / 1000000000000) (16535753157 / 1000000000000), orderedInterval (23595549749 / 1000000000000) (23595549750 / 1000000000000))
    | 18 => (orderedInterval (-23032240709 / 1000000000000) (-23032240708 / 1000000000000), orderedInterval (-31135265408 / 1000000000000) (-31135265407 / 1000000000000))
    | 19 => (orderedInterval (37452819309 / 1000000000000) (37452856413 / 1000000000000), orderedInterval (-19251586259 / 1000000000000) (-19251549154 / 1000000000000))
    | 20 => (orderedInterval (-26129315019 / 1000000000000) (-26129312146 / 1000000000000), orderedInterval (46404464161 / 1000000000000) (46404467033 / 1000000000000))
    | 21 => (orderedInterval (51417349288 / 1000000000000) (51417417398 / 1000000000000), orderedInterval (-51396028154 / 1000000000000) (-51395960045 / 1000000000000))
    | 22 => (orderedInterval (27659384880 / 1000000000000) (27659394325 / 1000000000000), orderedInterval (-34298371751 / 1000000000000) (-34298362307 / 1000000000000))
    | 23 => (orderedInterval (2126514475 / 1000000000000) (2126514477 / 1000000000000), orderedInterval (-37621753635 / 1000000000000) (-37621753634 / 1000000000000))
    | 24 => (orderedInterval (54968370421 / 1000000000000) (54968373993 / 1000000000000), orderedInterval (-18478131941 / 1000000000000) (-18478128369 / 1000000000000))
    | 25 => (orderedInterval (-27831829740 / 1000000000000) (-27831796807 / 1000000000000), orderedInterval (7186590939 / 1000000000000) (7186623871 / 1000000000000))
    | _ => (orderedInterval (12861945529 / 1000000000000) (12861945530 / 1000000000000), orderedInterval (32716405801 / 1000000000000) (32716405802 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (6306120413 / 1000000000000) (6306120442 / 1000000000000)
      | 1 => orderedInterval (1524292641 / 1000000000000) (1524292719 / 1000000000000)
      | 2 => orderedInterval (1481133469 / 1000000000000) (1481133599 / 1000000000000)
      | 3 => orderedInterval (9694578131 / 1000000000000) (9694580465 / 1000000000000)
      | 4 => orderedInterval (-2353713420 / 1000000000000) (-2353712751 / 1000000000000)
      | 5 => orderedInterval (-1249992351 / 1000000000000) (-1249991670 / 1000000000000)
      | 6 => orderedInterval (712204203 / 1000000000000) (712206501 / 1000000000000)
      | 7 => orderedInterval (-1739907182 / 1000000000000) (-1739905660 / 1000000000000)
      | _ => orderedInterval (183682856 / 1000000000000) (183685673 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (11942605693 / 1000000000000) (11942605726 / 1000000000000)
      | 1 => orderedInterval (3694236625 / 1000000000000) (3694236688 / 1000000000000)
      | 2 => orderedInterval (824289205 / 1000000000000) (824289401 / 1000000000000)
      | 3 => orderedInterval (5648038612 / 1000000000000) (5648043067 / 1000000000000)
      | 4 => orderedInterval (4325135913 / 1000000000000) (4325137233 / 1000000000000)
      | 5 => orderedInterval (1347831037 / 1000000000000) (1347831920 / 1000000000000)
      | 6 => orderedInterval (6856451328 / 1000000000000) (6856453296 / 1000000000000)
      | 7 => orderedInterval (4012563515 / 1000000000000) (4012564097 / 1000000000000)
      | _ => orderedInterval (-8762715750 / 1000000000000) (-8762710593 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-5696195440 / 1000000000000) (-5696195401 / 1000000000000)
      | 1 => orderedInterval (-1949773937 / 1000000000000) (-1949773857 / 1000000000000)
      | 2 => orderedInterval (-4407702211 / 1000000000000) (-4407701911 / 1000000000000)
      | 3 => orderedInterval (-41169260883 / 1000000000000) (-41169251822 / 1000000000000)
      | 4 => orderedInterval (6500028266 / 1000000000000) (6500030925 / 1000000000000)
      | 5 => orderedInterval (1159668982 / 1000000000000) (1159670132 / 1000000000000)
      | 6 => orderedInterval (-2025223522 / 1000000000000) (-2025221818 / 1000000000000)
      | 7 => orderedInterval (655782318 / 1000000000000) (655782606 / 1000000000000)
      | _ => orderedInterval (-4158602830 / 1000000000000) (-4158593306 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-11601543747 / 1000000000000) (-11601543702 / 1000000000000)
      | 1 => orderedInterval (-8378962537 / 1000000000000) (-8378962419 / 1000000000000)
      | 2 => orderedInterval (-3487803491 / 1000000000000) (-3487803028 / 1000000000000)
      | 3 => orderedInterval (-30926247089 / 1000000000000) (-30926227834 / 1000000000000)
      | 4 => orderedInterval (-11359872377 / 1000000000000) (-11359866946 / 1000000000000)
      | 5 => orderedInterval (-4009741988 / 1000000000000) (-4009740484 / 1000000000000)
      | 6 => orderedInterval (-6273908470 / 1000000000000) (-6273906992 / 1000000000000)
      | 7 => orderedInterval (-4062429800 / 1000000000000) (-4062429616 / 1000000000000)
      | _ => orderedInterval (15542066117 / 1000000000000) (15542083743 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (4650263626 / 1000000000000) (4650263678 / 1000000000000)
      | 1 => orderedInterval (3609647109 / 1000000000000) (3609647290 / 1000000000000)
      | 2 => orderedInterval (14306285402 / 1000000000000) (14306286129 / 1000000000000)
      | 3 => orderedInterval (197002161328 / 1000000000000) (197002203531 / 1000000000000)
      | 4 => orderedInterval (-19699472405 / 1000000000000) (-19699461169 / 1000000000000)
      | 5 => orderedInterval (954993018 / 1000000000000) (954995000 / 1000000000000)
      | 6 => orderedInterval (2789170793 / 1000000000000) (2789172083 / 1000000000000)
      | 7 => orderedInterval (-457739907 / 1000000000000) (-457739764 / 1000000000000)
      | _ => orderedInterval (21279135296 / 1000000000000) (21279168016 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (14558398760 / 1000000000000) (14558409318 / 1000000000000)
    | 1 => orderedInterval (29888436178 / 1000000000000) (29888450835 / 1000000000000)
    | 2 => orderedInterval (-51091279257 / 1000000000000) (-51091254452 / 1000000000000)
    | 3 => orderedInterval (-64558443382 / 1000000000000) (-64558397278 / 1000000000000)
    | _ => orderedInterval (224434444260 / 1000000000000) (224434534794 / 1000000000000)

theorem compactCertificate543_stateChecks0 :
    compactCertificate543.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (829 / 2)) (orderedInterval (21962119344 / 1000000000000) (21962119345 / 1000000000000), orderedInterval (32431784460 / 1000000000000) (32431784461 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1221275295809929 / 4000000000000)) (orderedInterval (-44739236438 / 1000000000000) (-44739236431 / 1000000000000), orderedInterval (-9064375115 / 1000000000000) (-9064375108 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (394935337980457 / 800000000000)) (orderedInterval (-33775962146 / 1000000000000) (-33775962143 / 1000000000000), orderedInterval (-12162162411 / 1000000000000) (-12162162408 / 1000000000000))) = true
  rfl'

theorem compactCertificate543_stateChecks1 :
    compactCertificate543.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (356365085413403 / 4000000000000)) (orderedInterval (79696051416 / 1000000000000) (79696053925 / 1000000000000), orderedInterval (-28628010600 / 1000000000000) (-28628008092 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (957246746316191 / 4000000000000)) (orderedInterval (50156240418 / 1000000000000) (50156240421 / 1000000000000), orderedInterval (11918442387 / 1000000000000) (11918442390 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 207 12 (2599111127259747 / 4000000000000)) (orderedInterval (-7844271384 / 1000000000000) (-7844271383 / 1000000000000), orderedInterval (-30296070177 / 1000000000000) (-30296070176 / 1000000000000))) = true
  rfl'

theorem compactCertificate543_stateChecks2 :
    compactCertificate543.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1914493492633211 / 4000000000000)) (orderedInterval (34668982536 / 1000000000000) (34668997441 / 1000000000000), orderedInterval (-11357286086 / 1000000000000) (-11357271181 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 261 12 (3280517231123303 / 4000000000000)) (orderedInterval (-22805553868 / 1000000000000) (-22805553866 / 1000000000000), orderedInterval (-15990777943 / 1000000000000) (-15990777942 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2416414144660277 / 4000000000000)) (orderedInterval (32179662585 / 1000000000000) (32179667010 / 1000000000000), orderedInterval (-4303834386 / 1000000000000) (-4303829962 / 1000000000000))) = true
  rfl'

theorem compactCertificate543_stateChecks3 :
    compactCertificate543.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 295 12 (3707400706694171 / 4000000000000)) (orderedInterval (-19957165965 / 1000000000000) (-19957165963 / 1000000000000), orderedInterval (-16976736458 / 1000000000000) (-16976736457 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2140468796003459 / 4000000000000)) (orderedInterval (33325249363 / 1000000000000) (33325260905 / 1000000000000), orderedInterval (-8925512507 / 1000000000000) (-8925500965 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 302 12 (3798299440147231 / 4000000000000)) (orderedInterval (25882177577 / 1000000000000) (25882186818 / 1000000000000), orderedInterval (-747559734 / 1000000000000) (-747550493 / 1000000000000))) = true
  rfl'

theorem compactCertificate543_stateChecks4 :
    compactCertificate543.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 283 12 (3548864039430139 / 4000000000000)) (orderedInterval (23490596942 / 1000000000000) (23490623397 / 1000000000000), orderedInterval (-12887210397 / 1000000000000) (-12887183942 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (2532636834078187 / 4000000000000)) (orderedInterval (-19373831237 / 1000000000000) (-19373829822 / 1000000000000), orderedInterval (25117496125 / 1000000000000) (25117497541 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (2871740238948573 / 4000000000000)) (orderedInterval (19284392836 / 1000000000000) (19284394321 / 1000000000000), orderedInterval (-22703725690 / 1000000000000) (-22703724205 / 1000000000000))) = true
  rfl'

theorem compactCertificate543_stateChecks5 :
    compactCertificate543.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (2394157617265037 / 4000000000000)) (orderedInterval (21494921410 / 1000000000000) (21494924870 / 1000000000000), orderedInterval (-24545299379 / 1000000000000) (-24545295919 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2115310862369777 / 4000000000000)) (orderedInterval (33578545644 / 1000000000000) (33578556150 / 1000000000000), orderedInterval (-8767457347 / 1000000000000) (-8767446840 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 244 12 (613099536115923 / 800000000000)) (orderedInterval (16535753156 / 1000000000000) (16535753157 / 1000000000000), orderedInterval (23595549749 / 1000000000000) (23595549750 / 1000000000000))) = true
  rfl'

theorem compactCertificate543_stateChecks6 :
    compactCertificate543.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1695865582557481 / 4000000000000)) (orderedInterval (-23032240709 / 1000000000000) (-23032240708 / 1000000000000), orderedInterval (-31135265408 / 1000000000000) (-31135265407 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1437604035531041 / 4000000000000)) (orderedInterval (37452819309 / 1000000000000) (37452856413 / 1000000000000), orderedInterval (-19251586259 / 1000000000000) (-19251549154 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (899585855339723 / 4000000000000)) (orderedInterval (-26129315019 / 1000000000000) (-26129312146 / 1000000000000), orderedInterval (46404464161 / 1000000000000) (46404467033 / 1000000000000))) = true
  rfl'

theorem compactCertificate543_stateChecks7 :
    compactCertificate543.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (483800264889141 / 4000000000000)) (orderedInterval (51417349288 / 1000000000000) (51417417398 / 1000000000000), orderedInterval (-51396028154 / 1000000000000) (-51395960045 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1313611831730423 / 4000000000000)) (orderedInterval (27659384880 / 1000000000000) (27659394325 / 1000000000000), orderedInterval (-34298371751 / 1000000000000) (-34298362307 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1793624652098071 / 4000000000000)) (orderedInterval (2126514475 / 1000000000000) (2126514477 / 1000000000000), orderedInterval (-37621753635 / 1000000000000) (-37621753634 / 1000000000000))) = true
  rfl'

theorem compactCertificate543_stateChecks8 :
    compactCertificate543.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (758414144660277 / 4000000000000)) (orderedInterval (54968370421 / 1000000000000) (54968373993 / 1000000000000), orderedInterval (-18478131941 / 1000000000000) (-18478128369 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 245 12 (3082911392149717 / 4000000000000)) (orderedInterval (-27831829740 / 1000000000000) (-27831796807 / 1000000000000), orderedInterval (7186590939 / 1000000000000) (7186623871 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2059241935314203 / 4000000000000)) (orderedInterval (12861945529 / 1000000000000) (12861945530 / 1000000000000), orderedInterval (32716405801 / 1000000000000) (32716405802 / 1000000000000))) = true
  rfl'

theorem compactCertificate543_states : ∀ j,
    BesselStateValid (compactCertificate543.point j) (compactCertificate543.state j) :=
  compactCertificate543.statesValid_of_checks3 compactCertificate543_stateChecks0
    compactCertificate543_stateChecks1 compactCertificate543_stateChecks2
    compactCertificate543_stateChecks3 compactCertificate543_stateChecks4
    compactCertificate543_stateChecks5 compactCertificate543_stateChecks6
    compactCertificate543_stateChecks7 compactCertificate543_stateChecks8

theorem compactCertificate543_chunkChecks0_0 :
    compactCertificate543.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (829 / 2) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (21962119344 / 1000000000000) (21962119345 / 1000000000000), orderedInterval (32431784460 / 1000000000000) (32431784461 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1221275295809929 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44739236438 / 1000000000000) (-44739236431 / 1000000000000), orderedInterval (-9064375115 / 1000000000000) (-9064375108 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (394935337980457 / 800000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33775962146 / 1000000000000) (-33775962143 / 1000000000000), orderedInterval (-12162162411 / 1000000000000) (-12162162408 / 1000000000000)))) (orderedInterval (6306120413 / 1000000000000) (6306120442 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (356365085413403 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79696051416 / 1000000000000) (79696053925 / 1000000000000), orderedInterval (-28628010600 / 1000000000000) (-28628008092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (957246746316191 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50156240418 / 1000000000000) (50156240421 / 1000000000000), orderedInterval (11918442387 / 1000000000000) (11918442390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2599111127259747 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-7844271384 / 1000000000000) (-7844271383 / 1000000000000), orderedInterval (-30296070177 / 1000000000000) (-30296070176 / 1000000000000)))) (orderedInterval (1524292641 / 1000000000000) (1524292719 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1914493492633211 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34668982536 / 1000000000000) (34668997441 / 1000000000000), orderedInterval (-11357286086 / 1000000000000) (-11357271181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3280517231123303 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22805553868 / 1000000000000) (-22805553866 / 1000000000000), orderedInterval (-15990777943 / 1000000000000) (-15990777942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2416414144660277 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32179662585 / 1000000000000) (32179667010 / 1000000000000), orderedInterval (-4303834386 / 1000000000000) (-4303829962 / 1000000000000)))) (orderedInterval (1481133469 / 1000000000000) (1481133599 / 1000000000000))) = true
  rfl'

theorem compactCertificate543_chunkChecks0_1 :
    compactCertificate543.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3707400706694171 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19957165965 / 1000000000000) (-19957165963 / 1000000000000), orderedInterval (-16976736458 / 1000000000000) (-16976736457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2140468796003459 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33325249363 / 1000000000000) (33325260905 / 1000000000000), orderedInterval (-8925512507 / 1000000000000) (-8925500965 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3798299440147231 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25882177577 / 1000000000000) (25882186818 / 1000000000000), orderedInterval (-747559734 / 1000000000000) (-747550493 / 1000000000000)))) (orderedInterval (9694578131 / 1000000000000) (9694580465 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3548864039430139 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23490596942 / 1000000000000) (23490623397 / 1000000000000), orderedInterval (-12887210397 / 1000000000000) (-12887183942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2532636834078187 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19373831237 / 1000000000000) (-19373829822 / 1000000000000), orderedInterval (25117496125 / 1000000000000) (25117497541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2871740238948573 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19284392836 / 1000000000000) (19284394321 / 1000000000000), orderedInterval (-22703725690 / 1000000000000) (-22703724205 / 1000000000000)))) (orderedInterval (-2353713420 / 1000000000000) (-2353712751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2394157617265037 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21494921410 / 1000000000000) (21494924870 / 1000000000000), orderedInterval (-24545299379 / 1000000000000) (-24545295919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2115310862369777 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33578545644 / 1000000000000) (33578556150 / 1000000000000), orderedInterval (-8767457347 / 1000000000000) (-8767446840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (613099536115923 / 800000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16535753156 / 1000000000000) (16535753157 / 1000000000000), orderedInterval (23595549749 / 1000000000000) (23595549750 / 1000000000000)))) (orderedInterval (-1249992351 / 1000000000000) (-1249991670 / 1000000000000))) = true
  rfl'

theorem compactCertificate543_chunkChecks0_2 :
    compactCertificate543.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1695865582557481 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23032240709 / 1000000000000) (-23032240708 / 1000000000000), orderedInterval (-31135265408 / 1000000000000) (-31135265407 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1437604035531041 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37452819309 / 1000000000000) (37452856413 / 1000000000000), orderedInterval (-19251586259 / 1000000000000) (-19251549154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (899585855339723 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-26129315019 / 1000000000000) (-26129312146 / 1000000000000), orderedInterval (46404464161 / 1000000000000) (46404467033 / 1000000000000)))) (orderedInterval (712204203 / 1000000000000) (712206501 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (483800264889141 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (51417349288 / 1000000000000) (51417417398 / 1000000000000), orderedInterval (-51396028154 / 1000000000000) (-51395960045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1313611831730423 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27659384880 / 1000000000000) (27659394325 / 1000000000000), orderedInterval (-34298371751 / 1000000000000) (-34298362307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1793624652098071 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2126514475 / 1000000000000) (2126514477 / 1000000000000), orderedInterval (-37621753635 / 1000000000000) (-37621753634 / 1000000000000)))) (orderedInterval (-1739907182 / 1000000000000) (-1739905660 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (758414144660277 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54968370421 / 1000000000000) (54968373993 / 1000000000000), orderedInterval (-18478131941 / 1000000000000) (-18478128369 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3082911392149717 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27831829740 / 1000000000000) (-27831796807 / 1000000000000), orderedInterval (7186590939 / 1000000000000) (7186623871 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2059241935314203 / 4000000000000) 0 (IntervalRat.scale (829 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12861945529 / 1000000000000) (12861945530 / 1000000000000), orderedInterval (32716405801 / 1000000000000) (32716405802 / 1000000000000)))) (orderedInterval (183682856 / 1000000000000) (183685673 / 1000000000000))) = true
  rfl'

theorem compactCertificate543_chunkChecks0 :
    compactCertificate543.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate543.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate543_chunkChecks0_0
    compactCertificate543_chunkChecks0_1 compactCertificate543_chunkChecks0_2

theorem compactCertificate543_chunkChecks1_0 :
    compactCertificate543.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (829 / 2) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (21962119344 / 1000000000000) (21962119345 / 1000000000000), orderedInterval (32431784460 / 1000000000000) (32431784461 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1221275295809929 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44739236438 / 1000000000000) (-44739236431 / 1000000000000), orderedInterval (-9064375115 / 1000000000000) (-9064375108 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (394935337980457 / 800000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33775962146 / 1000000000000) (-33775962143 / 1000000000000), orderedInterval (-12162162411 / 1000000000000) (-12162162408 / 1000000000000)))) (orderedInterval (11942605693 / 1000000000000) (11942605726 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (356365085413403 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79696051416 / 1000000000000) (79696053925 / 1000000000000), orderedInterval (-28628010600 / 1000000000000) (-28628008092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (957246746316191 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50156240418 / 1000000000000) (50156240421 / 1000000000000), orderedInterval (11918442387 / 1000000000000) (11918442390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2599111127259747 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-7844271384 / 1000000000000) (-7844271383 / 1000000000000), orderedInterval (-30296070177 / 1000000000000) (-30296070176 / 1000000000000)))) (orderedInterval (3694236625 / 1000000000000) (3694236688 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1914493492633211 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34668982536 / 1000000000000) (34668997441 / 1000000000000), orderedInterval (-11357286086 / 1000000000000) (-11357271181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3280517231123303 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22805553868 / 1000000000000) (-22805553866 / 1000000000000), orderedInterval (-15990777943 / 1000000000000) (-15990777942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2416414144660277 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32179662585 / 1000000000000) (32179667010 / 1000000000000), orderedInterval (-4303834386 / 1000000000000) (-4303829962 / 1000000000000)))) (orderedInterval (824289205 / 1000000000000) (824289401 / 1000000000000))) = true
  rfl'

theorem compactCertificate543_chunkChecks1_1 :
    compactCertificate543.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3707400706694171 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19957165965 / 1000000000000) (-19957165963 / 1000000000000), orderedInterval (-16976736458 / 1000000000000) (-16976736457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2140468796003459 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33325249363 / 1000000000000) (33325260905 / 1000000000000), orderedInterval (-8925512507 / 1000000000000) (-8925500965 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3798299440147231 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25882177577 / 1000000000000) (25882186818 / 1000000000000), orderedInterval (-747559734 / 1000000000000) (-747550493 / 1000000000000)))) (orderedInterval (5648038612 / 1000000000000) (5648043067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3548864039430139 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23490596942 / 1000000000000) (23490623397 / 1000000000000), orderedInterval (-12887210397 / 1000000000000) (-12887183942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2532636834078187 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19373831237 / 1000000000000) (-19373829822 / 1000000000000), orderedInterval (25117496125 / 1000000000000) (25117497541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2871740238948573 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19284392836 / 1000000000000) (19284394321 / 1000000000000), orderedInterval (-22703725690 / 1000000000000) (-22703724205 / 1000000000000)))) (orderedInterval (4325135913 / 1000000000000) (4325137233 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2394157617265037 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21494921410 / 1000000000000) (21494924870 / 1000000000000), orderedInterval (-24545299379 / 1000000000000) (-24545295919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2115310862369777 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33578545644 / 1000000000000) (33578556150 / 1000000000000), orderedInterval (-8767457347 / 1000000000000) (-8767446840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (613099536115923 / 800000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16535753156 / 1000000000000) (16535753157 / 1000000000000), orderedInterval (23595549749 / 1000000000000) (23595549750 / 1000000000000)))) (orderedInterval (1347831037 / 1000000000000) (1347831920 / 1000000000000))) = true
  rfl'

theorem compactCertificate543_chunkChecks1_2 :
    compactCertificate543.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1695865582557481 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23032240709 / 1000000000000) (-23032240708 / 1000000000000), orderedInterval (-31135265408 / 1000000000000) (-31135265407 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1437604035531041 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37452819309 / 1000000000000) (37452856413 / 1000000000000), orderedInterval (-19251586259 / 1000000000000) (-19251549154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (899585855339723 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-26129315019 / 1000000000000) (-26129312146 / 1000000000000), orderedInterval (46404464161 / 1000000000000) (46404467033 / 1000000000000)))) (orderedInterval (6856451328 / 1000000000000) (6856453296 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (483800264889141 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (51417349288 / 1000000000000) (51417417398 / 1000000000000), orderedInterval (-51396028154 / 1000000000000) (-51395960045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1313611831730423 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27659384880 / 1000000000000) (27659394325 / 1000000000000), orderedInterval (-34298371751 / 1000000000000) (-34298362307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1793624652098071 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2126514475 / 1000000000000) (2126514477 / 1000000000000), orderedInterval (-37621753635 / 1000000000000) (-37621753634 / 1000000000000)))) (orderedInterval (4012563515 / 1000000000000) (4012564097 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (758414144660277 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54968370421 / 1000000000000) (54968373993 / 1000000000000), orderedInterval (-18478131941 / 1000000000000) (-18478128369 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3082911392149717 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27831829740 / 1000000000000) (-27831796807 / 1000000000000), orderedInterval (7186590939 / 1000000000000) (7186623871 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2059241935314203 / 4000000000000) 1 (IntervalRat.scale (829 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12861945529 / 1000000000000) (12861945530 / 1000000000000), orderedInterval (32716405801 / 1000000000000) (32716405802 / 1000000000000)))) (orderedInterval (-8762715750 / 1000000000000) (-8762710593 / 1000000000000))) = true
  rfl'

theorem compactCertificate543_chunkChecks1 :
    compactCertificate543.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate543.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate543_chunkChecks1_0
    compactCertificate543_chunkChecks1_1 compactCertificate543_chunkChecks1_2

theorem compactCertificate543_chunkChecks2_0 :
    compactCertificate543.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (829 / 2) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (21962119344 / 1000000000000) (21962119345 / 1000000000000), orderedInterval (32431784460 / 1000000000000) (32431784461 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1221275295809929 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44739236438 / 1000000000000) (-44739236431 / 1000000000000), orderedInterval (-9064375115 / 1000000000000) (-9064375108 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (394935337980457 / 800000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33775962146 / 1000000000000) (-33775962143 / 1000000000000), orderedInterval (-12162162411 / 1000000000000) (-12162162408 / 1000000000000)))) (orderedInterval (-5696195440 / 1000000000000) (-5696195401 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (356365085413403 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79696051416 / 1000000000000) (79696053925 / 1000000000000), orderedInterval (-28628010600 / 1000000000000) (-28628008092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (957246746316191 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50156240418 / 1000000000000) (50156240421 / 1000000000000), orderedInterval (11918442387 / 1000000000000) (11918442390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2599111127259747 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-7844271384 / 1000000000000) (-7844271383 / 1000000000000), orderedInterval (-30296070177 / 1000000000000) (-30296070176 / 1000000000000)))) (orderedInterval (-1949773937 / 1000000000000) (-1949773857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1914493492633211 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34668982536 / 1000000000000) (34668997441 / 1000000000000), orderedInterval (-11357286086 / 1000000000000) (-11357271181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3280517231123303 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22805553868 / 1000000000000) (-22805553866 / 1000000000000), orderedInterval (-15990777943 / 1000000000000) (-15990777942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2416414144660277 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32179662585 / 1000000000000) (32179667010 / 1000000000000), orderedInterval (-4303834386 / 1000000000000) (-4303829962 / 1000000000000)))) (orderedInterval (-4407702211 / 1000000000000) (-4407701911 / 1000000000000))) = true
  rfl'

theorem compactCertificate543_chunkChecks2_1 :
    compactCertificate543.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3707400706694171 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19957165965 / 1000000000000) (-19957165963 / 1000000000000), orderedInterval (-16976736458 / 1000000000000) (-16976736457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2140468796003459 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33325249363 / 1000000000000) (33325260905 / 1000000000000), orderedInterval (-8925512507 / 1000000000000) (-8925500965 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3798299440147231 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25882177577 / 1000000000000) (25882186818 / 1000000000000), orderedInterval (-747559734 / 1000000000000) (-747550493 / 1000000000000)))) (orderedInterval (-41169260883 / 1000000000000) (-41169251822 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3548864039430139 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23490596942 / 1000000000000) (23490623397 / 1000000000000), orderedInterval (-12887210397 / 1000000000000) (-12887183942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2532636834078187 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19373831237 / 1000000000000) (-19373829822 / 1000000000000), orderedInterval (25117496125 / 1000000000000) (25117497541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2871740238948573 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19284392836 / 1000000000000) (19284394321 / 1000000000000), orderedInterval (-22703725690 / 1000000000000) (-22703724205 / 1000000000000)))) (orderedInterval (6500028266 / 1000000000000) (6500030925 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2394157617265037 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21494921410 / 1000000000000) (21494924870 / 1000000000000), orderedInterval (-24545299379 / 1000000000000) (-24545295919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2115310862369777 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33578545644 / 1000000000000) (33578556150 / 1000000000000), orderedInterval (-8767457347 / 1000000000000) (-8767446840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (613099536115923 / 800000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16535753156 / 1000000000000) (16535753157 / 1000000000000), orderedInterval (23595549749 / 1000000000000) (23595549750 / 1000000000000)))) (orderedInterval (1159668982 / 1000000000000) (1159670132 / 1000000000000))) = true
  rfl'

theorem compactCertificate543_chunkChecks2_2 :
    compactCertificate543.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1695865582557481 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23032240709 / 1000000000000) (-23032240708 / 1000000000000), orderedInterval (-31135265408 / 1000000000000) (-31135265407 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1437604035531041 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37452819309 / 1000000000000) (37452856413 / 1000000000000), orderedInterval (-19251586259 / 1000000000000) (-19251549154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (899585855339723 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-26129315019 / 1000000000000) (-26129312146 / 1000000000000), orderedInterval (46404464161 / 1000000000000) (46404467033 / 1000000000000)))) (orderedInterval (-2025223522 / 1000000000000) (-2025221818 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (483800264889141 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (51417349288 / 1000000000000) (51417417398 / 1000000000000), orderedInterval (-51396028154 / 1000000000000) (-51395960045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1313611831730423 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27659384880 / 1000000000000) (27659394325 / 1000000000000), orderedInterval (-34298371751 / 1000000000000) (-34298362307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1793624652098071 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2126514475 / 1000000000000) (2126514477 / 1000000000000), orderedInterval (-37621753635 / 1000000000000) (-37621753634 / 1000000000000)))) (orderedInterval (655782318 / 1000000000000) (655782606 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (758414144660277 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54968370421 / 1000000000000) (54968373993 / 1000000000000), orderedInterval (-18478131941 / 1000000000000) (-18478128369 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3082911392149717 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27831829740 / 1000000000000) (-27831796807 / 1000000000000), orderedInterval (7186590939 / 1000000000000) (7186623871 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2059241935314203 / 4000000000000) 2 (IntervalRat.scale (829 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12861945529 / 1000000000000) (12861945530 / 1000000000000), orderedInterval (32716405801 / 1000000000000) (32716405802 / 1000000000000)))) (orderedInterval (-4158602830 / 1000000000000) (-4158593306 / 1000000000000))) = true
  rfl'

theorem compactCertificate543_chunkChecks2 :
    compactCertificate543.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate543.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate543_chunkChecks2_0
    compactCertificate543_chunkChecks2_1 compactCertificate543_chunkChecks2_2

theorem compactCertificate543_chunkChecks3_0 :
    compactCertificate543.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (829 / 2) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (21962119344 / 1000000000000) (21962119345 / 1000000000000), orderedInterval (32431784460 / 1000000000000) (32431784461 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1221275295809929 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44739236438 / 1000000000000) (-44739236431 / 1000000000000), orderedInterval (-9064375115 / 1000000000000) (-9064375108 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (394935337980457 / 800000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33775962146 / 1000000000000) (-33775962143 / 1000000000000), orderedInterval (-12162162411 / 1000000000000) (-12162162408 / 1000000000000)))) (orderedInterval (-11601543747 / 1000000000000) (-11601543702 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (356365085413403 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79696051416 / 1000000000000) (79696053925 / 1000000000000), orderedInterval (-28628010600 / 1000000000000) (-28628008092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (957246746316191 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50156240418 / 1000000000000) (50156240421 / 1000000000000), orderedInterval (11918442387 / 1000000000000) (11918442390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2599111127259747 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-7844271384 / 1000000000000) (-7844271383 / 1000000000000), orderedInterval (-30296070177 / 1000000000000) (-30296070176 / 1000000000000)))) (orderedInterval (-8378962537 / 1000000000000) (-8378962419 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1914493492633211 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34668982536 / 1000000000000) (34668997441 / 1000000000000), orderedInterval (-11357286086 / 1000000000000) (-11357271181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3280517231123303 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22805553868 / 1000000000000) (-22805553866 / 1000000000000), orderedInterval (-15990777943 / 1000000000000) (-15990777942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2416414144660277 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32179662585 / 1000000000000) (32179667010 / 1000000000000), orderedInterval (-4303834386 / 1000000000000) (-4303829962 / 1000000000000)))) (orderedInterval (-3487803491 / 1000000000000) (-3487803028 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate543_chunkChecks3_1 :
    compactCertificate543.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3707400706694171 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19957165965 / 1000000000000) (-19957165963 / 1000000000000), orderedInterval (-16976736458 / 1000000000000) (-16976736457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2140468796003459 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33325249363 / 1000000000000) (33325260905 / 1000000000000), orderedInterval (-8925512507 / 1000000000000) (-8925500965 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3798299440147231 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25882177577 / 1000000000000) (25882186818 / 1000000000000), orderedInterval (-747559734 / 1000000000000) (-747550493 / 1000000000000)))) (orderedInterval (-30926247089 / 1000000000000) (-30926227834 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3548864039430139 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23490596942 / 1000000000000) (23490623397 / 1000000000000), orderedInterval (-12887210397 / 1000000000000) (-12887183942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2532636834078187 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19373831237 / 1000000000000) (-19373829822 / 1000000000000), orderedInterval (25117496125 / 1000000000000) (25117497541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2871740238948573 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19284392836 / 1000000000000) (19284394321 / 1000000000000), orderedInterval (-22703725690 / 1000000000000) (-22703724205 / 1000000000000)))) (orderedInterval (-11359872377 / 1000000000000) (-11359866946 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2394157617265037 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21494921410 / 1000000000000) (21494924870 / 1000000000000), orderedInterval (-24545299379 / 1000000000000) (-24545295919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2115310862369777 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33578545644 / 1000000000000) (33578556150 / 1000000000000), orderedInterval (-8767457347 / 1000000000000) (-8767446840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (613099536115923 / 800000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16535753156 / 1000000000000) (16535753157 / 1000000000000), orderedInterval (23595549749 / 1000000000000) (23595549750 / 1000000000000)))) (orderedInterval (-4009741988 / 1000000000000) (-4009740484 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate543_chunkChecks3_2 :
    compactCertificate543.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1695865582557481 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23032240709 / 1000000000000) (-23032240708 / 1000000000000), orderedInterval (-31135265408 / 1000000000000) (-31135265407 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1437604035531041 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37452819309 / 1000000000000) (37452856413 / 1000000000000), orderedInterval (-19251586259 / 1000000000000) (-19251549154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (899585855339723 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-26129315019 / 1000000000000) (-26129312146 / 1000000000000), orderedInterval (46404464161 / 1000000000000) (46404467033 / 1000000000000)))) (orderedInterval (-6273908470 / 1000000000000) (-6273906992 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (483800264889141 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (51417349288 / 1000000000000) (51417417398 / 1000000000000), orderedInterval (-51396028154 / 1000000000000) (-51395960045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1313611831730423 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27659384880 / 1000000000000) (27659394325 / 1000000000000), orderedInterval (-34298371751 / 1000000000000) (-34298362307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1793624652098071 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2126514475 / 1000000000000) (2126514477 / 1000000000000), orderedInterval (-37621753635 / 1000000000000) (-37621753634 / 1000000000000)))) (orderedInterval (-4062429800 / 1000000000000) (-4062429616 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (758414144660277 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54968370421 / 1000000000000) (54968373993 / 1000000000000), orderedInterval (-18478131941 / 1000000000000) (-18478128369 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3082911392149717 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27831829740 / 1000000000000) (-27831796807 / 1000000000000), orderedInterval (7186590939 / 1000000000000) (7186623871 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2059241935314203 / 4000000000000) 3 (IntervalRat.scale (829 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12861945529 / 1000000000000) (12861945530 / 1000000000000), orderedInterval (32716405801 / 1000000000000) (32716405802 / 1000000000000)))) (orderedInterval (15542066117 / 1000000000000) (15542083743 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate543_chunkChecks3 :
    compactCertificate543.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate543.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate543_chunkChecks3_0
    compactCertificate543_chunkChecks3_1 compactCertificate543_chunkChecks3_2

theorem compactCertificate543_chunkChecks4_0 :
    compactCertificate543.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (829 / 2) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (21962119344 / 1000000000000) (21962119345 / 1000000000000), orderedInterval (32431784460 / 1000000000000) (32431784461 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1221275295809929 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44739236438 / 1000000000000) (-44739236431 / 1000000000000), orderedInterval (-9064375115 / 1000000000000) (-9064375108 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (394935337980457 / 800000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-33775962146 / 1000000000000) (-33775962143 / 1000000000000), orderedInterval (-12162162411 / 1000000000000) (-12162162408 / 1000000000000)))) (orderedInterval (4650263626 / 1000000000000) (4650263678 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (356365085413403 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79696051416 / 1000000000000) (79696053925 / 1000000000000), orderedInterval (-28628010600 / 1000000000000) (-28628008092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (957246746316191 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50156240418 / 1000000000000) (50156240421 / 1000000000000), orderedInterval (11918442387 / 1000000000000) (11918442390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2599111127259747 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-7844271384 / 1000000000000) (-7844271383 / 1000000000000), orderedInterval (-30296070177 / 1000000000000) (-30296070176 / 1000000000000)))) (orderedInterval (3609647109 / 1000000000000) (3609647290 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1914493492633211 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34668982536 / 1000000000000) (34668997441 / 1000000000000), orderedInterval (-11357286086 / 1000000000000) (-11357271181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3280517231123303 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-22805553868 / 1000000000000) (-22805553866 / 1000000000000), orderedInterval (-15990777943 / 1000000000000) (-15990777942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2416414144660277 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32179662585 / 1000000000000) (32179667010 / 1000000000000), orderedInterval (-4303834386 / 1000000000000) (-4303829962 / 1000000000000)))) (orderedInterval (14306285402 / 1000000000000) (14306286129 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate543_chunkChecks4_1 :
    compactCertificate543.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3707400706694171 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19957165965 / 1000000000000) (-19957165963 / 1000000000000), orderedInterval (-16976736458 / 1000000000000) (-16976736457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2140468796003459 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33325249363 / 1000000000000) (33325260905 / 1000000000000), orderedInterval (-8925512507 / 1000000000000) (-8925500965 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3798299440147231 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25882177577 / 1000000000000) (25882186818 / 1000000000000), orderedInterval (-747559734 / 1000000000000) (-747550493 / 1000000000000)))) (orderedInterval (197002161328 / 1000000000000) (197002203531 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3548864039430139 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23490596942 / 1000000000000) (23490623397 / 1000000000000), orderedInterval (-12887210397 / 1000000000000) (-12887183942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2532636834078187 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19373831237 / 1000000000000) (-19373829822 / 1000000000000), orderedInterval (25117496125 / 1000000000000) (25117497541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2871740238948573 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19284392836 / 1000000000000) (19284394321 / 1000000000000), orderedInterval (-22703725690 / 1000000000000) (-22703724205 / 1000000000000)))) (orderedInterval (-19699472405 / 1000000000000) (-19699461169 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2394157617265037 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21494921410 / 1000000000000) (21494924870 / 1000000000000), orderedInterval (-24545299379 / 1000000000000) (-24545295919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2115310862369777 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33578545644 / 1000000000000) (33578556150 / 1000000000000), orderedInterval (-8767457347 / 1000000000000) (-8767446840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (613099536115923 / 800000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16535753156 / 1000000000000) (16535753157 / 1000000000000), orderedInterval (23595549749 / 1000000000000) (23595549750 / 1000000000000)))) (orderedInterval (954993018 / 1000000000000) (954995000 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate543_chunkChecks4_2 :
    compactCertificate543.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1695865582557481 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23032240709 / 1000000000000) (-23032240708 / 1000000000000), orderedInterval (-31135265408 / 1000000000000) (-31135265407 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1437604035531041 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37452819309 / 1000000000000) (37452856413 / 1000000000000), orderedInterval (-19251586259 / 1000000000000) (-19251549154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (899585855339723 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-26129315019 / 1000000000000) (-26129312146 / 1000000000000), orderedInterval (46404464161 / 1000000000000) (46404467033 / 1000000000000)))) (orderedInterval (2789170793 / 1000000000000) (2789172083 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (483800264889141 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (51417349288 / 1000000000000) (51417417398 / 1000000000000), orderedInterval (-51396028154 / 1000000000000) (-51395960045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1313611831730423 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (27659384880 / 1000000000000) (27659394325 / 1000000000000), orderedInterval (-34298371751 / 1000000000000) (-34298362307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1793624652098071 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2126514475 / 1000000000000) (2126514477 / 1000000000000), orderedInterval (-37621753635 / 1000000000000) (-37621753634 / 1000000000000)))) (orderedInterval (-457739907 / 1000000000000) (-457739764 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (758414144660277 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54968370421 / 1000000000000) (54968373993 / 1000000000000), orderedInterval (-18478131941 / 1000000000000) (-18478128369 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3082911392149717 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27831829740 / 1000000000000) (-27831796807 / 1000000000000), orderedInterval (7186590939 / 1000000000000) (7186623871 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2059241935314203 / 4000000000000) 4 (IntervalRat.scale (829 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12861945529 / 1000000000000) (12861945530 / 1000000000000), orderedInterval (32716405801 / 1000000000000) (32716405802 / 1000000000000)))) (orderedInterval (21279135296 / 1000000000000) (21279168016 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate543_chunkChecks4 :
    compactCertificate543.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate543.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate543_chunkChecks4_0
    compactCertificate543_chunkChecks4_1 compactCertificate543_chunkChecks4_2

theorem compactCertificate543_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate543.chunkCheck r b = true :=
  compactCertificate543.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate543_chunkChecks0
    · exact compactCertificate543_chunkChecks1
    · exact compactCertificate543_chunkChecks2
    · exact compactCertificate543_chunkChecks3
    · exact compactCertificate543_chunkChecks4)

theorem compactCertificate543_coefficient0 :
    compactCertificate543.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate543_coefficient1 :
    compactCertificate543.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate543_coefficient2 :
    compactCertificate543.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate543_coefficient3 :
    compactCertificate543.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate543_coefficient4 :
    compactCertificate543.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate543_coefficients : ∀ r : Fin 5,
    compactCertificate543.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate543_coefficient0
  · exact compactCertificate543_coefficient1
  · exact compactCertificate543_coefficient2
  · exact compactCertificate543_coefficient3
  · exact compactCertificate543_coefficient4

theorem compactCertificate543_lower : (1 : ℚ) ≤ compactCertificate543.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate543, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate543_proves {t : ℝ} (ht : t ∈ compactCertificate543.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate543.proves compactCertificate543_states compactCertificate543_chunks
    compactCertificate543_coefficients compactCertificate543_lower ht

end Erdos232
