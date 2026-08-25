/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate460 : CompactCertificate where
  left := 331
  right := 332
  center := 663 / 2
  grid := fun i =>
    match i.val with
    | 0 => 106
    | 1 => 78
    | 2 => 126
    | 3 => 23
    | 4 => 61
    | 5 => 165
    | 6 => 122
    | 7 => 209
    | 8 => 154
    | 9 => 236
    | 10 => 136
    | 11 => 242
    | 12 => 226
    | 13 => 161
    | 14 => 183
    | 15 => 152
    | 16 => 135
    | 17 => 195
    | 18 => 108
    | 19 => 92
    | 20 => 57
    | 21 => 31
    | 22 => 84
    | 23 => 114
    | 24 => 48
    | 25 => 196
    | _ => 131
  point := fun i =>
    match i.val with
    | 0 => 663 / 2
    | 1 => 976725598458363 / 4000000000000
    | 2 => 315852990447579 / 800000000000
    | 3 => 285006093641841 / 4000000000000
    | 4 => 765566456945277 / 4000000000000
    | 5 => 2078661854491209 / 4000000000000
    | 6 => 1531132913891217 / 4000000000000
    | 7 => 2623622345277141 / 4000000000000
    | 8 => 1932548344885119 / 4000000000000
    | 9 => 2965026138164337 / 4000000000000
    | 10 => 1711858639023273 / 4000000000000
    | 11 => 3037723195196157 / 4000000000000
    | 12 => 2838235052041233 / 4000000000000
    | 13 => 2025498457169889 / 4000000000000
    | 14 => 2296699370835831 / 4000000000000
    | 15 => 1914748492456839 / 4000000000000
    | 16 => 1691738361581619 / 4000000000000
    | 17 => 490331715856281 / 800000000000
    | 18 => 1356283330802907 / 4000000000000
    | 19 => 1149736399948227 / 4000000000000
    | 20 => 719451655114881 / 4000000000000
    | 21 => 386923492908927 / 4000000000000
    | 22 => 1050572550587781 / 4000000000000
    | 23 => 1434467001617637 / 4000000000000
    | 24 => 606548344885119 / 4000000000000
    | 25 => 2465585347400799 / 4000000000000
    | _ => 1646896746819441 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-29020943875 / 1000000000000) (-29020929450 / 1000000000000), orderedInterval (32879829060 / 1000000000000) (32879843486 / 1000000000000))
    | 1 => (orderedInterval (-3975668055 / 1000000000000) (-3975668048 / 1000000000000), orderedInterval (50913529695 / 1000000000000) (50913529702 / 1000000000000))
    | 2 => (orderedInterval (-9519839255 / 1000000000000) (-9519839228 / 1000000000000), orderedInterval (39022561986 / 1000000000000) (39022562013 / 1000000000000))
    | 3 => (orderedInterval (20762715160 / 1000000000000) (20762715373 / 1000000000000), orderedInterval (-92362457654 / 1000000000000) (-92362457442 / 1000000000000))
    | 4 => (orderedInterval (-29612912999 / 1000000000000) (-29612912998 / 1000000000000), orderedInterval (-49413532493 / 1000000000000) (-49413532492 / 1000000000000))
    | 5 => (orderedInterval (-30425818237 / 1000000000000) (-30425709316 / 1000000000000), orderedInterval (17330358494 / 1000000000000) (17330467415 / 1000000000000))
    | 6 => (orderedInterval (11817645001 / 1000000000000) (11817645002 / 1000000000000), orderedInterval (39016324595 / 1000000000000) (39016324596 / 1000000000000))
    | 7 => (orderedInterval (-3046054238 / 1000000000000) (-3046054237 / 1000000000000), orderedInterval (-31002814518 / 1000000000000) (-31002814517 / 1000000000000))
    | 8 => (orderedInterval (4235848663 / 1000000000000) (4235848664 / 1000000000000), orderedInterval (36047490667 / 1000000000000) (36047490668 / 1000000000000))
    | 9 => (orderedInterval (17168159899 / 1000000000000) (17168159900 / 1000000000000), orderedInterval (23739061904 / 1000000000000) (23739061905 / 1000000000000))
    | 10 => (orderedInterval (38452623535 / 1000000000000) (38452623652 / 1000000000000), orderedInterval (2946218345 / 1000000000000) (2946218462 / 1000000000000))
    | 11 => (orderedInterval (-1429409374 / 1000000000000) (-1429409373 / 1000000000000), orderedInterval (28918797143 / 1000000000000) (28918797144 / 1000000000000))
    | 12 => (orderedInterval (10103217136 / 1000000000000) (10103217137 / 1000000000000), orderedInterval (28190935887 / 1000000000000) (28190935888 / 1000000000000))
    | 13 => (orderedInterval (-34696952558 / 1000000000000) (-34696952526 / 1000000000000), orderedInterval (-7268615811 / 1000000000000) (-7268615780 / 1000000000000))
    | 14 => (orderedInterval (-1616566048 / 1000000000000) (-1616566047 / 1000000000000), orderedInterval (-33257321670 / 1000000000000) (-33257321669 / 1000000000000))
    | 15 => (orderedInterval (33875067276 / 1000000000000) (33875094509 / 1000000000000), orderedInterval (-13541213940 / 1000000000000) (-13541186708 / 1000000000000))
    | 16 => (orderedInterval (14940868224 / 1000000000000) (14940868429 / 1000000000000), orderedInterval (-35822903743 / 1000000000000) (-35822903539 / 1000000000000))
    | 17 => (orderedInterval (-28563784080 / 1000000000000) (-28563784078 / 1000000000000), orderedInterval (-14902719594 / 1000000000000) (-14902719593 / 1000000000000))
    | 18 => (orderedInterval (23157988166 / 1000000000000) (23157988167 / 1000000000000), orderedInterval (36588939040 / 1000000000000) (36588939041 / 1000000000000))
    | 19 => (orderedInterval (-34003935138 / 1000000000000) (-34003896362 / 1000000000000), orderedInterval (32594816334 / 1000000000000) (32594855109 / 1000000000000))
    | 20 => (orderedInterval (-59492263115 / 1000000000000) (-59492263050 / 1000000000000), orderedInterval (524684149 / 1000000000000) (524684214 / 1000000000000))
    | 21 => (orderedInterval (-10163088606 / 1000000000000) (-10163088605 / 1000000000000), orderedInterval (-80434406602 / 1000000000000) (-80434406601 / 1000000000000))
    | 22 => (orderedInterval (-22109028712 / 1000000000000) (-22109027360 / 1000000000000), orderedInterval (44031746077 / 1000000000000) (44031747430 / 1000000000000))
    | 23 => (orderedInterval (40117682921 / 1000000000000) (40117682924 / 1000000000000), orderedInterval (12819599702 / 1000000000000) (12819599705 / 1000000000000))
    | 24 => (orderedInterval (64698296249 / 1000000000000) (64698296354 / 1000000000000), orderedInterval (-3737475024 / 1000000000000) (-3737474919 / 1000000000000))
    | 25 => (orderedInterval (31816491640 / 1000000000000) (31816491821 / 1000000000000), orderedInterval (4504055747 / 1000000000000) (4504055927 / 1000000000000))
    | _ => (orderedInterval (-32226842228 / 1000000000000) (-32226842227 / 1000000000000), orderedInterval (-22492152819 / 1000000000000) (-22492152818 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-12098566761 / 1000000000000) (-12098561018 / 1000000000000)
      | 1 => orderedInterval (856472834 / 1000000000000) (856480619 / 1000000000000)
      | 2 => orderedInterval (196324595 / 1000000000000) (196324614 / 1000000000000)
      | 3 => orderedInterval (-404750779 / 1000000000000) (-404750638 / 1000000000000)
      | 4 => orderedInterval (-3455256788 / 1000000000000) (-3455256745 / 1000000000000)
      | 5 => orderedInterval (-1195183869 / 1000000000000) (-1195183511 / 1000000000000)
      | 6 => orderedInterval (-3714955032 / 1000000000000) (-3714952751 / 1000000000000)
      | 7 => orderedInterval (-2385326833 / 1000000000000) (-2385326763 / 1000000000000)
      | _ => orderedInterval (3846714016 / 1000000000000) (3846714124 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (16109120685 / 1000000000000) (16109126432 / 1000000000000)
      | 1 => orderedInterval (-2757591458 / 1000000000000) (-2757579274 / 1000000000000)
      | 2 => orderedInterval (3161742722 / 1000000000000) (3161742755 / 1000000000000)
      | 3 => orderedInterval (267559996 / 1000000000000) (267560280 / 1000000000000)
      | 4 => orderedInterval (-1847770577 / 1000000000000) (-1847770508 / 1000000000000)
      | 5 => orderedInterval (1684180450 / 1000000000000) (1684180965 / 1000000000000)
      | 6 => orderedInterval (-7574268045 / 1000000000000) (-7574266063 / 1000000000000)
      | 7 => orderedInterval (-1420908907 / 1000000000000) (-1420908846 / 1000000000000)
      | _ => orderedInterval (4549370750 / 1000000000000) (4549370907 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (12266797833 / 1000000000000) (12266803600 / 1000000000000)
      | 1 => orderedInterval (-4936186362 / 1000000000000) (-4936167234 / 1000000000000)
      | 2 => orderedInterval (-594796006 / 1000000000000) (-594795947 / 1000000000000)
      | 3 => orderedInterval (11570120849 / 1000000000000) (11570121449 / 1000000000000)
      | 4 => orderedInterval (8472442340 / 1000000000000) (8472442454 / 1000000000000)
      | 5 => orderedInterval (3071071366 / 1000000000000) (3071072111 / 1000000000000)
      | 6 => orderedInterval (3019903739 / 1000000000000) (3019905469 / 1000000000000)
      | 7 => orderedInterval (3271601551 / 1000000000000) (3271601607 / 1000000000000)
      | _ => orderedInterval (-468213246 / 1000000000000) (-468213004 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-17127434272 / 1000000000000) (-17127428499 / 1000000000000)
      | 1 => orderedInterval (5098206243 / 1000000000000) (5098236223 / 1000000000000)
      | 2 => orderedInterval (-10102200124 / 1000000000000) (-10102200019 / 1000000000000)
      | 3 => orderedInterval (-2770710628 / 1000000000000) (-2770709326 / 1000000000000)
      | 4 => orderedInterval (6540606061 / 1000000000000) (6540606252 / 1000000000000)
      | 5 => orderedInterval (-1383977664 / 1000000000000) (-1383976586 / 1000000000000)
      | 6 => orderedInterval (7451061907 / 1000000000000) (7451063415 / 1000000000000)
      | 7 => orderedInterval (1693864596 / 1000000000000) (1693864648 / 1000000000000)
      | _ => orderedInterval (-5724605197 / 1000000000000) (-5724604808 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-12534367838 / 1000000000000) (-12534362042 / 1000000000000)
      | 1 => orderedInterval (12910539451 / 1000000000000) (12910586536 / 1000000000000)
      | 2 => orderedInterval (1962746520 / 1000000000000) (1962746715 / 1000000000000)
      | 3 => orderedInterval (-73930400477 / 1000000000000) (-73930397605 / 1000000000000)
      | 4 => orderedInterval (-21657730821 / 1000000000000) (-21657730491 / 1000000000000)
      | 5 => orderedInterval (-9102689116 / 1000000000000) (-9102687544 / 1000000000000)
      | 6 => orderedInterval (-3177747366 / 1000000000000) (-3177746046 / 1000000000000)
      | 7 => orderedInterval (-4022071543 / 1000000000000) (-4022071492 / 1000000000000)
      | _ => orderedInterval (-16519672640 / 1000000000000) (-16519671991 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-18354528617 / 1000000000000) (-18354512069 / 1000000000000)
    | 1 => orderedInterval (12171435616 / 1000000000000) (12171456648 / 1000000000000)
    | 2 => orderedInterval (35672742064 / 1000000000000) (35672770505 / 1000000000000)
    | 3 => orderedInterval (-16325189078 / 1000000000000) (-16325148700 / 1000000000000)
    | _ => orderedInterval (-126071393830 / 1000000000000) (-126071333960 / 1000000000000)

theorem compactCertificate460_stateChecks0 :
    compactCertificate460.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (663 / 2)) (orderedInterval (-29020943875 / 1000000000000) (-29020929450 / 1000000000000), orderedInterval (32879829060 / 1000000000000) (32879843486 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (976725598458363 / 4000000000000)) (orderedInterval (-3975668055 / 1000000000000) (-3975668048 / 1000000000000), orderedInterval (50913529695 / 1000000000000) (50913529702 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (315852990447579 / 800000000000)) (orderedInterval (-9519839255 / 1000000000000) (-9519839228 / 1000000000000), orderedInterval (39022561986 / 1000000000000) (39022562013 / 1000000000000))) = true
  rfl'

theorem compactCertificate460_stateChecks1 :
    compactCertificate460.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (285006093641841 / 4000000000000)) (orderedInterval (20762715160 / 1000000000000) (20762715373 / 1000000000000), orderedInterval (-92362457654 / 1000000000000) (-92362457442 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (765566456945277 / 4000000000000)) (orderedInterval (-29612912999 / 1000000000000) (-29612912998 / 1000000000000), orderedInterval (-49413532493 / 1000000000000) (-49413532492 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2078661854491209 / 4000000000000)) (orderedInterval (-30425818237 / 1000000000000) (-30425709316 / 1000000000000), orderedInterval (17330358494 / 1000000000000) (17330467415 / 1000000000000))) = true
  rfl'

theorem compactCertificate460_stateChecks2 :
    compactCertificate460.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1531132913891217 / 4000000000000)) (orderedInterval (11817645001 / 1000000000000) (11817645002 / 1000000000000), orderedInterval (39016324595 / 1000000000000) (39016324596 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 209 12 (2623622345277141 / 4000000000000)) (orderedInterval (-3046054238 / 1000000000000) (-3046054237 / 1000000000000), orderedInterval (-31002814518 / 1000000000000) (-31002814517 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1932548344885119 / 4000000000000)) (orderedInterval (4235848663 / 1000000000000) (4235848664 / 1000000000000), orderedInterval (36047490667 / 1000000000000) (36047490668 / 1000000000000))) = true
  rfl'

theorem compactCertificate460_stateChecks3 :
    compactCertificate460.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 236 12 (2965026138164337 / 4000000000000)) (orderedInterval (17168159899 / 1000000000000) (17168159900 / 1000000000000), orderedInterval (23739061904 / 1000000000000) (23739061905 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1711858639023273 / 4000000000000)) (orderedInterval (38452623535 / 1000000000000) (38452623652 / 1000000000000), orderedInterval (2946218345 / 1000000000000) (2946218462 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 242 12 (3037723195196157 / 4000000000000)) (orderedInterval (-1429409374 / 1000000000000) (-1429409373 / 1000000000000), orderedInterval (28918797143 / 1000000000000) (28918797144 / 1000000000000))) = true
  rfl'

theorem compactCertificate460_stateChecks4 :
    compactCertificate460.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 226 12 (2838235052041233 / 4000000000000)) (orderedInterval (10103217136 / 1000000000000) (10103217137 / 1000000000000), orderedInterval (28190935887 / 1000000000000) (28190935888 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2025498457169889 / 4000000000000)) (orderedInterval (-34696952558 / 1000000000000) (-34696952526 / 1000000000000), orderedInterval (-7268615811 / 1000000000000) (-7268615780 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2296699370835831 / 4000000000000)) (orderedInterval (-1616566048 / 1000000000000) (-1616566047 / 1000000000000), orderedInterval (-33257321670 / 1000000000000) (-33257321669 / 1000000000000))) = true
  rfl'

theorem compactCertificate460_stateChecks5 :
    compactCertificate460.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1914748492456839 / 4000000000000)) (orderedInterval (33875067276 / 1000000000000) (33875094509 / 1000000000000), orderedInterval (-13541213940 / 1000000000000) (-13541186708 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1691738361581619 / 4000000000000)) (orderedInterval (14940868224 / 1000000000000) (14940868429 / 1000000000000), orderedInterval (-35822903743 / 1000000000000) (-35822903539 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (490331715856281 / 800000000000)) (orderedInterval (-28563784080 / 1000000000000) (-28563784078 / 1000000000000), orderedInterval (-14902719594 / 1000000000000) (-14902719593 / 1000000000000))) = true
  rfl'

theorem compactCertificate460_stateChecks6 :
    compactCertificate460.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1356283330802907 / 4000000000000)) (orderedInterval (23157988166 / 1000000000000) (23157988167 / 1000000000000), orderedInterval (36588939040 / 1000000000000) (36588939041 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1149736399948227 / 4000000000000)) (orderedInterval (-34003935138 / 1000000000000) (-34003896362 / 1000000000000), orderedInterval (32594816334 / 1000000000000) (32594855109 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (719451655114881 / 4000000000000)) (orderedInterval (-59492263115 / 1000000000000) (-59492263050 / 1000000000000), orderedInterval (524684149 / 1000000000000) (524684214 / 1000000000000))) = true
  rfl'

theorem compactCertificate460_stateChecks7 :
    compactCertificate460.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (386923492908927 / 4000000000000)) (orderedInterval (-10163088606 / 1000000000000) (-10163088605 / 1000000000000), orderedInterval (-80434406602 / 1000000000000) (-80434406601 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1050572550587781 / 4000000000000)) (orderedInterval (-22109028712 / 1000000000000) (-22109027360 / 1000000000000), orderedInterval (44031746077 / 1000000000000) (44031747430 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1434467001617637 / 4000000000000)) (orderedInterval (40117682921 / 1000000000000) (40117682924 / 1000000000000), orderedInterval (12819599702 / 1000000000000) (12819599705 / 1000000000000))) = true
  rfl'

theorem compactCertificate460_stateChecks8 :
    compactCertificate460.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (606548344885119 / 4000000000000)) (orderedInterval (64698296249 / 1000000000000) (64698296354 / 1000000000000), orderedInterval (-3737475024 / 1000000000000) (-3737474919 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (2465585347400799 / 4000000000000)) (orderedInterval (31816491640 / 1000000000000) (31816491821 / 1000000000000), orderedInterval (4504055747 / 1000000000000) (4504055927 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1646896746819441 / 4000000000000)) (orderedInterval (-32226842228 / 1000000000000) (-32226842227 / 1000000000000), orderedInterval (-22492152819 / 1000000000000) (-22492152818 / 1000000000000))) = true
  rfl'

theorem compactCertificate460_states : ∀ j,
    BesselStateValid (compactCertificate460.point j) (compactCertificate460.state j) :=
  compactCertificate460.statesValid_of_checks3 compactCertificate460_stateChecks0
    compactCertificate460_stateChecks1 compactCertificate460_stateChecks2
    compactCertificate460_stateChecks3 compactCertificate460_stateChecks4
    compactCertificate460_stateChecks5 compactCertificate460_stateChecks6
    compactCertificate460_stateChecks7 compactCertificate460_stateChecks8

theorem compactCertificate460_chunkChecks0_0 :
    compactCertificate460.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (663 / 2) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-29020943875 / 1000000000000) (-29020929450 / 1000000000000), orderedInterval (32879829060 / 1000000000000) (32879843486 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (976725598458363 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-3975668055 / 1000000000000) (-3975668048 / 1000000000000), orderedInterval (50913529695 / 1000000000000) (50913529702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (315852990447579 / 800000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-9519839255 / 1000000000000) (-9519839228 / 1000000000000), orderedInterval (39022561986 / 1000000000000) (39022562013 / 1000000000000)))) (orderedInterval (-12098566761 / 1000000000000) (-12098561018 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (285006093641841 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (20762715160 / 1000000000000) (20762715373 / 1000000000000), orderedInterval (-92362457654 / 1000000000000) (-92362457442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (765566456945277 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29612912999 / 1000000000000) (-29612912998 / 1000000000000), orderedInterval (-49413532493 / 1000000000000) (-49413532492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2078661854491209 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30425818237 / 1000000000000) (-30425709316 / 1000000000000), orderedInterval (17330358494 / 1000000000000) (17330467415 / 1000000000000)))) (orderedInterval (856472834 / 1000000000000) (856480619 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1531132913891217 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11817645001 / 1000000000000) (11817645002 / 1000000000000), orderedInterval (39016324595 / 1000000000000) (39016324596 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2623622345277141 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3046054238 / 1000000000000) (-3046054237 / 1000000000000), orderedInterval (-31002814518 / 1000000000000) (-31002814517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1932548344885119 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4235848663 / 1000000000000) (4235848664 / 1000000000000), orderedInterval (36047490667 / 1000000000000) (36047490668 / 1000000000000)))) (orderedInterval (196324595 / 1000000000000) (196324614 / 1000000000000))) = true
  rfl'

theorem compactCertificate460_chunkChecks0_1 :
    compactCertificate460.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2965026138164337 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17168159899 / 1000000000000) (17168159900 / 1000000000000), orderedInterval (23739061904 / 1000000000000) (23739061905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1711858639023273 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38452623535 / 1000000000000) (38452623652 / 1000000000000), orderedInterval (2946218345 / 1000000000000) (2946218462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3037723195196157 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-1429409374 / 1000000000000) (-1429409373 / 1000000000000), orderedInterval (28918797143 / 1000000000000) (28918797144 / 1000000000000)))) (orderedInterval (-404750779 / 1000000000000) (-404750638 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2838235052041233 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10103217136 / 1000000000000) (10103217137 / 1000000000000), orderedInterval (28190935887 / 1000000000000) (28190935888 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2025498457169889 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34696952558 / 1000000000000) (-34696952526 / 1000000000000), orderedInterval (-7268615811 / 1000000000000) (-7268615780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2296699370835831 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1616566048 / 1000000000000) (-1616566047 / 1000000000000), orderedInterval (-33257321670 / 1000000000000) (-33257321669 / 1000000000000)))) (orderedInterval (-3455256788 / 1000000000000) (-3455256745 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1914748492456839 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33875067276 / 1000000000000) (33875094509 / 1000000000000), orderedInterval (-13541213940 / 1000000000000) (-13541186708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1691738361581619 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14940868224 / 1000000000000) (14940868429 / 1000000000000), orderedInterval (-35822903743 / 1000000000000) (-35822903539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (490331715856281 / 800000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28563784080 / 1000000000000) (-28563784078 / 1000000000000), orderedInterval (-14902719594 / 1000000000000) (-14902719593 / 1000000000000)))) (orderedInterval (-1195183869 / 1000000000000) (-1195183511 / 1000000000000))) = true
  rfl'

theorem compactCertificate460_chunkChecks0_2 :
    compactCertificate460.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1356283330802907 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23157988166 / 1000000000000) (23157988167 / 1000000000000), orderedInterval (36588939040 / 1000000000000) (36588939041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1149736399948227 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34003935138 / 1000000000000) (-34003896362 / 1000000000000), orderedInterval (32594816334 / 1000000000000) (32594855109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (719451655114881 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-59492263115 / 1000000000000) (-59492263050 / 1000000000000), orderedInterval (524684149 / 1000000000000) (524684214 / 1000000000000)))) (orderedInterval (-3714955032 / 1000000000000) (-3714952751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (386923492908927 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-10163088606 / 1000000000000) (-10163088605 / 1000000000000), orderedInterval (-80434406602 / 1000000000000) (-80434406601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1050572550587781 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-22109028712 / 1000000000000) (-22109027360 / 1000000000000), orderedInterval (44031746077 / 1000000000000) (44031747430 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1434467001617637 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40117682921 / 1000000000000) (40117682924 / 1000000000000), orderedInterval (12819599702 / 1000000000000) (12819599705 / 1000000000000)))) (orderedInterval (-2385326833 / 1000000000000) (-2385326763 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (606548344885119 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64698296249 / 1000000000000) (64698296354 / 1000000000000), orderedInterval (-3737475024 / 1000000000000) (-3737474919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2465585347400799 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31816491640 / 1000000000000) (31816491821 / 1000000000000), orderedInterval (4504055747 / 1000000000000) (4504055927 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1646896746819441 / 4000000000000) 0 (IntervalRat.scale (663 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32226842228 / 1000000000000) (-32226842227 / 1000000000000), orderedInterval (-22492152819 / 1000000000000) (-22492152818 / 1000000000000)))) (orderedInterval (3846714016 / 1000000000000) (3846714124 / 1000000000000))) = true
  rfl'

theorem compactCertificate460_chunkChecks0 :
    compactCertificate460.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate460.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate460_chunkChecks0_0
    compactCertificate460_chunkChecks0_1 compactCertificate460_chunkChecks0_2

theorem compactCertificate460_chunkChecks1_0 :
    compactCertificate460.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (663 / 2) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-29020943875 / 1000000000000) (-29020929450 / 1000000000000), orderedInterval (32879829060 / 1000000000000) (32879843486 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (976725598458363 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-3975668055 / 1000000000000) (-3975668048 / 1000000000000), orderedInterval (50913529695 / 1000000000000) (50913529702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (315852990447579 / 800000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-9519839255 / 1000000000000) (-9519839228 / 1000000000000), orderedInterval (39022561986 / 1000000000000) (39022562013 / 1000000000000)))) (orderedInterval (16109120685 / 1000000000000) (16109126432 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (285006093641841 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (20762715160 / 1000000000000) (20762715373 / 1000000000000), orderedInterval (-92362457654 / 1000000000000) (-92362457442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (765566456945277 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29612912999 / 1000000000000) (-29612912998 / 1000000000000), orderedInterval (-49413532493 / 1000000000000) (-49413532492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2078661854491209 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30425818237 / 1000000000000) (-30425709316 / 1000000000000), orderedInterval (17330358494 / 1000000000000) (17330467415 / 1000000000000)))) (orderedInterval (-2757591458 / 1000000000000) (-2757579274 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1531132913891217 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11817645001 / 1000000000000) (11817645002 / 1000000000000), orderedInterval (39016324595 / 1000000000000) (39016324596 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2623622345277141 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3046054238 / 1000000000000) (-3046054237 / 1000000000000), orderedInterval (-31002814518 / 1000000000000) (-31002814517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1932548344885119 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4235848663 / 1000000000000) (4235848664 / 1000000000000), orderedInterval (36047490667 / 1000000000000) (36047490668 / 1000000000000)))) (orderedInterval (3161742722 / 1000000000000) (3161742755 / 1000000000000))) = true
  rfl'

theorem compactCertificate460_chunkChecks1_1 :
    compactCertificate460.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2965026138164337 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17168159899 / 1000000000000) (17168159900 / 1000000000000), orderedInterval (23739061904 / 1000000000000) (23739061905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1711858639023273 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38452623535 / 1000000000000) (38452623652 / 1000000000000), orderedInterval (2946218345 / 1000000000000) (2946218462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3037723195196157 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-1429409374 / 1000000000000) (-1429409373 / 1000000000000), orderedInterval (28918797143 / 1000000000000) (28918797144 / 1000000000000)))) (orderedInterval (267559996 / 1000000000000) (267560280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2838235052041233 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10103217136 / 1000000000000) (10103217137 / 1000000000000), orderedInterval (28190935887 / 1000000000000) (28190935888 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2025498457169889 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34696952558 / 1000000000000) (-34696952526 / 1000000000000), orderedInterval (-7268615811 / 1000000000000) (-7268615780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2296699370835831 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1616566048 / 1000000000000) (-1616566047 / 1000000000000), orderedInterval (-33257321670 / 1000000000000) (-33257321669 / 1000000000000)))) (orderedInterval (-1847770577 / 1000000000000) (-1847770508 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1914748492456839 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33875067276 / 1000000000000) (33875094509 / 1000000000000), orderedInterval (-13541213940 / 1000000000000) (-13541186708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1691738361581619 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14940868224 / 1000000000000) (14940868429 / 1000000000000), orderedInterval (-35822903743 / 1000000000000) (-35822903539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (490331715856281 / 800000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28563784080 / 1000000000000) (-28563784078 / 1000000000000), orderedInterval (-14902719594 / 1000000000000) (-14902719593 / 1000000000000)))) (orderedInterval (1684180450 / 1000000000000) (1684180965 / 1000000000000))) = true
  rfl'

theorem compactCertificate460_chunkChecks1_2 :
    compactCertificate460.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1356283330802907 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23157988166 / 1000000000000) (23157988167 / 1000000000000), orderedInterval (36588939040 / 1000000000000) (36588939041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1149736399948227 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34003935138 / 1000000000000) (-34003896362 / 1000000000000), orderedInterval (32594816334 / 1000000000000) (32594855109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (719451655114881 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-59492263115 / 1000000000000) (-59492263050 / 1000000000000), orderedInterval (524684149 / 1000000000000) (524684214 / 1000000000000)))) (orderedInterval (-7574268045 / 1000000000000) (-7574266063 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (386923492908927 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-10163088606 / 1000000000000) (-10163088605 / 1000000000000), orderedInterval (-80434406602 / 1000000000000) (-80434406601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1050572550587781 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-22109028712 / 1000000000000) (-22109027360 / 1000000000000), orderedInterval (44031746077 / 1000000000000) (44031747430 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1434467001617637 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40117682921 / 1000000000000) (40117682924 / 1000000000000), orderedInterval (12819599702 / 1000000000000) (12819599705 / 1000000000000)))) (orderedInterval (-1420908907 / 1000000000000) (-1420908846 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (606548344885119 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64698296249 / 1000000000000) (64698296354 / 1000000000000), orderedInterval (-3737475024 / 1000000000000) (-3737474919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2465585347400799 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31816491640 / 1000000000000) (31816491821 / 1000000000000), orderedInterval (4504055747 / 1000000000000) (4504055927 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1646896746819441 / 4000000000000) 1 (IntervalRat.scale (663 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32226842228 / 1000000000000) (-32226842227 / 1000000000000), orderedInterval (-22492152819 / 1000000000000) (-22492152818 / 1000000000000)))) (orderedInterval (4549370750 / 1000000000000) (4549370907 / 1000000000000))) = true
  rfl'

theorem compactCertificate460_chunkChecks1 :
    compactCertificate460.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate460.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate460_chunkChecks1_0
    compactCertificate460_chunkChecks1_1 compactCertificate460_chunkChecks1_2

theorem compactCertificate460_chunkChecks2_0 :
    compactCertificate460.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (663 / 2) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-29020943875 / 1000000000000) (-29020929450 / 1000000000000), orderedInterval (32879829060 / 1000000000000) (32879843486 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (976725598458363 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-3975668055 / 1000000000000) (-3975668048 / 1000000000000), orderedInterval (50913529695 / 1000000000000) (50913529702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (315852990447579 / 800000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-9519839255 / 1000000000000) (-9519839228 / 1000000000000), orderedInterval (39022561986 / 1000000000000) (39022562013 / 1000000000000)))) (orderedInterval (12266797833 / 1000000000000) (12266803600 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (285006093641841 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (20762715160 / 1000000000000) (20762715373 / 1000000000000), orderedInterval (-92362457654 / 1000000000000) (-92362457442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (765566456945277 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29612912999 / 1000000000000) (-29612912998 / 1000000000000), orderedInterval (-49413532493 / 1000000000000) (-49413532492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2078661854491209 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30425818237 / 1000000000000) (-30425709316 / 1000000000000), orderedInterval (17330358494 / 1000000000000) (17330467415 / 1000000000000)))) (orderedInterval (-4936186362 / 1000000000000) (-4936167234 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1531132913891217 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11817645001 / 1000000000000) (11817645002 / 1000000000000), orderedInterval (39016324595 / 1000000000000) (39016324596 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2623622345277141 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3046054238 / 1000000000000) (-3046054237 / 1000000000000), orderedInterval (-31002814518 / 1000000000000) (-31002814517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1932548344885119 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4235848663 / 1000000000000) (4235848664 / 1000000000000), orderedInterval (36047490667 / 1000000000000) (36047490668 / 1000000000000)))) (orderedInterval (-594796006 / 1000000000000) (-594795947 / 1000000000000))) = true
  rfl'

theorem compactCertificate460_chunkChecks2_1 :
    compactCertificate460.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2965026138164337 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17168159899 / 1000000000000) (17168159900 / 1000000000000), orderedInterval (23739061904 / 1000000000000) (23739061905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1711858639023273 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38452623535 / 1000000000000) (38452623652 / 1000000000000), orderedInterval (2946218345 / 1000000000000) (2946218462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3037723195196157 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-1429409374 / 1000000000000) (-1429409373 / 1000000000000), orderedInterval (28918797143 / 1000000000000) (28918797144 / 1000000000000)))) (orderedInterval (11570120849 / 1000000000000) (11570121449 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2838235052041233 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10103217136 / 1000000000000) (10103217137 / 1000000000000), orderedInterval (28190935887 / 1000000000000) (28190935888 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2025498457169889 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34696952558 / 1000000000000) (-34696952526 / 1000000000000), orderedInterval (-7268615811 / 1000000000000) (-7268615780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2296699370835831 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1616566048 / 1000000000000) (-1616566047 / 1000000000000), orderedInterval (-33257321670 / 1000000000000) (-33257321669 / 1000000000000)))) (orderedInterval (8472442340 / 1000000000000) (8472442454 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1914748492456839 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33875067276 / 1000000000000) (33875094509 / 1000000000000), orderedInterval (-13541213940 / 1000000000000) (-13541186708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1691738361581619 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14940868224 / 1000000000000) (14940868429 / 1000000000000), orderedInterval (-35822903743 / 1000000000000) (-35822903539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (490331715856281 / 800000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28563784080 / 1000000000000) (-28563784078 / 1000000000000), orderedInterval (-14902719594 / 1000000000000) (-14902719593 / 1000000000000)))) (orderedInterval (3071071366 / 1000000000000) (3071072111 / 1000000000000))) = true
  rfl'

theorem compactCertificate460_chunkChecks2_2 :
    compactCertificate460.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1356283330802907 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23157988166 / 1000000000000) (23157988167 / 1000000000000), orderedInterval (36588939040 / 1000000000000) (36588939041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1149736399948227 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34003935138 / 1000000000000) (-34003896362 / 1000000000000), orderedInterval (32594816334 / 1000000000000) (32594855109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (719451655114881 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-59492263115 / 1000000000000) (-59492263050 / 1000000000000), orderedInterval (524684149 / 1000000000000) (524684214 / 1000000000000)))) (orderedInterval (3019903739 / 1000000000000) (3019905469 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (386923492908927 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-10163088606 / 1000000000000) (-10163088605 / 1000000000000), orderedInterval (-80434406602 / 1000000000000) (-80434406601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1050572550587781 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-22109028712 / 1000000000000) (-22109027360 / 1000000000000), orderedInterval (44031746077 / 1000000000000) (44031747430 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1434467001617637 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40117682921 / 1000000000000) (40117682924 / 1000000000000), orderedInterval (12819599702 / 1000000000000) (12819599705 / 1000000000000)))) (orderedInterval (3271601551 / 1000000000000) (3271601607 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (606548344885119 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64698296249 / 1000000000000) (64698296354 / 1000000000000), orderedInterval (-3737475024 / 1000000000000) (-3737474919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2465585347400799 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31816491640 / 1000000000000) (31816491821 / 1000000000000), orderedInterval (4504055747 / 1000000000000) (4504055927 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1646896746819441 / 4000000000000) 2 (IntervalRat.scale (663 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32226842228 / 1000000000000) (-32226842227 / 1000000000000), orderedInterval (-22492152819 / 1000000000000) (-22492152818 / 1000000000000)))) (orderedInterval (-468213246 / 1000000000000) (-468213004 / 1000000000000))) = true
  rfl'

theorem compactCertificate460_chunkChecks2 :
    compactCertificate460.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate460.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate460_chunkChecks2_0
    compactCertificate460_chunkChecks2_1 compactCertificate460_chunkChecks2_2

theorem compactCertificate460_chunkChecks3_0 :
    compactCertificate460.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (663 / 2) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-29020943875 / 1000000000000) (-29020929450 / 1000000000000), orderedInterval (32879829060 / 1000000000000) (32879843486 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (976725598458363 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-3975668055 / 1000000000000) (-3975668048 / 1000000000000), orderedInterval (50913529695 / 1000000000000) (50913529702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (315852990447579 / 800000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-9519839255 / 1000000000000) (-9519839228 / 1000000000000), orderedInterval (39022561986 / 1000000000000) (39022562013 / 1000000000000)))) (orderedInterval (-17127434272 / 1000000000000) (-17127428499 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (285006093641841 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (20762715160 / 1000000000000) (20762715373 / 1000000000000), orderedInterval (-92362457654 / 1000000000000) (-92362457442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (765566456945277 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29612912999 / 1000000000000) (-29612912998 / 1000000000000), orderedInterval (-49413532493 / 1000000000000) (-49413532492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2078661854491209 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30425818237 / 1000000000000) (-30425709316 / 1000000000000), orderedInterval (17330358494 / 1000000000000) (17330467415 / 1000000000000)))) (orderedInterval (5098206243 / 1000000000000) (5098236223 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1531132913891217 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11817645001 / 1000000000000) (11817645002 / 1000000000000), orderedInterval (39016324595 / 1000000000000) (39016324596 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2623622345277141 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3046054238 / 1000000000000) (-3046054237 / 1000000000000), orderedInterval (-31002814518 / 1000000000000) (-31002814517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1932548344885119 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4235848663 / 1000000000000) (4235848664 / 1000000000000), orderedInterval (36047490667 / 1000000000000) (36047490668 / 1000000000000)))) (orderedInterval (-10102200124 / 1000000000000) (-10102200019 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate460_chunkChecks3_1 :
    compactCertificate460.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2965026138164337 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17168159899 / 1000000000000) (17168159900 / 1000000000000), orderedInterval (23739061904 / 1000000000000) (23739061905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1711858639023273 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38452623535 / 1000000000000) (38452623652 / 1000000000000), orderedInterval (2946218345 / 1000000000000) (2946218462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3037723195196157 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-1429409374 / 1000000000000) (-1429409373 / 1000000000000), orderedInterval (28918797143 / 1000000000000) (28918797144 / 1000000000000)))) (orderedInterval (-2770710628 / 1000000000000) (-2770709326 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2838235052041233 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10103217136 / 1000000000000) (10103217137 / 1000000000000), orderedInterval (28190935887 / 1000000000000) (28190935888 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2025498457169889 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34696952558 / 1000000000000) (-34696952526 / 1000000000000), orderedInterval (-7268615811 / 1000000000000) (-7268615780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2296699370835831 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1616566048 / 1000000000000) (-1616566047 / 1000000000000), orderedInterval (-33257321670 / 1000000000000) (-33257321669 / 1000000000000)))) (orderedInterval (6540606061 / 1000000000000) (6540606252 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1914748492456839 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33875067276 / 1000000000000) (33875094509 / 1000000000000), orderedInterval (-13541213940 / 1000000000000) (-13541186708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1691738361581619 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14940868224 / 1000000000000) (14940868429 / 1000000000000), orderedInterval (-35822903743 / 1000000000000) (-35822903539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (490331715856281 / 800000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28563784080 / 1000000000000) (-28563784078 / 1000000000000), orderedInterval (-14902719594 / 1000000000000) (-14902719593 / 1000000000000)))) (orderedInterval (-1383977664 / 1000000000000) (-1383976586 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate460_chunkChecks3_2 :
    compactCertificate460.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1356283330802907 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23157988166 / 1000000000000) (23157988167 / 1000000000000), orderedInterval (36588939040 / 1000000000000) (36588939041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1149736399948227 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34003935138 / 1000000000000) (-34003896362 / 1000000000000), orderedInterval (32594816334 / 1000000000000) (32594855109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (719451655114881 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-59492263115 / 1000000000000) (-59492263050 / 1000000000000), orderedInterval (524684149 / 1000000000000) (524684214 / 1000000000000)))) (orderedInterval (7451061907 / 1000000000000) (7451063415 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (386923492908927 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-10163088606 / 1000000000000) (-10163088605 / 1000000000000), orderedInterval (-80434406602 / 1000000000000) (-80434406601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1050572550587781 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-22109028712 / 1000000000000) (-22109027360 / 1000000000000), orderedInterval (44031746077 / 1000000000000) (44031747430 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1434467001617637 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40117682921 / 1000000000000) (40117682924 / 1000000000000), orderedInterval (12819599702 / 1000000000000) (12819599705 / 1000000000000)))) (orderedInterval (1693864596 / 1000000000000) (1693864648 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (606548344885119 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64698296249 / 1000000000000) (64698296354 / 1000000000000), orderedInterval (-3737475024 / 1000000000000) (-3737474919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2465585347400799 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31816491640 / 1000000000000) (31816491821 / 1000000000000), orderedInterval (4504055747 / 1000000000000) (4504055927 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1646896746819441 / 4000000000000) 3 (IntervalRat.scale (663 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32226842228 / 1000000000000) (-32226842227 / 1000000000000), orderedInterval (-22492152819 / 1000000000000) (-22492152818 / 1000000000000)))) (orderedInterval (-5724605197 / 1000000000000) (-5724604808 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate460_chunkChecks3 :
    compactCertificate460.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate460.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate460_chunkChecks3_0
    compactCertificate460_chunkChecks3_1 compactCertificate460_chunkChecks3_2

theorem compactCertificate460_chunkChecks4_0 :
    compactCertificate460.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (663 / 2) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-29020943875 / 1000000000000) (-29020929450 / 1000000000000), orderedInterval (32879829060 / 1000000000000) (32879843486 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (976725598458363 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-3975668055 / 1000000000000) (-3975668048 / 1000000000000), orderedInterval (50913529695 / 1000000000000) (50913529702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (315852990447579 / 800000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-9519839255 / 1000000000000) (-9519839228 / 1000000000000), orderedInterval (39022561986 / 1000000000000) (39022562013 / 1000000000000)))) (orderedInterval (-12534367838 / 1000000000000) (-12534362042 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (285006093641841 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (20762715160 / 1000000000000) (20762715373 / 1000000000000), orderedInterval (-92362457654 / 1000000000000) (-92362457442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (765566456945277 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-29612912999 / 1000000000000) (-29612912998 / 1000000000000), orderedInterval (-49413532493 / 1000000000000) (-49413532492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2078661854491209 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30425818237 / 1000000000000) (-30425709316 / 1000000000000), orderedInterval (17330358494 / 1000000000000) (17330467415 / 1000000000000)))) (orderedInterval (12910539451 / 1000000000000) (12910586536 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1531132913891217 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11817645001 / 1000000000000) (11817645002 / 1000000000000), orderedInterval (39016324595 / 1000000000000) (39016324596 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2623622345277141 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3046054238 / 1000000000000) (-3046054237 / 1000000000000), orderedInterval (-31002814518 / 1000000000000) (-31002814517 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1932548344885119 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4235848663 / 1000000000000) (4235848664 / 1000000000000), orderedInterval (36047490667 / 1000000000000) (36047490668 / 1000000000000)))) (orderedInterval (1962746520 / 1000000000000) (1962746715 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate460_chunkChecks4_1 :
    compactCertificate460.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2965026138164337 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17168159899 / 1000000000000) (17168159900 / 1000000000000), orderedInterval (23739061904 / 1000000000000) (23739061905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1711858639023273 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38452623535 / 1000000000000) (38452623652 / 1000000000000), orderedInterval (2946218345 / 1000000000000) (2946218462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3037723195196157 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-1429409374 / 1000000000000) (-1429409373 / 1000000000000), orderedInterval (28918797143 / 1000000000000) (28918797144 / 1000000000000)))) (orderedInterval (-73930400477 / 1000000000000) (-73930397605 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2838235052041233 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (10103217136 / 1000000000000) (10103217137 / 1000000000000), orderedInterval (28190935887 / 1000000000000) (28190935888 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2025498457169889 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34696952558 / 1000000000000) (-34696952526 / 1000000000000), orderedInterval (-7268615811 / 1000000000000) (-7268615780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2296699370835831 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-1616566048 / 1000000000000) (-1616566047 / 1000000000000), orderedInterval (-33257321670 / 1000000000000) (-33257321669 / 1000000000000)))) (orderedInterval (-21657730821 / 1000000000000) (-21657730491 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1914748492456839 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33875067276 / 1000000000000) (33875094509 / 1000000000000), orderedInterval (-13541213940 / 1000000000000) (-13541186708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1691738361581619 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14940868224 / 1000000000000) (14940868429 / 1000000000000), orderedInterval (-35822903743 / 1000000000000) (-35822903539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (490331715856281 / 800000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28563784080 / 1000000000000) (-28563784078 / 1000000000000), orderedInterval (-14902719594 / 1000000000000) (-14902719593 / 1000000000000)))) (orderedInterval (-9102689116 / 1000000000000) (-9102687544 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate460_chunkChecks4_2 :
    compactCertificate460.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1356283330802907 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23157988166 / 1000000000000) (23157988167 / 1000000000000), orderedInterval (36588939040 / 1000000000000) (36588939041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1149736399948227 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34003935138 / 1000000000000) (-34003896362 / 1000000000000), orderedInterval (32594816334 / 1000000000000) (32594855109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (719451655114881 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-59492263115 / 1000000000000) (-59492263050 / 1000000000000), orderedInterval (524684149 / 1000000000000) (524684214 / 1000000000000)))) (orderedInterval (-3177747366 / 1000000000000) (-3177746046 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (386923492908927 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-10163088606 / 1000000000000) (-10163088605 / 1000000000000), orderedInterval (-80434406602 / 1000000000000) (-80434406601 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1050572550587781 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-22109028712 / 1000000000000) (-22109027360 / 1000000000000), orderedInterval (44031746077 / 1000000000000) (44031747430 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1434467001617637 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (40117682921 / 1000000000000) (40117682924 / 1000000000000), orderedInterval (12819599702 / 1000000000000) (12819599705 / 1000000000000)))) (orderedInterval (-4022071543 / 1000000000000) (-4022071492 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (606548344885119 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64698296249 / 1000000000000) (64698296354 / 1000000000000), orderedInterval (-3737475024 / 1000000000000) (-3737474919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2465585347400799 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31816491640 / 1000000000000) (31816491821 / 1000000000000), orderedInterval (4504055747 / 1000000000000) (4504055927 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1646896746819441 / 4000000000000) 4 (IntervalRat.scale (663 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-32226842228 / 1000000000000) (-32226842227 / 1000000000000), orderedInterval (-22492152819 / 1000000000000) (-22492152818 / 1000000000000)))) (orderedInterval (-16519672640 / 1000000000000) (-16519671991 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate460_chunkChecks4 :
    compactCertificate460.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate460.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate460_chunkChecks4_0
    compactCertificate460_chunkChecks4_1 compactCertificate460_chunkChecks4_2

theorem compactCertificate460_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate460.chunkCheck r b = true :=
  compactCertificate460.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate460_chunkChecks0
    · exact compactCertificate460_chunkChecks1
    · exact compactCertificate460_chunkChecks2
    · exact compactCertificate460_chunkChecks3
    · exact compactCertificate460_chunkChecks4)

theorem compactCertificate460_coefficient0 :
    compactCertificate460.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate460_coefficient1 :
    compactCertificate460.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate460_coefficient2 :
    compactCertificate460.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate460_coefficient3 :
    compactCertificate460.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate460_coefficient4 :
    compactCertificate460.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate460_coefficients : ∀ r : Fin 5,
    compactCertificate460.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate460_coefficient0
  · exact compactCertificate460_coefficient1
  · exact compactCertificate460_coefficient2
  · exact compactCertificate460_coefficient3
  · exact compactCertificate460_coefficient4

theorem compactCertificate460_lower : (1 : ℚ) ≤ compactCertificate460.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate460, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate460_proves {t : ℝ} (ht : t ∈ compactCertificate460.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate460.proves compactCertificate460_states compactCertificate460_chunks
    compactCertificate460_coefficients compactCertificate460_lower ht

end Erdos232
