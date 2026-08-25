/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate278 : CompactCertificate where
  left := 152
  right := 153
  center := 305 / 2
  grid := fun i =>
    match i.val with
    | 0 => 49
    | 1 => 36
    | 2 => 58
    | 3 => 10
    | 4 => 28
    | 5 => 76
    | 6 => 56
    | 7 => 96
    | 8 => 71
    | 9 => 109
    | 10 => 63
    | 11 => 111
    | 12 => 104
    | 13 => 74
    | 14 => 84
    | 15 => 70
    | 16 => 62
    | 17 => 90
    | 18 => 50
    | 19 => 42
    | 20 => 26
    | 21 => 14
    | 22 => 38
    | 23 => 53
    | 24 => 22
    | 25 => 90
    | _ => 60
  point := fun i =>
    match i.val with
    | 0 => 305 / 2
    | 1 => 89864647821961 / 800000000000
    | 2 => 29060380719913 / 160000000000
    | 3 => 26222280108827 / 800000000000
    | 4 => 70436732841119 / 800000000000
    | 5 => 191249431559523 / 800000000000
    | 6 => 140873465682299 / 800000000000
    | 7 => 241389084557927 / 800000000000
    | 8 => 177806107146293 / 800000000000
    | 9 => 272800293254939 / 800000000000
    | 10 => 157501322745731 / 800000000000
    | 11 => 279488861096479 / 800000000000
    | 12 => 261134748377851 / 800000000000
    | 13 => 186358078261483 / 800000000000
    | 14 => 211310198523357 / 800000000000
    | 15 => 176168413333133 / 800000000000
    | 16 => 155650135831793 / 800000000000
    | 17 => 45113476119507 / 160000000000
    | 18 => 124786249138729 / 800000000000
    | 19 => 105782685364769 / 800000000000
    | 20 => 66193892853707 / 800000000000
    | 21 => 35599295727669 / 800000000000
    | 22 => 96659012950007 / 800000000000
    | 23 => 131979618550039 / 800000000000
    | 24 => 55806107146293 / 800000000000
    | 25 => 226848727287253 / 800000000000
    | _ => 151524436736027 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (39279275589 / 1000000000000) (39279293078 / 1000000000000), orderedInterval (-51428884383 / 1000000000000) (-51428866893 / 1000000000000))
    | 1 => (orderedInterval (1336905154 / 1000000000000) (1336905158 / 1000000000000), orderedInterval (75264458102 / 1000000000000) (75264458107 / 1000000000000))
    | 2 => (orderedInterval (11745446512 / 1000000000000) (11745446513 / 1000000000000), orderedInterval (57994761322 / 1000000000000) (57994761323 / 1000000000000))
    | 3 => (orderedInterval (117119146091 / 1000000000000) (117119166811 / 1000000000000), orderedInterval (-77313813651 / 1000000000000) (-77313792931 / 1000000000000))
    | 4 => (orderedInterval (64733946610 / 1000000000000) (64733946611 / 1000000000000), orderedInterval (54768959421 / 1000000000000) (54768959422 / 1000000000000))
    | 5 => (orderedInterval (45648716584 / 1000000000000) (45648716585 / 1000000000000), orderedInterval (23970766927 / 1000000000000) (23970766928 / 1000000000000))
    | 6 => (orderedInterval (48814745882 / 1000000000000) (48814745883 / 1000000000000), orderedInterval (34966770728 / 1000000000000) (34966770729 / 1000000000000))
    | 7 => (orderedInterval (36778155172 / 1000000000000) (36778155173 / 1000000000000), orderedInterval (27456702443 / 1000000000000) (27456702444 / 1000000000000))
    | 8 => (orderedInterval (567761218 / 1000000000000) (567761221 / 1000000000000), orderedInterval (-53517792742 / 1000000000000) (-53517792738 / 1000000000000))
    | 9 => (orderedInterval (26086865003 / 1000000000000) (26086871459 / 1000000000000), orderedInterval (-34482324038 / 1000000000000) (-34482317581 / 1000000000000))
    | 10 => (orderedInterval (14559460129 / 1000000000000) (14559460281 / 1000000000000), orderedInterval (-55006315227 / 1000000000000) (-55006315075 / 1000000000000))
    | 11 => (orderedInterval (-42261259518 / 1000000000000) (-42261259492 / 1000000000000), orderedInterval (-5958177523 / 1000000000000) (-5958177497 / 1000000000000))
    | 12 => (orderedInterval (20307617299 / 1000000000000) (20307617300 / 1000000000000), orderedInterval (39185217344 / 1000000000000) (39185217345 / 1000000000000))
    | 13 => (orderedInterval (49685395465 / 1000000000000) (49685395467 / 1000000000000), orderedInterval (16148961686 / 1000000000000) (16148961687 / 1000000000000))
    | 14 => (orderedInterval (42059774959 / 1000000000000) (42059774960 / 1000000000000), orderedInterval (25241407496 / 1000000000000) (25241407497 / 1000000000000))
    | 15 => (orderedInterval (47518238870 / 1000000000000) (47518238871 / 1000000000000), orderedInterval (25051056148 / 1000000000000) (25051056149 / 1000000000000))
    | 16 => (orderedInterval (30804367905 / 1000000000000) (30804367906 / 1000000000000), orderedInterval (48119909377 / 1000000000000) (48119909378 / 1000000000000))
    | 17 => (orderedInterval (39997851 / 1000000000000) (39997853 / 1000000000000), orderedInterval (47516719093 / 1000000000000) (47516719094 / 1000000000000))
    | 18 => (orderedInterval (-19624033445 / 1000000000000) (-19624033043 / 1000000000000), orderedInterval (60859778549 / 1000000000000) (60859778950 / 1000000000000))
    | 19 => (orderedInterval (60729553178 / 1000000000000) (60729553179 / 1000000000000), orderedInterval (33333008393 / 1000000000000) (33333008394 / 1000000000000))
    | 20 => (orderedInterval (84441417501 / 1000000000000) (84441418642 / 1000000000000), orderedInterval (-24248975481 / 1000000000000) (-24248974340 / 1000000000000))
    | 21 => (orderedInterval (115227906235 / 1000000000000) (115227906236 / 1000000000000), orderedInterval (30769476361 / 1000000000000) (30769476362 / 1000000000000))
    | 22 => (orderedInterval (57485110839 / 1000000000000) (57485175419 / 1000000000000), orderedInterval (-44559932825 / 1000000000000) (-44559868245 / 1000000000000))
    | 23 => (orderedInterval (42126784851 / 1000000000000) (42126823480 / 1000000000000), orderedInterval (-45781075118 / 1000000000000) (-45781036490 / 1000000000000))
    | 24 => (orderedInterval (94532837729 / 1000000000000) (94532837732 / 1000000000000), orderedInterval (13087785116 / 1000000000000) (13087785119 / 1000000000000))
    | 25 => (orderedInterval (47358492108 / 1000000000000) (47358492300 / 1000000000000), orderedInterval (-1586760138 / 1000000000000) (-1586759945 / 1000000000000))
    | _ => (orderedInterval (57530662411 / 1000000000000) (57530662757 / 1000000000000), orderedInterval (-7318315306 / 1000000000000) (-7318314960 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (16270623342 / 1000000000000) (16270630285 / 1000000000000)
      | 1 => orderedInterval (-2152261390 / 1000000000000) (-2152261146 / 1000000000000)
      | 2 => orderedInterval (-1120663791 / 1000000000000) (-1120663782 / 1000000000000)
      | 3 => orderedInterval (-9564272974 / 1000000000000) (-9564271751 / 1000000000000)
      | 4 => orderedInterval (4118931535 / 1000000000000) (4118931554 / 1000000000000)
      | 5 => orderedInterval (-1213082576 / 1000000000000) (-1213082560 / 1000000000000)
      | 6 => orderedInterval (2449457738 / 1000000000000) (2449457879 / 1000000000000)
      | 7 => orderedInterval (-6660407170 / 1000000000000) (-6660402725 / 1000000000000)
      | _ => orderedInterval (-14079468947 / 1000000000000) (-14079468824 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-15814814225 / 1000000000000) (-15814807280 / 1000000000000)
      | 1 => orderedInterval (-1336514165 / 1000000000000) (-1336514095 / 1000000000000)
      | 2 => orderedInterval (-3560689789 / 1000000000000) (-3560689773 / 1000000000000)
      | 3 => orderedInterval (6498762415 / 1000000000000) (6498765130 / 1000000000000)
      | 4 => orderedInterval (597242723 / 1000000000000) (597242753 / 1000000000000)
      | 5 => orderedInterval (-846142195 / 1000000000000) (-846142173 / 1000000000000)
      | 6 => orderedInterval (-12017438229 / 1000000000000) (-12017438107 / 1000000000000)
      | 7 => orderedInterval (4430764828 / 1000000000000) (4430769208 / 1000000000000)
      | _ => orderedInterval (1981668956 / 1000000000000) (1981669126 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-16449659250 / 1000000000000) (-16449652258 / 1000000000000)
      | 1 => orderedInterval (7254337609 / 1000000000000) (7254337650 / 1000000000000)
      | 2 => orderedInterval (4435156341 / 1000000000000) (4435156369 / 1000000000000)
      | 3 => orderedInterval (52865564363 / 1000000000000) (52865570423 / 1000000000000)
      | 4 => orderedInterval (-8648639208 / 1000000000000) (-8648639158 / 1000000000000)
      | 5 => orderedInterval (1727270023 / 1000000000000) (1727270056 / 1000000000000)
      | 6 => orderedInterval (-1428959960 / 1000000000000) (-1428959846 / 1000000000000)
      | 7 => orderedInterval (4749097638 / 1000000000000) (4749102068 / 1000000000000)
      | _ => orderedInterval (29847333911 / 1000000000000) (29847334154 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (14462112798 / 1000000000000) (14462119792 / 1000000000000)
      | 1 => orderedInterval (6123814039 / 1000000000000) (6123814085 / 1000000000000)
      | 2 => orderedInterval (10534646192 / 1000000000000) (10534646241 / 1000000000000)
      | 3 => orderedInterval (-49896857165 / 1000000000000) (-49896843642 / 1000000000000)
      | 4 => orderedInterval (2214837317 / 1000000000000) (2214837401 / 1000000000000)
      | 5 => orderedInterval (-2853325394 / 1000000000000) (-2853325344 / 1000000000000)
      | 6 => orderedInterval (11777878790 / 1000000000000) (11777878898 / 1000000000000)
      | 7 => orderedInterval (-4961577568 / 1000000000000) (-4961573045 / 1000000000000)
      | _ => orderedInterval (-3664277962 / 1000000000000) (-3664277599 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (16769027471 / 1000000000000) (16769034512 / 1000000000000)
      | 1 => orderedInterval (-19417392677 / 1000000000000) (-19417392609 / 1000000000000)
      | 2 => orderedInterval (-17461744792 / 1000000000000) (-17461744701 / 1000000000000)
      | 3 => orderedInterval (-277702470367 / 1000000000000) (-277702440080 / 1000000000000)
      | 4 => orderedInterval (15939727905 / 1000000000000) (15939728051 / 1000000000000)
      | 5 => orderedInterval (-2235338931 / 1000000000000) (-2235338852 / 1000000000000)
      | 6 => orderedInterval (1575227182 / 1000000000000) (1575227290 / 1000000000000)
      | 7 => orderedInterval (-4885799118 / 1000000000000) (-4885794410 / 1000000000000)
      | _ => orderedInterval (-71693722554 / 1000000000000) (-71693721992 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-11951144233 / 1000000000000) (-11951131070 / 1000000000000)
    | 1 => orderedInterval (-20067159681 / 1000000000000) (-20067145211 / 1000000000000)
    | 2 => orderedInterval (74351501467 / 1000000000000) (74351519458 / 1000000000000)
    | 3 => orderedInterval (-16262748953 / 1000000000000) (-16262723213 / 1000000000000)
    | _ => orderedInterval (-359112485881 / 1000000000000) (-359112442791 / 1000000000000)

theorem compactCertificate278_stateChecks0 :
    compactCertificate278.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (305 / 2)) (orderedInterval (39279275589 / 1000000000000) (39279293078 / 1000000000000), orderedInterval (-51428884383 / 1000000000000) (-51428866893 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (89864647821961 / 800000000000)) (orderedInterval (1336905154 / 1000000000000) (1336905158 / 1000000000000), orderedInterval (75264458102 / 1000000000000) (75264458107 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (29060380719913 / 160000000000)) (orderedInterval (11745446512 / 1000000000000) (11745446513 / 1000000000000), orderedInterval (57994761322 / 1000000000000) (57994761323 / 1000000000000))) = true
  rfl'

theorem compactCertificate278_stateChecks1 :
    compactCertificate278.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (26222280108827 / 800000000000)) (orderedInterval (117119146091 / 1000000000000) (117119166811 / 1000000000000), orderedInterval (-77313813651 / 1000000000000) (-77313792931 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (70436732841119 / 800000000000)) (orderedInterval (64733946610 / 1000000000000) (64733946611 / 1000000000000), orderedInterval (54768959421 / 1000000000000) (54768959422 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (191249431559523 / 800000000000)) (orderedInterval (45648716584 / 1000000000000) (45648716585 / 1000000000000), orderedInterval (23970766927 / 1000000000000) (23970766928 / 1000000000000))) = true
  rfl'

theorem compactCertificate278_stateChecks2 :
    compactCertificate278.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (140873465682299 / 800000000000)) (orderedInterval (48814745882 / 1000000000000) (48814745883 / 1000000000000), orderedInterval (34966770728 / 1000000000000) (34966770729 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (241389084557927 / 800000000000)) (orderedInterval (36778155172 / 1000000000000) (36778155173 / 1000000000000), orderedInterval (27456702443 / 1000000000000) (27456702444 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (177806107146293 / 800000000000)) (orderedInterval (567761218 / 1000000000000) (567761221 / 1000000000000), orderedInterval (-53517792742 / 1000000000000) (-53517792738 / 1000000000000))) = true
  rfl'

theorem compactCertificate278_stateChecks3 :
    compactCertificate278.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (272800293254939 / 800000000000)) (orderedInterval (26086865003 / 1000000000000) (26086871459 / 1000000000000), orderedInterval (-34482324038 / 1000000000000) (-34482317581 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (157501322745731 / 800000000000)) (orderedInterval (14559460129 / 1000000000000) (14559460281 / 1000000000000), orderedInterval (-55006315227 / 1000000000000) (-55006315075 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (279488861096479 / 800000000000)) (orderedInterval (-42261259518 / 1000000000000) (-42261259492 / 1000000000000), orderedInterval (-5958177523 / 1000000000000) (-5958177497 / 1000000000000))) = true
  rfl'

theorem compactCertificate278_stateChecks4 :
    compactCertificate278.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (261134748377851 / 800000000000)) (orderedInterval (20307617299 / 1000000000000) (20307617300 / 1000000000000), orderedInterval (39185217344 / 1000000000000) (39185217345 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (186358078261483 / 800000000000)) (orderedInterval (49685395465 / 1000000000000) (49685395467 / 1000000000000), orderedInterval (16148961686 / 1000000000000) (16148961687 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (211310198523357 / 800000000000)) (orderedInterval (42059774959 / 1000000000000) (42059774960 / 1000000000000), orderedInterval (25241407496 / 1000000000000) (25241407497 / 1000000000000))) = true
  rfl'

theorem compactCertificate278_stateChecks5 :
    compactCertificate278.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (176168413333133 / 800000000000)) (orderedInterval (47518238870 / 1000000000000) (47518238871 / 1000000000000), orderedInterval (25051056148 / 1000000000000) (25051056149 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (155650135831793 / 800000000000)) (orderedInterval (30804367905 / 1000000000000) (30804367906 / 1000000000000), orderedInterval (48119909377 / 1000000000000) (48119909378 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (45113476119507 / 160000000000)) (orderedInterval (39997851 / 1000000000000) (39997853 / 1000000000000), orderedInterval (47516719093 / 1000000000000) (47516719094 / 1000000000000))) = true
  rfl'

theorem compactCertificate278_stateChecks6 :
    compactCertificate278.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (124786249138729 / 800000000000)) (orderedInterval (-19624033445 / 1000000000000) (-19624033043 / 1000000000000), orderedInterval (60859778549 / 1000000000000) (60859778950 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (105782685364769 / 800000000000)) (orderedInterval (60729553178 / 1000000000000) (60729553179 / 1000000000000), orderedInterval (33333008393 / 1000000000000) (33333008394 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (66193892853707 / 800000000000)) (orderedInterval (84441417501 / 1000000000000) (84441418642 / 1000000000000), orderedInterval (-24248975481 / 1000000000000) (-24248974340 / 1000000000000))) = true
  rfl'

theorem compactCertificate278_stateChecks7 :
    compactCertificate278.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (35599295727669 / 800000000000)) (orderedInterval (115227906235 / 1000000000000) (115227906236 / 1000000000000), orderedInterval (30769476361 / 1000000000000) (30769476362 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (96659012950007 / 800000000000)) (orderedInterval (57485110839 / 1000000000000) (57485175419 / 1000000000000), orderedInterval (-44559932825 / 1000000000000) (-44559868245 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (131979618550039 / 800000000000)) (orderedInterval (42126784851 / 1000000000000) (42126823480 / 1000000000000), orderedInterval (-45781075118 / 1000000000000) (-45781036490 / 1000000000000))) = true
  rfl'

theorem compactCertificate278_stateChecks8 :
    compactCertificate278.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (55806107146293 / 800000000000)) (orderedInterval (94532837729 / 1000000000000) (94532837732 / 1000000000000), orderedInterval (13087785116 / 1000000000000) (13087785119 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (226848727287253 / 800000000000)) (orderedInterval (47358492108 / 1000000000000) (47358492300 / 1000000000000), orderedInterval (-1586760138 / 1000000000000) (-1586759945 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (151524436736027 / 800000000000)) (orderedInterval (57530662411 / 1000000000000) (57530662757 / 1000000000000), orderedInterval (-7318315306 / 1000000000000) (-7318314960 / 1000000000000))) = true
  rfl'

theorem compactCertificate278_states : ∀ j,
    BesselStateValid (compactCertificate278.point j) (compactCertificate278.state j) :=
  compactCertificate278.statesValid_of_checks3 compactCertificate278_stateChecks0
    compactCertificate278_stateChecks1 compactCertificate278_stateChecks2
    compactCertificate278_stateChecks3 compactCertificate278_stateChecks4
    compactCertificate278_stateChecks5 compactCertificate278_stateChecks6
    compactCertificate278_stateChecks7 compactCertificate278_stateChecks8

theorem compactCertificate278_chunkChecks0_0 :
    compactCertificate278.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (305 / 2) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39279275589 / 1000000000000) (39279293078 / 1000000000000), orderedInterval (-51428884383 / 1000000000000) (-51428866893 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (89864647821961 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (1336905154 / 1000000000000) (1336905158 / 1000000000000), orderedInterval (75264458102 / 1000000000000) (75264458107 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (29060380719913 / 160000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11745446512 / 1000000000000) (11745446513 / 1000000000000), orderedInterval (57994761322 / 1000000000000) (57994761323 / 1000000000000)))) (orderedInterval (16270623342 / 1000000000000) (16270630285 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (26222280108827 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (117119146091 / 1000000000000) (117119166811 / 1000000000000), orderedInterval (-77313813651 / 1000000000000) (-77313792931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (70436732841119 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (64733946610 / 1000000000000) (64733946611 / 1000000000000), orderedInterval (54768959421 / 1000000000000) (54768959422 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (191249431559523 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (45648716584 / 1000000000000) (45648716585 / 1000000000000), orderedInterval (23970766927 / 1000000000000) (23970766928 / 1000000000000)))) (orderedInterval (-2152261390 / 1000000000000) (-2152261146 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (140873465682299 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (48814745882 / 1000000000000) (48814745883 / 1000000000000), orderedInterval (34966770728 / 1000000000000) (34966770729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (241389084557927 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36778155172 / 1000000000000) (36778155173 / 1000000000000), orderedInterval (27456702443 / 1000000000000) (27456702444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (177806107146293 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (567761218 / 1000000000000) (567761221 / 1000000000000), orderedInterval (-53517792742 / 1000000000000) (-53517792738 / 1000000000000)))) (orderedInterval (-1120663791 / 1000000000000) (-1120663782 / 1000000000000))) = true
  rfl'

theorem compactCertificate278_chunkChecks0_1 :
    compactCertificate278.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (272800293254939 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26086865003 / 1000000000000) (26086871459 / 1000000000000), orderedInterval (-34482324038 / 1000000000000) (-34482317581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (157501322745731 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14559460129 / 1000000000000) (14559460281 / 1000000000000), orderedInterval (-55006315227 / 1000000000000) (-55006315075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (279488861096479 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-42261259518 / 1000000000000) (-42261259492 / 1000000000000), orderedInterval (-5958177523 / 1000000000000) (-5958177497 / 1000000000000)))) (orderedInterval (-9564272974 / 1000000000000) (-9564271751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (261134748377851 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20307617299 / 1000000000000) (20307617300 / 1000000000000), orderedInterval (39185217344 / 1000000000000) (39185217345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (186358078261483 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (49685395465 / 1000000000000) (49685395467 / 1000000000000), orderedInterval (16148961686 / 1000000000000) (16148961687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (211310198523357 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (42059774959 / 1000000000000) (42059774960 / 1000000000000), orderedInterval (25241407496 / 1000000000000) (25241407497 / 1000000000000)))) (orderedInterval (4118931535 / 1000000000000) (4118931554 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (176168413333133 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47518238870 / 1000000000000) (47518238871 / 1000000000000), orderedInterval (25051056148 / 1000000000000) (25051056149 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (155650135831793 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30804367905 / 1000000000000) (30804367906 / 1000000000000), orderedInterval (48119909377 / 1000000000000) (48119909378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (45113476119507 / 160000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (39997851 / 1000000000000) (39997853 / 1000000000000), orderedInterval (47516719093 / 1000000000000) (47516719094 / 1000000000000)))) (orderedInterval (-1213082576 / 1000000000000) (-1213082560 / 1000000000000))) = true
  rfl'

theorem compactCertificate278_chunkChecks0_2 :
    compactCertificate278.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (124786249138729 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-19624033445 / 1000000000000) (-19624033043 / 1000000000000), orderedInterval (60859778549 / 1000000000000) (60859778950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (105782685364769 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (60729553178 / 1000000000000) (60729553179 / 1000000000000), orderedInterval (33333008393 / 1000000000000) (33333008394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (66193892853707 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (84441417501 / 1000000000000) (84441418642 / 1000000000000), orderedInterval (-24248975481 / 1000000000000) (-24248974340 / 1000000000000)))) (orderedInterval (2449457738 / 1000000000000) (2449457879 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (35599295727669 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (115227906235 / 1000000000000) (115227906236 / 1000000000000), orderedInterval (30769476361 / 1000000000000) (30769476362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (96659012950007 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (57485110839 / 1000000000000) (57485175419 / 1000000000000), orderedInterval (-44559932825 / 1000000000000) (-44559868245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (131979618550039 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42126784851 / 1000000000000) (42126823480 / 1000000000000), orderedInterval (-45781075118 / 1000000000000) (-45781036490 / 1000000000000)))) (orderedInterval (-6660407170 / 1000000000000) (-6660402725 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (55806107146293 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (94532837729 / 1000000000000) (94532837732 / 1000000000000), orderedInterval (13087785116 / 1000000000000) (13087785119 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (226848727287253 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47358492108 / 1000000000000) (47358492300 / 1000000000000), orderedInterval (-1586760138 / 1000000000000) (-1586759945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (151524436736027 / 800000000000) 0 (IntervalRat.scale (305 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57530662411 / 1000000000000) (57530662757 / 1000000000000), orderedInterval (-7318315306 / 1000000000000) (-7318314960 / 1000000000000)))) (orderedInterval (-14079468947 / 1000000000000) (-14079468824 / 1000000000000))) = true
  rfl'

theorem compactCertificate278_chunkChecks0 :
    compactCertificate278.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate278.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate278_chunkChecks0_0
    compactCertificate278_chunkChecks0_1 compactCertificate278_chunkChecks0_2

theorem compactCertificate278_chunkChecks1_0 :
    compactCertificate278.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (305 / 2) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39279275589 / 1000000000000) (39279293078 / 1000000000000), orderedInterval (-51428884383 / 1000000000000) (-51428866893 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (89864647821961 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (1336905154 / 1000000000000) (1336905158 / 1000000000000), orderedInterval (75264458102 / 1000000000000) (75264458107 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (29060380719913 / 160000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11745446512 / 1000000000000) (11745446513 / 1000000000000), orderedInterval (57994761322 / 1000000000000) (57994761323 / 1000000000000)))) (orderedInterval (-15814814225 / 1000000000000) (-15814807280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (26222280108827 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (117119146091 / 1000000000000) (117119166811 / 1000000000000), orderedInterval (-77313813651 / 1000000000000) (-77313792931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (70436732841119 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (64733946610 / 1000000000000) (64733946611 / 1000000000000), orderedInterval (54768959421 / 1000000000000) (54768959422 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (191249431559523 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (45648716584 / 1000000000000) (45648716585 / 1000000000000), orderedInterval (23970766927 / 1000000000000) (23970766928 / 1000000000000)))) (orderedInterval (-1336514165 / 1000000000000) (-1336514095 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (140873465682299 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (48814745882 / 1000000000000) (48814745883 / 1000000000000), orderedInterval (34966770728 / 1000000000000) (34966770729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (241389084557927 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36778155172 / 1000000000000) (36778155173 / 1000000000000), orderedInterval (27456702443 / 1000000000000) (27456702444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (177806107146293 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (567761218 / 1000000000000) (567761221 / 1000000000000), orderedInterval (-53517792742 / 1000000000000) (-53517792738 / 1000000000000)))) (orderedInterval (-3560689789 / 1000000000000) (-3560689773 / 1000000000000))) = true
  rfl'

theorem compactCertificate278_chunkChecks1_1 :
    compactCertificate278.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (272800293254939 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26086865003 / 1000000000000) (26086871459 / 1000000000000), orderedInterval (-34482324038 / 1000000000000) (-34482317581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (157501322745731 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14559460129 / 1000000000000) (14559460281 / 1000000000000), orderedInterval (-55006315227 / 1000000000000) (-55006315075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (279488861096479 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-42261259518 / 1000000000000) (-42261259492 / 1000000000000), orderedInterval (-5958177523 / 1000000000000) (-5958177497 / 1000000000000)))) (orderedInterval (6498762415 / 1000000000000) (6498765130 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (261134748377851 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20307617299 / 1000000000000) (20307617300 / 1000000000000), orderedInterval (39185217344 / 1000000000000) (39185217345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (186358078261483 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (49685395465 / 1000000000000) (49685395467 / 1000000000000), orderedInterval (16148961686 / 1000000000000) (16148961687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (211310198523357 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (42059774959 / 1000000000000) (42059774960 / 1000000000000), orderedInterval (25241407496 / 1000000000000) (25241407497 / 1000000000000)))) (orderedInterval (597242723 / 1000000000000) (597242753 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (176168413333133 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47518238870 / 1000000000000) (47518238871 / 1000000000000), orderedInterval (25051056148 / 1000000000000) (25051056149 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (155650135831793 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30804367905 / 1000000000000) (30804367906 / 1000000000000), orderedInterval (48119909377 / 1000000000000) (48119909378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (45113476119507 / 160000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (39997851 / 1000000000000) (39997853 / 1000000000000), orderedInterval (47516719093 / 1000000000000) (47516719094 / 1000000000000)))) (orderedInterval (-846142195 / 1000000000000) (-846142173 / 1000000000000))) = true
  rfl'

theorem compactCertificate278_chunkChecks1_2 :
    compactCertificate278.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (124786249138729 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-19624033445 / 1000000000000) (-19624033043 / 1000000000000), orderedInterval (60859778549 / 1000000000000) (60859778950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (105782685364769 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (60729553178 / 1000000000000) (60729553179 / 1000000000000), orderedInterval (33333008393 / 1000000000000) (33333008394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (66193892853707 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (84441417501 / 1000000000000) (84441418642 / 1000000000000), orderedInterval (-24248975481 / 1000000000000) (-24248974340 / 1000000000000)))) (orderedInterval (-12017438229 / 1000000000000) (-12017438107 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (35599295727669 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (115227906235 / 1000000000000) (115227906236 / 1000000000000), orderedInterval (30769476361 / 1000000000000) (30769476362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (96659012950007 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (57485110839 / 1000000000000) (57485175419 / 1000000000000), orderedInterval (-44559932825 / 1000000000000) (-44559868245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (131979618550039 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42126784851 / 1000000000000) (42126823480 / 1000000000000), orderedInterval (-45781075118 / 1000000000000) (-45781036490 / 1000000000000)))) (orderedInterval (4430764828 / 1000000000000) (4430769208 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (55806107146293 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (94532837729 / 1000000000000) (94532837732 / 1000000000000), orderedInterval (13087785116 / 1000000000000) (13087785119 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (226848727287253 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47358492108 / 1000000000000) (47358492300 / 1000000000000), orderedInterval (-1586760138 / 1000000000000) (-1586759945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (151524436736027 / 800000000000) 1 (IntervalRat.scale (305 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57530662411 / 1000000000000) (57530662757 / 1000000000000), orderedInterval (-7318315306 / 1000000000000) (-7318314960 / 1000000000000)))) (orderedInterval (1981668956 / 1000000000000) (1981669126 / 1000000000000))) = true
  rfl'

theorem compactCertificate278_chunkChecks1 :
    compactCertificate278.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate278.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate278_chunkChecks1_0
    compactCertificate278_chunkChecks1_1 compactCertificate278_chunkChecks1_2

theorem compactCertificate278_chunkChecks2_0 :
    compactCertificate278.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (305 / 2) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39279275589 / 1000000000000) (39279293078 / 1000000000000), orderedInterval (-51428884383 / 1000000000000) (-51428866893 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (89864647821961 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (1336905154 / 1000000000000) (1336905158 / 1000000000000), orderedInterval (75264458102 / 1000000000000) (75264458107 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (29060380719913 / 160000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11745446512 / 1000000000000) (11745446513 / 1000000000000), orderedInterval (57994761322 / 1000000000000) (57994761323 / 1000000000000)))) (orderedInterval (-16449659250 / 1000000000000) (-16449652258 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (26222280108827 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (117119146091 / 1000000000000) (117119166811 / 1000000000000), orderedInterval (-77313813651 / 1000000000000) (-77313792931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (70436732841119 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (64733946610 / 1000000000000) (64733946611 / 1000000000000), orderedInterval (54768959421 / 1000000000000) (54768959422 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (191249431559523 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (45648716584 / 1000000000000) (45648716585 / 1000000000000), orderedInterval (23970766927 / 1000000000000) (23970766928 / 1000000000000)))) (orderedInterval (7254337609 / 1000000000000) (7254337650 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (140873465682299 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (48814745882 / 1000000000000) (48814745883 / 1000000000000), orderedInterval (34966770728 / 1000000000000) (34966770729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (241389084557927 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36778155172 / 1000000000000) (36778155173 / 1000000000000), orderedInterval (27456702443 / 1000000000000) (27456702444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (177806107146293 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (567761218 / 1000000000000) (567761221 / 1000000000000), orderedInterval (-53517792742 / 1000000000000) (-53517792738 / 1000000000000)))) (orderedInterval (4435156341 / 1000000000000) (4435156369 / 1000000000000))) = true
  rfl'

theorem compactCertificate278_chunkChecks2_1 :
    compactCertificate278.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (272800293254939 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26086865003 / 1000000000000) (26086871459 / 1000000000000), orderedInterval (-34482324038 / 1000000000000) (-34482317581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (157501322745731 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14559460129 / 1000000000000) (14559460281 / 1000000000000), orderedInterval (-55006315227 / 1000000000000) (-55006315075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (279488861096479 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-42261259518 / 1000000000000) (-42261259492 / 1000000000000), orderedInterval (-5958177523 / 1000000000000) (-5958177497 / 1000000000000)))) (orderedInterval (52865564363 / 1000000000000) (52865570423 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (261134748377851 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20307617299 / 1000000000000) (20307617300 / 1000000000000), orderedInterval (39185217344 / 1000000000000) (39185217345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (186358078261483 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (49685395465 / 1000000000000) (49685395467 / 1000000000000), orderedInterval (16148961686 / 1000000000000) (16148961687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (211310198523357 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (42059774959 / 1000000000000) (42059774960 / 1000000000000), orderedInterval (25241407496 / 1000000000000) (25241407497 / 1000000000000)))) (orderedInterval (-8648639208 / 1000000000000) (-8648639158 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (176168413333133 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47518238870 / 1000000000000) (47518238871 / 1000000000000), orderedInterval (25051056148 / 1000000000000) (25051056149 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (155650135831793 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30804367905 / 1000000000000) (30804367906 / 1000000000000), orderedInterval (48119909377 / 1000000000000) (48119909378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (45113476119507 / 160000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (39997851 / 1000000000000) (39997853 / 1000000000000), orderedInterval (47516719093 / 1000000000000) (47516719094 / 1000000000000)))) (orderedInterval (1727270023 / 1000000000000) (1727270056 / 1000000000000))) = true
  rfl'

theorem compactCertificate278_chunkChecks2_2 :
    compactCertificate278.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (124786249138729 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-19624033445 / 1000000000000) (-19624033043 / 1000000000000), orderedInterval (60859778549 / 1000000000000) (60859778950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (105782685364769 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (60729553178 / 1000000000000) (60729553179 / 1000000000000), orderedInterval (33333008393 / 1000000000000) (33333008394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (66193892853707 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (84441417501 / 1000000000000) (84441418642 / 1000000000000), orderedInterval (-24248975481 / 1000000000000) (-24248974340 / 1000000000000)))) (orderedInterval (-1428959960 / 1000000000000) (-1428959846 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (35599295727669 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (115227906235 / 1000000000000) (115227906236 / 1000000000000), orderedInterval (30769476361 / 1000000000000) (30769476362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (96659012950007 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (57485110839 / 1000000000000) (57485175419 / 1000000000000), orderedInterval (-44559932825 / 1000000000000) (-44559868245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (131979618550039 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42126784851 / 1000000000000) (42126823480 / 1000000000000), orderedInterval (-45781075118 / 1000000000000) (-45781036490 / 1000000000000)))) (orderedInterval (4749097638 / 1000000000000) (4749102068 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (55806107146293 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (94532837729 / 1000000000000) (94532837732 / 1000000000000), orderedInterval (13087785116 / 1000000000000) (13087785119 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (226848727287253 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47358492108 / 1000000000000) (47358492300 / 1000000000000), orderedInterval (-1586760138 / 1000000000000) (-1586759945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (151524436736027 / 800000000000) 2 (IntervalRat.scale (305 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57530662411 / 1000000000000) (57530662757 / 1000000000000), orderedInterval (-7318315306 / 1000000000000) (-7318314960 / 1000000000000)))) (orderedInterval (29847333911 / 1000000000000) (29847334154 / 1000000000000))) = true
  rfl'

theorem compactCertificate278_chunkChecks2 :
    compactCertificate278.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate278.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate278_chunkChecks2_0
    compactCertificate278_chunkChecks2_1 compactCertificate278_chunkChecks2_2

theorem compactCertificate278_chunkChecks3_0 :
    compactCertificate278.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (305 / 2) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39279275589 / 1000000000000) (39279293078 / 1000000000000), orderedInterval (-51428884383 / 1000000000000) (-51428866893 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (89864647821961 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (1336905154 / 1000000000000) (1336905158 / 1000000000000), orderedInterval (75264458102 / 1000000000000) (75264458107 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (29060380719913 / 160000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11745446512 / 1000000000000) (11745446513 / 1000000000000), orderedInterval (57994761322 / 1000000000000) (57994761323 / 1000000000000)))) (orderedInterval (14462112798 / 1000000000000) (14462119792 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (26222280108827 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (117119146091 / 1000000000000) (117119166811 / 1000000000000), orderedInterval (-77313813651 / 1000000000000) (-77313792931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (70436732841119 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (64733946610 / 1000000000000) (64733946611 / 1000000000000), orderedInterval (54768959421 / 1000000000000) (54768959422 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (191249431559523 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (45648716584 / 1000000000000) (45648716585 / 1000000000000), orderedInterval (23970766927 / 1000000000000) (23970766928 / 1000000000000)))) (orderedInterval (6123814039 / 1000000000000) (6123814085 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (140873465682299 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (48814745882 / 1000000000000) (48814745883 / 1000000000000), orderedInterval (34966770728 / 1000000000000) (34966770729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (241389084557927 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36778155172 / 1000000000000) (36778155173 / 1000000000000), orderedInterval (27456702443 / 1000000000000) (27456702444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (177806107146293 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (567761218 / 1000000000000) (567761221 / 1000000000000), orderedInterval (-53517792742 / 1000000000000) (-53517792738 / 1000000000000)))) (orderedInterval (10534646192 / 1000000000000) (10534646241 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate278_chunkChecks3_1 :
    compactCertificate278.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (272800293254939 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26086865003 / 1000000000000) (26086871459 / 1000000000000), orderedInterval (-34482324038 / 1000000000000) (-34482317581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (157501322745731 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14559460129 / 1000000000000) (14559460281 / 1000000000000), orderedInterval (-55006315227 / 1000000000000) (-55006315075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (279488861096479 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-42261259518 / 1000000000000) (-42261259492 / 1000000000000), orderedInterval (-5958177523 / 1000000000000) (-5958177497 / 1000000000000)))) (orderedInterval (-49896857165 / 1000000000000) (-49896843642 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (261134748377851 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20307617299 / 1000000000000) (20307617300 / 1000000000000), orderedInterval (39185217344 / 1000000000000) (39185217345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (186358078261483 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (49685395465 / 1000000000000) (49685395467 / 1000000000000), orderedInterval (16148961686 / 1000000000000) (16148961687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (211310198523357 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (42059774959 / 1000000000000) (42059774960 / 1000000000000), orderedInterval (25241407496 / 1000000000000) (25241407497 / 1000000000000)))) (orderedInterval (2214837317 / 1000000000000) (2214837401 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (176168413333133 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47518238870 / 1000000000000) (47518238871 / 1000000000000), orderedInterval (25051056148 / 1000000000000) (25051056149 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (155650135831793 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30804367905 / 1000000000000) (30804367906 / 1000000000000), orderedInterval (48119909377 / 1000000000000) (48119909378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (45113476119507 / 160000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (39997851 / 1000000000000) (39997853 / 1000000000000), orderedInterval (47516719093 / 1000000000000) (47516719094 / 1000000000000)))) (orderedInterval (-2853325394 / 1000000000000) (-2853325344 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate278_chunkChecks3_2 :
    compactCertificate278.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (124786249138729 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-19624033445 / 1000000000000) (-19624033043 / 1000000000000), orderedInterval (60859778549 / 1000000000000) (60859778950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (105782685364769 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (60729553178 / 1000000000000) (60729553179 / 1000000000000), orderedInterval (33333008393 / 1000000000000) (33333008394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (66193892853707 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (84441417501 / 1000000000000) (84441418642 / 1000000000000), orderedInterval (-24248975481 / 1000000000000) (-24248974340 / 1000000000000)))) (orderedInterval (11777878790 / 1000000000000) (11777878898 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (35599295727669 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (115227906235 / 1000000000000) (115227906236 / 1000000000000), orderedInterval (30769476361 / 1000000000000) (30769476362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (96659012950007 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (57485110839 / 1000000000000) (57485175419 / 1000000000000), orderedInterval (-44559932825 / 1000000000000) (-44559868245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (131979618550039 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42126784851 / 1000000000000) (42126823480 / 1000000000000), orderedInterval (-45781075118 / 1000000000000) (-45781036490 / 1000000000000)))) (orderedInterval (-4961577568 / 1000000000000) (-4961573045 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (55806107146293 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (94532837729 / 1000000000000) (94532837732 / 1000000000000), orderedInterval (13087785116 / 1000000000000) (13087785119 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (226848727287253 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47358492108 / 1000000000000) (47358492300 / 1000000000000), orderedInterval (-1586760138 / 1000000000000) (-1586759945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (151524436736027 / 800000000000) 3 (IntervalRat.scale (305 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57530662411 / 1000000000000) (57530662757 / 1000000000000), orderedInterval (-7318315306 / 1000000000000) (-7318314960 / 1000000000000)))) (orderedInterval (-3664277962 / 1000000000000) (-3664277599 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate278_chunkChecks3 :
    compactCertificate278.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate278.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate278_chunkChecks3_0
    compactCertificate278_chunkChecks3_1 compactCertificate278_chunkChecks3_2

theorem compactCertificate278_chunkChecks4_0 :
    compactCertificate278.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (305 / 2) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39279275589 / 1000000000000) (39279293078 / 1000000000000), orderedInterval (-51428884383 / 1000000000000) (-51428866893 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (89864647821961 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (1336905154 / 1000000000000) (1336905158 / 1000000000000), orderedInterval (75264458102 / 1000000000000) (75264458107 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (29060380719913 / 160000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11745446512 / 1000000000000) (11745446513 / 1000000000000), orderedInterval (57994761322 / 1000000000000) (57994761323 / 1000000000000)))) (orderedInterval (16769027471 / 1000000000000) (16769034512 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (26222280108827 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (117119146091 / 1000000000000) (117119166811 / 1000000000000), orderedInterval (-77313813651 / 1000000000000) (-77313792931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (70436732841119 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (64733946610 / 1000000000000) (64733946611 / 1000000000000), orderedInterval (54768959421 / 1000000000000) (54768959422 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (191249431559523 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (45648716584 / 1000000000000) (45648716585 / 1000000000000), orderedInterval (23970766927 / 1000000000000) (23970766928 / 1000000000000)))) (orderedInterval (-19417392677 / 1000000000000) (-19417392609 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (140873465682299 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (48814745882 / 1000000000000) (48814745883 / 1000000000000), orderedInterval (34966770728 / 1000000000000) (34966770729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (241389084557927 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36778155172 / 1000000000000) (36778155173 / 1000000000000), orderedInterval (27456702443 / 1000000000000) (27456702444 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (177806107146293 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (567761218 / 1000000000000) (567761221 / 1000000000000), orderedInterval (-53517792742 / 1000000000000) (-53517792738 / 1000000000000)))) (orderedInterval (-17461744792 / 1000000000000) (-17461744701 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate278_chunkChecks4_1 :
    compactCertificate278.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (272800293254939 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26086865003 / 1000000000000) (26086871459 / 1000000000000), orderedInterval (-34482324038 / 1000000000000) (-34482317581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (157501322745731 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (14559460129 / 1000000000000) (14559460281 / 1000000000000), orderedInterval (-55006315227 / 1000000000000) (-55006315075 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (279488861096479 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-42261259518 / 1000000000000) (-42261259492 / 1000000000000), orderedInterval (-5958177523 / 1000000000000) (-5958177497 / 1000000000000)))) (orderedInterval (-277702470367 / 1000000000000) (-277702440080 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (261134748377851 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20307617299 / 1000000000000) (20307617300 / 1000000000000), orderedInterval (39185217344 / 1000000000000) (39185217345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (186358078261483 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (49685395465 / 1000000000000) (49685395467 / 1000000000000), orderedInterval (16148961686 / 1000000000000) (16148961687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (211310198523357 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (42059774959 / 1000000000000) (42059774960 / 1000000000000), orderedInterval (25241407496 / 1000000000000) (25241407497 / 1000000000000)))) (orderedInterval (15939727905 / 1000000000000) (15939728051 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (176168413333133 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47518238870 / 1000000000000) (47518238871 / 1000000000000), orderedInterval (25051056148 / 1000000000000) (25051056149 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (155650135831793 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30804367905 / 1000000000000) (30804367906 / 1000000000000), orderedInterval (48119909377 / 1000000000000) (48119909378 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (45113476119507 / 160000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (39997851 / 1000000000000) (39997853 / 1000000000000), orderedInterval (47516719093 / 1000000000000) (47516719094 / 1000000000000)))) (orderedInterval (-2235338931 / 1000000000000) (-2235338852 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate278_chunkChecks4_2 :
    compactCertificate278.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (124786249138729 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-19624033445 / 1000000000000) (-19624033043 / 1000000000000), orderedInterval (60859778549 / 1000000000000) (60859778950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (105782685364769 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (60729553178 / 1000000000000) (60729553179 / 1000000000000), orderedInterval (33333008393 / 1000000000000) (33333008394 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (66193892853707 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (84441417501 / 1000000000000) (84441418642 / 1000000000000), orderedInterval (-24248975481 / 1000000000000) (-24248974340 / 1000000000000)))) (orderedInterval (1575227182 / 1000000000000) (1575227290 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (35599295727669 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (115227906235 / 1000000000000) (115227906236 / 1000000000000), orderedInterval (30769476361 / 1000000000000) (30769476362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (96659012950007 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (57485110839 / 1000000000000) (57485175419 / 1000000000000), orderedInterval (-44559932825 / 1000000000000) (-44559868245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (131979618550039 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42126784851 / 1000000000000) (42126823480 / 1000000000000), orderedInterval (-45781075118 / 1000000000000) (-45781036490 / 1000000000000)))) (orderedInterval (-4885799118 / 1000000000000) (-4885794410 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (55806107146293 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (94532837729 / 1000000000000) (94532837732 / 1000000000000), orderedInterval (13087785116 / 1000000000000) (13087785119 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (226848727287253 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (47358492108 / 1000000000000) (47358492300 / 1000000000000), orderedInterval (-1586760138 / 1000000000000) (-1586759945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (151524436736027 / 800000000000) 4 (IntervalRat.scale (305 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (57530662411 / 1000000000000) (57530662757 / 1000000000000), orderedInterval (-7318315306 / 1000000000000) (-7318314960 / 1000000000000)))) (orderedInterval (-71693722554 / 1000000000000) (-71693721992 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate278_chunkChecks4 :
    compactCertificate278.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate278.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate278_chunkChecks4_0
    compactCertificate278_chunkChecks4_1 compactCertificate278_chunkChecks4_2

theorem compactCertificate278_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate278.chunkCheck r b = true :=
  compactCertificate278.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate278_chunkChecks0
    · exact compactCertificate278_chunkChecks1
    · exact compactCertificate278_chunkChecks2
    · exact compactCertificate278_chunkChecks3
    · exact compactCertificate278_chunkChecks4)

theorem compactCertificate278_coefficient0 :
    compactCertificate278.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate278_coefficient1 :
    compactCertificate278.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate278_coefficient2 :
    compactCertificate278.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate278_coefficient3 :
    compactCertificate278.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate278_coefficient4 :
    compactCertificate278.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate278_coefficients : ∀ r : Fin 5,
    compactCertificate278.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate278_coefficient0
  · exact compactCertificate278_coefficient1
  · exact compactCertificate278_coefficient2
  · exact compactCertificate278_coefficient3
  · exact compactCertificate278_coefficient4

theorem compactCertificate278_lower : (1 : ℚ) ≤ compactCertificate278.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate278, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate278_proves {t : ℝ} (ht : t ∈ compactCertificate278.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate278.proves compactCertificate278_states compactCertificate278_chunks
    compactCertificate278_coefficients compactCertificate278_lower ht

end Erdos232
