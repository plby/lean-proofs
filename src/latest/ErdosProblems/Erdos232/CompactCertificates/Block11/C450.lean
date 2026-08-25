/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate450 : CompactCertificate where
  left := 321
  right := 322
  center := 643 / 2
  grid := fun i =>
    match i.val with
    | 0 => 102
    | 1 => 75
    | 2 => 122
    | 3 => 22
    | 4 => 59
    | 5 => 161
    | 6 => 118
    | 7 => 203
    | 8 => 149
    | 9 => 229
    | 10 => 132
    | 11 => 235
    | 12 => 219
    | 13 => 156
    | 14 => 177
    | 15 => 148
    | 16 => 131
    | 17 => 189
    | 18 => 105
    | 19 => 89
    | 20 => 56
    | 21 => 30
    | 22 => 81
    | 23 => 111
    | 24 => 47
    | 25 => 190
    | _ => 127
  point := fun i =>
    match i.val with
    | 0 => 643 / 2
    | 1 => 947261779500343 / 4000000000000
    | 2 => 306324996768919 / 800000000000
    | 3 => 276408624753701 / 4000000000000
    | 4 => 742472446177697 / 4000000000000
    | 5 => 2015957122832349 / 4000000000000
    | 6 => 1484944892356037 / 4000000000000
    | 7 => 2544478383127001 / 4000000000000
    | 8 => 1874251260574859 / 4000000000000
    | 9 => 2875583419064357 / 4000000000000
    | 10 => 1660218861073853 / 4000000000000
    | 11 => 2946087503033377 / 4000000000000
    | 12 => 2752617101753413 / 4000000000000
    | 13 => 1964397447903829 / 4000000000000
    | 14 => 2227417338533091 / 4000000000000
    | 15 => 1856988356937779 / 4000000000000
    | 16 => 1640705530161359 / 4000000000000
    | 17 => 475540412210541 / 800000000000
    | 18 => 1315369806495127 / 4000000000000
    | 19 => 1115053552287647 / 4000000000000
    | 20 => 697748739425141 / 4000000000000
    | 21 => 375251592670347 / 4000000000000
    | 22 => 1018881070932041 / 4000000000000
    | 23 => 1391194995535657 / 4000000000000
    | 24 => 588251260574859 / 4000000000000
    | 25 => 2391208715503339 / 4000000000000
    | _ => 1597216603627301 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (42865761362 / 1000000000000) (42865765623 / 1000000000000), orderedInterval (-12011501935 / 1000000000000) (-12011497674 / 1000000000000))
    | 1 => (orderedInterval (-47549721969 / 1000000000000) (-47549710626 / 1000000000000), orderedInterval (20770973801 / 1000000000000) (20770985144 / 1000000000000))
    | 2 => (orderedInterval (16515171685 / 1000000000000) (16515171686 / 1000000000000), orderedInterval (37259121964 / 1000000000000) (37259121965 / 1000000000000))
    | 3 => (orderedInterval (66864983006 / 1000000000000) (66864983007 / 1000000000000), orderedInterval (68377050439 / 1000000000000) (68377050440 / 1000000000000))
    | 4 => (orderedInterval (-50766614659 / 1000000000000) (-50766614658 / 1000000000000), orderedInterval (-29060396609 / 1000000000000) (-29060396608 / 1000000000000))
    | 5 => (orderedInterval (30321586613 / 1000000000000) (30321682926 / 1000000000000), orderedInterval (-18570879363 / 1000000000000) (-18570783050 / 1000000000000))
    | 6 => (orderedInterval (40046151483 / 1000000000000) (40046151488 / 1000000000000), orderedInterval (10489724011 / 1000000000000) (10489724017 / 1000000000000))
    | 7 => (orderedInterval (23525468441 / 1000000000000) (23525478210 / 1000000000000), orderedInterval (-21168871113 / 1000000000000) (-21168861344 / 1000000000000))
    | 8 => (orderedInterval (-34987073961 / 1000000000000) (-34987073957 / 1000000000000), orderedInterval (-11563043557 / 1000000000000) (-11563043552 / 1000000000000))
    | 9 => (orderedInterval (-7545570806 / 1000000000000) (-7545570805 / 1000000000000), orderedInterval (-28780455049 / 1000000000000) (-28780455048 / 1000000000000))
    | 10 => (orderedInterval (35740811875 / 1000000000000) (35740811877 / 1000000000000), orderedInterval (15969906404 / 1000000000000) (15969906405 / 1000000000000))
    | 11 => (orderedInterval (24204479947 / 1000000000000) (24204500721 / 1000000000000), orderedInterval (-16704826721 / 1000000000000) (-16704805947 / 1000000000000))
    | 12 => (orderedInterval (-24394528713 / 1000000000000) (-24394528712 / 1000000000000), orderedInterval (-18148697468 / 1000000000000) (-18148697467 / 1000000000000))
    | 13 => (orderedInterval (35094796167 / 1000000000000) (35094802605 / 1000000000000), orderedInterval (-8077503773 / 1000000000000) (-8077497335 / 1000000000000))
    | 14 => (orderedInterval (-33811084366 / 1000000000000) (-33811083549 / 1000000000000), orderedInterval (260693791 / 1000000000000) (260694608 / 1000000000000))
    | 15 => (orderedInterval (2830308450 / 1000000000000) (2830308451 / 1000000000000), orderedInterval (36919644877 / 1000000000000) (36919644878 / 1000000000000))
    | 16 => (orderedInterval (21825517356 / 1000000000000) (21825519660 / 1000000000000), orderedInterval (-32824634087 / 1000000000000) (-32824631783 / 1000000000000))
    | 17 => (orderedInterval (-32486183362 / 1000000000000) (-32486183157 / 1000000000000), orderedInterval (-3926252914 / 1000000000000) (-3926252710 / 1000000000000))
    | 18 => (orderedInterval (10448449711 / 1000000000000) (10448449756 / 1000000000000), orderedInterval (-42756657096 / 1000000000000) (-42756657052 / 1000000000000))
    | 19 => (orderedInterval (2551082119 / 1000000000000) (2551082123 / 1000000000000), orderedInterval (-47724840743 / 1000000000000) (-47724840739 / 1000000000000))
    | 20 => (orderedInterval (-39255446685 / 1000000000000) (-39255420517 / 1000000000000), orderedInterval (46031758838 / 1000000000000) (46031785006 / 1000000000000))
    | 21 => (orderedInterval (28183749532 / 1000000000000) (28183749533 / 1000000000000), orderedInterval (77256562180 / 1000000000000) (77256562181 / 1000000000000))
    | 22 => (orderedInterval (-43016807224 / 1000000000000) (-43016807223 / 1000000000000), orderedInterval (-25387934334 / 1000000000000) (-25387934333 / 1000000000000))
    | 23 => (orderedInterval (5673307037 / 1000000000000) (5673307044 / 1000000000000), orderedInterval (-42413829255 / 1000000000000) (-42413829247 / 1000000000000))
    | 24 => (orderedInterval (-12587856802 / 1000000000000) (-12587856800 / 1000000000000), orderedInterval (-64536348188 / 1000000000000) (-64536348187 / 1000000000000))
    | 25 => (orderedInterval (32421615751 / 1000000000000) (32421619271 / 1000000000000), orderedInterval (-3738210015 / 1000000000000) (-3738206496 / 1000000000000))
    | _ => (orderedInterval (-35710336521 / 1000000000000) (-35710336520 / 1000000000000), orderedInterval (-17818488649 / 1000000000000) (-17818488647 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (17516545130 / 1000000000000) (17516546948 / 1000000000000)
      | 1 => orderedInterval (-4734572971 / 1000000000000) (-4734566085 / 1000000000000)
      | 2 => orderedInterval (-1571188431 / 1000000000000) (-1571188111 / 1000000000000)
      | 3 => orderedInterval (7429666249 / 1000000000000) (7429669330 / 1000000000000)
      | 4 => orderedInterval (3930164571 / 1000000000000) (3930165222 / 1000000000000)
      | 5 => orderedInterval (-2048093126 / 1000000000000) (-2048092958 / 1000000000000)
      | 6 => orderedInterval (-3092991028 / 1000000000000) (-3092990088 / 1000000000000)
      | 7 => orderedInterval (20704276 / 1000000000000) (20704316 / 1000000000000)
      | _ => orderedInterval (3985145223 / 1000000000000) (3985145599 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-2014364484 / 1000000000000) (-2014362692 / 1000000000000)
      | 1 => orderedInterval (1297510152 / 1000000000000) (1297520929 / 1000000000000)
      | 2 => orderedInterval (884604699 / 1000000000000) (884605327 / 1000000000000)
      | 3 => orderedInterval (7522512452 / 1000000000000) (7522519482 / 1000000000000)
      | 4 => orderedInterval (-467760953 / 1000000000000) (-467759953 / 1000000000000)
      | 5 => orderedInterval (2826322341 / 1000000000000) (2826322564 / 1000000000000)
      | 6 => orderedInterval (10147838560 / 1000000000000) (10147839105 / 1000000000000)
      | 7 => orderedInterval (3556514655 / 1000000000000) (3556514691 / 1000000000000)
      | _ => orderedInterval (4540146252 / 1000000000000) (4540146910 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-18118514441 / 1000000000000) (-18118512659 / 1000000000000)
      | 1 => orderedInterval (5944445740 / 1000000000000) (5944462660 / 1000000000000)
      | 2 => orderedInterval (4634010207 / 1000000000000) (4634011445 / 1000000000000)
      | 3 => orderedInterval (-29198711439 / 1000000000000) (-29198695352 / 1000000000000)
      | 4 => orderedInterval (-10273093620 / 1000000000000) (-10273092081 / 1000000000000)
      | 5 => orderedInterval (4799486863 / 1000000000000) (4799487163 / 1000000000000)
      | 6 => orderedInterval (2201014341 / 1000000000000) (2201014672 / 1000000000000)
      | 7 => orderedInterval (-70514049 / 1000000000000) (-70514013 / 1000000000000)
      | _ => orderedInterval (-1209038203 / 1000000000000) (-1209037025 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (1046188518 / 1000000000000) (1046190289 / 1000000000000)
      | 1 => orderedInterval (-4892718317 / 1000000000000) (-4892691797 / 1000000000000)
      | 2 => orderedInterval (-4206858912 / 1000000000000) (-4206856472 / 1000000000000)
      | 3 => orderedInterval (-31079678167 / 1000000000000) (-31079641370 / 1000000000000)
      | 4 => orderedInterval (-451734002 / 1000000000000) (-451731632 / 1000000000000)
      | 5 => orderedInterval (-4564122362 / 1000000000000) (-4564121952 / 1000000000000)
      | 6 => orderedInterval (-9322609932 / 1000000000000) (-9322609718 / 1000000000000)
      | 7 => orderedInterval (-4366017406 / 1000000000000) (-4366017369 / 1000000000000)
      | _ => orderedInterval (-8320435820 / 1000000000000) (-8320433689 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (18803338311 / 1000000000000) (18803340082 / 1000000000000)
      | 1 => orderedInterval (-13194307240 / 1000000000000) (-13194265588 / 1000000000000)
      | 2 => orderedInterval (-14909710395 / 1000000000000) (-14909705574 / 1000000000000)
      | 3 => orderedInterval (135839651799 / 1000000000000) (135839736119 / 1000000000000)
      | 4 => orderedInterval (28854997153 / 1000000000000) (28855000822 / 1000000000000)
      | 5 => orderedInterval (-12858767362 / 1000000000000) (-12858766787 / 1000000000000)
      | 6 => orderedInterval (-1962902475 / 1000000000000) (-1962902324 / 1000000000000)
      | 7 => orderedInterval (-187561095 / 1000000000000) (-187561057 / 1000000000000)
      | _ => orderedInterval (-15556429405 / 1000000000000) (-15556425510 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (21435379893 / 1000000000000) (21435394173 / 1000000000000)
    | 1 => orderedInterval (28293323674 / 1000000000000) (28293346363 / 1000000000000)
    | 2 => orderedInterval (-41290914601 / 1000000000000) (-41290875190 / 1000000000000)
    | 3 => orderedInterval (-66157986400 / 1000000000000) (-66157913710 / 1000000000000)
    | _ => orderedInterval (124828309291 / 1000000000000) (124828450183 / 1000000000000)

theorem compactCertificate450_stateChecks0 :
    compactCertificate450.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (643 / 2)) (orderedInterval (42865761362 / 1000000000000) (42865765623 / 1000000000000), orderedInterval (-12011501935 / 1000000000000) (-12011497674 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (947261779500343 / 4000000000000)) (orderedInterval (-47549721969 / 1000000000000) (-47549710626 / 1000000000000), orderedInterval (20770973801 / 1000000000000) (20770985144 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (306324996768919 / 800000000000)) (orderedInterval (16515171685 / 1000000000000) (16515171686 / 1000000000000), orderedInterval (37259121964 / 1000000000000) (37259121965 / 1000000000000))) = true
  rfl'

theorem compactCertificate450_stateChecks1 :
    compactCertificate450.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (276408624753701 / 4000000000000)) (orderedInterval (66864983006 / 1000000000000) (66864983007 / 1000000000000), orderedInterval (68377050439 / 1000000000000) (68377050440 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (742472446177697 / 4000000000000)) (orderedInterval (-50766614659 / 1000000000000) (-50766614658 / 1000000000000), orderedInterval (-29060396609 / 1000000000000) (-29060396608 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2015957122832349 / 4000000000000)) (orderedInterval (30321586613 / 1000000000000) (30321682926 / 1000000000000), orderedInterval (-18570879363 / 1000000000000) (-18570783050 / 1000000000000))) = true
  rfl'

theorem compactCertificate450_stateChecks2 :
    compactCertificate450.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1484944892356037 / 4000000000000)) (orderedInterval (40046151483 / 1000000000000) (40046151488 / 1000000000000), orderedInterval (10489724011 / 1000000000000) (10489724017 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (2544478383127001 / 4000000000000)) (orderedInterval (23525468441 / 1000000000000) (23525478210 / 1000000000000), orderedInterval (-21168871113 / 1000000000000) (-21168861344 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1874251260574859 / 4000000000000)) (orderedInterval (-34987073961 / 1000000000000) (-34987073957 / 1000000000000), orderedInterval (-11563043557 / 1000000000000) (-11563043552 / 1000000000000))) = true
  rfl'

theorem compactCertificate450_stateChecks3 :
    compactCertificate450.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (2875583419064357 / 4000000000000)) (orderedInterval (-7545570806 / 1000000000000) (-7545570805 / 1000000000000), orderedInterval (-28780455049 / 1000000000000) (-28780455048 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1660218861073853 / 4000000000000)) (orderedInterval (35740811875 / 1000000000000) (35740811877 / 1000000000000), orderedInterval (15969906404 / 1000000000000) (15969906405 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 235 12 (2946087503033377 / 4000000000000)) (orderedInterval (24204479947 / 1000000000000) (24204500721 / 1000000000000), orderedInterval (-16704826721 / 1000000000000) (-16704805947 / 1000000000000))) = true
  rfl'

theorem compactCertificate450_stateChecks4 :
    compactCertificate450.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 219 12 (2752617101753413 / 4000000000000)) (orderedInterval (-24394528713 / 1000000000000) (-24394528712 / 1000000000000), orderedInterval (-18148697468 / 1000000000000) (-18148697467 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1964397447903829 / 4000000000000)) (orderedInterval (35094796167 / 1000000000000) (35094802605 / 1000000000000), orderedInterval (-8077503773 / 1000000000000) (-8077497335 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2227417338533091 / 4000000000000)) (orderedInterval (-33811084366 / 1000000000000) (-33811083549 / 1000000000000), orderedInterval (260693791 / 1000000000000) (260694608 / 1000000000000))) = true
  rfl'

theorem compactCertificate450_stateChecks5 :
    compactCertificate450.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1856988356937779 / 4000000000000)) (orderedInterval (2830308450 / 1000000000000) (2830308451 / 1000000000000), orderedInterval (36919644877 / 1000000000000) (36919644878 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1640705530161359 / 4000000000000)) (orderedInterval (21825517356 / 1000000000000) (21825519660 / 1000000000000), orderedInterval (-32824634087 / 1000000000000) (-32824631783 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (475540412210541 / 800000000000)) (orderedInterval (-32486183362 / 1000000000000) (-32486183157 / 1000000000000), orderedInterval (-3926252914 / 1000000000000) (-3926252710 / 1000000000000))) = true
  rfl'

theorem compactCertificate450_stateChecks6 :
    compactCertificate450.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1315369806495127 / 4000000000000)) (orderedInterval (10448449711 / 1000000000000) (10448449756 / 1000000000000), orderedInterval (-42756657096 / 1000000000000) (-42756657052 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1115053552287647 / 4000000000000)) (orderedInterval (2551082119 / 1000000000000) (2551082123 / 1000000000000), orderedInterval (-47724840743 / 1000000000000) (-47724840739 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (697748739425141 / 4000000000000)) (orderedInterval (-39255446685 / 1000000000000) (-39255420517 / 1000000000000), orderedInterval (46031758838 / 1000000000000) (46031785006 / 1000000000000))) = true
  rfl'

theorem compactCertificate450_stateChecks7 :
    compactCertificate450.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (375251592670347 / 4000000000000)) (orderedInterval (28183749532 / 1000000000000) (28183749533 / 1000000000000), orderedInterval (77256562180 / 1000000000000) (77256562181 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1018881070932041 / 4000000000000)) (orderedInterval (-43016807224 / 1000000000000) (-43016807223 / 1000000000000), orderedInterval (-25387934334 / 1000000000000) (-25387934333 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1391194995535657 / 4000000000000)) (orderedInterval (5673307037 / 1000000000000) (5673307044 / 1000000000000), orderedInterval (-42413829255 / 1000000000000) (-42413829247 / 1000000000000))) = true
  rfl'

theorem compactCertificate450_stateChecks8 :
    compactCertificate450.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (588251260574859 / 4000000000000)) (orderedInterval (-12587856802 / 1000000000000) (-12587856800 / 1000000000000), orderedInterval (-64536348188 / 1000000000000) (-64536348187 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2391208715503339 / 4000000000000)) (orderedInterval (32421615751 / 1000000000000) (32421619271 / 1000000000000), orderedInterval (-3738210015 / 1000000000000) (-3738206496 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1597216603627301 / 4000000000000)) (orderedInterval (-35710336521 / 1000000000000) (-35710336520 / 1000000000000), orderedInterval (-17818488649 / 1000000000000) (-17818488647 / 1000000000000))) = true
  rfl'

theorem compactCertificate450_states : ∀ j,
    BesselStateValid (compactCertificate450.point j) (compactCertificate450.state j) :=
  compactCertificate450.statesValid_of_checks3 compactCertificate450_stateChecks0
    compactCertificate450_stateChecks1 compactCertificate450_stateChecks2
    compactCertificate450_stateChecks3 compactCertificate450_stateChecks4
    compactCertificate450_stateChecks5 compactCertificate450_stateChecks6
    compactCertificate450_stateChecks7 compactCertificate450_stateChecks8

theorem compactCertificate450_chunkChecks0_0 :
    compactCertificate450.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (643 / 2) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42865761362 / 1000000000000) (42865765623 / 1000000000000), orderedInterval (-12011501935 / 1000000000000) (-12011497674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (947261779500343 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47549721969 / 1000000000000) (-47549710626 / 1000000000000), orderedInterval (20770973801 / 1000000000000) (20770985144 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (306324996768919 / 800000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (16515171685 / 1000000000000) (16515171686 / 1000000000000), orderedInterval (37259121964 / 1000000000000) (37259121965 / 1000000000000)))) (orderedInterval (17516545130 / 1000000000000) (17516546948 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (276408624753701 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (66864983006 / 1000000000000) (66864983007 / 1000000000000), orderedInterval (68377050439 / 1000000000000) (68377050440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (742472446177697 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-50766614659 / 1000000000000) (-50766614658 / 1000000000000), orderedInterval (-29060396609 / 1000000000000) (-29060396608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2015957122832349 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30321586613 / 1000000000000) (30321682926 / 1000000000000), orderedInterval (-18570879363 / 1000000000000) (-18570783050 / 1000000000000)))) (orderedInterval (-4734572971 / 1000000000000) (-4734566085 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1484944892356037 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40046151483 / 1000000000000) (40046151488 / 1000000000000), orderedInterval (10489724011 / 1000000000000) (10489724017 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2544478383127001 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23525468441 / 1000000000000) (23525478210 / 1000000000000), orderedInterval (-21168871113 / 1000000000000) (-21168861344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1874251260574859 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34987073961 / 1000000000000) (-34987073957 / 1000000000000), orderedInterval (-11563043557 / 1000000000000) (-11563043552 / 1000000000000)))) (orderedInterval (-1571188431 / 1000000000000) (-1571188111 / 1000000000000))) = true
  rfl'

theorem compactCertificate450_chunkChecks0_1 :
    compactCertificate450.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2875583419064357 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7545570806 / 1000000000000) (-7545570805 / 1000000000000), orderedInterval (-28780455049 / 1000000000000) (-28780455048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1660218861073853 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (35740811875 / 1000000000000) (35740811877 / 1000000000000), orderedInterval (15969906404 / 1000000000000) (15969906405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2946087503033377 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24204479947 / 1000000000000) (24204500721 / 1000000000000), orderedInterval (-16704826721 / 1000000000000) (-16704805947 / 1000000000000)))) (orderedInterval (7429666249 / 1000000000000) (7429669330 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2752617101753413 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24394528713 / 1000000000000) (-24394528712 / 1000000000000), orderedInterval (-18148697468 / 1000000000000) (-18148697467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1964397447903829 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35094796167 / 1000000000000) (35094802605 / 1000000000000), orderedInterval (-8077503773 / 1000000000000) (-8077497335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2227417338533091 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33811084366 / 1000000000000) (-33811083549 / 1000000000000), orderedInterval (260693791 / 1000000000000) (260694608 / 1000000000000)))) (orderedInterval (3930164571 / 1000000000000) (3930165222 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1856988356937779 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2830308450 / 1000000000000) (2830308451 / 1000000000000), orderedInterval (36919644877 / 1000000000000) (36919644878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1640705530161359 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (21825517356 / 1000000000000) (21825519660 / 1000000000000), orderedInterval (-32824634087 / 1000000000000) (-32824631783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (475540412210541 / 800000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32486183362 / 1000000000000) (-32486183157 / 1000000000000), orderedInterval (-3926252914 / 1000000000000) (-3926252710 / 1000000000000)))) (orderedInterval (-2048093126 / 1000000000000) (-2048092958 / 1000000000000))) = true
  rfl'

theorem compactCertificate450_chunkChecks0_2 :
    compactCertificate450.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1315369806495127 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (10448449711 / 1000000000000) (10448449756 / 1000000000000), orderedInterval (-42756657096 / 1000000000000) (-42756657052 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1115053552287647 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (2551082119 / 1000000000000) (2551082123 / 1000000000000), orderedInterval (-47724840743 / 1000000000000) (-47724840739 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (697748739425141 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-39255446685 / 1000000000000) (-39255420517 / 1000000000000), orderedInterval (46031758838 / 1000000000000) (46031785006 / 1000000000000)))) (orderedInterval (-3092991028 / 1000000000000) (-3092990088 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (375251592670347 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (28183749532 / 1000000000000) (28183749533 / 1000000000000), orderedInterval (77256562180 / 1000000000000) (77256562181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1018881070932041 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43016807224 / 1000000000000) (-43016807223 / 1000000000000), orderedInterval (-25387934334 / 1000000000000) (-25387934333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1391194995535657 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5673307037 / 1000000000000) (5673307044 / 1000000000000), orderedInterval (-42413829255 / 1000000000000) (-42413829247 / 1000000000000)))) (orderedInterval (20704276 / 1000000000000) (20704316 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (588251260574859 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-12587856802 / 1000000000000) (-12587856800 / 1000000000000), orderedInterval (-64536348188 / 1000000000000) (-64536348187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2391208715503339 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32421615751 / 1000000000000) (32421619271 / 1000000000000), orderedInterval (-3738210015 / 1000000000000) (-3738206496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1597216603627301 / 4000000000000) 0 (IntervalRat.scale (643 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35710336521 / 1000000000000) (-35710336520 / 1000000000000), orderedInterval (-17818488649 / 1000000000000) (-17818488647 / 1000000000000)))) (orderedInterval (3985145223 / 1000000000000) (3985145599 / 1000000000000))) = true
  rfl'

theorem compactCertificate450_chunkChecks0 :
    compactCertificate450.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate450.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate450_chunkChecks0_0
    compactCertificate450_chunkChecks0_1 compactCertificate450_chunkChecks0_2

theorem compactCertificate450_chunkChecks1_0 :
    compactCertificate450.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (643 / 2) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42865761362 / 1000000000000) (42865765623 / 1000000000000), orderedInterval (-12011501935 / 1000000000000) (-12011497674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (947261779500343 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47549721969 / 1000000000000) (-47549710626 / 1000000000000), orderedInterval (20770973801 / 1000000000000) (20770985144 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (306324996768919 / 800000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (16515171685 / 1000000000000) (16515171686 / 1000000000000), orderedInterval (37259121964 / 1000000000000) (37259121965 / 1000000000000)))) (orderedInterval (-2014364484 / 1000000000000) (-2014362692 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (276408624753701 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (66864983006 / 1000000000000) (66864983007 / 1000000000000), orderedInterval (68377050439 / 1000000000000) (68377050440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (742472446177697 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-50766614659 / 1000000000000) (-50766614658 / 1000000000000), orderedInterval (-29060396609 / 1000000000000) (-29060396608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2015957122832349 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30321586613 / 1000000000000) (30321682926 / 1000000000000), orderedInterval (-18570879363 / 1000000000000) (-18570783050 / 1000000000000)))) (orderedInterval (1297510152 / 1000000000000) (1297520929 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1484944892356037 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40046151483 / 1000000000000) (40046151488 / 1000000000000), orderedInterval (10489724011 / 1000000000000) (10489724017 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2544478383127001 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23525468441 / 1000000000000) (23525478210 / 1000000000000), orderedInterval (-21168871113 / 1000000000000) (-21168861344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1874251260574859 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34987073961 / 1000000000000) (-34987073957 / 1000000000000), orderedInterval (-11563043557 / 1000000000000) (-11563043552 / 1000000000000)))) (orderedInterval (884604699 / 1000000000000) (884605327 / 1000000000000))) = true
  rfl'

theorem compactCertificate450_chunkChecks1_1 :
    compactCertificate450.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2875583419064357 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7545570806 / 1000000000000) (-7545570805 / 1000000000000), orderedInterval (-28780455049 / 1000000000000) (-28780455048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1660218861073853 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (35740811875 / 1000000000000) (35740811877 / 1000000000000), orderedInterval (15969906404 / 1000000000000) (15969906405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2946087503033377 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24204479947 / 1000000000000) (24204500721 / 1000000000000), orderedInterval (-16704826721 / 1000000000000) (-16704805947 / 1000000000000)))) (orderedInterval (7522512452 / 1000000000000) (7522519482 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2752617101753413 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24394528713 / 1000000000000) (-24394528712 / 1000000000000), orderedInterval (-18148697468 / 1000000000000) (-18148697467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1964397447903829 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35094796167 / 1000000000000) (35094802605 / 1000000000000), orderedInterval (-8077503773 / 1000000000000) (-8077497335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2227417338533091 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33811084366 / 1000000000000) (-33811083549 / 1000000000000), orderedInterval (260693791 / 1000000000000) (260694608 / 1000000000000)))) (orderedInterval (-467760953 / 1000000000000) (-467759953 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1856988356937779 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2830308450 / 1000000000000) (2830308451 / 1000000000000), orderedInterval (36919644877 / 1000000000000) (36919644878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1640705530161359 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (21825517356 / 1000000000000) (21825519660 / 1000000000000), orderedInterval (-32824634087 / 1000000000000) (-32824631783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (475540412210541 / 800000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32486183362 / 1000000000000) (-32486183157 / 1000000000000), orderedInterval (-3926252914 / 1000000000000) (-3926252710 / 1000000000000)))) (orderedInterval (2826322341 / 1000000000000) (2826322564 / 1000000000000))) = true
  rfl'

theorem compactCertificate450_chunkChecks1_2 :
    compactCertificate450.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1315369806495127 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (10448449711 / 1000000000000) (10448449756 / 1000000000000), orderedInterval (-42756657096 / 1000000000000) (-42756657052 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1115053552287647 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (2551082119 / 1000000000000) (2551082123 / 1000000000000), orderedInterval (-47724840743 / 1000000000000) (-47724840739 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (697748739425141 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-39255446685 / 1000000000000) (-39255420517 / 1000000000000), orderedInterval (46031758838 / 1000000000000) (46031785006 / 1000000000000)))) (orderedInterval (10147838560 / 1000000000000) (10147839105 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (375251592670347 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (28183749532 / 1000000000000) (28183749533 / 1000000000000), orderedInterval (77256562180 / 1000000000000) (77256562181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1018881070932041 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43016807224 / 1000000000000) (-43016807223 / 1000000000000), orderedInterval (-25387934334 / 1000000000000) (-25387934333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1391194995535657 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5673307037 / 1000000000000) (5673307044 / 1000000000000), orderedInterval (-42413829255 / 1000000000000) (-42413829247 / 1000000000000)))) (orderedInterval (3556514655 / 1000000000000) (3556514691 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (588251260574859 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-12587856802 / 1000000000000) (-12587856800 / 1000000000000), orderedInterval (-64536348188 / 1000000000000) (-64536348187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2391208715503339 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32421615751 / 1000000000000) (32421619271 / 1000000000000), orderedInterval (-3738210015 / 1000000000000) (-3738206496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1597216603627301 / 4000000000000) 1 (IntervalRat.scale (643 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35710336521 / 1000000000000) (-35710336520 / 1000000000000), orderedInterval (-17818488649 / 1000000000000) (-17818488647 / 1000000000000)))) (orderedInterval (4540146252 / 1000000000000) (4540146910 / 1000000000000))) = true
  rfl'

theorem compactCertificate450_chunkChecks1 :
    compactCertificate450.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate450.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate450_chunkChecks1_0
    compactCertificate450_chunkChecks1_1 compactCertificate450_chunkChecks1_2

theorem compactCertificate450_chunkChecks2_0 :
    compactCertificate450.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (643 / 2) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42865761362 / 1000000000000) (42865765623 / 1000000000000), orderedInterval (-12011501935 / 1000000000000) (-12011497674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (947261779500343 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47549721969 / 1000000000000) (-47549710626 / 1000000000000), orderedInterval (20770973801 / 1000000000000) (20770985144 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (306324996768919 / 800000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (16515171685 / 1000000000000) (16515171686 / 1000000000000), orderedInterval (37259121964 / 1000000000000) (37259121965 / 1000000000000)))) (orderedInterval (-18118514441 / 1000000000000) (-18118512659 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (276408624753701 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (66864983006 / 1000000000000) (66864983007 / 1000000000000), orderedInterval (68377050439 / 1000000000000) (68377050440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (742472446177697 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-50766614659 / 1000000000000) (-50766614658 / 1000000000000), orderedInterval (-29060396609 / 1000000000000) (-29060396608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2015957122832349 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30321586613 / 1000000000000) (30321682926 / 1000000000000), orderedInterval (-18570879363 / 1000000000000) (-18570783050 / 1000000000000)))) (orderedInterval (5944445740 / 1000000000000) (5944462660 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1484944892356037 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40046151483 / 1000000000000) (40046151488 / 1000000000000), orderedInterval (10489724011 / 1000000000000) (10489724017 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2544478383127001 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23525468441 / 1000000000000) (23525478210 / 1000000000000), orderedInterval (-21168871113 / 1000000000000) (-21168861344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1874251260574859 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34987073961 / 1000000000000) (-34987073957 / 1000000000000), orderedInterval (-11563043557 / 1000000000000) (-11563043552 / 1000000000000)))) (orderedInterval (4634010207 / 1000000000000) (4634011445 / 1000000000000))) = true
  rfl'

theorem compactCertificate450_chunkChecks2_1 :
    compactCertificate450.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2875583419064357 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7545570806 / 1000000000000) (-7545570805 / 1000000000000), orderedInterval (-28780455049 / 1000000000000) (-28780455048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1660218861073853 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (35740811875 / 1000000000000) (35740811877 / 1000000000000), orderedInterval (15969906404 / 1000000000000) (15969906405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2946087503033377 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24204479947 / 1000000000000) (24204500721 / 1000000000000), orderedInterval (-16704826721 / 1000000000000) (-16704805947 / 1000000000000)))) (orderedInterval (-29198711439 / 1000000000000) (-29198695352 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2752617101753413 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24394528713 / 1000000000000) (-24394528712 / 1000000000000), orderedInterval (-18148697468 / 1000000000000) (-18148697467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1964397447903829 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35094796167 / 1000000000000) (35094802605 / 1000000000000), orderedInterval (-8077503773 / 1000000000000) (-8077497335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2227417338533091 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33811084366 / 1000000000000) (-33811083549 / 1000000000000), orderedInterval (260693791 / 1000000000000) (260694608 / 1000000000000)))) (orderedInterval (-10273093620 / 1000000000000) (-10273092081 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1856988356937779 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2830308450 / 1000000000000) (2830308451 / 1000000000000), orderedInterval (36919644877 / 1000000000000) (36919644878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1640705530161359 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (21825517356 / 1000000000000) (21825519660 / 1000000000000), orderedInterval (-32824634087 / 1000000000000) (-32824631783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (475540412210541 / 800000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32486183362 / 1000000000000) (-32486183157 / 1000000000000), orderedInterval (-3926252914 / 1000000000000) (-3926252710 / 1000000000000)))) (orderedInterval (4799486863 / 1000000000000) (4799487163 / 1000000000000))) = true
  rfl'

theorem compactCertificate450_chunkChecks2_2 :
    compactCertificate450.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1315369806495127 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (10448449711 / 1000000000000) (10448449756 / 1000000000000), orderedInterval (-42756657096 / 1000000000000) (-42756657052 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1115053552287647 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (2551082119 / 1000000000000) (2551082123 / 1000000000000), orderedInterval (-47724840743 / 1000000000000) (-47724840739 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (697748739425141 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-39255446685 / 1000000000000) (-39255420517 / 1000000000000), orderedInterval (46031758838 / 1000000000000) (46031785006 / 1000000000000)))) (orderedInterval (2201014341 / 1000000000000) (2201014672 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (375251592670347 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (28183749532 / 1000000000000) (28183749533 / 1000000000000), orderedInterval (77256562180 / 1000000000000) (77256562181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1018881070932041 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43016807224 / 1000000000000) (-43016807223 / 1000000000000), orderedInterval (-25387934334 / 1000000000000) (-25387934333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1391194995535657 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5673307037 / 1000000000000) (5673307044 / 1000000000000), orderedInterval (-42413829255 / 1000000000000) (-42413829247 / 1000000000000)))) (orderedInterval (-70514049 / 1000000000000) (-70514013 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (588251260574859 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-12587856802 / 1000000000000) (-12587856800 / 1000000000000), orderedInterval (-64536348188 / 1000000000000) (-64536348187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2391208715503339 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32421615751 / 1000000000000) (32421619271 / 1000000000000), orderedInterval (-3738210015 / 1000000000000) (-3738206496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1597216603627301 / 4000000000000) 2 (IntervalRat.scale (643 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35710336521 / 1000000000000) (-35710336520 / 1000000000000), orderedInterval (-17818488649 / 1000000000000) (-17818488647 / 1000000000000)))) (orderedInterval (-1209038203 / 1000000000000) (-1209037025 / 1000000000000))) = true
  rfl'

theorem compactCertificate450_chunkChecks2 :
    compactCertificate450.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate450.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate450_chunkChecks2_0
    compactCertificate450_chunkChecks2_1 compactCertificate450_chunkChecks2_2

theorem compactCertificate450_chunkChecks3_0 :
    compactCertificate450.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (643 / 2) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42865761362 / 1000000000000) (42865765623 / 1000000000000), orderedInterval (-12011501935 / 1000000000000) (-12011497674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (947261779500343 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47549721969 / 1000000000000) (-47549710626 / 1000000000000), orderedInterval (20770973801 / 1000000000000) (20770985144 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (306324996768919 / 800000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (16515171685 / 1000000000000) (16515171686 / 1000000000000), orderedInterval (37259121964 / 1000000000000) (37259121965 / 1000000000000)))) (orderedInterval (1046188518 / 1000000000000) (1046190289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (276408624753701 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (66864983006 / 1000000000000) (66864983007 / 1000000000000), orderedInterval (68377050439 / 1000000000000) (68377050440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (742472446177697 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-50766614659 / 1000000000000) (-50766614658 / 1000000000000), orderedInterval (-29060396609 / 1000000000000) (-29060396608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2015957122832349 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30321586613 / 1000000000000) (30321682926 / 1000000000000), orderedInterval (-18570879363 / 1000000000000) (-18570783050 / 1000000000000)))) (orderedInterval (-4892718317 / 1000000000000) (-4892691797 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1484944892356037 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40046151483 / 1000000000000) (40046151488 / 1000000000000), orderedInterval (10489724011 / 1000000000000) (10489724017 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2544478383127001 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23525468441 / 1000000000000) (23525478210 / 1000000000000), orderedInterval (-21168871113 / 1000000000000) (-21168861344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1874251260574859 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34987073961 / 1000000000000) (-34987073957 / 1000000000000), orderedInterval (-11563043557 / 1000000000000) (-11563043552 / 1000000000000)))) (orderedInterval (-4206858912 / 1000000000000) (-4206856472 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate450_chunkChecks3_1 :
    compactCertificate450.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2875583419064357 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7545570806 / 1000000000000) (-7545570805 / 1000000000000), orderedInterval (-28780455049 / 1000000000000) (-28780455048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1660218861073853 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (35740811875 / 1000000000000) (35740811877 / 1000000000000), orderedInterval (15969906404 / 1000000000000) (15969906405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2946087503033377 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24204479947 / 1000000000000) (24204500721 / 1000000000000), orderedInterval (-16704826721 / 1000000000000) (-16704805947 / 1000000000000)))) (orderedInterval (-31079678167 / 1000000000000) (-31079641370 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2752617101753413 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24394528713 / 1000000000000) (-24394528712 / 1000000000000), orderedInterval (-18148697468 / 1000000000000) (-18148697467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1964397447903829 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35094796167 / 1000000000000) (35094802605 / 1000000000000), orderedInterval (-8077503773 / 1000000000000) (-8077497335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2227417338533091 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33811084366 / 1000000000000) (-33811083549 / 1000000000000), orderedInterval (260693791 / 1000000000000) (260694608 / 1000000000000)))) (orderedInterval (-451734002 / 1000000000000) (-451731632 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1856988356937779 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2830308450 / 1000000000000) (2830308451 / 1000000000000), orderedInterval (36919644877 / 1000000000000) (36919644878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1640705530161359 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (21825517356 / 1000000000000) (21825519660 / 1000000000000), orderedInterval (-32824634087 / 1000000000000) (-32824631783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (475540412210541 / 800000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32486183362 / 1000000000000) (-32486183157 / 1000000000000), orderedInterval (-3926252914 / 1000000000000) (-3926252710 / 1000000000000)))) (orderedInterval (-4564122362 / 1000000000000) (-4564121952 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate450_chunkChecks3_2 :
    compactCertificate450.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1315369806495127 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (10448449711 / 1000000000000) (10448449756 / 1000000000000), orderedInterval (-42756657096 / 1000000000000) (-42756657052 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1115053552287647 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (2551082119 / 1000000000000) (2551082123 / 1000000000000), orderedInterval (-47724840743 / 1000000000000) (-47724840739 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (697748739425141 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-39255446685 / 1000000000000) (-39255420517 / 1000000000000), orderedInterval (46031758838 / 1000000000000) (46031785006 / 1000000000000)))) (orderedInterval (-9322609932 / 1000000000000) (-9322609718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (375251592670347 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (28183749532 / 1000000000000) (28183749533 / 1000000000000), orderedInterval (77256562180 / 1000000000000) (77256562181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1018881070932041 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43016807224 / 1000000000000) (-43016807223 / 1000000000000), orderedInterval (-25387934334 / 1000000000000) (-25387934333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1391194995535657 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5673307037 / 1000000000000) (5673307044 / 1000000000000), orderedInterval (-42413829255 / 1000000000000) (-42413829247 / 1000000000000)))) (orderedInterval (-4366017406 / 1000000000000) (-4366017369 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (588251260574859 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-12587856802 / 1000000000000) (-12587856800 / 1000000000000), orderedInterval (-64536348188 / 1000000000000) (-64536348187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2391208715503339 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32421615751 / 1000000000000) (32421619271 / 1000000000000), orderedInterval (-3738210015 / 1000000000000) (-3738206496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1597216603627301 / 4000000000000) 3 (IntervalRat.scale (643 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35710336521 / 1000000000000) (-35710336520 / 1000000000000), orderedInterval (-17818488649 / 1000000000000) (-17818488647 / 1000000000000)))) (orderedInterval (-8320435820 / 1000000000000) (-8320433689 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate450_chunkChecks3 :
    compactCertificate450.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate450.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate450_chunkChecks3_0
    compactCertificate450_chunkChecks3_1 compactCertificate450_chunkChecks3_2

theorem compactCertificate450_chunkChecks4_0 :
    compactCertificate450.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (643 / 2) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42865761362 / 1000000000000) (42865765623 / 1000000000000), orderedInterval (-12011501935 / 1000000000000) (-12011497674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (947261779500343 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47549721969 / 1000000000000) (-47549710626 / 1000000000000), orderedInterval (20770973801 / 1000000000000) (20770985144 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (306324996768919 / 800000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (16515171685 / 1000000000000) (16515171686 / 1000000000000), orderedInterval (37259121964 / 1000000000000) (37259121965 / 1000000000000)))) (orderedInterval (18803338311 / 1000000000000) (18803340082 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (276408624753701 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (66864983006 / 1000000000000) (66864983007 / 1000000000000), orderedInterval (68377050439 / 1000000000000) (68377050440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (742472446177697 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-50766614659 / 1000000000000) (-50766614658 / 1000000000000), orderedInterval (-29060396609 / 1000000000000) (-29060396608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2015957122832349 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30321586613 / 1000000000000) (30321682926 / 1000000000000), orderedInterval (-18570879363 / 1000000000000) (-18570783050 / 1000000000000)))) (orderedInterval (-13194307240 / 1000000000000) (-13194265588 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1484944892356037 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40046151483 / 1000000000000) (40046151488 / 1000000000000), orderedInterval (10489724011 / 1000000000000) (10489724017 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2544478383127001 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23525468441 / 1000000000000) (23525478210 / 1000000000000), orderedInterval (-21168871113 / 1000000000000) (-21168861344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1874251260574859 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34987073961 / 1000000000000) (-34987073957 / 1000000000000), orderedInterval (-11563043557 / 1000000000000) (-11563043552 / 1000000000000)))) (orderedInterval (-14909710395 / 1000000000000) (-14909705574 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate450_chunkChecks4_1 :
    compactCertificate450.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2875583419064357 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7545570806 / 1000000000000) (-7545570805 / 1000000000000), orderedInterval (-28780455049 / 1000000000000) (-28780455048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1660218861073853 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (35740811875 / 1000000000000) (35740811877 / 1000000000000), orderedInterval (15969906404 / 1000000000000) (15969906405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2946087503033377 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24204479947 / 1000000000000) (24204500721 / 1000000000000), orderedInterval (-16704826721 / 1000000000000) (-16704805947 / 1000000000000)))) (orderedInterval (135839651799 / 1000000000000) (135839736119 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2752617101753413 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24394528713 / 1000000000000) (-24394528712 / 1000000000000), orderedInterval (-18148697468 / 1000000000000) (-18148697467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1964397447903829 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35094796167 / 1000000000000) (35094802605 / 1000000000000), orderedInterval (-8077503773 / 1000000000000) (-8077497335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2227417338533091 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-33811084366 / 1000000000000) (-33811083549 / 1000000000000), orderedInterval (260693791 / 1000000000000) (260694608 / 1000000000000)))) (orderedInterval (28854997153 / 1000000000000) (28855000822 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1856988356937779 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2830308450 / 1000000000000) (2830308451 / 1000000000000), orderedInterval (36919644877 / 1000000000000) (36919644878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1640705530161359 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (21825517356 / 1000000000000) (21825519660 / 1000000000000), orderedInterval (-32824634087 / 1000000000000) (-32824631783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (475540412210541 / 800000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32486183362 / 1000000000000) (-32486183157 / 1000000000000), orderedInterval (-3926252914 / 1000000000000) (-3926252710 / 1000000000000)))) (orderedInterval (-12858767362 / 1000000000000) (-12858766787 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate450_chunkChecks4_2 :
    compactCertificate450.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1315369806495127 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (10448449711 / 1000000000000) (10448449756 / 1000000000000), orderedInterval (-42756657096 / 1000000000000) (-42756657052 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1115053552287647 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (2551082119 / 1000000000000) (2551082123 / 1000000000000), orderedInterval (-47724840743 / 1000000000000) (-47724840739 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (697748739425141 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-39255446685 / 1000000000000) (-39255420517 / 1000000000000), orderedInterval (46031758838 / 1000000000000) (46031785006 / 1000000000000)))) (orderedInterval (-1962902475 / 1000000000000) (-1962902324 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (375251592670347 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (28183749532 / 1000000000000) (28183749533 / 1000000000000), orderedInterval (77256562180 / 1000000000000) (77256562181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1018881070932041 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43016807224 / 1000000000000) (-43016807223 / 1000000000000), orderedInterval (-25387934334 / 1000000000000) (-25387934333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1391194995535657 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5673307037 / 1000000000000) (5673307044 / 1000000000000), orderedInterval (-42413829255 / 1000000000000) (-42413829247 / 1000000000000)))) (orderedInterval (-187561095 / 1000000000000) (-187561057 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (588251260574859 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-12587856802 / 1000000000000) (-12587856800 / 1000000000000), orderedInterval (-64536348188 / 1000000000000) (-64536348187 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2391208715503339 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32421615751 / 1000000000000) (32421619271 / 1000000000000), orderedInterval (-3738210015 / 1000000000000) (-3738206496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1597216603627301 / 4000000000000) 4 (IntervalRat.scale (643 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35710336521 / 1000000000000) (-35710336520 / 1000000000000), orderedInterval (-17818488649 / 1000000000000) (-17818488647 / 1000000000000)))) (orderedInterval (-15556429405 / 1000000000000) (-15556425510 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate450_chunkChecks4 :
    compactCertificate450.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate450.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate450_chunkChecks4_0
    compactCertificate450_chunkChecks4_1 compactCertificate450_chunkChecks4_2

theorem compactCertificate450_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate450.chunkCheck r b = true :=
  compactCertificate450.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate450_chunkChecks0
    · exact compactCertificate450_chunkChecks1
    · exact compactCertificate450_chunkChecks2
    · exact compactCertificate450_chunkChecks3
    · exact compactCertificate450_chunkChecks4)

theorem compactCertificate450_coefficient0 :
    compactCertificate450.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate450_coefficient1 :
    compactCertificate450.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate450_coefficient2 :
    compactCertificate450.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate450_coefficient3 :
    compactCertificate450.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate450_coefficient4 :
    compactCertificate450.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate450_coefficients : ∀ r : Fin 5,
    compactCertificate450.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate450_coefficient0
  · exact compactCertificate450_coefficient1
  · exact compactCertificate450_coefficient2
  · exact compactCertificate450_coefficient3
  · exact compactCertificate450_coefficient4

theorem compactCertificate450_lower : (1 : ℚ) ≤ compactCertificate450.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate450, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate450_proves {t : ℝ} (ht : t ∈ compactCertificate450.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate450.proves compactCertificate450_states compactCertificate450_chunks
    compactCertificate450_coefficients compactCertificate450_lower ht

end Erdos232
