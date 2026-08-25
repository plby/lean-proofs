/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate307 : CompactCertificate where
  left := 180
  right := 181
  center := 361 / 2
  grid := fun i =>
    match i.val with
    | 0 => 57
    | 1 => 42
    | 2 => 68
    | 3 => 12
    | 4 => 33
    | 5 => 90
    | 6 => 66
    | 7 => 114
    | 8 => 84
    | 9 => 129
    | 10 => 74
    | 11 => 132
    | 12 => 123
    | 13 => 88
    | 14 => 100
    | 15 => 83
    | 16 => 73
    | 17 => 106
    | 18 => 59
    | 19 => 50
    | 20 => 31
    | 21 => 17
    | 22 => 46
    | 23 => 62
    | 24 => 26
    | 25 => 107
    | _ => 71
  point := fun i =>
    match i.val with
    | 0 => 361 / 2
    | 1 => 531821932192261 / 4000000000000
    | 2 => 171980285899813 / 800000000000
    | 3 => 155184313430927 / 4000000000000
    | 4 => 416846894354819 / 4000000000000
    | 5 => 1131820406442423 / 4000000000000
    | 6 => 833693788709999 / 4000000000000
    | 7 => 1428548516810027 / 4000000000000
    | 8 => 1052262371800193 / 4000000000000
    | 9 => 1614441079754639 / 4000000000000
    | 10 => 932097991987031 / 4000000000000
    | 11 => 1654024243538179 / 4000000000000
    | 12 => 1545404002695151 / 4000000000000
    | 13 => 1102873217252383 / 4000000000000
    | 14 => 1250540683064457 / 4000000000000
    | 15 => 1042570446119033 / 4000000000000
    | 16 => 921142607135693 / 4000000000000
    | 17 => 266983030805607 / 800000000000
    | 18 => 738489113755429 / 4000000000000
    | 19 => 626025400273469 / 4000000000000
    | 20 => 391737628199807 / 4000000000000
    | 21 => 210677799306369 / 4000000000000
    | 22 => 572031207786107 / 4000000000000
    | 23 => 781059709779739 / 4000000000000
    | 24 => 330262371800193 / 4000000000000
    | 25 => 1342498205749153 / 4000000000000
    | _ => 896726584618127 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-47523935380 / 1000000000000) (-47523861126 / 1000000000000), orderedInterval (35746974318 / 1000000000000) (35747048572 / 1000000000000))
    | 1 => (orderedInterval (67494687253 / 1000000000000) (67494688082 / 1000000000000), orderedInterval (-15506823564 / 1000000000000) (-15506822736 / 1000000000000))
    | 2 => (orderedInterval (46075010505 / 1000000000000) (46075052710 / 1000000000000), orderedInterval (-29063176280 / 1000000000000) (-29063134074 / 1000000000000))
    | 3 => (orderedInterval (122052438891 / 1000000000000) (122052440231 / 1000000000000), orderedInterval (-40450446959 / 1000000000000) (-40450445619 / 1000000000000))
    | 4 => (orderedInterval (-75778690180 / 1000000000000) (-75778690179 / 1000000000000), orderedInterval (-18778937535 / 1000000000000) (-18778937534 / 1000000000000))
    | 5 => (orderedInterval (39829230837 / 1000000000000) (39829230838 / 1000000000000), orderedInterval (25688651036 / 1000000000000) (25688651037 / 1000000000000))
    | 6 => (orderedInterval (52922261888 / 1000000000000) (52922264758 / 1000000000000), orderedInterval (-16054307473 / 1000000000000) (-16054304604 / 1000000000000))
    | 7 => (orderedInterval (-9188406693 / 1000000000000) (-9188406667 / 1000000000000), orderedInterval (41221342627 / 1000000000000) (41221342653 / 1000000000000))
    | 8 => (orderedInterval (-2127788357 / 1000000000000) (-2127788353 / 1000000000000), orderedInterval (49151585492 / 1000000000000) (49151585496 / 1000000000000))
    | 9 => (orderedInterval (30358003174 / 1000000000000) (30358043306 / 1000000000000), orderedInterval (-25644331811 / 1000000000000) (-25644291679 / 1000000000000))
    | 10 => (orderedInterval (50779002870 / 1000000000000) (50779002873 / 1000000000000), orderedInterval (12279496051 / 1000000000000) (12279496054 / 1000000000000))
    | 11 => (orderedInterval (-15246229533 / 1000000000000) (-15246229304 / 1000000000000), orderedInterval (36172536361 / 1000000000000) (36172536589 / 1000000000000))
    | 12 => (orderedInterval (-26771720292 / 1000000000000) (-26771720291 / 1000000000000), orderedInterval (-30478478624 / 1000000000000) (-30478478623 / 1000000000000))
    | 13 => (orderedInterval (2070167193 / 1000000000000) (2070167194 / 1000000000000), orderedInterval (48003205446 / 1000000000000) (48003205448 / 1000000000000))
    | 14 => (orderedInterval (-30397378143 / 1000000000000) (-30397359829 / 1000000000000), orderedInterval (33399806960 / 1000000000000) (33399825275 / 1000000000000))
    | 15 => (orderedInterval (-30896547491 / 1000000000000) (-30896547490 / 1000000000000), orderedInterval (-38514102922 / 1000000000000) (-38514102921 / 1000000000000))
    | 16 => (orderedInterval (-51877497568 / 1000000000000) (-51877496833 / 1000000000000), orderedInterval (8668206595 / 1000000000000) (8668207330 / 1000000000000))
    | 17 => (orderedInterval (43581480120 / 1000000000000) (43581480190 / 1000000000000), orderedInterval (2806756137 / 1000000000000) (2806756207 / 1000000000000))
    | 18 => (orderedInterval (-3112717831 / 1000000000000) (-3112717829 / 1000000000000), orderedInterval (-58630737043 / 1000000000000) (-58630737041 / 1000000000000))
    | 19 => (orderedInterval (13377350684 / 1000000000000) (13377350685 / 1000000000000), orderedInterval (62317172756 / 1000000000000) (62317172757 / 1000000000000))
    | 20 => (orderedInterval (-78282568953 / 1000000000000) (-78282568951 / 1000000000000), orderedInterval (-18893744769 / 1000000000000) (-18893744768 / 1000000000000))
    | 21 => (orderedInterval (-4989509410 / 1000000000000) (-4989509405 / 1000000000000), orderedInterval (-109783077096 / 1000000000000) (-109783077092 / 1000000000000))
    | 22 => (orderedInterval (-44041380120 / 1000000000000) (-44041345859 / 1000000000000), orderedInterval (50273872969 / 1000000000000) (50273907230 / 1000000000000))
    | 23 => (orderedInterval (54551037650 / 1000000000000) (54551037651 / 1000000000000), orderedInterval (16726341726 / 1000000000000) (16726341727 / 1000000000000))
    | 24 => (orderedInterval (87393406673 / 1000000000000) (87393406791 / 1000000000000), orderedInterval (-9057214605 / 1000000000000) (-9057214486 / 1000000000000))
    | 25 => (orderedInterval (-11161274843 / 1000000000000) (-11161274842 / 1000000000000), orderedInterval (-42081460213 / 1000000000000) (-42081460212 / 1000000000000))
    | _ => (orderedInterval (-50192088471 / 1000000000000) (-50192083115 / 1000000000000), orderedInterval (18014421774 / 1000000000000) (18014427129 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-15504170633 / 1000000000000) (-15504138704 / 1000000000000)
      | 1 => orderedInterval (-6922440462 / 1000000000000) (-6922440425 / 1000000000000)
      | 2 => orderedInterval (231982772 / 1000000000000) (231982784 / 1000000000000)
      | 3 => orderedInterval (-3799292895 / 1000000000000) (-3799285659 / 1000000000000)
      | 4 => orderedInterval (832901250 / 1000000000000) (832901365 / 1000000000000)
      | 5 => orderedInterval (3727851649 / 1000000000000) (3727851711 / 1000000000000)
      | 6 => orderedInterval (-2807967675 / 1000000000000) (-2807967629 / 1000000000000)
      | 7 => orderedInterval (-3089438083 / 1000000000000) (-3089437284 / 1000000000000)
      | _ => orderedInterval (10852749939 / 1000000000000) (10852750995 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (12031214062 / 1000000000000) (12031246464 / 1000000000000)
      | 1 => orderedInterval (-3164314211 / 1000000000000) (-3164314183 / 1000000000000)
      | 2 => orderedInterval (-784379384 / 1000000000000) (-784379364 / 1000000000000)
      | 3 => orderedInterval (23143694610 / 1000000000000) (23143710778 / 1000000000000)
      | 4 => orderedInterval (7818911952 / 1000000000000) (7818912148 / 1000000000000)
      | 5 => orderedInterval (-1142221835 / 1000000000000) (-1142221752 / 1000000000000)
      | 6 => orderedInterval (6196688909 / 1000000000000) (6196688952 / 1000000000000)
      | 7 => orderedInterval (-1698875733 / 1000000000000) (-1698875097 / 1000000000000)
      | _ => orderedInterval (2146511087 / 1000000000000) (2146512407 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (14593711135 / 1000000000000) (14593744280 / 1000000000000)
      | 1 => orderedInterval (7959047350 / 1000000000000) (7959047385 / 1000000000000)
      | 2 => orderedInterval (-995922048 / 1000000000000) (-995922013 / 1000000000000)
      | 3 => orderedInterval (31947136287 / 1000000000000) (31947172520 / 1000000000000)
      | 4 => orderedInterval (-3175883156 / 1000000000000) (-3175882819 / 1000000000000)
      | 5 => orderedInterval (-7896597918 / 1000000000000) (-7896597805 / 1000000000000)
      | 6 => orderedInterval (764461063 / 1000000000000) (764461104 / 1000000000000)
      | 7 => orderedInterval (4267048493 / 1000000000000) (4267049005 / 1000000000000)
      | _ => orderedInterval (-17790339591 / 1000000000000) (-17790337929 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-11310400072 / 1000000000000) (-11310366253 / 1000000000000)
      | 1 => orderedInterval (7118477121 / 1000000000000) (7118477174 / 1000000000000)
      | 2 => orderedInterval (6176519681 / 1000000000000) (6176519745 / 1000000000000)
      | 3 => orderedInterval (-114903309918 / 1000000000000) (-114903228906 / 1000000000000)
      | 4 => orderedInterval (-20678904640 / 1000000000000) (-20678904057 / 1000000000000)
      | 5 => orderedInterval (1958757930 / 1000000000000) (1958758088 / 1000000000000)
      | 6 => orderedInterval (-7638226600 / 1000000000000) (-7638226560 / 1000000000000)
      | 7 => orderedInterval (2116076835 / 1000000000000) (2116077245 / 1000000000000)
      | _ => orderedInterval (-15442372868 / 1000000000000) (-15442370774 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-13085773599 / 1000000000000) (-13085738789 / 1000000000000)
      | 1 => orderedInterval (-17487833459 / 1000000000000) (-17487833379 / 1000000000000)
      | 2 => orderedInterval (4043038916 / 1000000000000) (4043039034 / 1000000000000)
      | 3 => orderedInterval (-182827558495 / 1000000000000) (-182827376891 / 1000000000000)
      | 4 => orderedInterval (12824176815 / 1000000000000) (12824177826 / 1000000000000)
      | 5 => orderedInterval (19332416348 / 1000000000000) (19332416573 / 1000000000000)
      | 6 => orderedInterval (-19418847 / 1000000000000) (-19418808 / 1000000000000)
      | 7 => orderedInterval (-5354801811 / 1000000000000) (-5354801479 / 1000000000000)
      | _ => orderedInterval (33463140054 / 1000000000000) (33463142725 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-16477824138 / 1000000000000) (-16477782846 / 1000000000000)
    | 1 => orderedInterval (44547229457 / 1000000000000) (44547280353 / 1000000000000)
    | 2 => orderedInterval (29672661615 / 1000000000000) (29672733728 / 1000000000000)
    | 3 => orderedInterval (-152603382531 / 1000000000000) (-152603264298 / 1000000000000)
    | _ => orderedInterval (-149112614078 / 1000000000000) (-149112393188 / 1000000000000)

theorem compactCertificate307_stateChecks0 :
    compactCertificate307.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (361 / 2)) (orderedInterval (-47523935380 / 1000000000000) (-47523861126 / 1000000000000), orderedInterval (35746974318 / 1000000000000) (35747048572 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (531821932192261 / 4000000000000)) (orderedInterval (67494687253 / 1000000000000) (67494688082 / 1000000000000), orderedInterval (-15506823564 / 1000000000000) (-15506822736 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (171980285899813 / 800000000000)) (orderedInterval (46075010505 / 1000000000000) (46075052710 / 1000000000000), orderedInterval (-29063176280 / 1000000000000) (-29063134074 / 1000000000000))) = true
  rfl'

theorem compactCertificate307_stateChecks1 :
    compactCertificate307.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (155184313430927 / 4000000000000)) (orderedInterval (122052438891 / 1000000000000) (122052440231 / 1000000000000), orderedInterval (-40450446959 / 1000000000000) (-40450445619 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (416846894354819 / 4000000000000)) (orderedInterval (-75778690180 / 1000000000000) (-75778690179 / 1000000000000), orderedInterval (-18778937535 / 1000000000000) (-18778937534 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1131820406442423 / 4000000000000)) (orderedInterval (39829230837 / 1000000000000) (39829230838 / 1000000000000), orderedInterval (25688651036 / 1000000000000) (25688651037 / 1000000000000))) = true
  rfl'

theorem compactCertificate307_stateChecks2 :
    compactCertificate307.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (833693788709999 / 4000000000000)) (orderedInterval (52922261888 / 1000000000000) (52922264758 / 1000000000000), orderedInterval (-16054307473 / 1000000000000) (-16054304604 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1428548516810027 / 4000000000000)) (orderedInterval (-9188406693 / 1000000000000) (-9188406667 / 1000000000000), orderedInterval (41221342627 / 1000000000000) (41221342653 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1052262371800193 / 4000000000000)) (orderedInterval (-2127788357 / 1000000000000) (-2127788353 / 1000000000000), orderedInterval (49151585492 / 1000000000000) (49151585496 / 1000000000000))) = true
  rfl'

theorem compactCertificate307_stateChecks3 :
    compactCertificate307.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1614441079754639 / 4000000000000)) (orderedInterval (30358003174 / 1000000000000) (30358043306 / 1000000000000), orderedInterval (-25644331811 / 1000000000000) (-25644291679 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (932097991987031 / 4000000000000)) (orderedInterval (50779002870 / 1000000000000) (50779002873 / 1000000000000), orderedInterval (12279496051 / 1000000000000) (12279496054 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1654024243538179 / 4000000000000)) (orderedInterval (-15246229533 / 1000000000000) (-15246229304 / 1000000000000), orderedInterval (36172536361 / 1000000000000) (36172536589 / 1000000000000))) = true
  rfl'

theorem compactCertificate307_stateChecks4 :
    compactCertificate307.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1545404002695151 / 4000000000000)) (orderedInterval (-26771720292 / 1000000000000) (-26771720291 / 1000000000000), orderedInterval (-30478478624 / 1000000000000) (-30478478623 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1102873217252383 / 4000000000000)) (orderedInterval (2070167193 / 1000000000000) (2070167194 / 1000000000000), orderedInterval (48003205446 / 1000000000000) (48003205448 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1250540683064457 / 4000000000000)) (orderedInterval (-30397378143 / 1000000000000) (-30397359829 / 1000000000000), orderedInterval (33399806960 / 1000000000000) (33399825275 / 1000000000000))) = true
  rfl'

theorem compactCertificate307_stateChecks5 :
    compactCertificate307.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1042570446119033 / 4000000000000)) (orderedInterval (-30896547491 / 1000000000000) (-30896547490 / 1000000000000), orderedInterval (-38514102922 / 1000000000000) (-38514102921 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (921142607135693 / 4000000000000)) (orderedInterval (-51877497568 / 1000000000000) (-51877496833 / 1000000000000), orderedInterval (8668206595 / 1000000000000) (8668207330 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (266983030805607 / 800000000000)) (orderedInterval (43581480120 / 1000000000000) (43581480190 / 1000000000000), orderedInterval (2806756137 / 1000000000000) (2806756207 / 1000000000000))) = true
  rfl'

theorem compactCertificate307_stateChecks6 :
    compactCertificate307.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (738489113755429 / 4000000000000)) (orderedInterval (-3112717831 / 1000000000000) (-3112717829 / 1000000000000), orderedInterval (-58630737043 / 1000000000000) (-58630737041 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (626025400273469 / 4000000000000)) (orderedInterval (13377350684 / 1000000000000) (13377350685 / 1000000000000), orderedInterval (62317172756 / 1000000000000) (62317172757 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (391737628199807 / 4000000000000)) (orderedInterval (-78282568953 / 1000000000000) (-78282568951 / 1000000000000), orderedInterval (-18893744769 / 1000000000000) (-18893744768 / 1000000000000))) = true
  rfl'

theorem compactCertificate307_stateChecks7 :
    compactCertificate307.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (210677799306369 / 4000000000000)) (orderedInterval (-4989509410 / 1000000000000) (-4989509405 / 1000000000000), orderedInterval (-109783077096 / 1000000000000) (-109783077092 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (572031207786107 / 4000000000000)) (orderedInterval (-44041380120 / 1000000000000) (-44041345859 / 1000000000000), orderedInterval (50273872969 / 1000000000000) (50273907230 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (781059709779739 / 4000000000000)) (orderedInterval (54551037650 / 1000000000000) (54551037651 / 1000000000000), orderedInterval (16726341726 / 1000000000000) (16726341727 / 1000000000000))) = true
  rfl'

theorem compactCertificate307_stateChecks8 :
    compactCertificate307.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (330262371800193 / 4000000000000)) (orderedInterval (87393406673 / 1000000000000) (87393406791 / 1000000000000), orderedInterval (-9057214605 / 1000000000000) (-9057214486 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1342498205749153 / 4000000000000)) (orderedInterval (-11161274843 / 1000000000000) (-11161274842 / 1000000000000), orderedInterval (-42081460213 / 1000000000000) (-42081460212 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (896726584618127 / 4000000000000)) (orderedInterval (-50192088471 / 1000000000000) (-50192083115 / 1000000000000), orderedInterval (18014421774 / 1000000000000) (18014427129 / 1000000000000))) = true
  rfl'

theorem compactCertificate307_states : ∀ j,
    BesselStateValid (compactCertificate307.point j) (compactCertificate307.state j) :=
  compactCertificate307.statesValid_of_checks3 compactCertificate307_stateChecks0
    compactCertificate307_stateChecks1 compactCertificate307_stateChecks2
    compactCertificate307_stateChecks3 compactCertificate307_stateChecks4
    compactCertificate307_stateChecks5 compactCertificate307_stateChecks6
    compactCertificate307_stateChecks7 compactCertificate307_stateChecks8

theorem compactCertificate307_chunkChecks0_0 :
    compactCertificate307.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (361 / 2) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-47523935380 / 1000000000000) (-47523861126 / 1000000000000), orderedInterval (35746974318 / 1000000000000) (35747048572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (531821932192261 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (67494687253 / 1000000000000) (67494688082 / 1000000000000), orderedInterval (-15506823564 / 1000000000000) (-15506822736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (171980285899813 / 800000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46075010505 / 1000000000000) (46075052710 / 1000000000000), orderedInterval (-29063176280 / 1000000000000) (-29063134074 / 1000000000000)))) (orderedInterval (-15504170633 / 1000000000000) (-15504138704 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (155184313430927 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (122052438891 / 1000000000000) (122052440231 / 1000000000000), orderedInterval (-40450446959 / 1000000000000) (-40450445619 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (416846894354819 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-75778690180 / 1000000000000) (-75778690179 / 1000000000000), orderedInterval (-18778937535 / 1000000000000) (-18778937534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1131820406442423 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (39829230837 / 1000000000000) (39829230838 / 1000000000000), orderedInterval (25688651036 / 1000000000000) (25688651037 / 1000000000000)))) (orderedInterval (-6922440462 / 1000000000000) (-6922440425 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (833693788709999 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (52922261888 / 1000000000000) (52922264758 / 1000000000000), orderedInterval (-16054307473 / 1000000000000) (-16054304604 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1428548516810027 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-9188406693 / 1000000000000) (-9188406667 / 1000000000000), orderedInterval (41221342627 / 1000000000000) (41221342653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1052262371800193 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2127788357 / 1000000000000) (-2127788353 / 1000000000000), orderedInterval (49151585492 / 1000000000000) (49151585496 / 1000000000000)))) (orderedInterval (231982772 / 1000000000000) (231982784 / 1000000000000))) = true
  rfl'

theorem compactCertificate307_chunkChecks0_1 :
    compactCertificate307.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1614441079754639 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30358003174 / 1000000000000) (30358043306 / 1000000000000), orderedInterval (-25644331811 / 1000000000000) (-25644291679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (932097991987031 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (50779002870 / 1000000000000) (50779002873 / 1000000000000), orderedInterval (12279496051 / 1000000000000) (12279496054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1654024243538179 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15246229533 / 1000000000000) (-15246229304 / 1000000000000), orderedInterval (36172536361 / 1000000000000) (36172536589 / 1000000000000)))) (orderedInterval (-3799292895 / 1000000000000) (-3799285659 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1545404002695151 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26771720292 / 1000000000000) (-26771720291 / 1000000000000), orderedInterval (-30478478624 / 1000000000000) (-30478478623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1102873217252383 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2070167193 / 1000000000000) (2070167194 / 1000000000000), orderedInterval (48003205446 / 1000000000000) (48003205448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1250540683064457 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30397378143 / 1000000000000) (-30397359829 / 1000000000000), orderedInterval (33399806960 / 1000000000000) (33399825275 / 1000000000000)))) (orderedInterval (832901250 / 1000000000000) (832901365 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1042570446119033 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30896547491 / 1000000000000) (-30896547490 / 1000000000000), orderedInterval (-38514102922 / 1000000000000) (-38514102921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (921142607135693 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-51877497568 / 1000000000000) (-51877496833 / 1000000000000), orderedInterval (8668206595 / 1000000000000) (8668207330 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (266983030805607 / 800000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (43581480120 / 1000000000000) (43581480190 / 1000000000000), orderedInterval (2806756137 / 1000000000000) (2806756207 / 1000000000000)))) (orderedInterval (3727851649 / 1000000000000) (3727851711 / 1000000000000))) = true
  rfl'

theorem compactCertificate307_chunkChecks0_2 :
    compactCertificate307.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (738489113755429 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-3112717831 / 1000000000000) (-3112717829 / 1000000000000), orderedInterval (-58630737043 / 1000000000000) (-58630737041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (626025400273469 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13377350684 / 1000000000000) (13377350685 / 1000000000000), orderedInterval (62317172756 / 1000000000000) (62317172757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (391737628199807 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-78282568953 / 1000000000000) (-78282568951 / 1000000000000), orderedInterval (-18893744769 / 1000000000000) (-18893744768 / 1000000000000)))) (orderedInterval (-2807967675 / 1000000000000) (-2807967629 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (210677799306369 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-4989509410 / 1000000000000) (-4989509405 / 1000000000000), orderedInterval (-109783077096 / 1000000000000) (-109783077092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (572031207786107 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44041380120 / 1000000000000) (-44041345859 / 1000000000000), orderedInterval (50273872969 / 1000000000000) (50273907230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (781059709779739 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (54551037650 / 1000000000000) (54551037651 / 1000000000000), orderedInterval (16726341726 / 1000000000000) (16726341727 / 1000000000000)))) (orderedInterval (-3089438083 / 1000000000000) (-3089437284 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (330262371800193 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (87393406673 / 1000000000000) (87393406791 / 1000000000000), orderedInterval (-9057214605 / 1000000000000) (-9057214486 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1342498205749153 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11161274843 / 1000000000000) (-11161274842 / 1000000000000), orderedInterval (-42081460213 / 1000000000000) (-42081460212 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (896726584618127 / 4000000000000) 0 (IntervalRat.scale (361 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50192088471 / 1000000000000) (-50192083115 / 1000000000000), orderedInterval (18014421774 / 1000000000000) (18014427129 / 1000000000000)))) (orderedInterval (10852749939 / 1000000000000) (10852750995 / 1000000000000))) = true
  rfl'

theorem compactCertificate307_chunkChecks0 :
    compactCertificate307.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate307.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate307_chunkChecks0_0
    compactCertificate307_chunkChecks0_1 compactCertificate307_chunkChecks0_2

theorem compactCertificate307_chunkChecks1_0 :
    compactCertificate307.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (361 / 2) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-47523935380 / 1000000000000) (-47523861126 / 1000000000000), orderedInterval (35746974318 / 1000000000000) (35747048572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (531821932192261 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (67494687253 / 1000000000000) (67494688082 / 1000000000000), orderedInterval (-15506823564 / 1000000000000) (-15506822736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (171980285899813 / 800000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46075010505 / 1000000000000) (46075052710 / 1000000000000), orderedInterval (-29063176280 / 1000000000000) (-29063134074 / 1000000000000)))) (orderedInterval (12031214062 / 1000000000000) (12031246464 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (155184313430927 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (122052438891 / 1000000000000) (122052440231 / 1000000000000), orderedInterval (-40450446959 / 1000000000000) (-40450445619 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (416846894354819 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-75778690180 / 1000000000000) (-75778690179 / 1000000000000), orderedInterval (-18778937535 / 1000000000000) (-18778937534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1131820406442423 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (39829230837 / 1000000000000) (39829230838 / 1000000000000), orderedInterval (25688651036 / 1000000000000) (25688651037 / 1000000000000)))) (orderedInterval (-3164314211 / 1000000000000) (-3164314183 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (833693788709999 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (52922261888 / 1000000000000) (52922264758 / 1000000000000), orderedInterval (-16054307473 / 1000000000000) (-16054304604 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1428548516810027 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-9188406693 / 1000000000000) (-9188406667 / 1000000000000), orderedInterval (41221342627 / 1000000000000) (41221342653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1052262371800193 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2127788357 / 1000000000000) (-2127788353 / 1000000000000), orderedInterval (49151585492 / 1000000000000) (49151585496 / 1000000000000)))) (orderedInterval (-784379384 / 1000000000000) (-784379364 / 1000000000000))) = true
  rfl'

theorem compactCertificate307_chunkChecks1_1 :
    compactCertificate307.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1614441079754639 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30358003174 / 1000000000000) (30358043306 / 1000000000000), orderedInterval (-25644331811 / 1000000000000) (-25644291679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (932097991987031 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (50779002870 / 1000000000000) (50779002873 / 1000000000000), orderedInterval (12279496051 / 1000000000000) (12279496054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1654024243538179 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15246229533 / 1000000000000) (-15246229304 / 1000000000000), orderedInterval (36172536361 / 1000000000000) (36172536589 / 1000000000000)))) (orderedInterval (23143694610 / 1000000000000) (23143710778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1545404002695151 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26771720292 / 1000000000000) (-26771720291 / 1000000000000), orderedInterval (-30478478624 / 1000000000000) (-30478478623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1102873217252383 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2070167193 / 1000000000000) (2070167194 / 1000000000000), orderedInterval (48003205446 / 1000000000000) (48003205448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1250540683064457 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30397378143 / 1000000000000) (-30397359829 / 1000000000000), orderedInterval (33399806960 / 1000000000000) (33399825275 / 1000000000000)))) (orderedInterval (7818911952 / 1000000000000) (7818912148 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1042570446119033 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30896547491 / 1000000000000) (-30896547490 / 1000000000000), orderedInterval (-38514102922 / 1000000000000) (-38514102921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (921142607135693 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-51877497568 / 1000000000000) (-51877496833 / 1000000000000), orderedInterval (8668206595 / 1000000000000) (8668207330 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (266983030805607 / 800000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (43581480120 / 1000000000000) (43581480190 / 1000000000000), orderedInterval (2806756137 / 1000000000000) (2806756207 / 1000000000000)))) (orderedInterval (-1142221835 / 1000000000000) (-1142221752 / 1000000000000))) = true
  rfl'

theorem compactCertificate307_chunkChecks1_2 :
    compactCertificate307.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (738489113755429 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-3112717831 / 1000000000000) (-3112717829 / 1000000000000), orderedInterval (-58630737043 / 1000000000000) (-58630737041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (626025400273469 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13377350684 / 1000000000000) (13377350685 / 1000000000000), orderedInterval (62317172756 / 1000000000000) (62317172757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (391737628199807 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-78282568953 / 1000000000000) (-78282568951 / 1000000000000), orderedInterval (-18893744769 / 1000000000000) (-18893744768 / 1000000000000)))) (orderedInterval (6196688909 / 1000000000000) (6196688952 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (210677799306369 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-4989509410 / 1000000000000) (-4989509405 / 1000000000000), orderedInterval (-109783077096 / 1000000000000) (-109783077092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (572031207786107 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44041380120 / 1000000000000) (-44041345859 / 1000000000000), orderedInterval (50273872969 / 1000000000000) (50273907230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (781059709779739 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (54551037650 / 1000000000000) (54551037651 / 1000000000000), orderedInterval (16726341726 / 1000000000000) (16726341727 / 1000000000000)))) (orderedInterval (-1698875733 / 1000000000000) (-1698875097 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (330262371800193 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (87393406673 / 1000000000000) (87393406791 / 1000000000000), orderedInterval (-9057214605 / 1000000000000) (-9057214486 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1342498205749153 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11161274843 / 1000000000000) (-11161274842 / 1000000000000), orderedInterval (-42081460213 / 1000000000000) (-42081460212 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (896726584618127 / 4000000000000) 1 (IntervalRat.scale (361 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50192088471 / 1000000000000) (-50192083115 / 1000000000000), orderedInterval (18014421774 / 1000000000000) (18014427129 / 1000000000000)))) (orderedInterval (2146511087 / 1000000000000) (2146512407 / 1000000000000))) = true
  rfl'

theorem compactCertificate307_chunkChecks1 :
    compactCertificate307.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate307.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate307_chunkChecks1_0
    compactCertificate307_chunkChecks1_1 compactCertificate307_chunkChecks1_2

theorem compactCertificate307_chunkChecks2_0 :
    compactCertificate307.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (361 / 2) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-47523935380 / 1000000000000) (-47523861126 / 1000000000000), orderedInterval (35746974318 / 1000000000000) (35747048572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (531821932192261 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (67494687253 / 1000000000000) (67494688082 / 1000000000000), orderedInterval (-15506823564 / 1000000000000) (-15506822736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (171980285899813 / 800000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46075010505 / 1000000000000) (46075052710 / 1000000000000), orderedInterval (-29063176280 / 1000000000000) (-29063134074 / 1000000000000)))) (orderedInterval (14593711135 / 1000000000000) (14593744280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (155184313430927 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (122052438891 / 1000000000000) (122052440231 / 1000000000000), orderedInterval (-40450446959 / 1000000000000) (-40450445619 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (416846894354819 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-75778690180 / 1000000000000) (-75778690179 / 1000000000000), orderedInterval (-18778937535 / 1000000000000) (-18778937534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1131820406442423 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (39829230837 / 1000000000000) (39829230838 / 1000000000000), orderedInterval (25688651036 / 1000000000000) (25688651037 / 1000000000000)))) (orderedInterval (7959047350 / 1000000000000) (7959047385 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (833693788709999 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (52922261888 / 1000000000000) (52922264758 / 1000000000000), orderedInterval (-16054307473 / 1000000000000) (-16054304604 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1428548516810027 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-9188406693 / 1000000000000) (-9188406667 / 1000000000000), orderedInterval (41221342627 / 1000000000000) (41221342653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1052262371800193 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2127788357 / 1000000000000) (-2127788353 / 1000000000000), orderedInterval (49151585492 / 1000000000000) (49151585496 / 1000000000000)))) (orderedInterval (-995922048 / 1000000000000) (-995922013 / 1000000000000))) = true
  rfl'

theorem compactCertificate307_chunkChecks2_1 :
    compactCertificate307.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1614441079754639 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30358003174 / 1000000000000) (30358043306 / 1000000000000), orderedInterval (-25644331811 / 1000000000000) (-25644291679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (932097991987031 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (50779002870 / 1000000000000) (50779002873 / 1000000000000), orderedInterval (12279496051 / 1000000000000) (12279496054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1654024243538179 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15246229533 / 1000000000000) (-15246229304 / 1000000000000), orderedInterval (36172536361 / 1000000000000) (36172536589 / 1000000000000)))) (orderedInterval (31947136287 / 1000000000000) (31947172520 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1545404002695151 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26771720292 / 1000000000000) (-26771720291 / 1000000000000), orderedInterval (-30478478624 / 1000000000000) (-30478478623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1102873217252383 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2070167193 / 1000000000000) (2070167194 / 1000000000000), orderedInterval (48003205446 / 1000000000000) (48003205448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1250540683064457 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30397378143 / 1000000000000) (-30397359829 / 1000000000000), orderedInterval (33399806960 / 1000000000000) (33399825275 / 1000000000000)))) (orderedInterval (-3175883156 / 1000000000000) (-3175882819 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1042570446119033 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30896547491 / 1000000000000) (-30896547490 / 1000000000000), orderedInterval (-38514102922 / 1000000000000) (-38514102921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (921142607135693 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-51877497568 / 1000000000000) (-51877496833 / 1000000000000), orderedInterval (8668206595 / 1000000000000) (8668207330 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (266983030805607 / 800000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (43581480120 / 1000000000000) (43581480190 / 1000000000000), orderedInterval (2806756137 / 1000000000000) (2806756207 / 1000000000000)))) (orderedInterval (-7896597918 / 1000000000000) (-7896597805 / 1000000000000))) = true
  rfl'

theorem compactCertificate307_chunkChecks2_2 :
    compactCertificate307.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (738489113755429 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-3112717831 / 1000000000000) (-3112717829 / 1000000000000), orderedInterval (-58630737043 / 1000000000000) (-58630737041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (626025400273469 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13377350684 / 1000000000000) (13377350685 / 1000000000000), orderedInterval (62317172756 / 1000000000000) (62317172757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (391737628199807 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-78282568953 / 1000000000000) (-78282568951 / 1000000000000), orderedInterval (-18893744769 / 1000000000000) (-18893744768 / 1000000000000)))) (orderedInterval (764461063 / 1000000000000) (764461104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (210677799306369 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-4989509410 / 1000000000000) (-4989509405 / 1000000000000), orderedInterval (-109783077096 / 1000000000000) (-109783077092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (572031207786107 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44041380120 / 1000000000000) (-44041345859 / 1000000000000), orderedInterval (50273872969 / 1000000000000) (50273907230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (781059709779739 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (54551037650 / 1000000000000) (54551037651 / 1000000000000), orderedInterval (16726341726 / 1000000000000) (16726341727 / 1000000000000)))) (orderedInterval (4267048493 / 1000000000000) (4267049005 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (330262371800193 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (87393406673 / 1000000000000) (87393406791 / 1000000000000), orderedInterval (-9057214605 / 1000000000000) (-9057214486 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1342498205749153 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11161274843 / 1000000000000) (-11161274842 / 1000000000000), orderedInterval (-42081460213 / 1000000000000) (-42081460212 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (896726584618127 / 4000000000000) 2 (IntervalRat.scale (361 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50192088471 / 1000000000000) (-50192083115 / 1000000000000), orderedInterval (18014421774 / 1000000000000) (18014427129 / 1000000000000)))) (orderedInterval (-17790339591 / 1000000000000) (-17790337929 / 1000000000000))) = true
  rfl'

theorem compactCertificate307_chunkChecks2 :
    compactCertificate307.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate307.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate307_chunkChecks2_0
    compactCertificate307_chunkChecks2_1 compactCertificate307_chunkChecks2_2

theorem compactCertificate307_chunkChecks3_0 :
    compactCertificate307.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (361 / 2) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-47523935380 / 1000000000000) (-47523861126 / 1000000000000), orderedInterval (35746974318 / 1000000000000) (35747048572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (531821932192261 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (67494687253 / 1000000000000) (67494688082 / 1000000000000), orderedInterval (-15506823564 / 1000000000000) (-15506822736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (171980285899813 / 800000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46075010505 / 1000000000000) (46075052710 / 1000000000000), orderedInterval (-29063176280 / 1000000000000) (-29063134074 / 1000000000000)))) (orderedInterval (-11310400072 / 1000000000000) (-11310366253 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (155184313430927 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (122052438891 / 1000000000000) (122052440231 / 1000000000000), orderedInterval (-40450446959 / 1000000000000) (-40450445619 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (416846894354819 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-75778690180 / 1000000000000) (-75778690179 / 1000000000000), orderedInterval (-18778937535 / 1000000000000) (-18778937534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1131820406442423 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (39829230837 / 1000000000000) (39829230838 / 1000000000000), orderedInterval (25688651036 / 1000000000000) (25688651037 / 1000000000000)))) (orderedInterval (7118477121 / 1000000000000) (7118477174 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (833693788709999 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (52922261888 / 1000000000000) (52922264758 / 1000000000000), orderedInterval (-16054307473 / 1000000000000) (-16054304604 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1428548516810027 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-9188406693 / 1000000000000) (-9188406667 / 1000000000000), orderedInterval (41221342627 / 1000000000000) (41221342653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1052262371800193 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2127788357 / 1000000000000) (-2127788353 / 1000000000000), orderedInterval (49151585492 / 1000000000000) (49151585496 / 1000000000000)))) (orderedInterval (6176519681 / 1000000000000) (6176519745 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate307_chunkChecks3_1 :
    compactCertificate307.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1614441079754639 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30358003174 / 1000000000000) (30358043306 / 1000000000000), orderedInterval (-25644331811 / 1000000000000) (-25644291679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (932097991987031 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (50779002870 / 1000000000000) (50779002873 / 1000000000000), orderedInterval (12279496051 / 1000000000000) (12279496054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1654024243538179 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15246229533 / 1000000000000) (-15246229304 / 1000000000000), orderedInterval (36172536361 / 1000000000000) (36172536589 / 1000000000000)))) (orderedInterval (-114903309918 / 1000000000000) (-114903228906 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1545404002695151 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26771720292 / 1000000000000) (-26771720291 / 1000000000000), orderedInterval (-30478478624 / 1000000000000) (-30478478623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1102873217252383 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2070167193 / 1000000000000) (2070167194 / 1000000000000), orderedInterval (48003205446 / 1000000000000) (48003205448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1250540683064457 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30397378143 / 1000000000000) (-30397359829 / 1000000000000), orderedInterval (33399806960 / 1000000000000) (33399825275 / 1000000000000)))) (orderedInterval (-20678904640 / 1000000000000) (-20678904057 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1042570446119033 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30896547491 / 1000000000000) (-30896547490 / 1000000000000), orderedInterval (-38514102922 / 1000000000000) (-38514102921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (921142607135693 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-51877497568 / 1000000000000) (-51877496833 / 1000000000000), orderedInterval (8668206595 / 1000000000000) (8668207330 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (266983030805607 / 800000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (43581480120 / 1000000000000) (43581480190 / 1000000000000), orderedInterval (2806756137 / 1000000000000) (2806756207 / 1000000000000)))) (orderedInterval (1958757930 / 1000000000000) (1958758088 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate307_chunkChecks3_2 :
    compactCertificate307.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (738489113755429 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-3112717831 / 1000000000000) (-3112717829 / 1000000000000), orderedInterval (-58630737043 / 1000000000000) (-58630737041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (626025400273469 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13377350684 / 1000000000000) (13377350685 / 1000000000000), orderedInterval (62317172756 / 1000000000000) (62317172757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (391737628199807 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-78282568953 / 1000000000000) (-78282568951 / 1000000000000), orderedInterval (-18893744769 / 1000000000000) (-18893744768 / 1000000000000)))) (orderedInterval (-7638226600 / 1000000000000) (-7638226560 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (210677799306369 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-4989509410 / 1000000000000) (-4989509405 / 1000000000000), orderedInterval (-109783077096 / 1000000000000) (-109783077092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (572031207786107 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44041380120 / 1000000000000) (-44041345859 / 1000000000000), orderedInterval (50273872969 / 1000000000000) (50273907230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (781059709779739 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (54551037650 / 1000000000000) (54551037651 / 1000000000000), orderedInterval (16726341726 / 1000000000000) (16726341727 / 1000000000000)))) (orderedInterval (2116076835 / 1000000000000) (2116077245 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (330262371800193 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (87393406673 / 1000000000000) (87393406791 / 1000000000000), orderedInterval (-9057214605 / 1000000000000) (-9057214486 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1342498205749153 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11161274843 / 1000000000000) (-11161274842 / 1000000000000), orderedInterval (-42081460213 / 1000000000000) (-42081460212 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (896726584618127 / 4000000000000) 3 (IntervalRat.scale (361 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50192088471 / 1000000000000) (-50192083115 / 1000000000000), orderedInterval (18014421774 / 1000000000000) (18014427129 / 1000000000000)))) (orderedInterval (-15442372868 / 1000000000000) (-15442370774 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate307_chunkChecks3 :
    compactCertificate307.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate307.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate307_chunkChecks3_0
    compactCertificate307_chunkChecks3_1 compactCertificate307_chunkChecks3_2

theorem compactCertificate307_chunkChecks4_0 :
    compactCertificate307.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (361 / 2) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-47523935380 / 1000000000000) (-47523861126 / 1000000000000), orderedInterval (35746974318 / 1000000000000) (35747048572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (531821932192261 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (67494687253 / 1000000000000) (67494688082 / 1000000000000), orderedInterval (-15506823564 / 1000000000000) (-15506822736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (171980285899813 / 800000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (46075010505 / 1000000000000) (46075052710 / 1000000000000), orderedInterval (-29063176280 / 1000000000000) (-29063134074 / 1000000000000)))) (orderedInterval (-13085773599 / 1000000000000) (-13085738789 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (155184313430927 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (122052438891 / 1000000000000) (122052440231 / 1000000000000), orderedInterval (-40450446959 / 1000000000000) (-40450445619 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (416846894354819 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-75778690180 / 1000000000000) (-75778690179 / 1000000000000), orderedInterval (-18778937535 / 1000000000000) (-18778937534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1131820406442423 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (39829230837 / 1000000000000) (39829230838 / 1000000000000), orderedInterval (25688651036 / 1000000000000) (25688651037 / 1000000000000)))) (orderedInterval (-17487833459 / 1000000000000) (-17487833379 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (833693788709999 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (52922261888 / 1000000000000) (52922264758 / 1000000000000), orderedInterval (-16054307473 / 1000000000000) (-16054304604 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1428548516810027 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-9188406693 / 1000000000000) (-9188406667 / 1000000000000), orderedInterval (41221342627 / 1000000000000) (41221342653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1052262371800193 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2127788357 / 1000000000000) (-2127788353 / 1000000000000), orderedInterval (49151585492 / 1000000000000) (49151585496 / 1000000000000)))) (orderedInterval (4043038916 / 1000000000000) (4043039034 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate307_chunkChecks4_1 :
    compactCertificate307.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1614441079754639 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30358003174 / 1000000000000) (30358043306 / 1000000000000), orderedInterval (-25644331811 / 1000000000000) (-25644291679 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (932097991987031 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (50779002870 / 1000000000000) (50779002873 / 1000000000000), orderedInterval (12279496051 / 1000000000000) (12279496054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1654024243538179 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15246229533 / 1000000000000) (-15246229304 / 1000000000000), orderedInterval (36172536361 / 1000000000000) (36172536589 / 1000000000000)))) (orderedInterval (-182827558495 / 1000000000000) (-182827376891 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1545404002695151 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26771720292 / 1000000000000) (-26771720291 / 1000000000000), orderedInterval (-30478478624 / 1000000000000) (-30478478623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1102873217252383 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2070167193 / 1000000000000) (2070167194 / 1000000000000), orderedInterval (48003205446 / 1000000000000) (48003205448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1250540683064457 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30397378143 / 1000000000000) (-30397359829 / 1000000000000), orderedInterval (33399806960 / 1000000000000) (33399825275 / 1000000000000)))) (orderedInterval (12824176815 / 1000000000000) (12824177826 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1042570446119033 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30896547491 / 1000000000000) (-30896547490 / 1000000000000), orderedInterval (-38514102922 / 1000000000000) (-38514102921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (921142607135693 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-51877497568 / 1000000000000) (-51877496833 / 1000000000000), orderedInterval (8668206595 / 1000000000000) (8668207330 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (266983030805607 / 800000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (43581480120 / 1000000000000) (43581480190 / 1000000000000), orderedInterval (2806756137 / 1000000000000) (2806756207 / 1000000000000)))) (orderedInterval (19332416348 / 1000000000000) (19332416573 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate307_chunkChecks4_2 :
    compactCertificate307.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (738489113755429 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-3112717831 / 1000000000000) (-3112717829 / 1000000000000), orderedInterval (-58630737043 / 1000000000000) (-58630737041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (626025400273469 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (13377350684 / 1000000000000) (13377350685 / 1000000000000), orderedInterval (62317172756 / 1000000000000) (62317172757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (391737628199807 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-78282568953 / 1000000000000) (-78282568951 / 1000000000000), orderedInterval (-18893744769 / 1000000000000) (-18893744768 / 1000000000000)))) (orderedInterval (-19418847 / 1000000000000) (-19418808 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (210677799306369 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-4989509410 / 1000000000000) (-4989509405 / 1000000000000), orderedInterval (-109783077096 / 1000000000000) (-109783077092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (572031207786107 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44041380120 / 1000000000000) (-44041345859 / 1000000000000), orderedInterval (50273872969 / 1000000000000) (50273907230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (781059709779739 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (54551037650 / 1000000000000) (54551037651 / 1000000000000), orderedInterval (16726341726 / 1000000000000) (16726341727 / 1000000000000)))) (orderedInterval (-5354801811 / 1000000000000) (-5354801479 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (330262371800193 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (87393406673 / 1000000000000) (87393406791 / 1000000000000), orderedInterval (-9057214605 / 1000000000000) (-9057214486 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1342498205749153 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-11161274843 / 1000000000000) (-11161274842 / 1000000000000), orderedInterval (-42081460213 / 1000000000000) (-42081460212 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (896726584618127 / 4000000000000) 4 (IntervalRat.scale (361 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50192088471 / 1000000000000) (-50192083115 / 1000000000000), orderedInterval (18014421774 / 1000000000000) (18014427129 / 1000000000000)))) (orderedInterval (33463140054 / 1000000000000) (33463142725 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate307_chunkChecks4 :
    compactCertificate307.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate307.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate307_chunkChecks4_0
    compactCertificate307_chunkChecks4_1 compactCertificate307_chunkChecks4_2

theorem compactCertificate307_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate307.chunkCheck r b = true :=
  compactCertificate307.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate307_chunkChecks0
    · exact compactCertificate307_chunkChecks1
    · exact compactCertificate307_chunkChecks2
    · exact compactCertificate307_chunkChecks3
    · exact compactCertificate307_chunkChecks4)

theorem compactCertificate307_coefficient0 :
    compactCertificate307.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate307_coefficient1 :
    compactCertificate307.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate307_coefficient2 :
    compactCertificate307.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate307_coefficient3 :
    compactCertificate307.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate307_coefficient4 :
    compactCertificate307.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate307_coefficients : ∀ r : Fin 5,
    compactCertificate307.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate307_coefficient0
  · exact compactCertificate307_coefficient1
  · exact compactCertificate307_coefficient2
  · exact compactCertificate307_coefficient3
  · exact compactCertificate307_coefficient4

theorem compactCertificate307_lower : (1 : ℚ) ≤ compactCertificate307.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate307, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate307_proves {t : ℝ} (ht : t ∈ compactCertificate307.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate307.proves compactCertificate307_states compactCertificate307_chunks
    compactCertificate307_coefficients compactCertificate307_lower ht

end Erdos232
