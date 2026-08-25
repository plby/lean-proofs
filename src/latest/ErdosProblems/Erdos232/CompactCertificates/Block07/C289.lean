/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate289 : CompactCertificate where
  left := 163
  right := 164
  center := 327 / 2
  grid := fun i =>
    match i.val with
    | 0 => 52
    | 1 => 38
    | 2 => 62
    | 3 => 11
    | 4 => 30
    | 5 => 82
    | 6 => 60
    | 7 => 103
    | 8 => 76
    | 9 => 116
    | 10 => 67
    | 11 => 119
    | 12 => 111
    | 13 => 80
    | 14 => 90
    | 15 => 75
    | 16 => 66
    | 17 => 96
    | 18 => 53
    | 19 => 45
    | 20 => 28
    | 21 => 15
    | 22 => 41
    | 23 => 56
    | 24 => 24
    | 25 => 97
    | _ => 65
  point := fun i =>
    match i.val with
    | 0 => 327 / 2
    | 1 => 481733439963627 / 4000000000000
    | 2 => 155782696646091 / 800000000000
    | 3 => 140568616321089 / 4000000000000
    | 4 => 377587076049933 / 4000000000000
    | 5 => 1025222362622361 / 4000000000000
    | 6 => 755174152100193 / 4000000000000
    | 7 => 1294003781154789 / 4000000000000
    | 8 => 953157328472751 / 4000000000000
    | 9 => 1462388457284673 / 4000000000000
    | 10 => 844310369473017 / 4000000000000
    | 11 => 1498243566861453 / 4000000000000
    | 12 => 1399853487205857 / 4000000000000
    | 13 => 999001501500081 / 4000000000000
    | 14 => 1132761228149799 / 4000000000000
    | 15 => 944378215736631 / 4000000000000
    | 16 => 834386793721251 / 4000000000000
    | 17 => 241837814607849 / 800000000000
    | 18 => 668936122432203 / 4000000000000
    | 19 => 567064559250483 / 4000000000000
    | 20 => 354842671527249 / 4000000000000
    | 21 => 190835568900783 / 4000000000000
    | 22 => 518155692371349 / 4000000000000
    | 23 => 707497299440373 / 4000000000000
    | 24 => 299157328472751 / 4000000000000
    | 25 => 1216057931523471 / 4000000000000
    | _ => 812270341191489 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (49713590961 / 1000000000000) (49713590962 / 1000000000000), orderedInterval (37560740241 / 1000000000000) (37560740242 / 1000000000000))
    | 1 => (orderedInterval (70140344725 / 1000000000000) (70140346024 / 1000000000000), orderedInterval (-19431929483 / 1000000000000) (-19431928185 / 1000000000000))
    | 2 => (orderedInterval (38316261356 / 1000000000000) (38316261357 / 1000000000000), orderedInterval (42341409326 / 1000000000000) (42341409327 / 1000000000000))
    | 3 => (orderedInterval (-131787760076 / 1000000000000) (-131787760074 / 1000000000000), orderedInterval (-25435843905 / 1000000000000) (-25435843904 / 1000000000000))
    | 4 => (orderedInterval (65980562563 / 1000000000000) (65980562564 / 1000000000000), orderedInterval (48544513738 / 1000000000000) (48544513739 / 1000000000000))
    | 5 => (orderedInterval (-24767685994 / 1000000000000) (-24767683396 / 1000000000000), orderedInterval (43296380893 / 1000000000000) (43296383490 / 1000000000000))
    | 6 => (orderedInterval (51288688424 / 1000000000000) (51288688425 / 1000000000000), orderedInterval (27094775785 / 1000000000000) (27094775786 / 1000000000000))
    | 7 => (orderedInterval (-28643065940 / 1000000000000) (-28643065939 / 1000000000000), orderedInterval (-33830235657 / 1000000000000) (-33830235656 / 1000000000000))
    | 8 => (orderedInterval (15923449435 / 1000000000000) (15923449436 / 1000000000000), orderedInterval (49140500652 / 1000000000000) (49140500653 / 1000000000000))
    | 9 => (orderedInterval (38648867477 / 1000000000000) (38648884491 / 1000000000000), orderedInterval (-15787486117 / 1000000000000) (-15787469104 / 1000000000000))
    | 10 => (orderedInterval (-53876505735 / 1000000000000) (-53876505732 / 1000000000000), orderedInterval (-10519467665 / 1000000000000) (-10519467661 / 1000000000000))
    | 11 => (orderedInterval (-41112762239 / 1000000000000) (-41112762155 / 1000000000000), orderedInterval (-3008159713 / 1000000000000) (-3008159629 / 1000000000000))
    | 12 => (orderedInterval (-38201725744 / 1000000000000) (-38201694128 / 1000000000000), orderedInterval (19021170860 / 1000000000000) (19021202476 / 1000000000000))
    | 13 => (orderedInterval (-35940139034 / 1000000000000) (-35940098940 / 1000000000000), orderedInterval (35530808848 / 1000000000000) (35530848943 / 1000000000000))
    | 14 => (orderedInterval (44716963039 / 1000000000000) (44716963040 / 1000000000000), orderedInterval (15682348904 / 1000000000000) (15682348905 / 1000000000000))
    | 15 => (orderedInterval (-49439158647 / 1000000000000) (-49439158646 / 1000000000000), orderedInterval (-15776914916 / 1000000000000) (-15776914914 / 1000000000000))
    | 16 => (orderedInterval (49363815999 / 1000000000000) (49363832944 / 1000000000000), orderedInterval (-24920032366 / 1000000000000) (-24920015420 / 1000000000000))
    | 17 => (orderedInterval (45738392858 / 1000000000000) (45738392903 / 1000000000000), orderedInterval (3657460383 / 1000000000000) (3657460427 / 1000000000000))
    | 18 => (orderedInterval (-61600264259 / 1000000000000) (-61600264235 / 1000000000000), orderedInterval (-3301550836 / 1000000000000) (-3301550812 / 1000000000000))
    | 19 => (orderedInterval (-61933786249 / 1000000000000) (-61933786248 / 1000000000000), orderedInterval (-25371013462 / 1000000000000) (-25371013461 / 1000000000000))
    | 20 => (orderedInterval (84642463144 / 1000000000000) (84642463160 / 1000000000000), orderedInterval (2972696896 / 1000000000000) (2972696912 / 1000000000000))
    | 21 => (orderedInterval (-113140099364 / 1000000000000) (-113140099362 / 1000000000000), orderedInterval (-22105684112 / 1000000000000) (-22105684110 / 1000000000000))
    | 22 => (orderedInterval (-70005804947 / 1000000000000) (-70005804929 / 1000000000000), orderedInterval (-3425268935 / 1000000000000) (-3425268917 / 1000000000000))
    | 23 => (orderedInterval (59236804233 / 1000000000000) (59236804732 / 1000000000000), orderedInterval (-9668232510 / 1000000000000) (-9668232011 / 1000000000000))
    | 24 => (orderedInterval (16048332968 / 1000000000000) (16048332969 / 1000000000000), orderedInterval (90748662022 / 1000000000000) (90748662024 / 1000000000000))
    | 25 => (orderedInterval (-2971551382 / 1000000000000) (-2971551381 / 1000000000000), orderedInterval (-45659288239 / 1000000000000) (-45659288238 / 1000000000000))
    | _ => (orderedInterval (19259943360 / 1000000000000) (19259943847 / 1000000000000), orderedInterval (-52621903610 / 1000000000000) (-52621903122 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (22606740965 / 1000000000000) (22606740989 / 1000000000000)
      | 1 => orderedInterval (5599595011 / 1000000000000) (5599595216 / 1000000000000)
      | 2 => orderedInterval (1268305105 / 1000000000000) (1268305115 / 1000000000000)
      | 3 => orderedInterval (-16703667274 / 1000000000000) (-16703664173 / 1000000000000)
      | 4 => orderedInterval (-2935237682 / 1000000000000) (-2935233300 / 1000000000000)
      | 5 => orderedInterval (-2224751697 / 1000000000000) (-2224750710 / 1000000000000)
      | 6 => orderedInterval (16110424558 / 1000000000000) (16110424604 / 1000000000000)
      | 7 => orderedInterval (-862484579 / 1000000000000) (-862484521 / 1000000000000)
      | _ => orderedInterval (-3275042219 / 1000000000000) (-3275042082 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (17713595611 / 1000000000000) (17713595634 / 1000000000000)
      | 1 => orderedInterval (-3742374839 / 1000000000000) (-3742374526 / 1000000000000)
      | 2 => orderedInterval (3795471230 / 1000000000000) (3795471246 / 1000000000000)
      | 3 => orderedInterval (4286855527 / 1000000000000) (4286862450 / 1000000000000)
      | 4 => orderedInterval (4259854316 / 1000000000000) (4259861362 / 1000000000000)
      | 5 => orderedInterval (1729499012 / 1000000000000) (1729500274 / 1000000000000)
      | 6 => orderedInterval (1837570341 / 1000000000000) (1837570384 / 1000000000000)
      | 7 => orderedInterval (982247803 / 1000000000000) (982247863 / 1000000000000)
      | _ => orderedInterval (19423850117 / 1000000000000) (19423850295 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-23357045479 / 1000000000000) (-23357045456 / 1000000000000)
      | 1 => orderedInterval (-5173042072 / 1000000000000) (-5173041585 / 1000000000000)
      | 2 => orderedInterval (-4299290210 / 1000000000000) (-4299290181 / 1000000000000)
      | 3 => orderedInterval (71636595076 / 1000000000000) (71636610585 / 1000000000000)
      | 4 => orderedInterval (5423203025 / 1000000000000) (5423214582 / 1000000000000)
      | 5 => orderedInterval (1774708623 / 1000000000000) (1774710247 / 1000000000000)
      | 6 => orderedInterval (-13762313612 / 1000000000000) (-13762313571 / 1000000000000)
      | 7 => orderedInterval (4132098608 / 1000000000000) (4132098671 / 1000000000000)
      | _ => orderedInterval (4599000388 / 1000000000000) (4599000624 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-18869451515 / 1000000000000) (-18869451492 / 1000000000000)
      | 1 => orderedInterval (11544762955 / 1000000000000) (11544763716 / 1000000000000)
      | 2 => orderedInterval (-11732683143 / 1000000000000) (-11732683090 / 1000000000000)
      | 3 => orderedInterval (-24983188982 / 1000000000000) (-24983154316 / 1000000000000)
      | 4 => orderedInterval (-8228606239 / 1000000000000) (-8228586969 / 1000000000000)
      | 5 => orderedInterval (-3015646963 / 1000000000000) (-3015644880 / 1000000000000)
      | 6 => orderedInterval (-1432200654 / 1000000000000) (-1432200614 / 1000000000000)
      | 7 => orderedInterval (-1012099005 / 1000000000000) (-1012098938 / 1000000000000)
      | _ => orderedInterval (-42889967942 / 1000000000000) (-42889967620 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (24651122043 / 1000000000000) (24651122068 / 1000000000000)
      | 1 => orderedInterval (10762243498 / 1000000000000) (10762244694 / 1000000000000)
      | 2 => orderedInterval (15419746417 / 1000000000000) (15419746514 / 1000000000000)
      | 3 => orderedInterval (-343441730059 / 1000000000000) (-343441652335 / 1000000000000)
      | 4 => orderedInterval (-5963126431 / 1000000000000) (-5963093422 / 1000000000000)
      | 5 => orderedInterval (3755470453 / 1000000000000) (3755473143 / 1000000000000)
      | 6 => orderedInterval (13017645624 / 1000000000000) (13017645664 / 1000000000000)
      | 7 => orderedInterval (-5564202191 / 1000000000000) (-5564202118 / 1000000000000)
      | _ => orderedInterval (-5178304432 / 1000000000000) (-5178303979 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (19583882188 / 1000000000000) (19583891138 / 1000000000000)
    | 1 => orderedInterval (50286569118 / 1000000000000) (50286584982 / 1000000000000)
    | 2 => orderedInterval (40973914347 / 1000000000000) (40973943916 / 1000000000000)
    | 3 => orderedInterval (-100619081488 / 1000000000000) (-100619024203 / 1000000000000)
    | _ => orderedInterval (-292541135078 / 1000000000000) (-292541019771 / 1000000000000)

theorem compactCertificate289_stateChecks0 :
    compactCertificate289.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (327 / 2)) (orderedInterval (49713590961 / 1000000000000) (49713590962 / 1000000000000), orderedInterval (37560740241 / 1000000000000) (37560740242 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (481733439963627 / 4000000000000)) (orderedInterval (70140344725 / 1000000000000) (70140346024 / 1000000000000), orderedInterval (-19431929483 / 1000000000000) (-19431928185 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (155782696646091 / 800000000000)) (orderedInterval (38316261356 / 1000000000000) (38316261357 / 1000000000000), orderedInterval (42341409326 / 1000000000000) (42341409327 / 1000000000000))) = true
  rfl'

theorem compactCertificate289_stateChecks1 :
    compactCertificate289.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (140568616321089 / 4000000000000)) (orderedInterval (-131787760076 / 1000000000000) (-131787760074 / 1000000000000), orderedInterval (-25435843905 / 1000000000000) (-25435843904 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (377587076049933 / 4000000000000)) (orderedInterval (65980562563 / 1000000000000) (65980562564 / 1000000000000), orderedInterval (48544513738 / 1000000000000) (48544513739 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1025222362622361 / 4000000000000)) (orderedInterval (-24767685994 / 1000000000000) (-24767683396 / 1000000000000), orderedInterval (43296380893 / 1000000000000) (43296383490 / 1000000000000))) = true
  rfl'

theorem compactCertificate289_stateChecks2 :
    compactCertificate289.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (755174152100193 / 4000000000000)) (orderedInterval (51288688424 / 1000000000000) (51288688425 / 1000000000000), orderedInterval (27094775785 / 1000000000000) (27094775786 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1294003781154789 / 4000000000000)) (orderedInterval (-28643065940 / 1000000000000) (-28643065939 / 1000000000000), orderedInterval (-33830235657 / 1000000000000) (-33830235656 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (953157328472751 / 4000000000000)) (orderedInterval (15923449435 / 1000000000000) (15923449436 / 1000000000000), orderedInterval (49140500652 / 1000000000000) (49140500653 / 1000000000000))) = true
  rfl'

theorem compactCertificate289_stateChecks3 :
    compactCertificate289.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1462388457284673 / 4000000000000)) (orderedInterval (38648867477 / 1000000000000) (38648884491 / 1000000000000), orderedInterval (-15787486117 / 1000000000000) (-15787469104 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (844310369473017 / 4000000000000)) (orderedInterval (-53876505735 / 1000000000000) (-53876505732 / 1000000000000), orderedInterval (-10519467665 / 1000000000000) (-10519467661 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1498243566861453 / 4000000000000)) (orderedInterval (-41112762239 / 1000000000000) (-41112762155 / 1000000000000), orderedInterval (-3008159713 / 1000000000000) (-3008159629 / 1000000000000))) = true
  rfl'

theorem compactCertificate289_stateChecks4 :
    compactCertificate289.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1399853487205857 / 4000000000000)) (orderedInterval (-38201725744 / 1000000000000) (-38201694128 / 1000000000000), orderedInterval (19021170860 / 1000000000000) (19021202476 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (999001501500081 / 4000000000000)) (orderedInterval (-35940139034 / 1000000000000) (-35940098940 / 1000000000000), orderedInterval (35530808848 / 1000000000000) (35530848943 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1132761228149799 / 4000000000000)) (orderedInterval (44716963039 / 1000000000000) (44716963040 / 1000000000000), orderedInterval (15682348904 / 1000000000000) (15682348905 / 1000000000000))) = true
  rfl'

theorem compactCertificate289_stateChecks5 :
    compactCertificate289.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (944378215736631 / 4000000000000)) (orderedInterval (-49439158647 / 1000000000000) (-49439158646 / 1000000000000), orderedInterval (-15776914916 / 1000000000000) (-15776914914 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (834386793721251 / 4000000000000)) (orderedInterval (49363815999 / 1000000000000) (49363832944 / 1000000000000), orderedInterval (-24920032366 / 1000000000000) (-24920015420 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (241837814607849 / 800000000000)) (orderedInterval (45738392858 / 1000000000000) (45738392903 / 1000000000000), orderedInterval (3657460383 / 1000000000000) (3657460427 / 1000000000000))) = true
  rfl'

theorem compactCertificate289_stateChecks6 :
    compactCertificate289.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (668936122432203 / 4000000000000)) (orderedInterval (-61600264259 / 1000000000000) (-61600264235 / 1000000000000), orderedInterval (-3301550836 / 1000000000000) (-3301550812 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (567064559250483 / 4000000000000)) (orderedInterval (-61933786249 / 1000000000000) (-61933786248 / 1000000000000), orderedInterval (-25371013462 / 1000000000000) (-25371013461 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (354842671527249 / 4000000000000)) (orderedInterval (84642463144 / 1000000000000) (84642463160 / 1000000000000), orderedInterval (2972696896 / 1000000000000) (2972696912 / 1000000000000))) = true
  rfl'

theorem compactCertificate289_stateChecks7 :
    compactCertificate289.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (190835568900783 / 4000000000000)) (orderedInterval (-113140099364 / 1000000000000) (-113140099362 / 1000000000000), orderedInterval (-22105684112 / 1000000000000) (-22105684110 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (518155692371349 / 4000000000000)) (orderedInterval (-70005804947 / 1000000000000) (-70005804929 / 1000000000000), orderedInterval (-3425268935 / 1000000000000) (-3425268917 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (707497299440373 / 4000000000000)) (orderedInterval (59236804233 / 1000000000000) (59236804732 / 1000000000000), orderedInterval (-9668232510 / 1000000000000) (-9668232011 / 1000000000000))) = true
  rfl'

theorem compactCertificate289_stateChecks8 :
    compactCertificate289.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (299157328472751 / 4000000000000)) (orderedInterval (16048332968 / 1000000000000) (16048332969 / 1000000000000), orderedInterval (90748662022 / 1000000000000) (90748662024 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1216057931523471 / 4000000000000)) (orderedInterval (-2971551382 / 1000000000000) (-2971551381 / 1000000000000), orderedInterval (-45659288239 / 1000000000000) (-45659288238 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (812270341191489 / 4000000000000)) (orderedInterval (19259943360 / 1000000000000) (19259943847 / 1000000000000), orderedInterval (-52621903610 / 1000000000000) (-52621903122 / 1000000000000))) = true
  rfl'

theorem compactCertificate289_states : ∀ j,
    BesselStateValid (compactCertificate289.point j) (compactCertificate289.state j) :=
  compactCertificate289.statesValid_of_checks3 compactCertificate289_stateChecks0
    compactCertificate289_stateChecks1 compactCertificate289_stateChecks2
    compactCertificate289_stateChecks3 compactCertificate289_stateChecks4
    compactCertificate289_stateChecks5 compactCertificate289_stateChecks6
    compactCertificate289_stateChecks7 compactCertificate289_stateChecks8

theorem compactCertificate289_chunkChecks0_0 :
    compactCertificate289.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (327 / 2) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (49713590961 / 1000000000000) (49713590962 / 1000000000000), orderedInterval (37560740241 / 1000000000000) (37560740242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (481733439963627 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (70140344725 / 1000000000000) (70140346024 / 1000000000000), orderedInterval (-19431929483 / 1000000000000) (-19431928185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (155782696646091 / 800000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38316261356 / 1000000000000) (38316261357 / 1000000000000), orderedInterval (42341409326 / 1000000000000) (42341409327 / 1000000000000)))) (orderedInterval (22606740965 / 1000000000000) (22606740989 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (140568616321089 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-131787760076 / 1000000000000) (-131787760074 / 1000000000000), orderedInterval (-25435843905 / 1000000000000) (-25435843904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (377587076049933 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65980562563 / 1000000000000) (65980562564 / 1000000000000), orderedInterval (48544513738 / 1000000000000) (48544513739 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1025222362622361 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24767685994 / 1000000000000) (-24767683396 / 1000000000000), orderedInterval (43296380893 / 1000000000000) (43296383490 / 1000000000000)))) (orderedInterval (5599595011 / 1000000000000) (5599595216 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (755174152100193 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51288688424 / 1000000000000) (51288688425 / 1000000000000), orderedInterval (27094775785 / 1000000000000) (27094775786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1294003781154789 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28643065940 / 1000000000000) (-28643065939 / 1000000000000), orderedInterval (-33830235657 / 1000000000000) (-33830235656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (953157328472751 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15923449435 / 1000000000000) (15923449436 / 1000000000000), orderedInterval (49140500652 / 1000000000000) (49140500653 / 1000000000000)))) (orderedInterval (1268305105 / 1000000000000) (1268305115 / 1000000000000))) = true
  rfl'

theorem compactCertificate289_chunkChecks0_1 :
    compactCertificate289.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1462388457284673 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38648867477 / 1000000000000) (38648884491 / 1000000000000), orderedInterval (-15787486117 / 1000000000000) (-15787469104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (844310369473017 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-53876505735 / 1000000000000) (-53876505732 / 1000000000000), orderedInterval (-10519467665 / 1000000000000) (-10519467661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1498243566861453 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-41112762239 / 1000000000000) (-41112762155 / 1000000000000), orderedInterval (-3008159713 / 1000000000000) (-3008159629 / 1000000000000)))) (orderedInterval (-16703667274 / 1000000000000) (-16703664173 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1399853487205857 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38201725744 / 1000000000000) (-38201694128 / 1000000000000), orderedInterval (19021170860 / 1000000000000) (19021202476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (999001501500081 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35940139034 / 1000000000000) (-35940098940 / 1000000000000), orderedInterval (35530808848 / 1000000000000) (35530848943 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1132761228149799 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (44716963039 / 1000000000000) (44716963040 / 1000000000000), orderedInterval (15682348904 / 1000000000000) (15682348905 / 1000000000000)))) (orderedInterval (-2935237682 / 1000000000000) (-2935233300 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (944378215736631 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-49439158647 / 1000000000000) (-49439158646 / 1000000000000), orderedInterval (-15776914916 / 1000000000000) (-15776914914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (834386793721251 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49363815999 / 1000000000000) (49363832944 / 1000000000000), orderedInterval (-24920032366 / 1000000000000) (-24920015420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (241837814607849 / 800000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (45738392858 / 1000000000000) (45738392903 / 1000000000000), orderedInterval (3657460383 / 1000000000000) (3657460427 / 1000000000000)))) (orderedInterval (-2224751697 / 1000000000000) (-2224750710 / 1000000000000))) = true
  rfl'

theorem compactCertificate289_chunkChecks0_2 :
    compactCertificate289.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (668936122432203 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-61600264259 / 1000000000000) (-61600264235 / 1000000000000), orderedInterval (-3301550836 / 1000000000000) (-3301550812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (567064559250483 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-61933786249 / 1000000000000) (-61933786248 / 1000000000000), orderedInterval (-25371013462 / 1000000000000) (-25371013461 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (354842671527249 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (84642463144 / 1000000000000) (84642463160 / 1000000000000), orderedInterval (2972696896 / 1000000000000) (2972696912 / 1000000000000)))) (orderedInterval (16110424558 / 1000000000000) (16110424604 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (190835568900783 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-113140099364 / 1000000000000) (-113140099362 / 1000000000000), orderedInterval (-22105684112 / 1000000000000) (-22105684110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (518155692371349 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-70005804947 / 1000000000000) (-70005804929 / 1000000000000), orderedInterval (-3425268935 / 1000000000000) (-3425268917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (707497299440373 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (59236804233 / 1000000000000) (59236804732 / 1000000000000), orderedInterval (-9668232510 / 1000000000000) (-9668232011 / 1000000000000)))) (orderedInterval (-862484579 / 1000000000000) (-862484521 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (299157328472751 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16048332968 / 1000000000000) (16048332969 / 1000000000000), orderedInterval (90748662022 / 1000000000000) (90748662024 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1216057931523471 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2971551382 / 1000000000000) (-2971551381 / 1000000000000), orderedInterval (-45659288239 / 1000000000000) (-45659288238 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (812270341191489 / 4000000000000) 0 (IntervalRat.scale (327 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (19259943360 / 1000000000000) (19259943847 / 1000000000000), orderedInterval (-52621903610 / 1000000000000) (-52621903122 / 1000000000000)))) (orderedInterval (-3275042219 / 1000000000000) (-3275042082 / 1000000000000))) = true
  rfl'

theorem compactCertificate289_chunkChecks0 :
    compactCertificate289.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate289.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate289_chunkChecks0_0
    compactCertificate289_chunkChecks0_1 compactCertificate289_chunkChecks0_2

theorem compactCertificate289_chunkChecks1_0 :
    compactCertificate289.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (327 / 2) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (49713590961 / 1000000000000) (49713590962 / 1000000000000), orderedInterval (37560740241 / 1000000000000) (37560740242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (481733439963627 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (70140344725 / 1000000000000) (70140346024 / 1000000000000), orderedInterval (-19431929483 / 1000000000000) (-19431928185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (155782696646091 / 800000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38316261356 / 1000000000000) (38316261357 / 1000000000000), orderedInterval (42341409326 / 1000000000000) (42341409327 / 1000000000000)))) (orderedInterval (17713595611 / 1000000000000) (17713595634 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (140568616321089 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-131787760076 / 1000000000000) (-131787760074 / 1000000000000), orderedInterval (-25435843905 / 1000000000000) (-25435843904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (377587076049933 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65980562563 / 1000000000000) (65980562564 / 1000000000000), orderedInterval (48544513738 / 1000000000000) (48544513739 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1025222362622361 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24767685994 / 1000000000000) (-24767683396 / 1000000000000), orderedInterval (43296380893 / 1000000000000) (43296383490 / 1000000000000)))) (orderedInterval (-3742374839 / 1000000000000) (-3742374526 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (755174152100193 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51288688424 / 1000000000000) (51288688425 / 1000000000000), orderedInterval (27094775785 / 1000000000000) (27094775786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1294003781154789 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28643065940 / 1000000000000) (-28643065939 / 1000000000000), orderedInterval (-33830235657 / 1000000000000) (-33830235656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (953157328472751 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15923449435 / 1000000000000) (15923449436 / 1000000000000), orderedInterval (49140500652 / 1000000000000) (49140500653 / 1000000000000)))) (orderedInterval (3795471230 / 1000000000000) (3795471246 / 1000000000000))) = true
  rfl'

theorem compactCertificate289_chunkChecks1_1 :
    compactCertificate289.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1462388457284673 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38648867477 / 1000000000000) (38648884491 / 1000000000000), orderedInterval (-15787486117 / 1000000000000) (-15787469104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (844310369473017 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-53876505735 / 1000000000000) (-53876505732 / 1000000000000), orderedInterval (-10519467665 / 1000000000000) (-10519467661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1498243566861453 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-41112762239 / 1000000000000) (-41112762155 / 1000000000000), orderedInterval (-3008159713 / 1000000000000) (-3008159629 / 1000000000000)))) (orderedInterval (4286855527 / 1000000000000) (4286862450 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1399853487205857 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38201725744 / 1000000000000) (-38201694128 / 1000000000000), orderedInterval (19021170860 / 1000000000000) (19021202476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (999001501500081 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35940139034 / 1000000000000) (-35940098940 / 1000000000000), orderedInterval (35530808848 / 1000000000000) (35530848943 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1132761228149799 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (44716963039 / 1000000000000) (44716963040 / 1000000000000), orderedInterval (15682348904 / 1000000000000) (15682348905 / 1000000000000)))) (orderedInterval (4259854316 / 1000000000000) (4259861362 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (944378215736631 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-49439158647 / 1000000000000) (-49439158646 / 1000000000000), orderedInterval (-15776914916 / 1000000000000) (-15776914914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (834386793721251 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49363815999 / 1000000000000) (49363832944 / 1000000000000), orderedInterval (-24920032366 / 1000000000000) (-24920015420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (241837814607849 / 800000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (45738392858 / 1000000000000) (45738392903 / 1000000000000), orderedInterval (3657460383 / 1000000000000) (3657460427 / 1000000000000)))) (orderedInterval (1729499012 / 1000000000000) (1729500274 / 1000000000000))) = true
  rfl'

theorem compactCertificate289_chunkChecks1_2 :
    compactCertificate289.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (668936122432203 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-61600264259 / 1000000000000) (-61600264235 / 1000000000000), orderedInterval (-3301550836 / 1000000000000) (-3301550812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (567064559250483 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-61933786249 / 1000000000000) (-61933786248 / 1000000000000), orderedInterval (-25371013462 / 1000000000000) (-25371013461 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (354842671527249 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (84642463144 / 1000000000000) (84642463160 / 1000000000000), orderedInterval (2972696896 / 1000000000000) (2972696912 / 1000000000000)))) (orderedInterval (1837570341 / 1000000000000) (1837570384 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (190835568900783 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-113140099364 / 1000000000000) (-113140099362 / 1000000000000), orderedInterval (-22105684112 / 1000000000000) (-22105684110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (518155692371349 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-70005804947 / 1000000000000) (-70005804929 / 1000000000000), orderedInterval (-3425268935 / 1000000000000) (-3425268917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (707497299440373 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (59236804233 / 1000000000000) (59236804732 / 1000000000000), orderedInterval (-9668232510 / 1000000000000) (-9668232011 / 1000000000000)))) (orderedInterval (982247803 / 1000000000000) (982247863 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (299157328472751 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16048332968 / 1000000000000) (16048332969 / 1000000000000), orderedInterval (90748662022 / 1000000000000) (90748662024 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1216057931523471 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2971551382 / 1000000000000) (-2971551381 / 1000000000000), orderedInterval (-45659288239 / 1000000000000) (-45659288238 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (812270341191489 / 4000000000000) 1 (IntervalRat.scale (327 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (19259943360 / 1000000000000) (19259943847 / 1000000000000), orderedInterval (-52621903610 / 1000000000000) (-52621903122 / 1000000000000)))) (orderedInterval (19423850117 / 1000000000000) (19423850295 / 1000000000000))) = true
  rfl'

theorem compactCertificate289_chunkChecks1 :
    compactCertificate289.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate289.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate289_chunkChecks1_0
    compactCertificate289_chunkChecks1_1 compactCertificate289_chunkChecks1_2

theorem compactCertificate289_chunkChecks2_0 :
    compactCertificate289.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (327 / 2) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (49713590961 / 1000000000000) (49713590962 / 1000000000000), orderedInterval (37560740241 / 1000000000000) (37560740242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (481733439963627 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (70140344725 / 1000000000000) (70140346024 / 1000000000000), orderedInterval (-19431929483 / 1000000000000) (-19431928185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (155782696646091 / 800000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38316261356 / 1000000000000) (38316261357 / 1000000000000), orderedInterval (42341409326 / 1000000000000) (42341409327 / 1000000000000)))) (orderedInterval (-23357045479 / 1000000000000) (-23357045456 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (140568616321089 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-131787760076 / 1000000000000) (-131787760074 / 1000000000000), orderedInterval (-25435843905 / 1000000000000) (-25435843904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (377587076049933 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65980562563 / 1000000000000) (65980562564 / 1000000000000), orderedInterval (48544513738 / 1000000000000) (48544513739 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1025222362622361 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24767685994 / 1000000000000) (-24767683396 / 1000000000000), orderedInterval (43296380893 / 1000000000000) (43296383490 / 1000000000000)))) (orderedInterval (-5173042072 / 1000000000000) (-5173041585 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (755174152100193 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51288688424 / 1000000000000) (51288688425 / 1000000000000), orderedInterval (27094775785 / 1000000000000) (27094775786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1294003781154789 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28643065940 / 1000000000000) (-28643065939 / 1000000000000), orderedInterval (-33830235657 / 1000000000000) (-33830235656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (953157328472751 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15923449435 / 1000000000000) (15923449436 / 1000000000000), orderedInterval (49140500652 / 1000000000000) (49140500653 / 1000000000000)))) (orderedInterval (-4299290210 / 1000000000000) (-4299290181 / 1000000000000))) = true
  rfl'

theorem compactCertificate289_chunkChecks2_1 :
    compactCertificate289.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1462388457284673 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38648867477 / 1000000000000) (38648884491 / 1000000000000), orderedInterval (-15787486117 / 1000000000000) (-15787469104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (844310369473017 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-53876505735 / 1000000000000) (-53876505732 / 1000000000000), orderedInterval (-10519467665 / 1000000000000) (-10519467661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1498243566861453 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-41112762239 / 1000000000000) (-41112762155 / 1000000000000), orderedInterval (-3008159713 / 1000000000000) (-3008159629 / 1000000000000)))) (orderedInterval (71636595076 / 1000000000000) (71636610585 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1399853487205857 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38201725744 / 1000000000000) (-38201694128 / 1000000000000), orderedInterval (19021170860 / 1000000000000) (19021202476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (999001501500081 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35940139034 / 1000000000000) (-35940098940 / 1000000000000), orderedInterval (35530808848 / 1000000000000) (35530848943 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1132761228149799 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (44716963039 / 1000000000000) (44716963040 / 1000000000000), orderedInterval (15682348904 / 1000000000000) (15682348905 / 1000000000000)))) (orderedInterval (5423203025 / 1000000000000) (5423214582 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (944378215736631 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-49439158647 / 1000000000000) (-49439158646 / 1000000000000), orderedInterval (-15776914916 / 1000000000000) (-15776914914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (834386793721251 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49363815999 / 1000000000000) (49363832944 / 1000000000000), orderedInterval (-24920032366 / 1000000000000) (-24920015420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (241837814607849 / 800000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (45738392858 / 1000000000000) (45738392903 / 1000000000000), orderedInterval (3657460383 / 1000000000000) (3657460427 / 1000000000000)))) (orderedInterval (1774708623 / 1000000000000) (1774710247 / 1000000000000))) = true
  rfl'

theorem compactCertificate289_chunkChecks2_2 :
    compactCertificate289.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (668936122432203 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-61600264259 / 1000000000000) (-61600264235 / 1000000000000), orderedInterval (-3301550836 / 1000000000000) (-3301550812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (567064559250483 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-61933786249 / 1000000000000) (-61933786248 / 1000000000000), orderedInterval (-25371013462 / 1000000000000) (-25371013461 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (354842671527249 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (84642463144 / 1000000000000) (84642463160 / 1000000000000), orderedInterval (2972696896 / 1000000000000) (2972696912 / 1000000000000)))) (orderedInterval (-13762313612 / 1000000000000) (-13762313571 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (190835568900783 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-113140099364 / 1000000000000) (-113140099362 / 1000000000000), orderedInterval (-22105684112 / 1000000000000) (-22105684110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (518155692371349 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-70005804947 / 1000000000000) (-70005804929 / 1000000000000), orderedInterval (-3425268935 / 1000000000000) (-3425268917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (707497299440373 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (59236804233 / 1000000000000) (59236804732 / 1000000000000), orderedInterval (-9668232510 / 1000000000000) (-9668232011 / 1000000000000)))) (orderedInterval (4132098608 / 1000000000000) (4132098671 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (299157328472751 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16048332968 / 1000000000000) (16048332969 / 1000000000000), orderedInterval (90748662022 / 1000000000000) (90748662024 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1216057931523471 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2971551382 / 1000000000000) (-2971551381 / 1000000000000), orderedInterval (-45659288239 / 1000000000000) (-45659288238 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (812270341191489 / 4000000000000) 2 (IntervalRat.scale (327 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (19259943360 / 1000000000000) (19259943847 / 1000000000000), orderedInterval (-52621903610 / 1000000000000) (-52621903122 / 1000000000000)))) (orderedInterval (4599000388 / 1000000000000) (4599000624 / 1000000000000))) = true
  rfl'

theorem compactCertificate289_chunkChecks2 :
    compactCertificate289.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate289.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate289_chunkChecks2_0
    compactCertificate289_chunkChecks2_1 compactCertificate289_chunkChecks2_2

theorem compactCertificate289_chunkChecks3_0 :
    compactCertificate289.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (327 / 2) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (49713590961 / 1000000000000) (49713590962 / 1000000000000), orderedInterval (37560740241 / 1000000000000) (37560740242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (481733439963627 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (70140344725 / 1000000000000) (70140346024 / 1000000000000), orderedInterval (-19431929483 / 1000000000000) (-19431928185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (155782696646091 / 800000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38316261356 / 1000000000000) (38316261357 / 1000000000000), orderedInterval (42341409326 / 1000000000000) (42341409327 / 1000000000000)))) (orderedInterval (-18869451515 / 1000000000000) (-18869451492 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (140568616321089 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-131787760076 / 1000000000000) (-131787760074 / 1000000000000), orderedInterval (-25435843905 / 1000000000000) (-25435843904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (377587076049933 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65980562563 / 1000000000000) (65980562564 / 1000000000000), orderedInterval (48544513738 / 1000000000000) (48544513739 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1025222362622361 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24767685994 / 1000000000000) (-24767683396 / 1000000000000), orderedInterval (43296380893 / 1000000000000) (43296383490 / 1000000000000)))) (orderedInterval (11544762955 / 1000000000000) (11544763716 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (755174152100193 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51288688424 / 1000000000000) (51288688425 / 1000000000000), orderedInterval (27094775785 / 1000000000000) (27094775786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1294003781154789 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28643065940 / 1000000000000) (-28643065939 / 1000000000000), orderedInterval (-33830235657 / 1000000000000) (-33830235656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (953157328472751 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15923449435 / 1000000000000) (15923449436 / 1000000000000), orderedInterval (49140500652 / 1000000000000) (49140500653 / 1000000000000)))) (orderedInterval (-11732683143 / 1000000000000) (-11732683090 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate289_chunkChecks3_1 :
    compactCertificate289.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1462388457284673 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38648867477 / 1000000000000) (38648884491 / 1000000000000), orderedInterval (-15787486117 / 1000000000000) (-15787469104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (844310369473017 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-53876505735 / 1000000000000) (-53876505732 / 1000000000000), orderedInterval (-10519467665 / 1000000000000) (-10519467661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1498243566861453 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-41112762239 / 1000000000000) (-41112762155 / 1000000000000), orderedInterval (-3008159713 / 1000000000000) (-3008159629 / 1000000000000)))) (orderedInterval (-24983188982 / 1000000000000) (-24983154316 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1399853487205857 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38201725744 / 1000000000000) (-38201694128 / 1000000000000), orderedInterval (19021170860 / 1000000000000) (19021202476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (999001501500081 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35940139034 / 1000000000000) (-35940098940 / 1000000000000), orderedInterval (35530808848 / 1000000000000) (35530848943 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1132761228149799 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (44716963039 / 1000000000000) (44716963040 / 1000000000000), orderedInterval (15682348904 / 1000000000000) (15682348905 / 1000000000000)))) (orderedInterval (-8228606239 / 1000000000000) (-8228586969 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (944378215736631 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-49439158647 / 1000000000000) (-49439158646 / 1000000000000), orderedInterval (-15776914916 / 1000000000000) (-15776914914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (834386793721251 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49363815999 / 1000000000000) (49363832944 / 1000000000000), orderedInterval (-24920032366 / 1000000000000) (-24920015420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (241837814607849 / 800000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (45738392858 / 1000000000000) (45738392903 / 1000000000000), orderedInterval (3657460383 / 1000000000000) (3657460427 / 1000000000000)))) (orderedInterval (-3015646963 / 1000000000000) (-3015644880 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate289_chunkChecks3_2 :
    compactCertificate289.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (668936122432203 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-61600264259 / 1000000000000) (-61600264235 / 1000000000000), orderedInterval (-3301550836 / 1000000000000) (-3301550812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (567064559250483 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-61933786249 / 1000000000000) (-61933786248 / 1000000000000), orderedInterval (-25371013462 / 1000000000000) (-25371013461 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (354842671527249 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (84642463144 / 1000000000000) (84642463160 / 1000000000000), orderedInterval (2972696896 / 1000000000000) (2972696912 / 1000000000000)))) (orderedInterval (-1432200654 / 1000000000000) (-1432200614 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (190835568900783 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-113140099364 / 1000000000000) (-113140099362 / 1000000000000), orderedInterval (-22105684112 / 1000000000000) (-22105684110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (518155692371349 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-70005804947 / 1000000000000) (-70005804929 / 1000000000000), orderedInterval (-3425268935 / 1000000000000) (-3425268917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (707497299440373 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (59236804233 / 1000000000000) (59236804732 / 1000000000000), orderedInterval (-9668232510 / 1000000000000) (-9668232011 / 1000000000000)))) (orderedInterval (-1012099005 / 1000000000000) (-1012098938 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (299157328472751 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16048332968 / 1000000000000) (16048332969 / 1000000000000), orderedInterval (90748662022 / 1000000000000) (90748662024 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1216057931523471 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2971551382 / 1000000000000) (-2971551381 / 1000000000000), orderedInterval (-45659288239 / 1000000000000) (-45659288238 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (812270341191489 / 4000000000000) 3 (IntervalRat.scale (327 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (19259943360 / 1000000000000) (19259943847 / 1000000000000), orderedInterval (-52621903610 / 1000000000000) (-52621903122 / 1000000000000)))) (orderedInterval (-42889967942 / 1000000000000) (-42889967620 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate289_chunkChecks3 :
    compactCertificate289.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate289.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate289_chunkChecks3_0
    compactCertificate289_chunkChecks3_1 compactCertificate289_chunkChecks3_2

theorem compactCertificate289_chunkChecks4_0 :
    compactCertificate289.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (327 / 2) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (49713590961 / 1000000000000) (49713590962 / 1000000000000), orderedInterval (37560740241 / 1000000000000) (37560740242 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (481733439963627 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (70140344725 / 1000000000000) (70140346024 / 1000000000000), orderedInterval (-19431929483 / 1000000000000) (-19431928185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (155782696646091 / 800000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38316261356 / 1000000000000) (38316261357 / 1000000000000), orderedInterval (42341409326 / 1000000000000) (42341409327 / 1000000000000)))) (orderedInterval (24651122043 / 1000000000000) (24651122068 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (140568616321089 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-131787760076 / 1000000000000) (-131787760074 / 1000000000000), orderedInterval (-25435843905 / 1000000000000) (-25435843904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (377587076049933 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65980562563 / 1000000000000) (65980562564 / 1000000000000), orderedInterval (48544513738 / 1000000000000) (48544513739 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1025222362622361 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24767685994 / 1000000000000) (-24767683396 / 1000000000000), orderedInterval (43296380893 / 1000000000000) (43296383490 / 1000000000000)))) (orderedInterval (10762243498 / 1000000000000) (10762244694 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (755174152100193 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51288688424 / 1000000000000) (51288688425 / 1000000000000), orderedInterval (27094775785 / 1000000000000) (27094775786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1294003781154789 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28643065940 / 1000000000000) (-28643065939 / 1000000000000), orderedInterval (-33830235657 / 1000000000000) (-33830235656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (953157328472751 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15923449435 / 1000000000000) (15923449436 / 1000000000000), orderedInterval (49140500652 / 1000000000000) (49140500653 / 1000000000000)))) (orderedInterval (15419746417 / 1000000000000) (15419746514 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate289_chunkChecks4_1 :
    compactCertificate289.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1462388457284673 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38648867477 / 1000000000000) (38648884491 / 1000000000000), orderedInterval (-15787486117 / 1000000000000) (-15787469104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (844310369473017 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-53876505735 / 1000000000000) (-53876505732 / 1000000000000), orderedInterval (-10519467665 / 1000000000000) (-10519467661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1498243566861453 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-41112762239 / 1000000000000) (-41112762155 / 1000000000000), orderedInterval (-3008159713 / 1000000000000) (-3008159629 / 1000000000000)))) (orderedInterval (-343441730059 / 1000000000000) (-343441652335 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1399853487205857 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38201725744 / 1000000000000) (-38201694128 / 1000000000000), orderedInterval (19021170860 / 1000000000000) (19021202476 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (999001501500081 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35940139034 / 1000000000000) (-35940098940 / 1000000000000), orderedInterval (35530808848 / 1000000000000) (35530848943 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1132761228149799 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (44716963039 / 1000000000000) (44716963040 / 1000000000000), orderedInterval (15682348904 / 1000000000000) (15682348905 / 1000000000000)))) (orderedInterval (-5963126431 / 1000000000000) (-5963093422 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (944378215736631 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-49439158647 / 1000000000000) (-49439158646 / 1000000000000), orderedInterval (-15776914916 / 1000000000000) (-15776914914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (834386793721251 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49363815999 / 1000000000000) (49363832944 / 1000000000000), orderedInterval (-24920032366 / 1000000000000) (-24920015420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (241837814607849 / 800000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (45738392858 / 1000000000000) (45738392903 / 1000000000000), orderedInterval (3657460383 / 1000000000000) (3657460427 / 1000000000000)))) (orderedInterval (3755470453 / 1000000000000) (3755473143 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate289_chunkChecks4_2 :
    compactCertificate289.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (668936122432203 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-61600264259 / 1000000000000) (-61600264235 / 1000000000000), orderedInterval (-3301550836 / 1000000000000) (-3301550812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (567064559250483 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-61933786249 / 1000000000000) (-61933786248 / 1000000000000), orderedInterval (-25371013462 / 1000000000000) (-25371013461 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (354842671527249 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (84642463144 / 1000000000000) (84642463160 / 1000000000000), orderedInterval (2972696896 / 1000000000000) (2972696912 / 1000000000000)))) (orderedInterval (13017645624 / 1000000000000) (13017645664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (190835568900783 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-113140099364 / 1000000000000) (-113140099362 / 1000000000000), orderedInterval (-22105684112 / 1000000000000) (-22105684110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (518155692371349 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-70005804947 / 1000000000000) (-70005804929 / 1000000000000), orderedInterval (-3425268935 / 1000000000000) (-3425268917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (707497299440373 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (59236804233 / 1000000000000) (59236804732 / 1000000000000), orderedInterval (-9668232510 / 1000000000000) (-9668232011 / 1000000000000)))) (orderedInterval (-5564202191 / 1000000000000) (-5564202118 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (299157328472751 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16048332968 / 1000000000000) (16048332969 / 1000000000000), orderedInterval (90748662022 / 1000000000000) (90748662024 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1216057931523471 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2971551382 / 1000000000000) (-2971551381 / 1000000000000), orderedInterval (-45659288239 / 1000000000000) (-45659288238 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (812270341191489 / 4000000000000) 4 (IntervalRat.scale (327 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (19259943360 / 1000000000000) (19259943847 / 1000000000000), orderedInterval (-52621903610 / 1000000000000) (-52621903122 / 1000000000000)))) (orderedInterval (-5178304432 / 1000000000000) (-5178303979 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate289_chunkChecks4 :
    compactCertificate289.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate289.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate289_chunkChecks4_0
    compactCertificate289_chunkChecks4_1 compactCertificate289_chunkChecks4_2

theorem compactCertificate289_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate289.chunkCheck r b = true :=
  compactCertificate289.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate289_chunkChecks0
    · exact compactCertificate289_chunkChecks1
    · exact compactCertificate289_chunkChecks2
    · exact compactCertificate289_chunkChecks3
    · exact compactCertificate289_chunkChecks4)

theorem compactCertificate289_coefficient0 :
    compactCertificate289.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate289_coefficient1 :
    compactCertificate289.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate289_coefficient2 :
    compactCertificate289.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate289_coefficient3 :
    compactCertificate289.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate289_coefficient4 :
    compactCertificate289.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate289_coefficients : ∀ r : Fin 5,
    compactCertificate289.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate289_coefficient0
  · exact compactCertificate289_coefficient1
  · exact compactCertificate289_coefficient2
  · exact compactCertificate289_coefficient3
  · exact compactCertificate289_coefficient4

theorem compactCertificate289_lower : (1 : ℚ) ≤ compactCertificate289.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate289, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate289_proves {t : ℝ} (ht : t ∈ compactCertificate289.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate289.proves compactCertificate289_states compactCertificate289_chunks
    compactCertificate289_coefficients compactCertificate289_lower ht

end Erdos232
