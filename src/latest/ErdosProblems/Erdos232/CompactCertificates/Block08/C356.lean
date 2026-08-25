/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate356 : CompactCertificate where
  left := 227
  right := 228
  center := 455 / 2
  grid := fun i =>
    match i.val with
    | 0 => 72
    | 1 => 53
    | 2 => 86
    | 3 => 16
    | 4 => 42
    | 5 => 114
    | 6 => 84
    | 7 => 143
    | 8 => 106
    | 9 => 162
    | 10 => 94
    | 11 => 166
    | 12 => 155
    | 13 => 111
    | 14 => 125
    | 15 => 105
    | 16 => 92
    | 17 => 134
    | 18 => 74
    | 19 => 63
    | 20 => 39
    | 21 => 21
    | 22 => 57
    | 23 => 78
    | 24 => 33
    | 25 => 135
    | _ => 90
  point := fun i =>
    match i.val with
    | 0 => 455 / 2
    | 1 => 134060376258991 / 800000000000
    | 2 => 43352371237903 / 160000000000
    | 3 => 39118483441037 / 800000000000
    | 4 => 105077748992489 / 800000000000
    | 5 => 285306529047813 / 800000000000
    | 6 => 210155497985069 / 800000000000
    | 7 => 360105027783137 / 800000000000
    | 8 => 265251733611683 / 800000000000
    | 9 => 406964371904909 / 800000000000
    | 10 => 234960989669861 / 800000000000
    | 11 => 416942399340649 / 800000000000
    | 12 => 389561673809581 / 800000000000
    | 13 => 278009592160573 / 800000000000
    | 14 => 315233246977467 / 800000000000
    | 15 => 262808616611723 / 800000000000
    | 16 => 232199382962183 / 800000000000
    | 17 => 67300431588117 / 160000000000
    | 18 => 186156535600399 / 800000000000
    | 19 => 157806956855639 / 800000000000
    | 20 => 98748266388317 / 800000000000
    | 21 => 53107146085539 / 800000000000
    | 22 => 144196232433617 / 800000000000
    | 23 => 196887627673009 / 800000000000
    | 24 => 83251733611683 / 800000000000
    | 25 => 338413675133443 / 800000000000
    | _ => 226044651524237 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (45923148758 / 1000000000000) (45923179414 / 1000000000000), orderedInterval (-26357147177 / 1000000000000) (-26357116521 / 1000000000000))
    | 1 => (orderedInterval (-59151090680 / 1000000000000) (-59151088577 / 1000000000000), orderedInterval (17500970850 / 1000000000000) (17500972953 / 1000000000000))
    | 2 => (orderedInterval (48469582530 / 1000000000000) (48469582629 / 1000000000000), orderedInterval (419869432 / 1000000000000) (419869531 / 1000000000000))
    | 3 => (orderedInterval (-62961363155 / 1000000000000) (-62961348461 / 1000000000000), orderedInterval (95803841742 / 1000000000000) (95803856436 / 1000000000000))
    | 4 => (orderedInterval (12788480011 / 1000000000000) (12788480012 / 1000000000000), orderedInterval (68386214482 / 1000000000000) (68386214483 / 1000000000000))
    | 5 => (orderedInterval (-27965519008 / 1000000000000) (-27965506320 / 1000000000000), orderedInterval (31709585493 / 1000000000000) (31709598181 / 1000000000000))
    | 6 => (orderedInterval (-19825265975 / 1000000000000) (-19825265240 / 1000000000000), orderedInterval (45097533388 / 1000000000000) (45097534123 / 1000000000000))
    | 7 => (orderedInterval (-37427214440 / 1000000000000) (-37427213173 / 1000000000000), orderedInterval (3715916711 / 1000000000000) (3715917978 / 1000000000000))
    | 8 => (orderedInterval (-26835733432 / 1000000000000) (-26835725848 / 1000000000000), orderedInterval (34679910614 / 1000000000000) (34679918198 / 1000000000000))
    | 9 => (orderedInterval (18569073818 / 1000000000000) (18569073819 / 1000000000000), orderedInterval (30092218567 / 1000000000000) (30092218568 / 1000000000000))
    | 10 => (orderedInterval (-34151076560 / 1000000000000) (-34151033053 / 1000000000000), orderedInterval (31701144721 / 1000000000000) (31701188228 / 1000000000000))
    | 11 => (orderedInterval (15477664976 / 1000000000000) (15477664977 / 1000000000000), orderedInterval (31321134630 / 1000000000000) (31321134631 / 1000000000000))
    | 12 => (orderedInterval (-25693981863 / 1000000000000) (-25693981862 / 1000000000000), orderedInterval (-25413259015 / 1000000000000) (-25413259014 / 1000000000000))
    | 13 => (orderedInterval (17443055138 / 1000000000000) (17443055599 / 1000000000000), orderedInterval (-39110608879 / 1000000000000) (-39110608418 / 1000000000000))
    | 14 => (orderedInterval (-34124177817 / 1000000000000) (-34124088643 / 1000000000000), orderedInterval (21283750471 / 1000000000000) (21283839644 / 1000000000000))
    | 15 => (orderedInterval (23808771529 / 1000000000000) (23808774586 / 1000000000000), orderedInterval (-37063788696 / 1000000000000) (-37063785639 / 1000000000000))
    | 16 => (orderedInterval (42434557810 / 1000000000000) (42434576907 / 1000000000000), orderedInterval (-19888784372 / 1000000000000) (-19888765275 / 1000000000000))
    | 17 => (orderedInterval (16548897449 / 1000000000000) (16548897450 / 1000000000000), orderedInterval (35188766078 / 1000000000000) (35188766079 / 1000000000000))
    | 18 => (orderedInterval (44088778103 / 1000000000000) (44088778104 / 1000000000000), orderedInterval (28048188066 / 1000000000000) (28048188067 / 1000000000000))
    | 19 => (orderedInterval (-6976923908 / 1000000000000) (-6976923907 / 1000000000000), orderedInterval (-56361983475 / 1000000000000) (-56361983474 / 1000000000000))
    | 20 => (orderedInterval (-71238917511 / 1000000000000) (-71238917278 / 1000000000000), orderedInterval (9371086797 / 1000000000000) (9371087030 / 1000000000000))
    | 21 => (orderedInterval (-91057317392 / 1000000000000) (-91057317391 / 1000000000000), orderedInterval (-35346608013 / 1000000000000) (-35346608012 / 1000000000000))
    | 22 => (orderedInterval (-55003226873 / 1000000000000) (-55003220030 / 1000000000000), orderedInterval (22660330987 / 1000000000000) (22660337830 / 1000000000000))
    | 23 => (orderedInterval (48887572461 / 1000000000000) (48887575528 / 1000000000000), orderedInterval (-14125513591 / 1000000000000) (-14125510523 / 1000000000000))
    | 24 => (orderedInterval (-72206832755 / 1000000000000) (-72206832754 / 1000000000000), orderedInterval (-29714074308 / 1000000000000) (-29714074307 / 1000000000000))
    | 25 => (orderedInterval (11938174473 / 1000000000000) (11938174538 / 1000000000000), orderedInterval (-36925237903 / 1000000000000) (-36925237838 / 1000000000000))
    | _ => (orderedInterval (26700908897 / 1000000000000) (26700908898 / 1000000000000), orderedInterval (39197355070 / 1000000000000) (39197355071 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (20495405474 / 1000000000000) (20495417667 / 1000000000000)
      | 1 => orderedInterval (3138073516 / 1000000000000) (3138074605 / 1000000000000)
      | 2 => orderedInterval (505838264 / 1000000000000) (505838500 / 1000000000000)
      | 3 => orderedInterval (-3629572733 / 1000000000000) (-3629569419 / 1000000000000)
      | 4 => orderedInterval (2286008480 / 1000000000000) (2286009003 / 1000000000000)
      | 5 => orderedInterval (-1729736858 / 1000000000000) (-1729735707 / 1000000000000)
      | 6 => orderedInterval (-8973771104 / 1000000000000) (-8973771038 / 1000000000000)
      | 7 => orderedInterval (-817454078 / 1000000000000) (-817453660 / 1000000000000)
      | _ => orderedInterval (-6416873929 / 1000000000000) (-6416873860 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-10297585753 / 1000000000000) (-10297573562 / 1000000000000)
      | 1 => orderedInterval (-2315582845 / 1000000000000) (-2315581365 / 1000000000000)
      | 2 => orderedInterval (994760543 / 1000000000000) (994760910 / 1000000000000)
      | 3 => orderedInterval (1276131877 / 1000000000000) (1276136226 / 1000000000000)
      | 4 => orderedInterval (-4853961452 / 1000000000000) (-4853960560 / 1000000000000)
      | 5 => orderedInterval (2499881986 / 1000000000000) (2499883463 / 1000000000000)
      | 6 => orderedInterval (-1655556537 / 1000000000000) (-1655556479 / 1000000000000)
      | 7 => orderedInterval (954258792 / 1000000000000) (954259194 / 1000000000000)
      | _ => orderedInterval (-3627212565 / 1000000000000) (-3627212466 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-21892534643 / 1000000000000) (-21892522399 / 1000000000000)
      | 1 => orderedInterval (-5062531318 / 1000000000000) (-5062529044 / 1000000000000)
      | 2 => orderedInterval (-3146083867 / 1000000000000) (-3146083283 / 1000000000000)
      | 3 => orderedInterval (9161796841 / 1000000000000) (9161802634 / 1000000000000)
      | 4 => orderedInterval (-6470644779 / 1000000000000) (-6470643246 / 1000000000000)
      | 5 => orderedInterval (1919995594 / 1000000000000) (1919997501 / 1000000000000)
      | 6 => orderedInterval (7768262395 / 1000000000000) (7768262449 / 1000000000000)
      | 7 => orderedInterval (3454061283 / 1000000000000) (3454061682 / 1000000000000)
      | _ => orderedInterval (11194891011 / 1000000000000) (11194891160 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (10436271793 / 1000000000000) (10436284039 / 1000000000000)
      | 1 => orderedInterval (8235961095 / 1000000000000) (8235964646 / 1000000000000)
      | 2 => orderedInterval (-1693018265 / 1000000000000) (-1693017320 / 1000000000000)
      | 3 => orderedInterval (1155132683 / 1000000000000) (1155140524 / 1000000000000)
      | 4 => orderedInterval (9270880683 / 1000000000000) (9270883314 / 1000000000000)
      | 5 => orderedInterval (-6777873219 / 1000000000000) (-6777870763 / 1000000000000)
      | 6 => orderedInterval (2636585885 / 1000000000000) (2636585936 / 1000000000000)
      | 7 => orderedInterval (-1146253944 / 1000000000000) (-1146253542 / 1000000000000)
      | _ => orderedInterval (-5265398585 / 1000000000000) (-5265398349 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (23670769293 / 1000000000000) (23670781596 / 1000000000000)
      | 1 => orderedInterval (11986614879 / 1000000000000) (11986620457 / 1000000000000)
      | 2 => orderedInterval (14781143450 / 1000000000000) (14781145017 / 1000000000000)
      | 3 => orderedInterval (-28923848758 / 1000000000000) (-28923837785 / 1000000000000)
      | 4 => orderedInterval (20189468152 / 1000000000000) (20189472687 / 1000000000000)
      | 5 => orderedInterval (-227385453 / 1000000000000) (-227382268 / 1000000000000)
      | 6 => orderedInterval (-7716661286 / 1000000000000) (-7716661236 / 1000000000000)
      | 7 => orderedInterval (-4617373787 / 1000000000000) (-4617373374 / 1000000000000)
      | _ => orderedInterval (-23510092864 / 1000000000000) (-23510092476 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (4857917032 / 1000000000000) (4857936091 / 1000000000000)
    | 1 => orderedInterval (-17024865954 / 1000000000000) (-17024844639 / 1000000000000)
    | 2 => orderedInterval (-3072787483 / 1000000000000) (-3072762546 / 1000000000000)
    | 3 => orderedInterval (16852288126 / 1000000000000) (16852318485 / 1000000000000)
    | _ => orderedInterval (5632633626 / 1000000000000) (5632672618 / 1000000000000)

theorem compactCertificate356_stateChecks0 :
    compactCertificate356.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (455 / 2)) (orderedInterval (45923148758 / 1000000000000) (45923179414 / 1000000000000), orderedInterval (-26357147177 / 1000000000000) (-26357116521 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (134060376258991 / 800000000000)) (orderedInterval (-59151090680 / 1000000000000) (-59151088577 / 1000000000000), orderedInterval (17500970850 / 1000000000000) (17500972953 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (43352371237903 / 160000000000)) (orderedInterval (48469582530 / 1000000000000) (48469582629 / 1000000000000), orderedInterval (419869432 / 1000000000000) (419869531 / 1000000000000))) = true
  rfl'

theorem compactCertificate356_stateChecks1 :
    compactCertificate356.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (39118483441037 / 800000000000)) (orderedInterval (-62961363155 / 1000000000000) (-62961348461 / 1000000000000), orderedInterval (95803841742 / 1000000000000) (95803856436 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (105077748992489 / 800000000000)) (orderedInterval (12788480011 / 1000000000000) (12788480012 / 1000000000000), orderedInterval (68386214482 / 1000000000000) (68386214483 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (285306529047813 / 800000000000)) (orderedInterval (-27965519008 / 1000000000000) (-27965506320 / 1000000000000), orderedInterval (31709585493 / 1000000000000) (31709598181 / 1000000000000))) = true
  rfl'

theorem compactCertificate356_stateChecks2 :
    compactCertificate356.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (210155497985069 / 800000000000)) (orderedInterval (-19825265975 / 1000000000000) (-19825265240 / 1000000000000), orderedInterval (45097533388 / 1000000000000) (45097534123 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (360105027783137 / 800000000000)) (orderedInterval (-37427214440 / 1000000000000) (-37427213173 / 1000000000000), orderedInterval (3715916711 / 1000000000000) (3715917978 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (265251733611683 / 800000000000)) (orderedInterval (-26835733432 / 1000000000000) (-26835725848 / 1000000000000), orderedInterval (34679910614 / 1000000000000) (34679918198 / 1000000000000))) = true
  rfl'

theorem compactCertificate356_stateChecks3 :
    compactCertificate356.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (406964371904909 / 800000000000)) (orderedInterval (18569073818 / 1000000000000) (18569073819 / 1000000000000), orderedInterval (30092218567 / 1000000000000) (30092218568 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (234960989669861 / 800000000000)) (orderedInterval (-34151076560 / 1000000000000) (-34151033053 / 1000000000000), orderedInterval (31701144721 / 1000000000000) (31701188228 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (416942399340649 / 800000000000)) (orderedInterval (15477664976 / 1000000000000) (15477664977 / 1000000000000), orderedInterval (31321134630 / 1000000000000) (31321134631 / 1000000000000))) = true
  rfl'

theorem compactCertificate356_stateChecks4 :
    compactCertificate356.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (389561673809581 / 800000000000)) (orderedInterval (-25693981863 / 1000000000000) (-25693981862 / 1000000000000), orderedInterval (-25413259015 / 1000000000000) (-25413259014 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (278009592160573 / 800000000000)) (orderedInterval (17443055138 / 1000000000000) (17443055599 / 1000000000000), orderedInterval (-39110608879 / 1000000000000) (-39110608418 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (315233246977467 / 800000000000)) (orderedInterval (-34124177817 / 1000000000000) (-34124088643 / 1000000000000), orderedInterval (21283750471 / 1000000000000) (21283839644 / 1000000000000))) = true
  rfl'

theorem compactCertificate356_stateChecks5 :
    compactCertificate356.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (262808616611723 / 800000000000)) (orderedInterval (23808771529 / 1000000000000) (23808774586 / 1000000000000), orderedInterval (-37063788696 / 1000000000000) (-37063785639 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (232199382962183 / 800000000000)) (orderedInterval (42434557810 / 1000000000000) (42434576907 / 1000000000000), orderedInterval (-19888784372 / 1000000000000) (-19888765275 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (67300431588117 / 160000000000)) (orderedInterval (16548897449 / 1000000000000) (16548897450 / 1000000000000), orderedInterval (35188766078 / 1000000000000) (35188766079 / 1000000000000))) = true
  rfl'

theorem compactCertificate356_stateChecks6 :
    compactCertificate356.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (186156535600399 / 800000000000)) (orderedInterval (44088778103 / 1000000000000) (44088778104 / 1000000000000), orderedInterval (28048188066 / 1000000000000) (28048188067 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (157806956855639 / 800000000000)) (orderedInterval (-6976923908 / 1000000000000) (-6976923907 / 1000000000000), orderedInterval (-56361983475 / 1000000000000) (-56361983474 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (98748266388317 / 800000000000)) (orderedInterval (-71238917511 / 1000000000000) (-71238917278 / 1000000000000), orderedInterval (9371086797 / 1000000000000) (9371087030 / 1000000000000))) = true
  rfl'

theorem compactCertificate356_stateChecks7 :
    compactCertificate356.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (53107146085539 / 800000000000)) (orderedInterval (-91057317392 / 1000000000000) (-91057317391 / 1000000000000), orderedInterval (-35346608013 / 1000000000000) (-35346608012 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (144196232433617 / 800000000000)) (orderedInterval (-55003226873 / 1000000000000) (-55003220030 / 1000000000000), orderedInterval (22660330987 / 1000000000000) (22660337830 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (196887627673009 / 800000000000)) (orderedInterval (48887572461 / 1000000000000) (48887575528 / 1000000000000), orderedInterval (-14125513591 / 1000000000000) (-14125510523 / 1000000000000))) = true
  rfl'

theorem compactCertificate356_stateChecks8 :
    compactCertificate356.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (83251733611683 / 800000000000)) (orderedInterval (-72206832755 / 1000000000000) (-72206832754 / 1000000000000), orderedInterval (-29714074308 / 1000000000000) (-29714074307 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (338413675133443 / 800000000000)) (orderedInterval (11938174473 / 1000000000000) (11938174538 / 1000000000000), orderedInterval (-36925237903 / 1000000000000) (-36925237838 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (226044651524237 / 800000000000)) (orderedInterval (26700908897 / 1000000000000) (26700908898 / 1000000000000), orderedInterval (39197355070 / 1000000000000) (39197355071 / 1000000000000))) = true
  rfl'

theorem compactCertificate356_states : ∀ j,
    BesselStateValid (compactCertificate356.point j) (compactCertificate356.state j) :=
  compactCertificate356.statesValid_of_checks3 compactCertificate356_stateChecks0
    compactCertificate356_stateChecks1 compactCertificate356_stateChecks2
    compactCertificate356_stateChecks3 compactCertificate356_stateChecks4
    compactCertificate356_stateChecks5 compactCertificate356_stateChecks6
    compactCertificate356_stateChecks7 compactCertificate356_stateChecks8

theorem compactCertificate356_chunkChecks0_0 :
    compactCertificate356.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (455 / 2) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (45923148758 / 1000000000000) (45923179414 / 1000000000000), orderedInterval (-26357147177 / 1000000000000) (-26357116521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (134060376258991 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-59151090680 / 1000000000000) (-59151088577 / 1000000000000), orderedInterval (17500970850 / 1000000000000) (17500972953 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (43352371237903 / 160000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (48469582530 / 1000000000000) (48469582629 / 1000000000000), orderedInterval (419869432 / 1000000000000) (419869531 / 1000000000000)))) (orderedInterval (20495405474 / 1000000000000) (20495417667 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (39118483441037 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-62961363155 / 1000000000000) (-62961348461 / 1000000000000), orderedInterval (95803841742 / 1000000000000) (95803856436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (105077748992489 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (12788480011 / 1000000000000) (12788480012 / 1000000000000), orderedInterval (68386214482 / 1000000000000) (68386214483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (285306529047813 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27965519008 / 1000000000000) (-27965506320 / 1000000000000), orderedInterval (31709585493 / 1000000000000) (31709598181 / 1000000000000)))) (orderedInterval (3138073516 / 1000000000000) (3138074605 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (210155497985069 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19825265975 / 1000000000000) (-19825265240 / 1000000000000), orderedInterval (45097533388 / 1000000000000) (45097534123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (360105027783137 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-37427214440 / 1000000000000) (-37427213173 / 1000000000000), orderedInterval (3715916711 / 1000000000000) (3715917978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (265251733611683 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26835733432 / 1000000000000) (-26835725848 / 1000000000000), orderedInterval (34679910614 / 1000000000000) (34679918198 / 1000000000000)))) (orderedInterval (505838264 / 1000000000000) (505838500 / 1000000000000))) = true
  rfl'

theorem compactCertificate356_chunkChecks0_1 :
    compactCertificate356.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (406964371904909 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18569073818 / 1000000000000) (18569073819 / 1000000000000), orderedInterval (30092218567 / 1000000000000) (30092218568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (234960989669861 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34151076560 / 1000000000000) (-34151033053 / 1000000000000), orderedInterval (31701144721 / 1000000000000) (31701188228 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (416942399340649 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15477664976 / 1000000000000) (15477664977 / 1000000000000), orderedInterval (31321134630 / 1000000000000) (31321134631 / 1000000000000)))) (orderedInterval (-3629572733 / 1000000000000) (-3629569419 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (389561673809581 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25693981863 / 1000000000000) (-25693981862 / 1000000000000), orderedInterval (-25413259015 / 1000000000000) (-25413259014 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (278009592160573 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17443055138 / 1000000000000) (17443055599 / 1000000000000), orderedInterval (-39110608879 / 1000000000000) (-39110608418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (315233246977467 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-34124177817 / 1000000000000) (-34124088643 / 1000000000000), orderedInterval (21283750471 / 1000000000000) (21283839644 / 1000000000000)))) (orderedInterval (2286008480 / 1000000000000) (2286009003 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (262808616611723 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23808771529 / 1000000000000) (23808774586 / 1000000000000), orderedInterval (-37063788696 / 1000000000000) (-37063785639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (232199382962183 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42434557810 / 1000000000000) (42434576907 / 1000000000000), orderedInterval (-19888784372 / 1000000000000) (-19888765275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (67300431588117 / 160000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16548897449 / 1000000000000) (16548897450 / 1000000000000), orderedInterval (35188766078 / 1000000000000) (35188766079 / 1000000000000)))) (orderedInterval (-1729736858 / 1000000000000) (-1729735707 / 1000000000000))) = true
  rfl'

theorem compactCertificate356_chunkChecks0_2 :
    compactCertificate356.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (186156535600399 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (44088778103 / 1000000000000) (44088778104 / 1000000000000), orderedInterval (28048188066 / 1000000000000) (28048188067 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (157806956855639 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6976923908 / 1000000000000) (-6976923907 / 1000000000000), orderedInterval (-56361983475 / 1000000000000) (-56361983474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (98748266388317 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-71238917511 / 1000000000000) (-71238917278 / 1000000000000), orderedInterval (9371086797 / 1000000000000) (9371087030 / 1000000000000)))) (orderedInterval (-8973771104 / 1000000000000) (-8973771038 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (53107146085539 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-91057317392 / 1000000000000) (-91057317391 / 1000000000000), orderedInterval (-35346608013 / 1000000000000) (-35346608012 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (144196232433617 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55003226873 / 1000000000000) (-55003220030 / 1000000000000), orderedInterval (22660330987 / 1000000000000) (22660337830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (196887627673009 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48887572461 / 1000000000000) (48887575528 / 1000000000000), orderedInterval (-14125513591 / 1000000000000) (-14125510523 / 1000000000000)))) (orderedInterval (-817454078 / 1000000000000) (-817453660 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (83251733611683 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-72206832755 / 1000000000000) (-72206832754 / 1000000000000), orderedInterval (-29714074308 / 1000000000000) (-29714074307 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (338413675133443 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (11938174473 / 1000000000000) (11938174538 / 1000000000000), orderedInterval (-36925237903 / 1000000000000) (-36925237838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (226044651524237 / 800000000000) 0 (IntervalRat.scale (455 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26700908897 / 1000000000000) (26700908898 / 1000000000000), orderedInterval (39197355070 / 1000000000000) (39197355071 / 1000000000000)))) (orderedInterval (-6416873929 / 1000000000000) (-6416873860 / 1000000000000))) = true
  rfl'

theorem compactCertificate356_chunkChecks0 :
    compactCertificate356.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate356.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate356_chunkChecks0_0
    compactCertificate356_chunkChecks0_1 compactCertificate356_chunkChecks0_2

theorem compactCertificate356_chunkChecks1_0 :
    compactCertificate356.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (455 / 2) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (45923148758 / 1000000000000) (45923179414 / 1000000000000), orderedInterval (-26357147177 / 1000000000000) (-26357116521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (134060376258991 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-59151090680 / 1000000000000) (-59151088577 / 1000000000000), orderedInterval (17500970850 / 1000000000000) (17500972953 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (43352371237903 / 160000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (48469582530 / 1000000000000) (48469582629 / 1000000000000), orderedInterval (419869432 / 1000000000000) (419869531 / 1000000000000)))) (orderedInterval (-10297585753 / 1000000000000) (-10297573562 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (39118483441037 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-62961363155 / 1000000000000) (-62961348461 / 1000000000000), orderedInterval (95803841742 / 1000000000000) (95803856436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (105077748992489 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (12788480011 / 1000000000000) (12788480012 / 1000000000000), orderedInterval (68386214482 / 1000000000000) (68386214483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (285306529047813 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27965519008 / 1000000000000) (-27965506320 / 1000000000000), orderedInterval (31709585493 / 1000000000000) (31709598181 / 1000000000000)))) (orderedInterval (-2315582845 / 1000000000000) (-2315581365 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (210155497985069 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19825265975 / 1000000000000) (-19825265240 / 1000000000000), orderedInterval (45097533388 / 1000000000000) (45097534123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (360105027783137 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-37427214440 / 1000000000000) (-37427213173 / 1000000000000), orderedInterval (3715916711 / 1000000000000) (3715917978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (265251733611683 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26835733432 / 1000000000000) (-26835725848 / 1000000000000), orderedInterval (34679910614 / 1000000000000) (34679918198 / 1000000000000)))) (orderedInterval (994760543 / 1000000000000) (994760910 / 1000000000000))) = true
  rfl'

theorem compactCertificate356_chunkChecks1_1 :
    compactCertificate356.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (406964371904909 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18569073818 / 1000000000000) (18569073819 / 1000000000000), orderedInterval (30092218567 / 1000000000000) (30092218568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (234960989669861 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34151076560 / 1000000000000) (-34151033053 / 1000000000000), orderedInterval (31701144721 / 1000000000000) (31701188228 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (416942399340649 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15477664976 / 1000000000000) (15477664977 / 1000000000000), orderedInterval (31321134630 / 1000000000000) (31321134631 / 1000000000000)))) (orderedInterval (1276131877 / 1000000000000) (1276136226 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (389561673809581 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25693981863 / 1000000000000) (-25693981862 / 1000000000000), orderedInterval (-25413259015 / 1000000000000) (-25413259014 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (278009592160573 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17443055138 / 1000000000000) (17443055599 / 1000000000000), orderedInterval (-39110608879 / 1000000000000) (-39110608418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (315233246977467 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-34124177817 / 1000000000000) (-34124088643 / 1000000000000), orderedInterval (21283750471 / 1000000000000) (21283839644 / 1000000000000)))) (orderedInterval (-4853961452 / 1000000000000) (-4853960560 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (262808616611723 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23808771529 / 1000000000000) (23808774586 / 1000000000000), orderedInterval (-37063788696 / 1000000000000) (-37063785639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (232199382962183 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42434557810 / 1000000000000) (42434576907 / 1000000000000), orderedInterval (-19888784372 / 1000000000000) (-19888765275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (67300431588117 / 160000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16548897449 / 1000000000000) (16548897450 / 1000000000000), orderedInterval (35188766078 / 1000000000000) (35188766079 / 1000000000000)))) (orderedInterval (2499881986 / 1000000000000) (2499883463 / 1000000000000))) = true
  rfl'

theorem compactCertificate356_chunkChecks1_2 :
    compactCertificate356.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (186156535600399 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (44088778103 / 1000000000000) (44088778104 / 1000000000000), orderedInterval (28048188066 / 1000000000000) (28048188067 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (157806956855639 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6976923908 / 1000000000000) (-6976923907 / 1000000000000), orderedInterval (-56361983475 / 1000000000000) (-56361983474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (98748266388317 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-71238917511 / 1000000000000) (-71238917278 / 1000000000000), orderedInterval (9371086797 / 1000000000000) (9371087030 / 1000000000000)))) (orderedInterval (-1655556537 / 1000000000000) (-1655556479 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (53107146085539 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-91057317392 / 1000000000000) (-91057317391 / 1000000000000), orderedInterval (-35346608013 / 1000000000000) (-35346608012 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (144196232433617 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55003226873 / 1000000000000) (-55003220030 / 1000000000000), orderedInterval (22660330987 / 1000000000000) (22660337830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (196887627673009 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48887572461 / 1000000000000) (48887575528 / 1000000000000), orderedInterval (-14125513591 / 1000000000000) (-14125510523 / 1000000000000)))) (orderedInterval (954258792 / 1000000000000) (954259194 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (83251733611683 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-72206832755 / 1000000000000) (-72206832754 / 1000000000000), orderedInterval (-29714074308 / 1000000000000) (-29714074307 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (338413675133443 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (11938174473 / 1000000000000) (11938174538 / 1000000000000), orderedInterval (-36925237903 / 1000000000000) (-36925237838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (226044651524237 / 800000000000) 1 (IntervalRat.scale (455 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26700908897 / 1000000000000) (26700908898 / 1000000000000), orderedInterval (39197355070 / 1000000000000) (39197355071 / 1000000000000)))) (orderedInterval (-3627212565 / 1000000000000) (-3627212466 / 1000000000000))) = true
  rfl'

theorem compactCertificate356_chunkChecks1 :
    compactCertificate356.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate356.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate356_chunkChecks1_0
    compactCertificate356_chunkChecks1_1 compactCertificate356_chunkChecks1_2

theorem compactCertificate356_chunkChecks2_0 :
    compactCertificate356.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (455 / 2) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (45923148758 / 1000000000000) (45923179414 / 1000000000000), orderedInterval (-26357147177 / 1000000000000) (-26357116521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (134060376258991 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-59151090680 / 1000000000000) (-59151088577 / 1000000000000), orderedInterval (17500970850 / 1000000000000) (17500972953 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (43352371237903 / 160000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (48469582530 / 1000000000000) (48469582629 / 1000000000000), orderedInterval (419869432 / 1000000000000) (419869531 / 1000000000000)))) (orderedInterval (-21892534643 / 1000000000000) (-21892522399 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (39118483441037 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-62961363155 / 1000000000000) (-62961348461 / 1000000000000), orderedInterval (95803841742 / 1000000000000) (95803856436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (105077748992489 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (12788480011 / 1000000000000) (12788480012 / 1000000000000), orderedInterval (68386214482 / 1000000000000) (68386214483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (285306529047813 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27965519008 / 1000000000000) (-27965506320 / 1000000000000), orderedInterval (31709585493 / 1000000000000) (31709598181 / 1000000000000)))) (orderedInterval (-5062531318 / 1000000000000) (-5062529044 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (210155497985069 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19825265975 / 1000000000000) (-19825265240 / 1000000000000), orderedInterval (45097533388 / 1000000000000) (45097534123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (360105027783137 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-37427214440 / 1000000000000) (-37427213173 / 1000000000000), orderedInterval (3715916711 / 1000000000000) (3715917978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (265251733611683 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26835733432 / 1000000000000) (-26835725848 / 1000000000000), orderedInterval (34679910614 / 1000000000000) (34679918198 / 1000000000000)))) (orderedInterval (-3146083867 / 1000000000000) (-3146083283 / 1000000000000))) = true
  rfl'

theorem compactCertificate356_chunkChecks2_1 :
    compactCertificate356.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (406964371904909 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18569073818 / 1000000000000) (18569073819 / 1000000000000), orderedInterval (30092218567 / 1000000000000) (30092218568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (234960989669861 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34151076560 / 1000000000000) (-34151033053 / 1000000000000), orderedInterval (31701144721 / 1000000000000) (31701188228 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (416942399340649 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15477664976 / 1000000000000) (15477664977 / 1000000000000), orderedInterval (31321134630 / 1000000000000) (31321134631 / 1000000000000)))) (orderedInterval (9161796841 / 1000000000000) (9161802634 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (389561673809581 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25693981863 / 1000000000000) (-25693981862 / 1000000000000), orderedInterval (-25413259015 / 1000000000000) (-25413259014 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (278009592160573 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17443055138 / 1000000000000) (17443055599 / 1000000000000), orderedInterval (-39110608879 / 1000000000000) (-39110608418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (315233246977467 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-34124177817 / 1000000000000) (-34124088643 / 1000000000000), orderedInterval (21283750471 / 1000000000000) (21283839644 / 1000000000000)))) (orderedInterval (-6470644779 / 1000000000000) (-6470643246 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (262808616611723 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23808771529 / 1000000000000) (23808774586 / 1000000000000), orderedInterval (-37063788696 / 1000000000000) (-37063785639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (232199382962183 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42434557810 / 1000000000000) (42434576907 / 1000000000000), orderedInterval (-19888784372 / 1000000000000) (-19888765275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (67300431588117 / 160000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16548897449 / 1000000000000) (16548897450 / 1000000000000), orderedInterval (35188766078 / 1000000000000) (35188766079 / 1000000000000)))) (orderedInterval (1919995594 / 1000000000000) (1919997501 / 1000000000000))) = true
  rfl'

theorem compactCertificate356_chunkChecks2_2 :
    compactCertificate356.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (186156535600399 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (44088778103 / 1000000000000) (44088778104 / 1000000000000), orderedInterval (28048188066 / 1000000000000) (28048188067 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (157806956855639 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6976923908 / 1000000000000) (-6976923907 / 1000000000000), orderedInterval (-56361983475 / 1000000000000) (-56361983474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (98748266388317 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-71238917511 / 1000000000000) (-71238917278 / 1000000000000), orderedInterval (9371086797 / 1000000000000) (9371087030 / 1000000000000)))) (orderedInterval (7768262395 / 1000000000000) (7768262449 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (53107146085539 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-91057317392 / 1000000000000) (-91057317391 / 1000000000000), orderedInterval (-35346608013 / 1000000000000) (-35346608012 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (144196232433617 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55003226873 / 1000000000000) (-55003220030 / 1000000000000), orderedInterval (22660330987 / 1000000000000) (22660337830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (196887627673009 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48887572461 / 1000000000000) (48887575528 / 1000000000000), orderedInterval (-14125513591 / 1000000000000) (-14125510523 / 1000000000000)))) (orderedInterval (3454061283 / 1000000000000) (3454061682 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (83251733611683 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-72206832755 / 1000000000000) (-72206832754 / 1000000000000), orderedInterval (-29714074308 / 1000000000000) (-29714074307 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (338413675133443 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (11938174473 / 1000000000000) (11938174538 / 1000000000000), orderedInterval (-36925237903 / 1000000000000) (-36925237838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (226044651524237 / 800000000000) 2 (IntervalRat.scale (455 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26700908897 / 1000000000000) (26700908898 / 1000000000000), orderedInterval (39197355070 / 1000000000000) (39197355071 / 1000000000000)))) (orderedInterval (11194891011 / 1000000000000) (11194891160 / 1000000000000))) = true
  rfl'

theorem compactCertificate356_chunkChecks2 :
    compactCertificate356.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate356.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate356_chunkChecks2_0
    compactCertificate356_chunkChecks2_1 compactCertificate356_chunkChecks2_2

theorem compactCertificate356_chunkChecks3_0 :
    compactCertificate356.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (455 / 2) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (45923148758 / 1000000000000) (45923179414 / 1000000000000), orderedInterval (-26357147177 / 1000000000000) (-26357116521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (134060376258991 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-59151090680 / 1000000000000) (-59151088577 / 1000000000000), orderedInterval (17500970850 / 1000000000000) (17500972953 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (43352371237903 / 160000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (48469582530 / 1000000000000) (48469582629 / 1000000000000), orderedInterval (419869432 / 1000000000000) (419869531 / 1000000000000)))) (orderedInterval (10436271793 / 1000000000000) (10436284039 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (39118483441037 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-62961363155 / 1000000000000) (-62961348461 / 1000000000000), orderedInterval (95803841742 / 1000000000000) (95803856436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (105077748992489 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (12788480011 / 1000000000000) (12788480012 / 1000000000000), orderedInterval (68386214482 / 1000000000000) (68386214483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (285306529047813 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27965519008 / 1000000000000) (-27965506320 / 1000000000000), orderedInterval (31709585493 / 1000000000000) (31709598181 / 1000000000000)))) (orderedInterval (8235961095 / 1000000000000) (8235964646 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (210155497985069 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19825265975 / 1000000000000) (-19825265240 / 1000000000000), orderedInterval (45097533388 / 1000000000000) (45097534123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (360105027783137 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-37427214440 / 1000000000000) (-37427213173 / 1000000000000), orderedInterval (3715916711 / 1000000000000) (3715917978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (265251733611683 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26835733432 / 1000000000000) (-26835725848 / 1000000000000), orderedInterval (34679910614 / 1000000000000) (34679918198 / 1000000000000)))) (orderedInterval (-1693018265 / 1000000000000) (-1693017320 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate356_chunkChecks3_1 :
    compactCertificate356.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (406964371904909 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18569073818 / 1000000000000) (18569073819 / 1000000000000), orderedInterval (30092218567 / 1000000000000) (30092218568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (234960989669861 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34151076560 / 1000000000000) (-34151033053 / 1000000000000), orderedInterval (31701144721 / 1000000000000) (31701188228 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (416942399340649 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15477664976 / 1000000000000) (15477664977 / 1000000000000), orderedInterval (31321134630 / 1000000000000) (31321134631 / 1000000000000)))) (orderedInterval (1155132683 / 1000000000000) (1155140524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (389561673809581 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25693981863 / 1000000000000) (-25693981862 / 1000000000000), orderedInterval (-25413259015 / 1000000000000) (-25413259014 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (278009592160573 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17443055138 / 1000000000000) (17443055599 / 1000000000000), orderedInterval (-39110608879 / 1000000000000) (-39110608418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (315233246977467 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-34124177817 / 1000000000000) (-34124088643 / 1000000000000), orderedInterval (21283750471 / 1000000000000) (21283839644 / 1000000000000)))) (orderedInterval (9270880683 / 1000000000000) (9270883314 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (262808616611723 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23808771529 / 1000000000000) (23808774586 / 1000000000000), orderedInterval (-37063788696 / 1000000000000) (-37063785639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (232199382962183 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42434557810 / 1000000000000) (42434576907 / 1000000000000), orderedInterval (-19888784372 / 1000000000000) (-19888765275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (67300431588117 / 160000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16548897449 / 1000000000000) (16548897450 / 1000000000000), orderedInterval (35188766078 / 1000000000000) (35188766079 / 1000000000000)))) (orderedInterval (-6777873219 / 1000000000000) (-6777870763 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate356_chunkChecks3_2 :
    compactCertificate356.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (186156535600399 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (44088778103 / 1000000000000) (44088778104 / 1000000000000), orderedInterval (28048188066 / 1000000000000) (28048188067 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (157806956855639 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6976923908 / 1000000000000) (-6976923907 / 1000000000000), orderedInterval (-56361983475 / 1000000000000) (-56361983474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (98748266388317 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-71238917511 / 1000000000000) (-71238917278 / 1000000000000), orderedInterval (9371086797 / 1000000000000) (9371087030 / 1000000000000)))) (orderedInterval (2636585885 / 1000000000000) (2636585936 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (53107146085539 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-91057317392 / 1000000000000) (-91057317391 / 1000000000000), orderedInterval (-35346608013 / 1000000000000) (-35346608012 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (144196232433617 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55003226873 / 1000000000000) (-55003220030 / 1000000000000), orderedInterval (22660330987 / 1000000000000) (22660337830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (196887627673009 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48887572461 / 1000000000000) (48887575528 / 1000000000000), orderedInterval (-14125513591 / 1000000000000) (-14125510523 / 1000000000000)))) (orderedInterval (-1146253944 / 1000000000000) (-1146253542 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (83251733611683 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-72206832755 / 1000000000000) (-72206832754 / 1000000000000), orderedInterval (-29714074308 / 1000000000000) (-29714074307 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (338413675133443 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (11938174473 / 1000000000000) (11938174538 / 1000000000000), orderedInterval (-36925237903 / 1000000000000) (-36925237838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (226044651524237 / 800000000000) 3 (IntervalRat.scale (455 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26700908897 / 1000000000000) (26700908898 / 1000000000000), orderedInterval (39197355070 / 1000000000000) (39197355071 / 1000000000000)))) (orderedInterval (-5265398585 / 1000000000000) (-5265398349 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate356_chunkChecks3 :
    compactCertificate356.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate356.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate356_chunkChecks3_0
    compactCertificate356_chunkChecks3_1 compactCertificate356_chunkChecks3_2

theorem compactCertificate356_chunkChecks4_0 :
    compactCertificate356.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (455 / 2) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (45923148758 / 1000000000000) (45923179414 / 1000000000000), orderedInterval (-26357147177 / 1000000000000) (-26357116521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (134060376258991 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-59151090680 / 1000000000000) (-59151088577 / 1000000000000), orderedInterval (17500970850 / 1000000000000) (17500972953 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (43352371237903 / 160000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (48469582530 / 1000000000000) (48469582629 / 1000000000000), orderedInterval (419869432 / 1000000000000) (419869531 / 1000000000000)))) (orderedInterval (23670769293 / 1000000000000) (23670781596 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (39118483441037 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-62961363155 / 1000000000000) (-62961348461 / 1000000000000), orderedInterval (95803841742 / 1000000000000) (95803856436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (105077748992489 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (12788480011 / 1000000000000) (12788480012 / 1000000000000), orderedInterval (68386214482 / 1000000000000) (68386214483 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (285306529047813 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27965519008 / 1000000000000) (-27965506320 / 1000000000000), orderedInterval (31709585493 / 1000000000000) (31709598181 / 1000000000000)))) (orderedInterval (11986614879 / 1000000000000) (11986620457 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (210155497985069 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19825265975 / 1000000000000) (-19825265240 / 1000000000000), orderedInterval (45097533388 / 1000000000000) (45097534123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (360105027783137 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-37427214440 / 1000000000000) (-37427213173 / 1000000000000), orderedInterval (3715916711 / 1000000000000) (3715917978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (265251733611683 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26835733432 / 1000000000000) (-26835725848 / 1000000000000), orderedInterval (34679910614 / 1000000000000) (34679918198 / 1000000000000)))) (orderedInterval (14781143450 / 1000000000000) (14781145017 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate356_chunkChecks4_1 :
    compactCertificate356.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (406964371904909 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18569073818 / 1000000000000) (18569073819 / 1000000000000), orderedInterval (30092218567 / 1000000000000) (30092218568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (234960989669861 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34151076560 / 1000000000000) (-34151033053 / 1000000000000), orderedInterval (31701144721 / 1000000000000) (31701188228 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (416942399340649 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15477664976 / 1000000000000) (15477664977 / 1000000000000), orderedInterval (31321134630 / 1000000000000) (31321134631 / 1000000000000)))) (orderedInterval (-28923848758 / 1000000000000) (-28923837785 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (389561673809581 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25693981863 / 1000000000000) (-25693981862 / 1000000000000), orderedInterval (-25413259015 / 1000000000000) (-25413259014 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (278009592160573 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17443055138 / 1000000000000) (17443055599 / 1000000000000), orderedInterval (-39110608879 / 1000000000000) (-39110608418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (315233246977467 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-34124177817 / 1000000000000) (-34124088643 / 1000000000000), orderedInterval (21283750471 / 1000000000000) (21283839644 / 1000000000000)))) (orderedInterval (20189468152 / 1000000000000) (20189472687 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (262808616611723 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23808771529 / 1000000000000) (23808774586 / 1000000000000), orderedInterval (-37063788696 / 1000000000000) (-37063785639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (232199382962183 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42434557810 / 1000000000000) (42434576907 / 1000000000000), orderedInterval (-19888784372 / 1000000000000) (-19888765275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (67300431588117 / 160000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16548897449 / 1000000000000) (16548897450 / 1000000000000), orderedInterval (35188766078 / 1000000000000) (35188766079 / 1000000000000)))) (orderedInterval (-227385453 / 1000000000000) (-227382268 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate356_chunkChecks4_2 :
    compactCertificate356.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (186156535600399 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (44088778103 / 1000000000000) (44088778104 / 1000000000000), orderedInterval (28048188066 / 1000000000000) (28048188067 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (157806956855639 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6976923908 / 1000000000000) (-6976923907 / 1000000000000), orderedInterval (-56361983475 / 1000000000000) (-56361983474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (98748266388317 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-71238917511 / 1000000000000) (-71238917278 / 1000000000000), orderedInterval (9371086797 / 1000000000000) (9371087030 / 1000000000000)))) (orderedInterval (-7716661286 / 1000000000000) (-7716661236 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (53107146085539 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-91057317392 / 1000000000000) (-91057317391 / 1000000000000), orderedInterval (-35346608013 / 1000000000000) (-35346608012 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (144196232433617 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-55003226873 / 1000000000000) (-55003220030 / 1000000000000), orderedInterval (22660330987 / 1000000000000) (22660337830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (196887627673009 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (48887572461 / 1000000000000) (48887575528 / 1000000000000), orderedInterval (-14125513591 / 1000000000000) (-14125510523 / 1000000000000)))) (orderedInterval (-4617373787 / 1000000000000) (-4617373374 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (83251733611683 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-72206832755 / 1000000000000) (-72206832754 / 1000000000000), orderedInterval (-29714074308 / 1000000000000) (-29714074307 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (338413675133443 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (11938174473 / 1000000000000) (11938174538 / 1000000000000), orderedInterval (-36925237903 / 1000000000000) (-36925237838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (226044651524237 / 800000000000) 4 (IntervalRat.scale (455 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26700908897 / 1000000000000) (26700908898 / 1000000000000), orderedInterval (39197355070 / 1000000000000) (39197355071 / 1000000000000)))) (orderedInterval (-23510092864 / 1000000000000) (-23510092476 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate356_chunkChecks4 :
    compactCertificate356.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate356.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate356_chunkChecks4_0
    compactCertificate356_chunkChecks4_1 compactCertificate356_chunkChecks4_2

theorem compactCertificate356_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate356.chunkCheck r b = true :=
  compactCertificate356.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate356_chunkChecks0
    · exact compactCertificate356_chunkChecks1
    · exact compactCertificate356_chunkChecks2
    · exact compactCertificate356_chunkChecks3
    · exact compactCertificate356_chunkChecks4)

theorem compactCertificate356_coefficient0 :
    compactCertificate356.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate356_coefficient1 :
    compactCertificate356.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate356_coefficient2 :
    compactCertificate356.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate356_coefficient3 :
    compactCertificate356.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate356_coefficient4 :
    compactCertificate356.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate356_coefficients : ∀ r : Fin 5,
    compactCertificate356.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate356_coefficient0
  · exact compactCertificate356_coefficient1
  · exact compactCertificate356_coefficient2
  · exact compactCertificate356_coefficient3
  · exact compactCertificate356_coefficient4

theorem compactCertificate356_lower : (1 : ℚ) ≤ compactCertificate356.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate356, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate356_proves {t : ℝ} (ht : t ∈ compactCertificate356.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate356.proves compactCertificate356_states compactCertificate356_chunks
    compactCertificate356_coefficients compactCertificate356_lower ht

end Erdos232
