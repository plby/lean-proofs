/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate355 : CompactCertificate where
  left := 226
  right := 227
  center := 453 / 2
  grid := fun i =>
    match i.val with
    | 0 => 72
    | 1 => 53
    | 2 => 86
    | 3 => 16
    | 4 => 42
    | 5 => 113
    | 6 => 83
    | 7 => 143
    | 8 => 105
    | 9 => 161
    | 10 => 93
    | 11 => 165
    | 12 => 154
    | 13 => 110
    | 14 => 125
    | 15 => 104
    | 16 => 92
    | 17 => 133
    | 18 => 74
    | 19 => 63
    | 20 => 39
    | 21 => 21
    | 22 => 57
    | 23 => 78
    | 24 => 33
    | 25 => 134
    | _ => 90
  point := fun i =>
    match i.val with
    | 0 => 453 / 2
    | 1 => 667355499399153 / 4000000000000
    | 2 => 215809056821649 / 800000000000
    | 3 => 194732670316371 / 4000000000000
    | 4 => 523079343885687 / 4000000000000
    | 5 => 1420262172073179 / 4000000000000
    | 6 => 1046158687771827 / 4000000000000
    | 7 => 1792610742700671 / 4000000000000
    | 8 => 1320428959627389 / 4000000000000
    | 9 => 2025877587614547 / 4000000000000
    | 10 => 1169640970554363 / 4000000000000
    | 11 => 2075548427486967 / 4000000000000
    | 12 => 1939246574019123 / 4000000000000
    | 13 => 1383937859876259 / 4000000000000
    | 14 => 1569238031657061 / 4000000000000
    | 15 => 1308267069506709 / 4000000000000
    | 16 => 1155893631668889 / 4000000000000
    | 17 => 335023027576011 / 800000000000
    | 18 => 926691325571217 / 4000000000000
    | 19 => 785566499512137 / 4000000000000
    | 20 => 491571040372611 / 4000000000000
    | 21 => 264368540403837 / 4000000000000
    | 22 => 717812014202511 / 4000000000000
    | 23 => 980110937756847 / 4000000000000
    | 24 => 414428959627389 / 4000000000000
    | 25 => 1684630712477469 / 4000000000000
    | _ => 1125255243301971 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (47009542929 / 1000000000000) (47009542930 / 1000000000000), orderedInterval (24407087022 / 1000000000000) (24407087023 / 1000000000000))
    | 1 => (orderedInterval (-55576961288 / 1000000000000) (-55576961287 / 1000000000000), orderedInterval (-26795763741 / 1000000000000) (-26795763740 / 1000000000000))
    | 2 => (orderedInterval (17534698094 / 1000000000000) (17534698095 / 1000000000000), orderedInterval (45271743938 / 1000000000000) (45271743939 / 1000000000000))
    | 3 => (orderedInterval (-81989150571 / 1000000000000) (-81989049204 / 1000000000000), orderedInterval (80557430551 / 1000000000000) (80557531919 / 1000000000000))
    | 4 => (orderedInterval (-26695266574 / 1000000000000) (-26695265323 / 1000000000000), orderedInterval (64566276625 / 1000000000000) (64566277875 / 1000000000000))
    | 5 => (orderedInterval (-31829056309 / 1000000000000) (-31829056308 / 1000000000000), orderedInterval (-27881421651 / 1000000000000) (-27881421650 / 1000000000000))
    | 6 => (orderedInterval (-49336725071 / 1000000000000) (-49336724962 / 1000000000000), orderedInterval (173534447 / 1000000000000) (173534556 / 1000000000000))
    | 7 => (orderedInterval (11495690395 / 1000000000000) (11495690446 / 1000000000000), orderedInterval (-35907002826 / 1000000000000) (-35907002774 / 1000000000000))
    | 8 => (orderedInterval (-37535423485 / 1000000000000) (-37535423484 / 1000000000000), orderedInterval (-22738213714 / 1000000000000) (-22738213713 / 1000000000000))
    | 9 => (orderedInterval (-35229067637 / 1000000000000) (-35229067512 / 1000000000000), orderedInterval (-3951195784 / 1000000000000) (-3951195659 / 1000000000000))
    | 10 => (orderedInterval (-39931539211 / 1000000000000) (-39931539210 / 1000000000000), orderedInterval (-24069173184 / 1000000000000) (-24069173183 / 1000000000000))
    | 11 => (orderedInterval (-33837870769 / 1000000000000) (-33837870754 / 1000000000000), orderedInterval (-9016845529 / 1000000000000) (-9016845513 / 1000000000000))
    | 12 => (orderedInterval (35357995787 / 1000000000000) (35358001731 / 1000000000000), orderedInterval (-7969900695 / 1000000000000) (-7969894751 / 1000000000000))
    | 13 => (orderedInterval (39891174211 / 1000000000000) (39891174212 / 1000000000000), orderedInterval (15713114524 / 1000000000000) (15713114525 / 1000000000000))
    | 14 => (orderedInterval (-15520161627 / 1000000000000) (-15520161626 / 1000000000000), orderedInterval (-37153789198 / 1000000000000) (-37153789197 / 1000000000000))
    | 15 => (orderedInterval (39828572048 / 1000000000000) (39828572049 / 1000000000000), orderedInterval (18916347475 / 1000000000000) (18916347477 / 1000000000000))
    | 16 => (orderedInterval (31365163862 / 1000000000000) (31365163863 / 1000000000000), orderedInterval (34863721841 / 1000000000000) (34863721842 / 1000000000000))
    | 17 => (orderedInterval (-38483602819 / 1000000000000) (-38483600637 / 1000000000000), orderedInterval (6306369184 / 1000000000000) (6306371367 / 1000000000000))
    | 18 => (orderedInterval (-1057060983 / 1000000000000) (-1057060980 / 1000000000000), orderedInterval (52412346328 / 1000000000000) (52412346332 / 1000000000000))
    | 19 => (orderedInterval (38556238510 / 1000000000000) (38556271601 / 1000000000000), orderedInterval (-41990886515 / 1000000000000) (-41990853424 / 1000000000000))
    | 20 => (orderedInterval (-65842176865 / 1000000000000) (-65842176864 / 1000000000000), orderedInterval (-28802136974 / 1000000000000) (-28802136973 / 1000000000000))
    | 21 => (orderedInterval (-77011800692 / 1000000000000) (-77011800691 / 1000000000000), orderedInterval (-60256772469 / 1000000000000) (-60256772468 / 1000000000000))
    | 22 => (orderedInterval (-54769321445 / 1000000000000) (-54769321444 / 1000000000000), orderedInterval (-23254001803 / 1000000000000) (-23254001802 / 1000000000000))
    | 23 => (orderedInterval (35424670515 / 1000000000000) (35424670516 / 1000000000000), orderedInterval (36578045263 / 1000000000000) (36578045264 / 1000000000000))
    | 24 => (orderedInterval (-51620615382 / 1000000000000) (-51620615381 / 1000000000000), orderedInterval (-58741317468 / 1000000000000) (-58741317467 / 1000000000000))
    | 25 => (orderedInterval (32056926477 / 1000000000000) (32056926478 / 1000000000000), orderedInterval (21960758280 / 1000000000000) (21960758281 / 1000000000000))
    | _ => (orderedInterval (-28583550836 / 1000000000000) (-28583542368 / 1000000000000), orderedInterval (38077176517 / 1000000000000) (38077184984 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (19144023760 / 1000000000000) (19144023776 / 1000000000000)
      | 1 => orderedInterval (2177548433 / 1000000000000) (2177549607 / 1000000000000)
      | 2 => orderedInterval (-1261730223 / 1000000000000) (-1261730208 / 1000000000000)
      | 3 => orderedInterval (-1509071265 / 1000000000000) (-1509071151 / 1000000000000)
      | 4 => orderedInterval (3212443659 / 1000000000000) (3212443794 / 1000000000000)
      | 5 => orderedInterval (-2320329148 / 1000000000000) (-2320329070 / 1000000000000)
      | 6 => orderedInterval (-4156777154 / 1000000000000) (-4156775224 / 1000000000000)
      | 7 => orderedInterval (-50330785 / 1000000000000) (-50330757 / 1000000000000)
      | _ => orderedInterval (2442353971 / 1000000000000) (2442355623 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (12654203945 / 1000000000000) (12654203964 / 1000000000000)
      | 1 => orderedInterval (4280353647 / 1000000000000) (4280353941 / 1000000000000)
      | 2 => orderedInterval (1390418133 / 1000000000000) (1390418159 / 1000000000000)
      | 3 => orderedInterval (-3668828670 / 1000000000000) (-3668828428 / 1000000000000)
      | 4 => orderedInterval (2903344586 / 1000000000000) (2903344860 / 1000000000000)
      | 5 => orderedInterval (-1931466726 / 1000000000000) (-1931466591 / 1000000000000)
      | 6 => orderedInterval (-7019727624 / 1000000000000) (-7019725946 / 1000000000000)
      | 7 => orderedInterval (-2289963238 / 1000000000000) (-2289963213 / 1000000000000)
      | _ => orderedInterval (-12359189051 / 1000000000000) (-12359186989 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-19867376388 / 1000000000000) (-19867376367 / 1000000000000)
      | 1 => orderedInterval (-5295555064 / 1000000000000) (-5295554953 / 1000000000000)
      | 2 => orderedInterval (3308850018 / 1000000000000) (3308850064 / 1000000000000)
      | 3 => orderedInterval (-1106596337 / 1000000000000) (-1106595816 / 1000000000000)
      | 4 => orderedInterval (-6125815942 / 1000000000000) (-6125815376 / 1000000000000)
      | 5 => orderedInterval (5339481134 / 1000000000000) (5339481373 / 1000000000000)
      | 6 => orderedInterval (2125852143 / 1000000000000) (2125853610 / 1000000000000)
      | 7 => orderedInterval (2286294522 / 1000000000000) (2286294547 / 1000000000000)
      | _ => orderedInterval (868934107 / 1000000000000) (868936697 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-13974441275 / 1000000000000) (-13974441250 / 1000000000000)
      | 1 => orderedInterval (-8057128422 / 1000000000000) (-8057128337 / 1000000000000)
      | 2 => orderedInterval (-6892106040 / 1000000000000) (-6892105955 / 1000000000000)
      | 3 => orderedInterval (11403528832 / 1000000000000) (11403529983 / 1000000000000)
      | 4 => orderedInterval (-7656851086 / 1000000000000) (-7656849907 / 1000000000000)
      | 5 => orderedInterval (2441373349 / 1000000000000) (2441373776 / 1000000000000)
      | 6 => orderedInterval (7558670407 / 1000000000000) (7558671684 / 1000000000000)
      | 7 => orderedInterval (3248882294 / 1000000000000) (3248882320 / 1000000000000)
      | _ => orderedInterval (25209822974 / 1000000000000) (25209826230 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (20673835267 / 1000000000000) (20673835296 / 1000000000000)
      | 1 => orderedInterval (13629065821 / 1000000000000) (13629065928 / 1000000000000)
      | 2 => orderedInterval (-9466183273 / 1000000000000) (-9466183116 / 1000000000000)
      | 3 => orderedInterval (15684390572 / 1000000000000) (15684393130 / 1000000000000)
      | 4 => orderedInterval (7913450013 / 1000000000000) (7913452489 / 1000000000000)
      | 5 => orderedInterval (-14291952739 / 1000000000000) (-14291951969 / 1000000000000)
      | 6 => orderedInterval (-1300944956 / 1000000000000) (-1300943837 / 1000000000000)
      | 7 => orderedInterval (-3247021298 / 1000000000000) (-3247021271 / 1000000000000)
      | _ => orderedInterval (-18668047532 / 1000000000000) (-18668043401 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (17678131248 / 1000000000000) (17678136390 / 1000000000000)
    | 1 => orderedInterval (-6040854998 / 1000000000000) (-6040850243 / 1000000000000)
    | 2 => orderedInterval (-18465931807 / 1000000000000) (-18465926221 / 1000000000000)
    | 3 => orderedInterval (13281751033 / 1000000000000) (13281758544 / 1000000000000)
    | _ => orderedInterval (10926591875 / 1000000000000) (10926603249 / 1000000000000)

theorem compactCertificate355_stateChecks0 :
    compactCertificate355.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (453 / 2)) (orderedInterval (47009542929 / 1000000000000) (47009542930 / 1000000000000), orderedInterval (24407087022 / 1000000000000) (24407087023 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (667355499399153 / 4000000000000)) (orderedInterval (-55576961288 / 1000000000000) (-55576961287 / 1000000000000), orderedInterval (-26795763741 / 1000000000000) (-26795763740 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (215809056821649 / 800000000000)) (orderedInterval (17534698094 / 1000000000000) (17534698095 / 1000000000000), orderedInterval (45271743938 / 1000000000000) (45271743939 / 1000000000000))) = true
  rfl'

theorem compactCertificate355_stateChecks1 :
    compactCertificate355.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (194732670316371 / 4000000000000)) (orderedInterval (-81989150571 / 1000000000000) (-81989049204 / 1000000000000), orderedInterval (80557430551 / 1000000000000) (80557531919 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (523079343885687 / 4000000000000)) (orderedInterval (-26695266574 / 1000000000000) (-26695265323 / 1000000000000), orderedInterval (64566276625 / 1000000000000) (64566277875 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1420262172073179 / 4000000000000)) (orderedInterval (-31829056309 / 1000000000000) (-31829056308 / 1000000000000), orderedInterval (-27881421651 / 1000000000000) (-27881421650 / 1000000000000))) = true
  rfl'

theorem compactCertificate355_stateChecks2 :
    compactCertificate355.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1046158687771827 / 4000000000000)) (orderedInterval (-49336725071 / 1000000000000) (-49336724962 / 1000000000000), orderedInterval (173534447 / 1000000000000) (173534556 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1792610742700671 / 4000000000000)) (orderedInterval (11495690395 / 1000000000000) (11495690446 / 1000000000000), orderedInterval (-35907002826 / 1000000000000) (-35907002774 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1320428959627389 / 4000000000000)) (orderedInterval (-37535423485 / 1000000000000) (-37535423484 / 1000000000000), orderedInterval (-22738213714 / 1000000000000) (-22738213713 / 1000000000000))) = true
  rfl'

theorem compactCertificate355_stateChecks3 :
    compactCertificate355.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2025877587614547 / 4000000000000)) (orderedInterval (-35229067637 / 1000000000000) (-35229067512 / 1000000000000), orderedInterval (-3951195784 / 1000000000000) (-3951195659 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1169640970554363 / 4000000000000)) (orderedInterval (-39931539211 / 1000000000000) (-39931539210 / 1000000000000), orderedInterval (-24069173184 / 1000000000000) (-24069173183 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2075548427486967 / 4000000000000)) (orderedInterval (-33837870769 / 1000000000000) (-33837870754 / 1000000000000), orderedInterval (-9016845529 / 1000000000000) (-9016845513 / 1000000000000))) = true
  rfl'

theorem compactCertificate355_stateChecks4 :
    compactCertificate355.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1939246574019123 / 4000000000000)) (orderedInterval (35357995787 / 1000000000000) (35358001731 / 1000000000000), orderedInterval (-7969900695 / 1000000000000) (-7969894751 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1383937859876259 / 4000000000000)) (orderedInterval (39891174211 / 1000000000000) (39891174212 / 1000000000000), orderedInterval (15713114524 / 1000000000000) (15713114525 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1569238031657061 / 4000000000000)) (orderedInterval (-15520161627 / 1000000000000) (-15520161626 / 1000000000000), orderedInterval (-37153789198 / 1000000000000) (-37153789197 / 1000000000000))) = true
  rfl'

theorem compactCertificate355_stateChecks5 :
    compactCertificate355.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1308267069506709 / 4000000000000)) (orderedInterval (39828572048 / 1000000000000) (39828572049 / 1000000000000), orderedInterval (18916347475 / 1000000000000) (18916347477 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1155893631668889 / 4000000000000)) (orderedInterval (31365163862 / 1000000000000) (31365163863 / 1000000000000), orderedInterval (34863721841 / 1000000000000) (34863721842 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (335023027576011 / 800000000000)) (orderedInterval (-38483602819 / 1000000000000) (-38483600637 / 1000000000000), orderedInterval (6306369184 / 1000000000000) (6306371367 / 1000000000000))) = true
  rfl'

theorem compactCertificate355_stateChecks6 :
    compactCertificate355.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (926691325571217 / 4000000000000)) (orderedInterval (-1057060983 / 1000000000000) (-1057060980 / 1000000000000), orderedInterval (52412346328 / 1000000000000) (52412346332 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (785566499512137 / 4000000000000)) (orderedInterval (38556238510 / 1000000000000) (38556271601 / 1000000000000), orderedInterval (-41990886515 / 1000000000000) (-41990853424 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (491571040372611 / 4000000000000)) (orderedInterval (-65842176865 / 1000000000000) (-65842176864 / 1000000000000), orderedInterval (-28802136974 / 1000000000000) (-28802136973 / 1000000000000))) = true
  rfl'

theorem compactCertificate355_stateChecks7 :
    compactCertificate355.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (264368540403837 / 4000000000000)) (orderedInterval (-77011800692 / 1000000000000) (-77011800691 / 1000000000000), orderedInterval (-60256772469 / 1000000000000) (-60256772468 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (717812014202511 / 4000000000000)) (orderedInterval (-54769321445 / 1000000000000) (-54769321444 / 1000000000000), orderedInterval (-23254001803 / 1000000000000) (-23254001802 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (980110937756847 / 4000000000000)) (orderedInterval (35424670515 / 1000000000000) (35424670516 / 1000000000000), orderedInterval (36578045263 / 1000000000000) (36578045264 / 1000000000000))) = true
  rfl'

theorem compactCertificate355_stateChecks8 :
    compactCertificate355.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (414428959627389 / 4000000000000)) (orderedInterval (-51620615382 / 1000000000000) (-51620615381 / 1000000000000), orderedInterval (-58741317468 / 1000000000000) (-58741317467 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1684630712477469 / 4000000000000)) (orderedInterval (32056926477 / 1000000000000) (32056926478 / 1000000000000), orderedInterval (21960758280 / 1000000000000) (21960758281 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1125255243301971 / 4000000000000)) (orderedInterval (-28583550836 / 1000000000000) (-28583542368 / 1000000000000), orderedInterval (38077176517 / 1000000000000) (38077184984 / 1000000000000))) = true
  rfl'

theorem compactCertificate355_states : ∀ j,
    BesselStateValid (compactCertificate355.point j) (compactCertificate355.state j) :=
  compactCertificate355.statesValid_of_checks3 compactCertificate355_stateChecks0
    compactCertificate355_stateChecks1 compactCertificate355_stateChecks2
    compactCertificate355_stateChecks3 compactCertificate355_stateChecks4
    compactCertificate355_stateChecks5 compactCertificate355_stateChecks6
    compactCertificate355_stateChecks7 compactCertificate355_stateChecks8

theorem compactCertificate355_chunkChecks0_0 :
    compactCertificate355.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (453 / 2) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (47009542929 / 1000000000000) (47009542930 / 1000000000000), orderedInterval (24407087022 / 1000000000000) (24407087023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (667355499399153 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-55576961288 / 1000000000000) (-55576961287 / 1000000000000), orderedInterval (-26795763741 / 1000000000000) (-26795763740 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (215809056821649 / 800000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17534698094 / 1000000000000) (17534698095 / 1000000000000), orderedInterval (45271743938 / 1000000000000) (45271743939 / 1000000000000)))) (orderedInterval (19144023760 / 1000000000000) (19144023776 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (194732670316371 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-81989150571 / 1000000000000) (-81989049204 / 1000000000000), orderedInterval (80557430551 / 1000000000000) (80557531919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (523079343885687 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26695266574 / 1000000000000) (-26695265323 / 1000000000000), orderedInterval (64566276625 / 1000000000000) (64566277875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1420262172073179 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-31829056309 / 1000000000000) (-31829056308 / 1000000000000), orderedInterval (-27881421651 / 1000000000000) (-27881421650 / 1000000000000)))) (orderedInterval (2177548433 / 1000000000000) (2177549607 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1046158687771827 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-49336725071 / 1000000000000) (-49336724962 / 1000000000000), orderedInterval (173534447 / 1000000000000) (173534556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1792610742700671 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (11495690395 / 1000000000000) (11495690446 / 1000000000000), orderedInterval (-35907002826 / 1000000000000) (-35907002774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1320428959627389 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-37535423485 / 1000000000000) (-37535423484 / 1000000000000), orderedInterval (-22738213714 / 1000000000000) (-22738213713 / 1000000000000)))) (orderedInterval (-1261730223 / 1000000000000) (-1261730208 / 1000000000000))) = true
  rfl'

theorem compactCertificate355_chunkChecks0_1 :
    compactCertificate355.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2025877587614547 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-35229067637 / 1000000000000) (-35229067512 / 1000000000000), orderedInterval (-3951195784 / 1000000000000) (-3951195659 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1169640970554363 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39931539211 / 1000000000000) (-39931539210 / 1000000000000), orderedInterval (-24069173184 / 1000000000000) (-24069173183 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2075548427486967 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33837870769 / 1000000000000) (-33837870754 / 1000000000000), orderedInterval (-9016845529 / 1000000000000) (-9016845513 / 1000000000000)))) (orderedInterval (-1509071265 / 1000000000000) (-1509071151 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1939246574019123 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (35357995787 / 1000000000000) (35358001731 / 1000000000000), orderedInterval (-7969900695 / 1000000000000) (-7969894751 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1383937859876259 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39891174211 / 1000000000000) (39891174212 / 1000000000000), orderedInterval (15713114524 / 1000000000000) (15713114525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1569238031657061 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15520161627 / 1000000000000) (-15520161626 / 1000000000000), orderedInterval (-37153789198 / 1000000000000) (-37153789197 / 1000000000000)))) (orderedInterval (3212443659 / 1000000000000) (3212443794 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1308267069506709 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39828572048 / 1000000000000) (39828572049 / 1000000000000), orderedInterval (18916347475 / 1000000000000) (18916347477 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1155893631668889 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31365163862 / 1000000000000) (31365163863 / 1000000000000), orderedInterval (34863721841 / 1000000000000) (34863721842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (335023027576011 / 800000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38483602819 / 1000000000000) (-38483600637 / 1000000000000), orderedInterval (6306369184 / 1000000000000) (6306371367 / 1000000000000)))) (orderedInterval (-2320329148 / 1000000000000) (-2320329070 / 1000000000000))) = true
  rfl'

theorem compactCertificate355_chunkChecks0_2 :
    compactCertificate355.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (926691325571217 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1057060983 / 1000000000000) (-1057060980 / 1000000000000), orderedInterval (52412346328 / 1000000000000) (52412346332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (785566499512137 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38556238510 / 1000000000000) (38556271601 / 1000000000000), orderedInterval (-41990886515 / 1000000000000) (-41990853424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (491571040372611 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65842176865 / 1000000000000) (-65842176864 / 1000000000000), orderedInterval (-28802136974 / 1000000000000) (-28802136973 / 1000000000000)))) (orderedInterval (-4156777154 / 1000000000000) (-4156775224 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (264368540403837 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77011800692 / 1000000000000) (-77011800691 / 1000000000000), orderedInterval (-60256772469 / 1000000000000) (-60256772468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (717812014202511 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54769321445 / 1000000000000) (-54769321444 / 1000000000000), orderedInterval (-23254001803 / 1000000000000) (-23254001802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (980110937756847 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35424670515 / 1000000000000) (35424670516 / 1000000000000), orderedInterval (36578045263 / 1000000000000) (36578045264 / 1000000000000)))) (orderedInterval (-50330785 / 1000000000000) (-50330757 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (414428959627389 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-51620615382 / 1000000000000) (-51620615381 / 1000000000000), orderedInterval (-58741317468 / 1000000000000) (-58741317467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1684630712477469 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32056926477 / 1000000000000) (32056926478 / 1000000000000), orderedInterval (21960758280 / 1000000000000) (21960758281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1125255243301971 / 4000000000000) 0 (IntervalRat.scale (453 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28583550836 / 1000000000000) (-28583542368 / 1000000000000), orderedInterval (38077176517 / 1000000000000) (38077184984 / 1000000000000)))) (orderedInterval (2442353971 / 1000000000000) (2442355623 / 1000000000000))) = true
  rfl'

theorem compactCertificate355_chunkChecks0 :
    compactCertificate355.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate355.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate355_chunkChecks0_0
    compactCertificate355_chunkChecks0_1 compactCertificate355_chunkChecks0_2

theorem compactCertificate355_chunkChecks1_0 :
    compactCertificate355.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (453 / 2) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (47009542929 / 1000000000000) (47009542930 / 1000000000000), orderedInterval (24407087022 / 1000000000000) (24407087023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (667355499399153 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-55576961288 / 1000000000000) (-55576961287 / 1000000000000), orderedInterval (-26795763741 / 1000000000000) (-26795763740 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (215809056821649 / 800000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17534698094 / 1000000000000) (17534698095 / 1000000000000), orderedInterval (45271743938 / 1000000000000) (45271743939 / 1000000000000)))) (orderedInterval (12654203945 / 1000000000000) (12654203964 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (194732670316371 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-81989150571 / 1000000000000) (-81989049204 / 1000000000000), orderedInterval (80557430551 / 1000000000000) (80557531919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (523079343885687 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26695266574 / 1000000000000) (-26695265323 / 1000000000000), orderedInterval (64566276625 / 1000000000000) (64566277875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1420262172073179 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-31829056309 / 1000000000000) (-31829056308 / 1000000000000), orderedInterval (-27881421651 / 1000000000000) (-27881421650 / 1000000000000)))) (orderedInterval (4280353647 / 1000000000000) (4280353941 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1046158687771827 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-49336725071 / 1000000000000) (-49336724962 / 1000000000000), orderedInterval (173534447 / 1000000000000) (173534556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1792610742700671 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (11495690395 / 1000000000000) (11495690446 / 1000000000000), orderedInterval (-35907002826 / 1000000000000) (-35907002774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1320428959627389 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-37535423485 / 1000000000000) (-37535423484 / 1000000000000), orderedInterval (-22738213714 / 1000000000000) (-22738213713 / 1000000000000)))) (orderedInterval (1390418133 / 1000000000000) (1390418159 / 1000000000000))) = true
  rfl'

theorem compactCertificate355_chunkChecks1_1 :
    compactCertificate355.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2025877587614547 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-35229067637 / 1000000000000) (-35229067512 / 1000000000000), orderedInterval (-3951195784 / 1000000000000) (-3951195659 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1169640970554363 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39931539211 / 1000000000000) (-39931539210 / 1000000000000), orderedInterval (-24069173184 / 1000000000000) (-24069173183 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2075548427486967 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33837870769 / 1000000000000) (-33837870754 / 1000000000000), orderedInterval (-9016845529 / 1000000000000) (-9016845513 / 1000000000000)))) (orderedInterval (-3668828670 / 1000000000000) (-3668828428 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1939246574019123 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (35357995787 / 1000000000000) (35358001731 / 1000000000000), orderedInterval (-7969900695 / 1000000000000) (-7969894751 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1383937859876259 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39891174211 / 1000000000000) (39891174212 / 1000000000000), orderedInterval (15713114524 / 1000000000000) (15713114525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1569238031657061 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15520161627 / 1000000000000) (-15520161626 / 1000000000000), orderedInterval (-37153789198 / 1000000000000) (-37153789197 / 1000000000000)))) (orderedInterval (2903344586 / 1000000000000) (2903344860 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1308267069506709 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39828572048 / 1000000000000) (39828572049 / 1000000000000), orderedInterval (18916347475 / 1000000000000) (18916347477 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1155893631668889 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31365163862 / 1000000000000) (31365163863 / 1000000000000), orderedInterval (34863721841 / 1000000000000) (34863721842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (335023027576011 / 800000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38483602819 / 1000000000000) (-38483600637 / 1000000000000), orderedInterval (6306369184 / 1000000000000) (6306371367 / 1000000000000)))) (orderedInterval (-1931466726 / 1000000000000) (-1931466591 / 1000000000000))) = true
  rfl'

theorem compactCertificate355_chunkChecks1_2 :
    compactCertificate355.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (926691325571217 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1057060983 / 1000000000000) (-1057060980 / 1000000000000), orderedInterval (52412346328 / 1000000000000) (52412346332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (785566499512137 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38556238510 / 1000000000000) (38556271601 / 1000000000000), orderedInterval (-41990886515 / 1000000000000) (-41990853424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (491571040372611 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65842176865 / 1000000000000) (-65842176864 / 1000000000000), orderedInterval (-28802136974 / 1000000000000) (-28802136973 / 1000000000000)))) (orderedInterval (-7019727624 / 1000000000000) (-7019725946 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (264368540403837 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77011800692 / 1000000000000) (-77011800691 / 1000000000000), orderedInterval (-60256772469 / 1000000000000) (-60256772468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (717812014202511 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54769321445 / 1000000000000) (-54769321444 / 1000000000000), orderedInterval (-23254001803 / 1000000000000) (-23254001802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (980110937756847 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35424670515 / 1000000000000) (35424670516 / 1000000000000), orderedInterval (36578045263 / 1000000000000) (36578045264 / 1000000000000)))) (orderedInterval (-2289963238 / 1000000000000) (-2289963213 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (414428959627389 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-51620615382 / 1000000000000) (-51620615381 / 1000000000000), orderedInterval (-58741317468 / 1000000000000) (-58741317467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1684630712477469 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32056926477 / 1000000000000) (32056926478 / 1000000000000), orderedInterval (21960758280 / 1000000000000) (21960758281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1125255243301971 / 4000000000000) 1 (IntervalRat.scale (453 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28583550836 / 1000000000000) (-28583542368 / 1000000000000), orderedInterval (38077176517 / 1000000000000) (38077184984 / 1000000000000)))) (orderedInterval (-12359189051 / 1000000000000) (-12359186989 / 1000000000000))) = true
  rfl'

theorem compactCertificate355_chunkChecks1 :
    compactCertificate355.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate355.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate355_chunkChecks1_0
    compactCertificate355_chunkChecks1_1 compactCertificate355_chunkChecks1_2

theorem compactCertificate355_chunkChecks2_0 :
    compactCertificate355.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (453 / 2) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (47009542929 / 1000000000000) (47009542930 / 1000000000000), orderedInterval (24407087022 / 1000000000000) (24407087023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (667355499399153 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-55576961288 / 1000000000000) (-55576961287 / 1000000000000), orderedInterval (-26795763741 / 1000000000000) (-26795763740 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (215809056821649 / 800000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17534698094 / 1000000000000) (17534698095 / 1000000000000), orderedInterval (45271743938 / 1000000000000) (45271743939 / 1000000000000)))) (orderedInterval (-19867376388 / 1000000000000) (-19867376367 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (194732670316371 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-81989150571 / 1000000000000) (-81989049204 / 1000000000000), orderedInterval (80557430551 / 1000000000000) (80557531919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (523079343885687 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26695266574 / 1000000000000) (-26695265323 / 1000000000000), orderedInterval (64566276625 / 1000000000000) (64566277875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1420262172073179 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-31829056309 / 1000000000000) (-31829056308 / 1000000000000), orderedInterval (-27881421651 / 1000000000000) (-27881421650 / 1000000000000)))) (orderedInterval (-5295555064 / 1000000000000) (-5295554953 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1046158687771827 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-49336725071 / 1000000000000) (-49336724962 / 1000000000000), orderedInterval (173534447 / 1000000000000) (173534556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1792610742700671 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (11495690395 / 1000000000000) (11495690446 / 1000000000000), orderedInterval (-35907002826 / 1000000000000) (-35907002774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1320428959627389 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-37535423485 / 1000000000000) (-37535423484 / 1000000000000), orderedInterval (-22738213714 / 1000000000000) (-22738213713 / 1000000000000)))) (orderedInterval (3308850018 / 1000000000000) (3308850064 / 1000000000000))) = true
  rfl'

theorem compactCertificate355_chunkChecks2_1 :
    compactCertificate355.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2025877587614547 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-35229067637 / 1000000000000) (-35229067512 / 1000000000000), orderedInterval (-3951195784 / 1000000000000) (-3951195659 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1169640970554363 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39931539211 / 1000000000000) (-39931539210 / 1000000000000), orderedInterval (-24069173184 / 1000000000000) (-24069173183 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2075548427486967 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33837870769 / 1000000000000) (-33837870754 / 1000000000000), orderedInterval (-9016845529 / 1000000000000) (-9016845513 / 1000000000000)))) (orderedInterval (-1106596337 / 1000000000000) (-1106595816 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1939246574019123 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (35357995787 / 1000000000000) (35358001731 / 1000000000000), orderedInterval (-7969900695 / 1000000000000) (-7969894751 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1383937859876259 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39891174211 / 1000000000000) (39891174212 / 1000000000000), orderedInterval (15713114524 / 1000000000000) (15713114525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1569238031657061 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15520161627 / 1000000000000) (-15520161626 / 1000000000000), orderedInterval (-37153789198 / 1000000000000) (-37153789197 / 1000000000000)))) (orderedInterval (-6125815942 / 1000000000000) (-6125815376 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1308267069506709 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39828572048 / 1000000000000) (39828572049 / 1000000000000), orderedInterval (18916347475 / 1000000000000) (18916347477 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1155893631668889 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31365163862 / 1000000000000) (31365163863 / 1000000000000), orderedInterval (34863721841 / 1000000000000) (34863721842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (335023027576011 / 800000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38483602819 / 1000000000000) (-38483600637 / 1000000000000), orderedInterval (6306369184 / 1000000000000) (6306371367 / 1000000000000)))) (orderedInterval (5339481134 / 1000000000000) (5339481373 / 1000000000000))) = true
  rfl'

theorem compactCertificate355_chunkChecks2_2 :
    compactCertificate355.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (926691325571217 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1057060983 / 1000000000000) (-1057060980 / 1000000000000), orderedInterval (52412346328 / 1000000000000) (52412346332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (785566499512137 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38556238510 / 1000000000000) (38556271601 / 1000000000000), orderedInterval (-41990886515 / 1000000000000) (-41990853424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (491571040372611 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65842176865 / 1000000000000) (-65842176864 / 1000000000000), orderedInterval (-28802136974 / 1000000000000) (-28802136973 / 1000000000000)))) (orderedInterval (2125852143 / 1000000000000) (2125853610 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (264368540403837 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77011800692 / 1000000000000) (-77011800691 / 1000000000000), orderedInterval (-60256772469 / 1000000000000) (-60256772468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (717812014202511 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54769321445 / 1000000000000) (-54769321444 / 1000000000000), orderedInterval (-23254001803 / 1000000000000) (-23254001802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (980110937756847 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35424670515 / 1000000000000) (35424670516 / 1000000000000), orderedInterval (36578045263 / 1000000000000) (36578045264 / 1000000000000)))) (orderedInterval (2286294522 / 1000000000000) (2286294547 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (414428959627389 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-51620615382 / 1000000000000) (-51620615381 / 1000000000000), orderedInterval (-58741317468 / 1000000000000) (-58741317467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1684630712477469 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32056926477 / 1000000000000) (32056926478 / 1000000000000), orderedInterval (21960758280 / 1000000000000) (21960758281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1125255243301971 / 4000000000000) 2 (IntervalRat.scale (453 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28583550836 / 1000000000000) (-28583542368 / 1000000000000), orderedInterval (38077176517 / 1000000000000) (38077184984 / 1000000000000)))) (orderedInterval (868934107 / 1000000000000) (868936697 / 1000000000000))) = true
  rfl'

theorem compactCertificate355_chunkChecks2 :
    compactCertificate355.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate355.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate355_chunkChecks2_0
    compactCertificate355_chunkChecks2_1 compactCertificate355_chunkChecks2_2

theorem compactCertificate355_chunkChecks3_0 :
    compactCertificate355.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (453 / 2) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (47009542929 / 1000000000000) (47009542930 / 1000000000000), orderedInterval (24407087022 / 1000000000000) (24407087023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (667355499399153 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-55576961288 / 1000000000000) (-55576961287 / 1000000000000), orderedInterval (-26795763741 / 1000000000000) (-26795763740 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (215809056821649 / 800000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17534698094 / 1000000000000) (17534698095 / 1000000000000), orderedInterval (45271743938 / 1000000000000) (45271743939 / 1000000000000)))) (orderedInterval (-13974441275 / 1000000000000) (-13974441250 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (194732670316371 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-81989150571 / 1000000000000) (-81989049204 / 1000000000000), orderedInterval (80557430551 / 1000000000000) (80557531919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (523079343885687 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26695266574 / 1000000000000) (-26695265323 / 1000000000000), orderedInterval (64566276625 / 1000000000000) (64566277875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1420262172073179 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-31829056309 / 1000000000000) (-31829056308 / 1000000000000), orderedInterval (-27881421651 / 1000000000000) (-27881421650 / 1000000000000)))) (orderedInterval (-8057128422 / 1000000000000) (-8057128337 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1046158687771827 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-49336725071 / 1000000000000) (-49336724962 / 1000000000000), orderedInterval (173534447 / 1000000000000) (173534556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1792610742700671 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (11495690395 / 1000000000000) (11495690446 / 1000000000000), orderedInterval (-35907002826 / 1000000000000) (-35907002774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1320428959627389 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-37535423485 / 1000000000000) (-37535423484 / 1000000000000), orderedInterval (-22738213714 / 1000000000000) (-22738213713 / 1000000000000)))) (orderedInterval (-6892106040 / 1000000000000) (-6892105955 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate355_chunkChecks3_1 :
    compactCertificate355.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2025877587614547 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-35229067637 / 1000000000000) (-35229067512 / 1000000000000), orderedInterval (-3951195784 / 1000000000000) (-3951195659 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1169640970554363 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39931539211 / 1000000000000) (-39931539210 / 1000000000000), orderedInterval (-24069173184 / 1000000000000) (-24069173183 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2075548427486967 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33837870769 / 1000000000000) (-33837870754 / 1000000000000), orderedInterval (-9016845529 / 1000000000000) (-9016845513 / 1000000000000)))) (orderedInterval (11403528832 / 1000000000000) (11403529983 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1939246574019123 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (35357995787 / 1000000000000) (35358001731 / 1000000000000), orderedInterval (-7969900695 / 1000000000000) (-7969894751 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1383937859876259 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39891174211 / 1000000000000) (39891174212 / 1000000000000), orderedInterval (15713114524 / 1000000000000) (15713114525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1569238031657061 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15520161627 / 1000000000000) (-15520161626 / 1000000000000), orderedInterval (-37153789198 / 1000000000000) (-37153789197 / 1000000000000)))) (orderedInterval (-7656851086 / 1000000000000) (-7656849907 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1308267069506709 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39828572048 / 1000000000000) (39828572049 / 1000000000000), orderedInterval (18916347475 / 1000000000000) (18916347477 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1155893631668889 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31365163862 / 1000000000000) (31365163863 / 1000000000000), orderedInterval (34863721841 / 1000000000000) (34863721842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (335023027576011 / 800000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38483602819 / 1000000000000) (-38483600637 / 1000000000000), orderedInterval (6306369184 / 1000000000000) (6306371367 / 1000000000000)))) (orderedInterval (2441373349 / 1000000000000) (2441373776 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate355_chunkChecks3_2 :
    compactCertificate355.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (926691325571217 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1057060983 / 1000000000000) (-1057060980 / 1000000000000), orderedInterval (52412346328 / 1000000000000) (52412346332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (785566499512137 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38556238510 / 1000000000000) (38556271601 / 1000000000000), orderedInterval (-41990886515 / 1000000000000) (-41990853424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (491571040372611 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65842176865 / 1000000000000) (-65842176864 / 1000000000000), orderedInterval (-28802136974 / 1000000000000) (-28802136973 / 1000000000000)))) (orderedInterval (7558670407 / 1000000000000) (7558671684 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (264368540403837 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77011800692 / 1000000000000) (-77011800691 / 1000000000000), orderedInterval (-60256772469 / 1000000000000) (-60256772468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (717812014202511 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54769321445 / 1000000000000) (-54769321444 / 1000000000000), orderedInterval (-23254001803 / 1000000000000) (-23254001802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (980110937756847 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35424670515 / 1000000000000) (35424670516 / 1000000000000), orderedInterval (36578045263 / 1000000000000) (36578045264 / 1000000000000)))) (orderedInterval (3248882294 / 1000000000000) (3248882320 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (414428959627389 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-51620615382 / 1000000000000) (-51620615381 / 1000000000000), orderedInterval (-58741317468 / 1000000000000) (-58741317467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1684630712477469 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32056926477 / 1000000000000) (32056926478 / 1000000000000), orderedInterval (21960758280 / 1000000000000) (21960758281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1125255243301971 / 4000000000000) 3 (IntervalRat.scale (453 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28583550836 / 1000000000000) (-28583542368 / 1000000000000), orderedInterval (38077176517 / 1000000000000) (38077184984 / 1000000000000)))) (orderedInterval (25209822974 / 1000000000000) (25209826230 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate355_chunkChecks3 :
    compactCertificate355.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate355.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate355_chunkChecks3_0
    compactCertificate355_chunkChecks3_1 compactCertificate355_chunkChecks3_2

theorem compactCertificate355_chunkChecks4_0 :
    compactCertificate355.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (453 / 2) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (47009542929 / 1000000000000) (47009542930 / 1000000000000), orderedInterval (24407087022 / 1000000000000) (24407087023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (667355499399153 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-55576961288 / 1000000000000) (-55576961287 / 1000000000000), orderedInterval (-26795763741 / 1000000000000) (-26795763740 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (215809056821649 / 800000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17534698094 / 1000000000000) (17534698095 / 1000000000000), orderedInterval (45271743938 / 1000000000000) (45271743939 / 1000000000000)))) (orderedInterval (20673835267 / 1000000000000) (20673835296 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (194732670316371 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-81989150571 / 1000000000000) (-81989049204 / 1000000000000), orderedInterval (80557430551 / 1000000000000) (80557531919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (523079343885687 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-26695266574 / 1000000000000) (-26695265323 / 1000000000000), orderedInterval (64566276625 / 1000000000000) (64566277875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1420262172073179 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-31829056309 / 1000000000000) (-31829056308 / 1000000000000), orderedInterval (-27881421651 / 1000000000000) (-27881421650 / 1000000000000)))) (orderedInterval (13629065821 / 1000000000000) (13629065928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1046158687771827 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-49336725071 / 1000000000000) (-49336724962 / 1000000000000), orderedInterval (173534447 / 1000000000000) (173534556 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1792610742700671 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (11495690395 / 1000000000000) (11495690446 / 1000000000000), orderedInterval (-35907002826 / 1000000000000) (-35907002774 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1320428959627389 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-37535423485 / 1000000000000) (-37535423484 / 1000000000000), orderedInterval (-22738213714 / 1000000000000) (-22738213713 / 1000000000000)))) (orderedInterval (-9466183273 / 1000000000000) (-9466183116 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate355_chunkChecks4_1 :
    compactCertificate355.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2025877587614547 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-35229067637 / 1000000000000) (-35229067512 / 1000000000000), orderedInterval (-3951195784 / 1000000000000) (-3951195659 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1169640970554363 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-39931539211 / 1000000000000) (-39931539210 / 1000000000000), orderedInterval (-24069173184 / 1000000000000) (-24069173183 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2075548427486967 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33837870769 / 1000000000000) (-33837870754 / 1000000000000), orderedInterval (-9016845529 / 1000000000000) (-9016845513 / 1000000000000)))) (orderedInterval (15684390572 / 1000000000000) (15684393130 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1939246574019123 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (35357995787 / 1000000000000) (35358001731 / 1000000000000), orderedInterval (-7969900695 / 1000000000000) (-7969894751 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1383937859876259 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39891174211 / 1000000000000) (39891174212 / 1000000000000), orderedInterval (15713114524 / 1000000000000) (15713114525 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1569238031657061 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-15520161627 / 1000000000000) (-15520161626 / 1000000000000), orderedInterval (-37153789198 / 1000000000000) (-37153789197 / 1000000000000)))) (orderedInterval (7913450013 / 1000000000000) (7913452489 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1308267069506709 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39828572048 / 1000000000000) (39828572049 / 1000000000000), orderedInterval (18916347475 / 1000000000000) (18916347477 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1155893631668889 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31365163862 / 1000000000000) (31365163863 / 1000000000000), orderedInterval (34863721841 / 1000000000000) (34863721842 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (335023027576011 / 800000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38483602819 / 1000000000000) (-38483600637 / 1000000000000), orderedInterval (6306369184 / 1000000000000) (6306371367 / 1000000000000)))) (orderedInterval (-14291952739 / 1000000000000) (-14291951969 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate355_chunkChecks4_2 :
    compactCertificate355.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (926691325571217 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-1057060983 / 1000000000000) (-1057060980 / 1000000000000), orderedInterval (52412346328 / 1000000000000) (52412346332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (785566499512137 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38556238510 / 1000000000000) (38556271601 / 1000000000000), orderedInterval (-41990886515 / 1000000000000) (-41990853424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (491571040372611 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65842176865 / 1000000000000) (-65842176864 / 1000000000000), orderedInterval (-28802136974 / 1000000000000) (-28802136973 / 1000000000000)))) (orderedInterval (-1300944956 / 1000000000000) (-1300943837 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (264368540403837 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77011800692 / 1000000000000) (-77011800691 / 1000000000000), orderedInterval (-60256772469 / 1000000000000) (-60256772468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (717812014202511 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54769321445 / 1000000000000) (-54769321444 / 1000000000000), orderedInterval (-23254001803 / 1000000000000) (-23254001802 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (980110937756847 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35424670515 / 1000000000000) (35424670516 / 1000000000000), orderedInterval (36578045263 / 1000000000000) (36578045264 / 1000000000000)))) (orderedInterval (-3247021298 / 1000000000000) (-3247021271 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (414428959627389 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-51620615382 / 1000000000000) (-51620615381 / 1000000000000), orderedInterval (-58741317468 / 1000000000000) (-58741317467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1684630712477469 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32056926477 / 1000000000000) (32056926478 / 1000000000000), orderedInterval (21960758280 / 1000000000000) (21960758281 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1125255243301971 / 4000000000000) 4 (IntervalRat.scale (453 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28583550836 / 1000000000000) (-28583542368 / 1000000000000), orderedInterval (38077176517 / 1000000000000) (38077184984 / 1000000000000)))) (orderedInterval (-18668047532 / 1000000000000) (-18668043401 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate355_chunkChecks4 :
    compactCertificate355.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate355.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate355_chunkChecks4_0
    compactCertificate355_chunkChecks4_1 compactCertificate355_chunkChecks4_2

theorem compactCertificate355_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate355.chunkCheck r b = true :=
  compactCertificate355.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate355_chunkChecks0
    · exact compactCertificate355_chunkChecks1
    · exact compactCertificate355_chunkChecks2
    · exact compactCertificate355_chunkChecks3
    · exact compactCertificate355_chunkChecks4)

theorem compactCertificate355_coefficient0 :
    compactCertificate355.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate355_coefficient1 :
    compactCertificate355.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate355_coefficient2 :
    compactCertificate355.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate355_coefficient3 :
    compactCertificate355.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate355_coefficient4 :
    compactCertificate355.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate355_coefficients : ∀ r : Fin 5,
    compactCertificate355.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate355_coefficient0
  · exact compactCertificate355_coefficient1
  · exact compactCertificate355_coefficient2
  · exact compactCertificate355_coefficient3
  · exact compactCertificate355_coefficient4

theorem compactCertificate355_lower : (1 : ℚ) ≤ compactCertificate355.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate355, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate355_proves {t : ℝ} (ht : t ∈ compactCertificate355.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate355.proves compactCertificate355_states compactCertificate355_chunks
    compactCertificate355_coefficients compactCertificate355_lower ht

end Erdos232
