/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate436 : CompactCertificate where
  left := 307
  right := 308
  center := 615 / 2
  grid := fun i =>
    match i.val with
    | 0 => 98
    | 1 => 72
    | 2 => 117
    | 3 => 21
    | 4 => 57
    | 5 => 154
    | 6 => 113
    | 7 => 194
    | 8 => 143
    | 9 => 219
    | 10 => 126
    | 11 => 224
    | 12 => 210
    | 13 => 150
    | 14 => 170
    | 15 => 141
    | 16 => 125
    | 17 => 181
    | 18 => 100
    | 19 => 85
    | 20 => 53
    | 21 => 29
    | 22 => 78
    | 23 => 106
    | 24 => 45
    | 25 => 182
    | _ => 122
  point := fun i =>
    match i.val with
    | 0 => 615 / 2
    | 1 => 181202486591823 / 800000000000
    | 2 => 58597161123759 / 160000000000
    | 3 => 52874433662061 / 800000000000
    | 4 => 142028166220617 / 800000000000
    | 5 => 385634099701989 / 800000000000
    | 6 => 284056332441357 / 800000000000
    | 7 => 486735367223361 / 800000000000
    | 8 => 358527068508099 / 800000000000
    | 9 => 550072722464877 / 800000000000
    | 10 => 317584634388933 / 800000000000
    | 11 => 563559506801097 / 800000000000
    | 12 => 526550394270093 / 800000000000
    | 13 => 375771206986269 / 800000000000
    | 14 => 426084498661851 / 800000000000
    | 15 => 355224833442219 / 800000000000
    | 16 => 313851913234599 / 800000000000
    | 17 => 90966517421301 / 160000000000
    | 18 => 251618174492847 / 800000000000
    | 19 => 213299513112567 / 800000000000
    | 20 => 133472931491901 / 800000000000
    | 21 => 71782186467267 / 800000000000
    | 22 => 194902599882801 / 800000000000
    | 23 => 266122837404177 / 800000000000
    | 24 => 112527068508099 / 800000000000
    | 25 => 457416286169379 / 800000000000
    | _ => 305532880631661 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (18091538605 / 1000000000000) (18091538606 / 1000000000000), orderedInterval (41719909944 / 1000000000000) (41719909945 / 1000000000000))
    | 1 => (orderedInterval (47085178283 / 1000000000000) (47085178284 / 1000000000000), orderedInterval (24260518498 / 1000000000000) (24260518499 / 1000000000000))
    | 2 => (orderedInterval (21757709001 / 1000000000000) (21757710928 / 1000000000000), orderedInterval (-35595110048 / 1000000000000) (-35595108121 / 1000000000000))
    | 3 => (orderedInterval (-77066420119 / 1000000000000) (-77066420118 / 1000000000000), orderedInterval (-60186073385 / 1000000000000) (-60186073384 / 1000000000000))
    | 4 => (orderedInterval (40856448580 / 1000000000000) (40856486971 / 1000000000000), orderedInterval (-43894404364 / 1000000000000) (-43894365973 / 1000000000000))
    | 5 => (orderedInterval (-30130568310 / 1000000000000) (-30130495705 / 1000000000000), orderedInterval (20349233255 / 1000000000000) (20349305860 / 1000000000000))
    | 6 => (orderedInterval (-31964530164 / 1000000000000) (-31964530163 / 1000000000000), orderedInterval (-27725621609 / 1000000000000) (-27725621608 / 1000000000000))
    | 7 => (orderedInterval (-8458738049 / 1000000000000) (-8458738042 / 1000000000000), orderedInterval (31228748319 / 1000000000000) (31228748327 / 1000000000000))
    | 8 => (orderedInterval (11274649282 / 1000000000000) (11274649329 / 1000000000000), orderedInterval (-35976528157 / 1000000000000) (-35976528110 / 1000000000000))
    | 9 => (orderedInterval (-10927441150 / 1000000000000) (-10927441149 / 1000000000000), orderedInterval (-28390314102 / 1000000000000) (-28390314101 / 1000000000000))
    | 10 => (orderedInterval (37556905031 / 1000000000000) (37556919568 / 1000000000000), orderedInterval (-13944475171 / 1000000000000) (-13944460634 / 1000000000000))
    | 11 => (orderedInterval (30019681639 / 1000000000000) (30019682617 / 1000000000000), orderedInterval (1569617027 / 1000000000000) (1569618006 / 1000000000000))
    | 12 => (orderedInterval (-21453987797 / 1000000000000) (-21453983885 / 1000000000000), orderedInterval (22532010606 / 1000000000000) (22532014518 / 1000000000000))
    | 13 => (orderedInterval (-24817220816 / 1000000000000) (-24817212365 / 1000000000000), orderedInterval (27219071765 / 1000000000000) (27219080216 / 1000000000000))
    | 14 => (orderedInterval (-21738304730 / 1000000000000) (-21738301496 / 1000000000000), orderedInterval (26904216662 / 1000000000000) (26904219896 / 1000000000000))
    | 15 => (orderedInterval (-36381612734 / 1000000000000) (-36381603841 / 1000000000000), orderedInterval (10534097616 / 1000000000000) (10534106509 / 1000000000000))
    | 16 => (orderedInterval (-15719956593 / 1000000000000) (-15719956592 / 1000000000000), orderedInterval (-37069187115 / 1000000000000) (-37069187114 / 1000000000000))
    | 17 => (orderedInterval (-21496761634 / 1000000000000) (-21496761633 / 1000000000000), orderedInterval (-25625446654 / 1000000000000) (-25625446653 / 1000000000000))
    | 18 => (orderedInterval (41036569733 / 1000000000000) (41036569734 / 1000000000000), orderedInterval (18376028682 / 1000000000000) (18376028683 / 1000000000000))
    | 19 => (orderedInterval (-17849599757 / 1000000000000) (-17849599756 / 1000000000000), orderedInterval (-45453860663 / 1000000000000) (-45453860662 / 1000000000000))
    | 20 => (orderedInterval (-55638164456 / 1000000000000) (-55638164455 / 1000000000000), orderedInterval (-26668082494 / 1000000000000) (-26668082492 / 1000000000000))
    | 21 => (orderedInterval (47173894212 / 1000000000000) (47173907593 / 1000000000000), orderedInterval (-70045969345 / 1000000000000) (-70045955964 / 1000000000000))
    | 22 => (orderedInterval (-30161128195 / 1000000000000) (-30161119239 / 1000000000000), orderedInterval (41334003065 / 1000000000000) (41334012021 / 1000000000000))
    | 23 => (orderedInterval (18226630227 / 1000000000000) (18226630228 / 1000000000000), orderedInterval (39741354898 / 1000000000000) (39741354899 / 1000000000000))
    | 24 => (orderedInterval (-4817873755 / 1000000000000) (-4817873753 / 1000000000000), orderedInterval (-67085790124 / 1000000000000) (-67085790122 / 1000000000000))
    | 25 => (orderedInterval (23601198367 / 1000000000000) (23601198368 / 1000000000000), orderedInterval (23567537850 / 1000000000000) (23567537851 / 1000000000000))
    | _ => (orderedInterval (-22139536694 / 1000000000000) (-22139534383 / 1000000000000), orderedInterval (34332796280 / 1000000000000) (34332798591 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (8886362246 / 1000000000000) (8886362381 / 1000000000000)
      | 1 => orderedInterval (4469822395 / 1000000000000) (4469828996 / 1000000000000)
      | 2 => orderedInterval (533387344 / 1000000000000) (533387363 / 1000000000000)
      | 3 => orderedInterval (8991806521 / 1000000000000) (8991807860 / 1000000000000)
      | 4 => orderedInterval (-1849468602 / 1000000000000) (-1849467679 / 1000000000000)
      | 5 => orderedInterval (-70924005 / 1000000000000) (-70923872 / 1000000000000)
      | 6 => orderedInterval (-7362466346 / 1000000000000) (-7362466268 / 1000000000000)
      | 7 => orderedInterval (-1583678936 / 1000000000000) (-1583678449 / 1000000000000)
      | _ => orderedInterval (2203740693 / 1000000000000) (2203741212 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (14215113828 / 1000000000000) (14215113987 / 1000000000000)
      | 1 => orderedInterval (-3052703983 / 1000000000000) (-3052695040 / 1000000000000)
      | 2 => orderedInterval (-3173031500 / 1000000000000) (-3173031467 / 1000000000000)
      | 3 => orderedInterval (10457453900 / 1000000000000) (10457455862 / 1000000000000)
      | 4 => orderedInterval (2825222030 / 1000000000000) (2825223490 / 1000000000000)
      | 5 => orderedInterval (1669017375 / 1000000000000) (1669017566 / 1000000000000)
      | 6 => orderedInterval (-1245642975 / 1000000000000) (-1245642903 / 1000000000000)
      | 7 => orderedInterval (-3660419495 / 1000000000000) (-3660419228 / 1000000000000)
      | _ => orderedInterval (-11752835963 / 1000000000000) (-11752835304 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-9266198122 / 1000000000000) (-9266197933 / 1000000000000)
      | 1 => orderedInterval (-5789684805 / 1000000000000) (-5789671566 / 1000000000000)
      | 2 => orderedInterval (-1589857755 / 1000000000000) (-1589857698 / 1000000000000)
      | 3 => orderedInterval (-36776652403 / 1000000000000) (-36776649330 / 1000000000000)
      | 4 => orderedInterval (3362150900 / 1000000000000) (3362153241 / 1000000000000)
      | 5 => orderedInterval (1287830087 / 1000000000000) (1287830366 / 1000000000000)
      | 6 => orderedInterval (6642290844 / 1000000000000) (6642290912 / 1000000000000)
      | 7 => orderedInterval (1291291465 / 1000000000000) (1291291648 / 1000000000000)
      | _ => orderedInterval (278842798 / 1000000000000) (278843646 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-13067604906 / 1000000000000) (-13067604681 / 1000000000000)
      | 1 => orderedInterval (5893568262 / 1000000000000) (5893588546 / 1000000000000)
      | 2 => orderedInterval (10157829598 / 1000000000000) (10157829701 / 1000000000000)
      | 3 => orderedInterval (-56740490160 / 1000000000000) (-56740484973 / 1000000000000)
      | 4 => orderedInterval (-4488437260 / 1000000000000) (-4488433459 / 1000000000000)
      | 5 => orderedInterval (-628847935 / 1000000000000) (-628847526 / 1000000000000)
      | 6 => orderedInterval (1584116152 / 1000000000000) (1584116219 / 1000000000000)
      | 7 => orderedInterval (4285958775 / 1000000000000) (4285958917 / 1000000000000)
      | _ => orderedInterval (24712543291 / 1000000000000) (24712544397 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (9953867509 / 1000000000000) (9953867776 / 1000000000000)
      | 1 => orderedInterval (13064361925 / 1000000000000) (13064393516 / 1000000000000)
      | 2 => orderedInterval (5161906991 / 1000000000000) (5161907179 / 1000000000000)
      | 3 => orderedInterval (174181186583 / 1000000000000) (174181196069 / 1000000000000)
      | 4 => orderedInterval (-3627871954 / 1000000000000) (-3627865660 / 1000000000000)
      | 5 => orderedInterval (-5871054232 / 1000000000000) (-5871053628 / 1000000000000)
      | 6 => orderedInterval (-6777859207 / 1000000000000) (-6777859141 / 1000000000000)
      | 7 => orderedInterval (-1677683805 / 1000000000000) (-1677683686 / 1000000000000)
      | _ => orderedInterval (-13242913499 / 1000000000000) (-13242912024 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (14218581310 / 1000000000000) (14218591544 / 1000000000000)
    | 1 => orderedInterval (6282173217 / 1000000000000) (6282186963 / 1000000000000)
    | 2 => orderedInterval (-40559986991 / 1000000000000) (-40559966714 / 1000000000000)
    | 3 => orderedInterval (-28291364183 / 1000000000000) (-28291332859 / 1000000000000)
    | _ => orderedInterval (171163940311 / 1000000000000) (171163990401 / 1000000000000)

theorem compactCertificate436_stateChecks0 :
    compactCertificate436.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (615 / 2)) (orderedInterval (18091538605 / 1000000000000) (18091538606 / 1000000000000), orderedInterval (41719909944 / 1000000000000) (41719909945 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (181202486591823 / 800000000000)) (orderedInterval (47085178283 / 1000000000000) (47085178284 / 1000000000000), orderedInterval (24260518498 / 1000000000000) (24260518499 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (58597161123759 / 160000000000)) (orderedInterval (21757709001 / 1000000000000) (21757710928 / 1000000000000), orderedInterval (-35595110048 / 1000000000000) (-35595108121 / 1000000000000))) = true
  rfl'

theorem compactCertificate436_stateChecks1 :
    compactCertificate436.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (52874433662061 / 800000000000)) (orderedInterval (-77066420119 / 1000000000000) (-77066420118 / 1000000000000), orderedInterval (-60186073385 / 1000000000000) (-60186073384 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (142028166220617 / 800000000000)) (orderedInterval (40856448580 / 1000000000000) (40856486971 / 1000000000000), orderedInterval (-43894404364 / 1000000000000) (-43894365973 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (385634099701989 / 800000000000)) (orderedInterval (-30130568310 / 1000000000000) (-30130495705 / 1000000000000), orderedInterval (20349233255 / 1000000000000) (20349305860 / 1000000000000))) = true
  rfl'

theorem compactCertificate436_stateChecks2 :
    compactCertificate436.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (284056332441357 / 800000000000)) (orderedInterval (-31964530164 / 1000000000000) (-31964530163 / 1000000000000), orderedInterval (-27725621609 / 1000000000000) (-27725621608 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (486735367223361 / 800000000000)) (orderedInterval (-8458738049 / 1000000000000) (-8458738042 / 1000000000000), orderedInterval (31228748319 / 1000000000000) (31228748327 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (358527068508099 / 800000000000)) (orderedInterval (11274649282 / 1000000000000) (11274649329 / 1000000000000), orderedInterval (-35976528157 / 1000000000000) (-35976528110 / 1000000000000))) = true
  rfl'

theorem compactCertificate436_stateChecks3 :
    compactCertificate436.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 219 12 (550072722464877 / 800000000000)) (orderedInterval (-10927441150 / 1000000000000) (-10927441149 / 1000000000000), orderedInterval (-28390314102 / 1000000000000) (-28390314101 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (317584634388933 / 800000000000)) (orderedInterval (37556905031 / 1000000000000) (37556919568 / 1000000000000), orderedInterval (-13944475171 / 1000000000000) (-13944460634 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 224 12 (563559506801097 / 800000000000)) (orderedInterval (30019681639 / 1000000000000) (30019682617 / 1000000000000), orderedInterval (1569617027 / 1000000000000) (1569618006 / 1000000000000))) = true
  rfl'

theorem compactCertificate436_stateChecks4 :
    compactCertificate436.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (526550394270093 / 800000000000)) (orderedInterval (-21453987797 / 1000000000000) (-21453983885 / 1000000000000), orderedInterval (22532010606 / 1000000000000) (22532014518 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (375771206986269 / 800000000000)) (orderedInterval (-24817220816 / 1000000000000) (-24817212365 / 1000000000000), orderedInterval (27219071765 / 1000000000000) (27219080216 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (426084498661851 / 800000000000)) (orderedInterval (-21738304730 / 1000000000000) (-21738301496 / 1000000000000), orderedInterval (26904216662 / 1000000000000) (26904219896 / 1000000000000))) = true
  rfl'

theorem compactCertificate436_stateChecks5 :
    compactCertificate436.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (355224833442219 / 800000000000)) (orderedInterval (-36381612734 / 1000000000000) (-36381603841 / 1000000000000), orderedInterval (10534097616 / 1000000000000) (10534106509 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (313851913234599 / 800000000000)) (orderedInterval (-15719956593 / 1000000000000) (-15719956592 / 1000000000000), orderedInterval (-37069187115 / 1000000000000) (-37069187114 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (90966517421301 / 160000000000)) (orderedInterval (-21496761634 / 1000000000000) (-21496761633 / 1000000000000), orderedInterval (-25625446654 / 1000000000000) (-25625446653 / 1000000000000))) = true
  rfl'

theorem compactCertificate436_stateChecks6 :
    compactCertificate436.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (251618174492847 / 800000000000)) (orderedInterval (41036569733 / 1000000000000) (41036569734 / 1000000000000), orderedInterval (18376028682 / 1000000000000) (18376028683 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (213299513112567 / 800000000000)) (orderedInterval (-17849599757 / 1000000000000) (-17849599756 / 1000000000000), orderedInterval (-45453860663 / 1000000000000) (-45453860662 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (133472931491901 / 800000000000)) (orderedInterval (-55638164456 / 1000000000000) (-55638164455 / 1000000000000), orderedInterval (-26668082494 / 1000000000000) (-26668082492 / 1000000000000))) = true
  rfl'

theorem compactCertificate436_stateChecks7 :
    compactCertificate436.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (71782186467267 / 800000000000)) (orderedInterval (47173894212 / 1000000000000) (47173907593 / 1000000000000), orderedInterval (-70045969345 / 1000000000000) (-70045955964 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (194902599882801 / 800000000000)) (orderedInterval (-30161128195 / 1000000000000) (-30161119239 / 1000000000000), orderedInterval (41334003065 / 1000000000000) (41334012021 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (266122837404177 / 800000000000)) (orderedInterval (18226630227 / 1000000000000) (18226630228 / 1000000000000), orderedInterval (39741354898 / 1000000000000) (39741354899 / 1000000000000))) = true
  rfl'

theorem compactCertificate436_stateChecks8 :
    compactCertificate436.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (112527068508099 / 800000000000)) (orderedInterval (-4817873755 / 1000000000000) (-4817873753 / 1000000000000), orderedInterval (-67085790124 / 1000000000000) (-67085790122 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (457416286169379 / 800000000000)) (orderedInterval (23601198367 / 1000000000000) (23601198368 / 1000000000000), orderedInterval (23567537850 / 1000000000000) (23567537851 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (305532880631661 / 800000000000)) (orderedInterval (-22139536694 / 1000000000000) (-22139534383 / 1000000000000), orderedInterval (34332796280 / 1000000000000) (34332798591 / 1000000000000))) = true
  rfl'

theorem compactCertificate436_states : ∀ j,
    BesselStateValid (compactCertificate436.point j) (compactCertificate436.state j) :=
  compactCertificate436.statesValid_of_checks3 compactCertificate436_stateChecks0
    compactCertificate436_stateChecks1 compactCertificate436_stateChecks2
    compactCertificate436_stateChecks3 compactCertificate436_stateChecks4
    compactCertificate436_stateChecks5 compactCertificate436_stateChecks6
    compactCertificate436_stateChecks7 compactCertificate436_stateChecks8

theorem compactCertificate436_chunkChecks0_0 :
    compactCertificate436.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (615 / 2) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (18091538605 / 1000000000000) (18091538606 / 1000000000000), orderedInterval (41719909944 / 1000000000000) (41719909945 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (181202486591823 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (47085178283 / 1000000000000) (47085178284 / 1000000000000), orderedInterval (24260518498 / 1000000000000) (24260518499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (58597161123759 / 160000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21757709001 / 1000000000000) (21757710928 / 1000000000000), orderedInterval (-35595110048 / 1000000000000) (-35595108121 / 1000000000000)))) (orderedInterval (8886362246 / 1000000000000) (8886362381 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (52874433662061 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77066420119 / 1000000000000) (-77066420118 / 1000000000000), orderedInterval (-60186073385 / 1000000000000) (-60186073384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (142028166220617 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40856448580 / 1000000000000) (40856486971 / 1000000000000), orderedInterval (-43894404364 / 1000000000000) (-43894365973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (385634099701989 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30130568310 / 1000000000000) (-30130495705 / 1000000000000), orderedInterval (20349233255 / 1000000000000) (20349305860 / 1000000000000)))) (orderedInterval (4469822395 / 1000000000000) (4469828996 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (284056332441357 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31964530164 / 1000000000000) (-31964530163 / 1000000000000), orderedInterval (-27725621609 / 1000000000000) (-27725621608 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (486735367223361 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-8458738049 / 1000000000000) (-8458738042 / 1000000000000), orderedInterval (31228748319 / 1000000000000) (31228748327 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (358527068508099 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11274649282 / 1000000000000) (11274649329 / 1000000000000), orderedInterval (-35976528157 / 1000000000000) (-35976528110 / 1000000000000)))) (orderedInterval (533387344 / 1000000000000) (533387363 / 1000000000000))) = true
  rfl'

theorem compactCertificate436_chunkChecks0_1 :
    compactCertificate436.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (550072722464877 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10927441150 / 1000000000000) (-10927441149 / 1000000000000), orderedInterval (-28390314102 / 1000000000000) (-28390314101 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (317584634388933 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (37556905031 / 1000000000000) (37556919568 / 1000000000000), orderedInterval (-13944475171 / 1000000000000) (-13944460634 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (563559506801097 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30019681639 / 1000000000000) (30019682617 / 1000000000000), orderedInterval (1569617027 / 1000000000000) (1569618006 / 1000000000000)))) (orderedInterval (8991806521 / 1000000000000) (8991807860 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (526550394270093 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21453987797 / 1000000000000) (-21453983885 / 1000000000000), orderedInterval (22532010606 / 1000000000000) (22532014518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (375771206986269 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24817220816 / 1000000000000) (-24817212365 / 1000000000000), orderedInterval (27219071765 / 1000000000000) (27219080216 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (426084498661851 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21738304730 / 1000000000000) (-21738301496 / 1000000000000), orderedInterval (26904216662 / 1000000000000) (26904219896 / 1000000000000)))) (orderedInterval (-1849468602 / 1000000000000) (-1849467679 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (355224833442219 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36381612734 / 1000000000000) (-36381603841 / 1000000000000), orderedInterval (10534097616 / 1000000000000) (10534106509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (313851913234599 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-15719956593 / 1000000000000) (-15719956592 / 1000000000000), orderedInterval (-37069187115 / 1000000000000) (-37069187114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (90966517421301 / 160000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21496761634 / 1000000000000) (-21496761633 / 1000000000000), orderedInterval (-25625446654 / 1000000000000) (-25625446653 / 1000000000000)))) (orderedInterval (-70924005 / 1000000000000) (-70923872 / 1000000000000))) = true
  rfl'

theorem compactCertificate436_chunkChecks0_2 :
    compactCertificate436.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (251618174492847 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (41036569733 / 1000000000000) (41036569734 / 1000000000000), orderedInterval (18376028682 / 1000000000000) (18376028683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (213299513112567 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17849599757 / 1000000000000) (-17849599756 / 1000000000000), orderedInterval (-45453860663 / 1000000000000) (-45453860662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (133472931491901 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-55638164456 / 1000000000000) (-55638164455 / 1000000000000), orderedInterval (-26668082494 / 1000000000000) (-26668082492 / 1000000000000)))) (orderedInterval (-7362466346 / 1000000000000) (-7362466268 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (71782186467267 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (47173894212 / 1000000000000) (47173907593 / 1000000000000), orderedInterval (-70045969345 / 1000000000000) (-70045955964 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (194902599882801 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-30161128195 / 1000000000000) (-30161119239 / 1000000000000), orderedInterval (41334003065 / 1000000000000) (41334012021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (266122837404177 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18226630227 / 1000000000000) (18226630228 / 1000000000000), orderedInterval (39741354898 / 1000000000000) (39741354899 / 1000000000000)))) (orderedInterval (-1583678936 / 1000000000000) (-1583678449 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (112527068508099 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-4817873755 / 1000000000000) (-4817873753 / 1000000000000), orderedInterval (-67085790124 / 1000000000000) (-67085790122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (457416286169379 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23601198367 / 1000000000000) (23601198368 / 1000000000000), orderedInterval (23567537850 / 1000000000000) (23567537851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (305532880631661 / 800000000000) 0 (IntervalRat.scale (615 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22139536694 / 1000000000000) (-22139534383 / 1000000000000), orderedInterval (34332796280 / 1000000000000) (34332798591 / 1000000000000)))) (orderedInterval (2203740693 / 1000000000000) (2203741212 / 1000000000000))) = true
  rfl'

theorem compactCertificate436_chunkChecks0 :
    compactCertificate436.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate436.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate436_chunkChecks0_0
    compactCertificate436_chunkChecks0_1 compactCertificate436_chunkChecks0_2

theorem compactCertificate436_chunkChecks1_0 :
    compactCertificate436.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (615 / 2) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (18091538605 / 1000000000000) (18091538606 / 1000000000000), orderedInterval (41719909944 / 1000000000000) (41719909945 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (181202486591823 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (47085178283 / 1000000000000) (47085178284 / 1000000000000), orderedInterval (24260518498 / 1000000000000) (24260518499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (58597161123759 / 160000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21757709001 / 1000000000000) (21757710928 / 1000000000000), orderedInterval (-35595110048 / 1000000000000) (-35595108121 / 1000000000000)))) (orderedInterval (14215113828 / 1000000000000) (14215113987 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (52874433662061 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77066420119 / 1000000000000) (-77066420118 / 1000000000000), orderedInterval (-60186073385 / 1000000000000) (-60186073384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (142028166220617 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40856448580 / 1000000000000) (40856486971 / 1000000000000), orderedInterval (-43894404364 / 1000000000000) (-43894365973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (385634099701989 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30130568310 / 1000000000000) (-30130495705 / 1000000000000), orderedInterval (20349233255 / 1000000000000) (20349305860 / 1000000000000)))) (orderedInterval (-3052703983 / 1000000000000) (-3052695040 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (284056332441357 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31964530164 / 1000000000000) (-31964530163 / 1000000000000), orderedInterval (-27725621609 / 1000000000000) (-27725621608 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (486735367223361 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-8458738049 / 1000000000000) (-8458738042 / 1000000000000), orderedInterval (31228748319 / 1000000000000) (31228748327 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (358527068508099 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11274649282 / 1000000000000) (11274649329 / 1000000000000), orderedInterval (-35976528157 / 1000000000000) (-35976528110 / 1000000000000)))) (orderedInterval (-3173031500 / 1000000000000) (-3173031467 / 1000000000000))) = true
  rfl'

theorem compactCertificate436_chunkChecks1_1 :
    compactCertificate436.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (550072722464877 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10927441150 / 1000000000000) (-10927441149 / 1000000000000), orderedInterval (-28390314102 / 1000000000000) (-28390314101 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (317584634388933 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (37556905031 / 1000000000000) (37556919568 / 1000000000000), orderedInterval (-13944475171 / 1000000000000) (-13944460634 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (563559506801097 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30019681639 / 1000000000000) (30019682617 / 1000000000000), orderedInterval (1569617027 / 1000000000000) (1569618006 / 1000000000000)))) (orderedInterval (10457453900 / 1000000000000) (10457455862 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (526550394270093 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21453987797 / 1000000000000) (-21453983885 / 1000000000000), orderedInterval (22532010606 / 1000000000000) (22532014518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (375771206986269 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24817220816 / 1000000000000) (-24817212365 / 1000000000000), orderedInterval (27219071765 / 1000000000000) (27219080216 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (426084498661851 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21738304730 / 1000000000000) (-21738301496 / 1000000000000), orderedInterval (26904216662 / 1000000000000) (26904219896 / 1000000000000)))) (orderedInterval (2825222030 / 1000000000000) (2825223490 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (355224833442219 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36381612734 / 1000000000000) (-36381603841 / 1000000000000), orderedInterval (10534097616 / 1000000000000) (10534106509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (313851913234599 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-15719956593 / 1000000000000) (-15719956592 / 1000000000000), orderedInterval (-37069187115 / 1000000000000) (-37069187114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (90966517421301 / 160000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21496761634 / 1000000000000) (-21496761633 / 1000000000000), orderedInterval (-25625446654 / 1000000000000) (-25625446653 / 1000000000000)))) (orderedInterval (1669017375 / 1000000000000) (1669017566 / 1000000000000))) = true
  rfl'

theorem compactCertificate436_chunkChecks1_2 :
    compactCertificate436.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (251618174492847 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (41036569733 / 1000000000000) (41036569734 / 1000000000000), orderedInterval (18376028682 / 1000000000000) (18376028683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (213299513112567 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17849599757 / 1000000000000) (-17849599756 / 1000000000000), orderedInterval (-45453860663 / 1000000000000) (-45453860662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (133472931491901 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-55638164456 / 1000000000000) (-55638164455 / 1000000000000), orderedInterval (-26668082494 / 1000000000000) (-26668082492 / 1000000000000)))) (orderedInterval (-1245642975 / 1000000000000) (-1245642903 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (71782186467267 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (47173894212 / 1000000000000) (47173907593 / 1000000000000), orderedInterval (-70045969345 / 1000000000000) (-70045955964 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (194902599882801 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-30161128195 / 1000000000000) (-30161119239 / 1000000000000), orderedInterval (41334003065 / 1000000000000) (41334012021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (266122837404177 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18226630227 / 1000000000000) (18226630228 / 1000000000000), orderedInterval (39741354898 / 1000000000000) (39741354899 / 1000000000000)))) (orderedInterval (-3660419495 / 1000000000000) (-3660419228 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (112527068508099 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-4817873755 / 1000000000000) (-4817873753 / 1000000000000), orderedInterval (-67085790124 / 1000000000000) (-67085790122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (457416286169379 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23601198367 / 1000000000000) (23601198368 / 1000000000000), orderedInterval (23567537850 / 1000000000000) (23567537851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (305532880631661 / 800000000000) 1 (IntervalRat.scale (615 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22139536694 / 1000000000000) (-22139534383 / 1000000000000), orderedInterval (34332796280 / 1000000000000) (34332798591 / 1000000000000)))) (orderedInterval (-11752835963 / 1000000000000) (-11752835304 / 1000000000000))) = true
  rfl'

theorem compactCertificate436_chunkChecks1 :
    compactCertificate436.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate436.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate436_chunkChecks1_0
    compactCertificate436_chunkChecks1_1 compactCertificate436_chunkChecks1_2

theorem compactCertificate436_chunkChecks2_0 :
    compactCertificate436.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (615 / 2) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (18091538605 / 1000000000000) (18091538606 / 1000000000000), orderedInterval (41719909944 / 1000000000000) (41719909945 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (181202486591823 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (47085178283 / 1000000000000) (47085178284 / 1000000000000), orderedInterval (24260518498 / 1000000000000) (24260518499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (58597161123759 / 160000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21757709001 / 1000000000000) (21757710928 / 1000000000000), orderedInterval (-35595110048 / 1000000000000) (-35595108121 / 1000000000000)))) (orderedInterval (-9266198122 / 1000000000000) (-9266197933 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (52874433662061 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77066420119 / 1000000000000) (-77066420118 / 1000000000000), orderedInterval (-60186073385 / 1000000000000) (-60186073384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (142028166220617 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40856448580 / 1000000000000) (40856486971 / 1000000000000), orderedInterval (-43894404364 / 1000000000000) (-43894365973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (385634099701989 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30130568310 / 1000000000000) (-30130495705 / 1000000000000), orderedInterval (20349233255 / 1000000000000) (20349305860 / 1000000000000)))) (orderedInterval (-5789684805 / 1000000000000) (-5789671566 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (284056332441357 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31964530164 / 1000000000000) (-31964530163 / 1000000000000), orderedInterval (-27725621609 / 1000000000000) (-27725621608 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (486735367223361 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-8458738049 / 1000000000000) (-8458738042 / 1000000000000), orderedInterval (31228748319 / 1000000000000) (31228748327 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (358527068508099 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11274649282 / 1000000000000) (11274649329 / 1000000000000), orderedInterval (-35976528157 / 1000000000000) (-35976528110 / 1000000000000)))) (orderedInterval (-1589857755 / 1000000000000) (-1589857698 / 1000000000000))) = true
  rfl'

theorem compactCertificate436_chunkChecks2_1 :
    compactCertificate436.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (550072722464877 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10927441150 / 1000000000000) (-10927441149 / 1000000000000), orderedInterval (-28390314102 / 1000000000000) (-28390314101 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (317584634388933 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (37556905031 / 1000000000000) (37556919568 / 1000000000000), orderedInterval (-13944475171 / 1000000000000) (-13944460634 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (563559506801097 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30019681639 / 1000000000000) (30019682617 / 1000000000000), orderedInterval (1569617027 / 1000000000000) (1569618006 / 1000000000000)))) (orderedInterval (-36776652403 / 1000000000000) (-36776649330 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (526550394270093 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21453987797 / 1000000000000) (-21453983885 / 1000000000000), orderedInterval (22532010606 / 1000000000000) (22532014518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (375771206986269 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24817220816 / 1000000000000) (-24817212365 / 1000000000000), orderedInterval (27219071765 / 1000000000000) (27219080216 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (426084498661851 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21738304730 / 1000000000000) (-21738301496 / 1000000000000), orderedInterval (26904216662 / 1000000000000) (26904219896 / 1000000000000)))) (orderedInterval (3362150900 / 1000000000000) (3362153241 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (355224833442219 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36381612734 / 1000000000000) (-36381603841 / 1000000000000), orderedInterval (10534097616 / 1000000000000) (10534106509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (313851913234599 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-15719956593 / 1000000000000) (-15719956592 / 1000000000000), orderedInterval (-37069187115 / 1000000000000) (-37069187114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (90966517421301 / 160000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21496761634 / 1000000000000) (-21496761633 / 1000000000000), orderedInterval (-25625446654 / 1000000000000) (-25625446653 / 1000000000000)))) (orderedInterval (1287830087 / 1000000000000) (1287830366 / 1000000000000))) = true
  rfl'

theorem compactCertificate436_chunkChecks2_2 :
    compactCertificate436.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (251618174492847 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (41036569733 / 1000000000000) (41036569734 / 1000000000000), orderedInterval (18376028682 / 1000000000000) (18376028683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (213299513112567 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17849599757 / 1000000000000) (-17849599756 / 1000000000000), orderedInterval (-45453860663 / 1000000000000) (-45453860662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (133472931491901 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-55638164456 / 1000000000000) (-55638164455 / 1000000000000), orderedInterval (-26668082494 / 1000000000000) (-26668082492 / 1000000000000)))) (orderedInterval (6642290844 / 1000000000000) (6642290912 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (71782186467267 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (47173894212 / 1000000000000) (47173907593 / 1000000000000), orderedInterval (-70045969345 / 1000000000000) (-70045955964 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (194902599882801 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-30161128195 / 1000000000000) (-30161119239 / 1000000000000), orderedInterval (41334003065 / 1000000000000) (41334012021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (266122837404177 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18226630227 / 1000000000000) (18226630228 / 1000000000000), orderedInterval (39741354898 / 1000000000000) (39741354899 / 1000000000000)))) (orderedInterval (1291291465 / 1000000000000) (1291291648 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (112527068508099 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-4817873755 / 1000000000000) (-4817873753 / 1000000000000), orderedInterval (-67085790124 / 1000000000000) (-67085790122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (457416286169379 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23601198367 / 1000000000000) (23601198368 / 1000000000000), orderedInterval (23567537850 / 1000000000000) (23567537851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (305532880631661 / 800000000000) 2 (IntervalRat.scale (615 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22139536694 / 1000000000000) (-22139534383 / 1000000000000), orderedInterval (34332796280 / 1000000000000) (34332798591 / 1000000000000)))) (orderedInterval (278842798 / 1000000000000) (278843646 / 1000000000000))) = true
  rfl'

theorem compactCertificate436_chunkChecks2 :
    compactCertificate436.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate436.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate436_chunkChecks2_0
    compactCertificate436_chunkChecks2_1 compactCertificate436_chunkChecks2_2

theorem compactCertificate436_chunkChecks3_0 :
    compactCertificate436.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (615 / 2) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (18091538605 / 1000000000000) (18091538606 / 1000000000000), orderedInterval (41719909944 / 1000000000000) (41719909945 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (181202486591823 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (47085178283 / 1000000000000) (47085178284 / 1000000000000), orderedInterval (24260518498 / 1000000000000) (24260518499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (58597161123759 / 160000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21757709001 / 1000000000000) (21757710928 / 1000000000000), orderedInterval (-35595110048 / 1000000000000) (-35595108121 / 1000000000000)))) (orderedInterval (-13067604906 / 1000000000000) (-13067604681 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (52874433662061 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77066420119 / 1000000000000) (-77066420118 / 1000000000000), orderedInterval (-60186073385 / 1000000000000) (-60186073384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (142028166220617 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40856448580 / 1000000000000) (40856486971 / 1000000000000), orderedInterval (-43894404364 / 1000000000000) (-43894365973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (385634099701989 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30130568310 / 1000000000000) (-30130495705 / 1000000000000), orderedInterval (20349233255 / 1000000000000) (20349305860 / 1000000000000)))) (orderedInterval (5893568262 / 1000000000000) (5893588546 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (284056332441357 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31964530164 / 1000000000000) (-31964530163 / 1000000000000), orderedInterval (-27725621609 / 1000000000000) (-27725621608 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (486735367223361 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-8458738049 / 1000000000000) (-8458738042 / 1000000000000), orderedInterval (31228748319 / 1000000000000) (31228748327 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (358527068508099 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11274649282 / 1000000000000) (11274649329 / 1000000000000), orderedInterval (-35976528157 / 1000000000000) (-35976528110 / 1000000000000)))) (orderedInterval (10157829598 / 1000000000000) (10157829701 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate436_chunkChecks3_1 :
    compactCertificate436.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (550072722464877 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10927441150 / 1000000000000) (-10927441149 / 1000000000000), orderedInterval (-28390314102 / 1000000000000) (-28390314101 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (317584634388933 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (37556905031 / 1000000000000) (37556919568 / 1000000000000), orderedInterval (-13944475171 / 1000000000000) (-13944460634 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (563559506801097 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30019681639 / 1000000000000) (30019682617 / 1000000000000), orderedInterval (1569617027 / 1000000000000) (1569618006 / 1000000000000)))) (orderedInterval (-56740490160 / 1000000000000) (-56740484973 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (526550394270093 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21453987797 / 1000000000000) (-21453983885 / 1000000000000), orderedInterval (22532010606 / 1000000000000) (22532014518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (375771206986269 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24817220816 / 1000000000000) (-24817212365 / 1000000000000), orderedInterval (27219071765 / 1000000000000) (27219080216 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (426084498661851 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21738304730 / 1000000000000) (-21738301496 / 1000000000000), orderedInterval (26904216662 / 1000000000000) (26904219896 / 1000000000000)))) (orderedInterval (-4488437260 / 1000000000000) (-4488433459 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (355224833442219 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36381612734 / 1000000000000) (-36381603841 / 1000000000000), orderedInterval (10534097616 / 1000000000000) (10534106509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (313851913234599 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-15719956593 / 1000000000000) (-15719956592 / 1000000000000), orderedInterval (-37069187115 / 1000000000000) (-37069187114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (90966517421301 / 160000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21496761634 / 1000000000000) (-21496761633 / 1000000000000), orderedInterval (-25625446654 / 1000000000000) (-25625446653 / 1000000000000)))) (orderedInterval (-628847935 / 1000000000000) (-628847526 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate436_chunkChecks3_2 :
    compactCertificate436.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (251618174492847 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (41036569733 / 1000000000000) (41036569734 / 1000000000000), orderedInterval (18376028682 / 1000000000000) (18376028683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (213299513112567 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17849599757 / 1000000000000) (-17849599756 / 1000000000000), orderedInterval (-45453860663 / 1000000000000) (-45453860662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (133472931491901 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-55638164456 / 1000000000000) (-55638164455 / 1000000000000), orderedInterval (-26668082494 / 1000000000000) (-26668082492 / 1000000000000)))) (orderedInterval (1584116152 / 1000000000000) (1584116219 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (71782186467267 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (47173894212 / 1000000000000) (47173907593 / 1000000000000), orderedInterval (-70045969345 / 1000000000000) (-70045955964 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (194902599882801 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-30161128195 / 1000000000000) (-30161119239 / 1000000000000), orderedInterval (41334003065 / 1000000000000) (41334012021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (266122837404177 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18226630227 / 1000000000000) (18226630228 / 1000000000000), orderedInterval (39741354898 / 1000000000000) (39741354899 / 1000000000000)))) (orderedInterval (4285958775 / 1000000000000) (4285958917 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (112527068508099 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-4817873755 / 1000000000000) (-4817873753 / 1000000000000), orderedInterval (-67085790124 / 1000000000000) (-67085790122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (457416286169379 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23601198367 / 1000000000000) (23601198368 / 1000000000000), orderedInterval (23567537850 / 1000000000000) (23567537851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (305532880631661 / 800000000000) 3 (IntervalRat.scale (615 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22139536694 / 1000000000000) (-22139534383 / 1000000000000), orderedInterval (34332796280 / 1000000000000) (34332798591 / 1000000000000)))) (orderedInterval (24712543291 / 1000000000000) (24712544397 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate436_chunkChecks3 :
    compactCertificate436.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate436.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate436_chunkChecks3_0
    compactCertificate436_chunkChecks3_1 compactCertificate436_chunkChecks3_2

theorem compactCertificate436_chunkChecks4_0 :
    compactCertificate436.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (615 / 2) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (18091538605 / 1000000000000) (18091538606 / 1000000000000), orderedInterval (41719909944 / 1000000000000) (41719909945 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (181202486591823 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (47085178283 / 1000000000000) (47085178284 / 1000000000000), orderedInterval (24260518498 / 1000000000000) (24260518499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (58597161123759 / 160000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21757709001 / 1000000000000) (21757710928 / 1000000000000), orderedInterval (-35595110048 / 1000000000000) (-35595108121 / 1000000000000)))) (orderedInterval (9953867509 / 1000000000000) (9953867776 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (52874433662061 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77066420119 / 1000000000000) (-77066420118 / 1000000000000), orderedInterval (-60186073385 / 1000000000000) (-60186073384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (142028166220617 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40856448580 / 1000000000000) (40856486971 / 1000000000000), orderedInterval (-43894404364 / 1000000000000) (-43894365973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (385634099701989 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30130568310 / 1000000000000) (-30130495705 / 1000000000000), orderedInterval (20349233255 / 1000000000000) (20349305860 / 1000000000000)))) (orderedInterval (13064361925 / 1000000000000) (13064393516 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (284056332441357 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31964530164 / 1000000000000) (-31964530163 / 1000000000000), orderedInterval (-27725621609 / 1000000000000) (-27725621608 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (486735367223361 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-8458738049 / 1000000000000) (-8458738042 / 1000000000000), orderedInterval (31228748319 / 1000000000000) (31228748327 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (358527068508099 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (11274649282 / 1000000000000) (11274649329 / 1000000000000), orderedInterval (-35976528157 / 1000000000000) (-35976528110 / 1000000000000)))) (orderedInterval (5161906991 / 1000000000000) (5161907179 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate436_chunkChecks4_1 :
    compactCertificate436.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (550072722464877 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10927441150 / 1000000000000) (-10927441149 / 1000000000000), orderedInterval (-28390314102 / 1000000000000) (-28390314101 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (317584634388933 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (37556905031 / 1000000000000) (37556919568 / 1000000000000), orderedInterval (-13944475171 / 1000000000000) (-13944460634 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (563559506801097 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30019681639 / 1000000000000) (30019682617 / 1000000000000), orderedInterval (1569617027 / 1000000000000) (1569618006 / 1000000000000)))) (orderedInterval (174181186583 / 1000000000000) (174181196069 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (526550394270093 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21453987797 / 1000000000000) (-21453983885 / 1000000000000), orderedInterval (22532010606 / 1000000000000) (22532014518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (375771206986269 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24817220816 / 1000000000000) (-24817212365 / 1000000000000), orderedInterval (27219071765 / 1000000000000) (27219080216 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (426084498661851 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21738304730 / 1000000000000) (-21738301496 / 1000000000000), orderedInterval (26904216662 / 1000000000000) (26904219896 / 1000000000000)))) (orderedInterval (-3627871954 / 1000000000000) (-3627865660 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (355224833442219 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36381612734 / 1000000000000) (-36381603841 / 1000000000000), orderedInterval (10534097616 / 1000000000000) (10534106509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (313851913234599 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-15719956593 / 1000000000000) (-15719956592 / 1000000000000), orderedInterval (-37069187115 / 1000000000000) (-37069187114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (90966517421301 / 160000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21496761634 / 1000000000000) (-21496761633 / 1000000000000), orderedInterval (-25625446654 / 1000000000000) (-25625446653 / 1000000000000)))) (orderedInterval (-5871054232 / 1000000000000) (-5871053628 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate436_chunkChecks4_2 :
    compactCertificate436.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (251618174492847 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (41036569733 / 1000000000000) (41036569734 / 1000000000000), orderedInterval (18376028682 / 1000000000000) (18376028683 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (213299513112567 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17849599757 / 1000000000000) (-17849599756 / 1000000000000), orderedInterval (-45453860663 / 1000000000000) (-45453860662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (133472931491901 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-55638164456 / 1000000000000) (-55638164455 / 1000000000000), orderedInterval (-26668082494 / 1000000000000) (-26668082492 / 1000000000000)))) (orderedInterval (-6777859207 / 1000000000000) (-6777859141 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (71782186467267 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (47173894212 / 1000000000000) (47173907593 / 1000000000000), orderedInterval (-70045969345 / 1000000000000) (-70045955964 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (194902599882801 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-30161128195 / 1000000000000) (-30161119239 / 1000000000000), orderedInterval (41334003065 / 1000000000000) (41334012021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (266122837404177 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18226630227 / 1000000000000) (18226630228 / 1000000000000), orderedInterval (39741354898 / 1000000000000) (39741354899 / 1000000000000)))) (orderedInterval (-1677683805 / 1000000000000) (-1677683686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (112527068508099 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-4817873755 / 1000000000000) (-4817873753 / 1000000000000), orderedInterval (-67085790124 / 1000000000000) (-67085790122 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (457416286169379 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23601198367 / 1000000000000) (23601198368 / 1000000000000), orderedInterval (23567537850 / 1000000000000) (23567537851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (305532880631661 / 800000000000) 4 (IntervalRat.scale (615 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22139536694 / 1000000000000) (-22139534383 / 1000000000000), orderedInterval (34332796280 / 1000000000000) (34332798591 / 1000000000000)))) (orderedInterval (-13242913499 / 1000000000000) (-13242912024 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate436_chunkChecks4 :
    compactCertificate436.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate436.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate436_chunkChecks4_0
    compactCertificate436_chunkChecks4_1 compactCertificate436_chunkChecks4_2

theorem compactCertificate436_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate436.chunkCheck r b = true :=
  compactCertificate436.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate436_chunkChecks0
    · exact compactCertificate436_chunkChecks1
    · exact compactCertificate436_chunkChecks2
    · exact compactCertificate436_chunkChecks3
    · exact compactCertificate436_chunkChecks4)

theorem compactCertificate436_coefficient0 :
    compactCertificate436.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate436_coefficient1 :
    compactCertificate436.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate436_coefficient2 :
    compactCertificate436.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate436_coefficient3 :
    compactCertificate436.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate436_coefficient4 :
    compactCertificate436.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate436_coefficients : ∀ r : Fin 5,
    compactCertificate436.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate436_coefficient0
  · exact compactCertificate436_coefficient1
  · exact compactCertificate436_coefficient2
  · exact compactCertificate436_coefficient3
  · exact compactCertificate436_coefficient4

theorem compactCertificate436_lower : (1 : ℚ) ≤ compactCertificate436.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate436, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate436_proves {t : ℝ} (ht : t ∈ compactCertificate436.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate436.proves compactCertificate436_states compactCertificate436_chunks
    compactCertificate436_coefficients compactCertificate436_lower ht

end Erdos232
