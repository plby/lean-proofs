/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate463 : CompactCertificate where
  left := 334
  right := 335
  center := 669 / 2
  grid := fun i =>
    match i.val with
    | 0 => 107
    | 1 => 78
    | 2 => 127
    | 3 => 23
    | 4 => 62
    | 5 => 167
    | 6 => 123
    | 7 => 211
    | 8 => 155
    | 9 => 238
    | 10 => 138
    | 11 => 244
    | 12 => 228
    | 13 => 163
    | 14 => 185
    | 15 => 154
    | 16 => 136
    | 17 => 197
    | 18 => 109
    | 19 => 92
    | 20 => 58
    | 21 => 31
    | 22 => 84
    | 23 => 115
    | 24 => 49
    | 25 => 198
    | _ => 132
  point := fun i =>
    match i.val with
    | 0 => 669 / 2
    | 1 => 985564744145769 / 4000000000000
    | 2 => 318711388551177 / 800000000000
    | 3 => 287585334308283 / 4000000000000
    | 4 => 772494660175551 / 4000000000000
    | 5 => 2097473273988867 / 4000000000000
    | 6 => 1544989320351771 / 4000000000000
    | 7 => 2647365533922183 / 4000000000000
    | 8 => 1950037470178197 / 4000000000000
    | 9 => 2991858953894331 / 4000000000000
    | 10 => 1727350572408099 / 4000000000000
    | 11 => 3065213902844991 / 4000000000000
    | 12 => 2863920437127579 / 4000000000000
    | 13 => 2043828759949707 / 4000000000000
    | 14 => 2317483980526653 / 4000000000000
    | 15 => 1932076533112557 / 4000000000000
    | 16 => 1707048211007697 / 4000000000000
    | 17 => 494769106950003 / 800000000000
    | 18 => 1368557388095241 / 4000000000000
    | 19 => 1160141254246401 / 4000000000000
    | 20 => 725962529821803 / 4000000000000
    | 21 => 390425062980501 / 4000000000000
    | 22 => 1060079994484503 / 4000000000000
    | 23 => 1447448603442231 / 4000000000000
    | 24 => 612037470178197 / 4000000000000
    | 25 => 2487898336970037 / 4000000000000
    | _ => 1661800789777083 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (33214254856 / 1000000000000) (33214307356 / 1000000000000), orderedInterval (-28334107993 / 1000000000000) (-28334055493 / 1000000000000))
    | 1 => (orderedInterval (43038167362 / 1000000000000) (43038215940 / 1000000000000), orderedInterval (-27133399483 / 1000000000000) (-27133350906 / 1000000000000))
    | 2 => (orderedInterval (-7630171634 / 1000000000000) (-7630171633 / 1000000000000), orderedInterval (-39230276173 / 1000000000000) (-39230276172 / 1000000000000))
    | 3 => (orderedInterval (-38658204506 / 1000000000000) (-38658204505 / 1000000000000), orderedInterval (-85523796347 / 1000000000000) (-85523796346 / 1000000000000))
    | 4 => (orderedInterval (-43895773509 / 1000000000000) (-43895672562 / 1000000000000), orderedInterval (37121691181 / 1000000000000) (37121792128 / 1000000000000))
    | 5 => (orderedInterval (-16933882079 / 1000000000000) (-16933882078 / 1000000000000), orderedInterval (-30435680472 / 1000000000000) (-30435680471 / 1000000000000))
    | 6 => (orderedInterval (-23473482377 / 1000000000000) (-23473482376 / 1000000000000), orderedInterval (-33093834297 / 1000000000000) (-33093834296 / 1000000000000))
    | 7 => (orderedInterval (7656764796 / 1000000000000) (7656764800 / 1000000000000), orderedInterval (-30060167691 / 1000000000000) (-30060167687 / 1000000000000))
    | 8 => (orderedInterval (-35240708515 / 1000000000000) (-35240708494 / 1000000000000), orderedInterval (-7960947420 / 1000000000000) (-7960947398 / 1000000000000))
    | 9 => (orderedInterval (25319722222 / 1000000000000) (25319722224 / 1000000000000), orderedInterval (14476094860 / 1000000000000) (14476094862 / 1000000000000))
    | 10 => (orderedInterval (-30478384972 / 1000000000000) (-30478331375 / 1000000000000), orderedInterval (23386499438 / 1000000000000) (23386553035 / 1000000000000))
    | 11 => (orderedInterval (14821509697 / 1000000000000) (14821509698 / 1000000000000), orderedInterval (24710566009 / 1000000000000) (24710566010 / 1000000000000))
    | 12 => (orderedInterval (13828042605 / 1000000000000) (13828042606 / 1000000000000), orderedInterval (26408969716 / 1000000000000) (26408969717 / 1000000000000))
    | 13 => (orderedInterval (11680106267 / 1000000000000) (11680106315 / 1000000000000), orderedInterval (-33320755977 / 1000000000000) (-33320755929 / 1000000000000))
    | 14 => (orderedInterval (28561396523 / 1000000000000) (28561476704 / 1000000000000), orderedInterval (-16848956993 / 1000000000000) (-16848876812 / 1000000000000))
    | 15 => (orderedInterval (-36159040 / 1000000000000) (-36159039 / 1000000000000), orderedInterval (36304314686 / 1000000000000) (36304314687 / 1000000000000))
    | 16 => (orderedInterval (11064976149 / 1000000000000) (11064976150 / 1000000000000), orderedInterval (36991242044 / 1000000000000) (36991242045 / 1000000000000))
    | 17 => (orderedInterval (-11086568231 / 1000000000000) (-11086568230 / 1000000000000), orderedInterval (-30098325917 / 1000000000000) (-30098325916 / 1000000000000))
    | 18 => (orderedInterval (-20330549323 / 1000000000000) (-20330549322 / 1000000000000), orderedInterval (-38014645524 / 1000000000000) (-38014645523 / 1000000000000))
    | 19 => (orderedInterval (45690822860 / 1000000000000) (45690824960 / 1000000000000), orderedInterval (-10438255670 / 1000000000000) (-10438253571 / 1000000000000))
    | 20 => (orderedInterval (3726875330 / 1000000000000) (3726875332 / 1000000000000), orderedInterval (59098544208 / 1000000000000) (59098544210 / 1000000000000))
    | 21 => (orderedInterval (-68001601056 / 1000000000000) (-68001601055 / 1000000000000), orderedInterval (-43218523197 / 1000000000000) (-43218523196 / 1000000000000))
    | 22 => (orderedInterval (46200411324 / 1000000000000) (46200417805 / 1000000000000), orderedInterval (-16447968847 / 1000000000000) (-16447962366 / 1000000000000))
    | 23 => (orderedInterval (-41050598452 / 1000000000000) (-41050598442 / 1000000000000), orderedInterval (-8553442532 / 1000000000000) (-8553442522 / 1000000000000))
    | 24 => (orderedInterval (9262188468 / 1000000000000) (9262188508 / 1000000000000), orderedInterval (-63865146919 / 1000000000000) (-63865146879 / 1000000000000))
    | 25 => (orderedInterval (21202120252 / 1000000000000) (21202120253 / 1000000000000), orderedInterval (23941595539 / 1000000000000) (23941595540 / 1000000000000))
    | _ => (orderedInterval (39132412491 / 1000000000000) (39132412709 / 1000000000000), orderedInterval (960076773 / 1000000000000) (960076991 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (13118252938 / 1000000000000) (13118274223 / 1000000000000)
      | 1 => orderedInterval (20526355 / 1000000000000) (20530081 / 1000000000000)
      | 2 => orderedInterval (-1087863666 / 1000000000000) (-1087863646 / 1000000000000)
      | 3 => orderedInterval (-4650241583 / 1000000000000) (-4650237479 / 1000000000000)
      | 4 => orderedInterval (710327938 / 1000000000000) (710328388 / 1000000000000)
      | 5 => orderedInterval (-917489324 / 1000000000000) (-917489291 / 1000000000000)
      | 6 => orderedInterval (785931890 / 1000000000000) (785932094 / 1000000000000)
      | 7 => orderedInterval (3353586474 / 1000000000000) (3353586662 / 1000000000000)
      | _ => orderedInterval (-9012333491 / 1000000000000) (-9012333357 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-14158654717 / 1000000000000) (-14158633548 / 1000000000000)
      | 1 => orderedInterval (4373757075 / 1000000000000) (4373759249 / 1000000000000)
      | 2 => orderedInterval (1554099680 / 1000000000000) (1554099715 / 1000000000000)
      | 3 => orderedInterval (4532629583 / 1000000000000) (4532634985 / 1000000000000)
      | 4 => orderedInterval (-5685893009 / 1000000000000) (-5685892235 / 1000000000000)
      | 5 => orderedInterval (-3520236053 / 1000000000000) (-3520236006 / 1000000000000)
      | 6 => orderedInterval (7773233517 / 1000000000000) (7773233698 / 1000000000000)
      | 7 => orderedInterval (1237656932 / 1000000000000) (1237657086 / 1000000000000)
      | _ => orderedInterval (-4023632891 / 1000000000000) (-4023632709 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-12705130414 / 1000000000000) (-12705109266 / 1000000000000)
      | 1 => orderedInterval (-2456524412 / 1000000000000) (-2456523113 / 1000000000000)
      | 2 => orderedInterval (2728993758 / 1000000000000) (2728993818 / 1000000000000)
      | 3 => orderedInterval (15187402663 / 1000000000000) (15187409889 / 1000000000000)
      | 4 => orderedInterval (-982841714 / 1000000000000) (-982840376 / 1000000000000)
      | 5 => orderedInterval (2012454470 / 1000000000000) (2012454540 / 1000000000000)
      | 6 => orderedInterval (-1515571315 / 1000000000000) (-1515571151 / 1000000000000)
      | 7 => orderedInterval (-3134496377 / 1000000000000) (-3134496248 / 1000000000000)
      | _ => orderedInterval (17293485501 / 1000000000000) (17293485757 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (15258675552 / 1000000000000) (15258696640 / 1000000000000)
      | 1 => orderedInterval (-8597763979 / 1000000000000) (-8597763171 / 1000000000000)
      | 2 => orderedInterval (-6594364667 / 1000000000000) (-6594364558 / 1000000000000)
      | 3 => orderedInterval (-17249213091 / 1000000000000) (-17249203231 / 1000000000000)
      | 4 => orderedInterval (15465760835 / 1000000000000) (15465763146 / 1000000000000)
      | 5 => orderedInterval (7998538725 / 1000000000000) (7998538832 / 1000000000000)
      | 6 => orderedInterval (-7192122764 / 1000000000000) (-7192122614 / 1000000000000)
      | 7 => orderedInterval (-1025937327 / 1000000000000) (-1025937215 / 1000000000000)
      | _ => orderedInterval (12859235674 / 1000000000000) (12859236049 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (12290775374 / 1000000000000) (12290796483 / 1000000000000)
      | 1 => orderedInterval (7144028699 / 1000000000000) (7144029259 / 1000000000000)
      | 2 => orderedInterval (-7422707062 / 1000000000000) (-7422706862 / 1000000000000)
      | 3 => orderedInterval (-60611594919 / 1000000000000) (-60611580958 / 1000000000000)
      | 4 => orderedInterval (-619907581 / 1000000000000) (-619903577 / 1000000000000)
      | 5 => orderedInterval (-5044482899 / 1000000000000) (-5044482730 / 1000000000000)
      | 6 => orderedInterval (2149772802 / 1000000000000) (2149772941 / 1000000000000)
      | 7 => orderedInterval (3911012983 / 1000000000000) (3911013082 / 1000000000000)
      | _ => orderedInterval (-38176418886 / 1000000000000) (-38176418311 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (2320697531 / 1000000000000) (2320727675 / 1000000000000)
    | 1 => orderedInterval (-7917039883 / 1000000000000) (-7917009765 / 1000000000000)
    | 2 => orderedInterval (16427772160 / 1000000000000) (16427803850 / 1000000000000)
    | 3 => orderedInterval (10922808958 / 1000000000000) (10922843878 / 1000000000000)
    | _ => orderedInterval (-86379521489 / 1000000000000) (-86379480673 / 1000000000000)

theorem compactCertificate463_stateChecks0 :
    compactCertificate463.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (669 / 2)) (orderedInterval (33214254856 / 1000000000000) (33214307356 / 1000000000000), orderedInterval (-28334107993 / 1000000000000) (-28334055493 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (985564744145769 / 4000000000000)) (orderedInterval (43038167362 / 1000000000000) (43038215940 / 1000000000000), orderedInterval (-27133399483 / 1000000000000) (-27133350906 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (318711388551177 / 800000000000)) (orderedInterval (-7630171634 / 1000000000000) (-7630171633 / 1000000000000), orderedInterval (-39230276173 / 1000000000000) (-39230276172 / 1000000000000))) = true
  rfl'

theorem compactCertificate463_stateChecks1 :
    compactCertificate463.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (287585334308283 / 4000000000000)) (orderedInterval (-38658204506 / 1000000000000) (-38658204505 / 1000000000000), orderedInterval (-85523796347 / 1000000000000) (-85523796346 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (772494660175551 / 4000000000000)) (orderedInterval (-43895773509 / 1000000000000) (-43895672562 / 1000000000000), orderedInterval (37121691181 / 1000000000000) (37121792128 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2097473273988867 / 4000000000000)) (orderedInterval (-16933882079 / 1000000000000) (-16933882078 / 1000000000000), orderedInterval (-30435680472 / 1000000000000) (-30435680471 / 1000000000000))) = true
  rfl'

theorem compactCertificate463_stateChecks2 :
    compactCertificate463.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1544989320351771 / 4000000000000)) (orderedInterval (-23473482377 / 1000000000000) (-23473482376 / 1000000000000), orderedInterval (-33093834297 / 1000000000000) (-33093834296 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 211 12 (2647365533922183 / 4000000000000)) (orderedInterval (7656764796 / 1000000000000) (7656764800 / 1000000000000), orderedInterval (-30060167691 / 1000000000000) (-30060167687 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1950037470178197 / 4000000000000)) (orderedInterval (-35240708515 / 1000000000000) (-35240708494 / 1000000000000), orderedInterval (-7960947420 / 1000000000000) (-7960947398 / 1000000000000))) = true
  rfl'

theorem compactCertificate463_stateChecks3 :
    compactCertificate463.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 238 12 (2991858953894331 / 4000000000000)) (orderedInterval (25319722222 / 1000000000000) (25319722224 / 1000000000000), orderedInterval (14476094860 / 1000000000000) (14476094862 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1727350572408099 / 4000000000000)) (orderedInterval (-30478384972 / 1000000000000) (-30478331375 / 1000000000000), orderedInterval (23386499438 / 1000000000000) (23386553035 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 244 12 (3065213902844991 / 4000000000000)) (orderedInterval (14821509697 / 1000000000000) (14821509698 / 1000000000000), orderedInterval (24710566009 / 1000000000000) (24710566010 / 1000000000000))) = true
  rfl'

theorem compactCertificate463_stateChecks4 :
    compactCertificate463.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (2863920437127579 / 4000000000000)) (orderedInterval (13828042605 / 1000000000000) (13828042606 / 1000000000000), orderedInterval (26408969716 / 1000000000000) (26408969717 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2043828759949707 / 4000000000000)) (orderedInterval (11680106267 / 1000000000000) (11680106315 / 1000000000000), orderedInterval (-33320755977 / 1000000000000) (-33320755929 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2317483980526653 / 4000000000000)) (orderedInterval (28561396523 / 1000000000000) (28561476704 / 1000000000000), orderedInterval (-16848956993 / 1000000000000) (-16848876812 / 1000000000000))) = true
  rfl'

theorem compactCertificate463_stateChecks5 :
    compactCertificate463.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1932076533112557 / 4000000000000)) (orderedInterval (-36159040 / 1000000000000) (-36159039 / 1000000000000), orderedInterval (36304314686 / 1000000000000) (36304314687 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1707048211007697 / 4000000000000)) (orderedInterval (11064976149 / 1000000000000) (11064976150 / 1000000000000), orderedInterval (36991242044 / 1000000000000) (36991242045 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (494769106950003 / 800000000000)) (orderedInterval (-11086568231 / 1000000000000) (-11086568230 / 1000000000000), orderedInterval (-30098325917 / 1000000000000) (-30098325916 / 1000000000000))) = true
  rfl'

theorem compactCertificate463_stateChecks6 :
    compactCertificate463.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1368557388095241 / 4000000000000)) (orderedInterval (-20330549323 / 1000000000000) (-20330549322 / 1000000000000), orderedInterval (-38014645524 / 1000000000000) (-38014645523 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1160141254246401 / 4000000000000)) (orderedInterval (45690822860 / 1000000000000) (45690824960 / 1000000000000), orderedInterval (-10438255670 / 1000000000000) (-10438253571 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (725962529821803 / 4000000000000)) (orderedInterval (3726875330 / 1000000000000) (3726875332 / 1000000000000), orderedInterval (59098544208 / 1000000000000) (59098544210 / 1000000000000))) = true
  rfl'

theorem compactCertificate463_stateChecks7 :
    compactCertificate463.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (390425062980501 / 4000000000000)) (orderedInterval (-68001601056 / 1000000000000) (-68001601055 / 1000000000000), orderedInterval (-43218523197 / 1000000000000) (-43218523196 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1060079994484503 / 4000000000000)) (orderedInterval (46200411324 / 1000000000000) (46200417805 / 1000000000000), orderedInterval (-16447968847 / 1000000000000) (-16447962366 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1447448603442231 / 4000000000000)) (orderedInterval (-41050598452 / 1000000000000) (-41050598442 / 1000000000000), orderedInterval (-8553442532 / 1000000000000) (-8553442522 / 1000000000000))) = true
  rfl'

theorem compactCertificate463_stateChecks8 :
    compactCertificate463.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (612037470178197 / 4000000000000)) (orderedInterval (9262188468 / 1000000000000) (9262188508 / 1000000000000), orderedInterval (-63865146919 / 1000000000000) (-63865146879 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (2487898336970037 / 4000000000000)) (orderedInterval (21202120252 / 1000000000000) (21202120253 / 1000000000000), orderedInterval (23941595539 / 1000000000000) (23941595540 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1661800789777083 / 4000000000000)) (orderedInterval (39132412491 / 1000000000000) (39132412709 / 1000000000000), orderedInterval (960076773 / 1000000000000) (960076991 / 1000000000000))) = true
  rfl'

theorem compactCertificate463_states : ∀ j,
    BesselStateValid (compactCertificate463.point j) (compactCertificate463.state j) :=
  compactCertificate463.statesValid_of_checks3 compactCertificate463_stateChecks0
    compactCertificate463_stateChecks1 compactCertificate463_stateChecks2
    compactCertificate463_stateChecks3 compactCertificate463_stateChecks4
    compactCertificate463_stateChecks5 compactCertificate463_stateChecks6
    compactCertificate463_stateChecks7 compactCertificate463_stateChecks8

theorem compactCertificate463_chunkChecks0_0 :
    compactCertificate463.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (669 / 2) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33214254856 / 1000000000000) (33214307356 / 1000000000000), orderedInterval (-28334107993 / 1000000000000) (-28334055493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (985564744145769 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43038167362 / 1000000000000) (43038215940 / 1000000000000), orderedInterval (-27133399483 / 1000000000000) (-27133350906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (318711388551177 / 800000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7630171634 / 1000000000000) (-7630171633 / 1000000000000), orderedInterval (-39230276173 / 1000000000000) (-39230276172 / 1000000000000)))) (orderedInterval (13118252938 / 1000000000000) (13118274223 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (287585334308283 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-38658204506 / 1000000000000) (-38658204505 / 1000000000000), orderedInterval (-85523796347 / 1000000000000) (-85523796346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (772494660175551 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-43895773509 / 1000000000000) (-43895672562 / 1000000000000), orderedInterval (37121691181 / 1000000000000) (37121792128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2097473273988867 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-16933882079 / 1000000000000) (-16933882078 / 1000000000000), orderedInterval (-30435680472 / 1000000000000) (-30435680471 / 1000000000000)))) (orderedInterval (20526355 / 1000000000000) (20530081 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1544989320351771 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-23473482377 / 1000000000000) (-23473482376 / 1000000000000), orderedInterval (-33093834297 / 1000000000000) (-33093834296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2647365533922183 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7656764796 / 1000000000000) (7656764800 / 1000000000000), orderedInterval (-30060167691 / 1000000000000) (-30060167687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1950037470178197 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35240708515 / 1000000000000) (-35240708494 / 1000000000000), orderedInterval (-7960947420 / 1000000000000) (-7960947398 / 1000000000000)))) (orderedInterval (-1087863666 / 1000000000000) (-1087863646 / 1000000000000))) = true
  rfl'

theorem compactCertificate463_chunkChecks0_1 :
    compactCertificate463.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2991858953894331 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25319722222 / 1000000000000) (25319722224 / 1000000000000), orderedInterval (14476094860 / 1000000000000) (14476094862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1727350572408099 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30478384972 / 1000000000000) (-30478331375 / 1000000000000), orderedInterval (23386499438 / 1000000000000) (23386553035 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3065213902844991 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14821509697 / 1000000000000) (14821509698 / 1000000000000), orderedInterval (24710566009 / 1000000000000) (24710566010 / 1000000000000)))) (orderedInterval (-4650241583 / 1000000000000) (-4650237479 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2863920437127579 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13828042605 / 1000000000000) (13828042606 / 1000000000000), orderedInterval (26408969716 / 1000000000000) (26408969717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2043828759949707 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (11680106267 / 1000000000000) (11680106315 / 1000000000000), orderedInterval (-33320755977 / 1000000000000) (-33320755929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2317483980526653 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28561396523 / 1000000000000) (28561476704 / 1000000000000), orderedInterval (-16848956993 / 1000000000000) (-16848876812 / 1000000000000)))) (orderedInterval (710327938 / 1000000000000) (710328388 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1932076533112557 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36159040 / 1000000000000) (-36159039 / 1000000000000), orderedInterval (36304314686 / 1000000000000) (36304314687 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1707048211007697 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11064976149 / 1000000000000) (11064976150 / 1000000000000), orderedInterval (36991242044 / 1000000000000) (36991242045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (494769106950003 / 800000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11086568231 / 1000000000000) (-11086568230 / 1000000000000), orderedInterval (-30098325917 / 1000000000000) (-30098325916 / 1000000000000)))) (orderedInterval (-917489324 / 1000000000000) (-917489291 / 1000000000000))) = true
  rfl'

theorem compactCertificate463_chunkChecks0_2 :
    compactCertificate463.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1368557388095241 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20330549323 / 1000000000000) (-20330549322 / 1000000000000), orderedInterval (-38014645524 / 1000000000000) (-38014645523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1160141254246401 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45690822860 / 1000000000000) (45690824960 / 1000000000000), orderedInterval (-10438255670 / 1000000000000) (-10438253571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (725962529821803 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3726875330 / 1000000000000) (3726875332 / 1000000000000), orderedInterval (59098544208 / 1000000000000) (59098544210 / 1000000000000)))) (orderedInterval (785931890 / 1000000000000) (785932094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (390425062980501 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68001601056 / 1000000000000) (-68001601055 / 1000000000000), orderedInterval (-43218523197 / 1000000000000) (-43218523196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1060079994484503 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (46200411324 / 1000000000000) (46200417805 / 1000000000000), orderedInterval (-16447968847 / 1000000000000) (-16447962366 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1447448603442231 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41050598452 / 1000000000000) (-41050598442 / 1000000000000), orderedInterval (-8553442532 / 1000000000000) (-8553442522 / 1000000000000)))) (orderedInterval (3353586474 / 1000000000000) (3353586662 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (612037470178197 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (9262188468 / 1000000000000) (9262188508 / 1000000000000), orderedInterval (-63865146919 / 1000000000000) (-63865146879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2487898336970037 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21202120252 / 1000000000000) (21202120253 / 1000000000000), orderedInterval (23941595539 / 1000000000000) (23941595540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1661800789777083 / 4000000000000) 0 (IntervalRat.scale (669 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39132412491 / 1000000000000) (39132412709 / 1000000000000), orderedInterval (960076773 / 1000000000000) (960076991 / 1000000000000)))) (orderedInterval (-9012333491 / 1000000000000) (-9012333357 / 1000000000000))) = true
  rfl'

theorem compactCertificate463_chunkChecks0 :
    compactCertificate463.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate463.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate463_chunkChecks0_0
    compactCertificate463_chunkChecks0_1 compactCertificate463_chunkChecks0_2

theorem compactCertificate463_chunkChecks1_0 :
    compactCertificate463.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (669 / 2) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33214254856 / 1000000000000) (33214307356 / 1000000000000), orderedInterval (-28334107993 / 1000000000000) (-28334055493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (985564744145769 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43038167362 / 1000000000000) (43038215940 / 1000000000000), orderedInterval (-27133399483 / 1000000000000) (-27133350906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (318711388551177 / 800000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7630171634 / 1000000000000) (-7630171633 / 1000000000000), orderedInterval (-39230276173 / 1000000000000) (-39230276172 / 1000000000000)))) (orderedInterval (-14158654717 / 1000000000000) (-14158633548 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (287585334308283 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-38658204506 / 1000000000000) (-38658204505 / 1000000000000), orderedInterval (-85523796347 / 1000000000000) (-85523796346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (772494660175551 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-43895773509 / 1000000000000) (-43895672562 / 1000000000000), orderedInterval (37121691181 / 1000000000000) (37121792128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2097473273988867 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-16933882079 / 1000000000000) (-16933882078 / 1000000000000), orderedInterval (-30435680472 / 1000000000000) (-30435680471 / 1000000000000)))) (orderedInterval (4373757075 / 1000000000000) (4373759249 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1544989320351771 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-23473482377 / 1000000000000) (-23473482376 / 1000000000000), orderedInterval (-33093834297 / 1000000000000) (-33093834296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2647365533922183 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7656764796 / 1000000000000) (7656764800 / 1000000000000), orderedInterval (-30060167691 / 1000000000000) (-30060167687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1950037470178197 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35240708515 / 1000000000000) (-35240708494 / 1000000000000), orderedInterval (-7960947420 / 1000000000000) (-7960947398 / 1000000000000)))) (orderedInterval (1554099680 / 1000000000000) (1554099715 / 1000000000000))) = true
  rfl'

theorem compactCertificate463_chunkChecks1_1 :
    compactCertificate463.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2991858953894331 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25319722222 / 1000000000000) (25319722224 / 1000000000000), orderedInterval (14476094860 / 1000000000000) (14476094862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1727350572408099 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30478384972 / 1000000000000) (-30478331375 / 1000000000000), orderedInterval (23386499438 / 1000000000000) (23386553035 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3065213902844991 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14821509697 / 1000000000000) (14821509698 / 1000000000000), orderedInterval (24710566009 / 1000000000000) (24710566010 / 1000000000000)))) (orderedInterval (4532629583 / 1000000000000) (4532634985 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2863920437127579 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13828042605 / 1000000000000) (13828042606 / 1000000000000), orderedInterval (26408969716 / 1000000000000) (26408969717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2043828759949707 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (11680106267 / 1000000000000) (11680106315 / 1000000000000), orderedInterval (-33320755977 / 1000000000000) (-33320755929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2317483980526653 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28561396523 / 1000000000000) (28561476704 / 1000000000000), orderedInterval (-16848956993 / 1000000000000) (-16848876812 / 1000000000000)))) (orderedInterval (-5685893009 / 1000000000000) (-5685892235 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1932076533112557 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36159040 / 1000000000000) (-36159039 / 1000000000000), orderedInterval (36304314686 / 1000000000000) (36304314687 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1707048211007697 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11064976149 / 1000000000000) (11064976150 / 1000000000000), orderedInterval (36991242044 / 1000000000000) (36991242045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (494769106950003 / 800000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11086568231 / 1000000000000) (-11086568230 / 1000000000000), orderedInterval (-30098325917 / 1000000000000) (-30098325916 / 1000000000000)))) (orderedInterval (-3520236053 / 1000000000000) (-3520236006 / 1000000000000))) = true
  rfl'

theorem compactCertificate463_chunkChecks1_2 :
    compactCertificate463.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1368557388095241 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20330549323 / 1000000000000) (-20330549322 / 1000000000000), orderedInterval (-38014645524 / 1000000000000) (-38014645523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1160141254246401 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45690822860 / 1000000000000) (45690824960 / 1000000000000), orderedInterval (-10438255670 / 1000000000000) (-10438253571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (725962529821803 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3726875330 / 1000000000000) (3726875332 / 1000000000000), orderedInterval (59098544208 / 1000000000000) (59098544210 / 1000000000000)))) (orderedInterval (7773233517 / 1000000000000) (7773233698 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (390425062980501 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68001601056 / 1000000000000) (-68001601055 / 1000000000000), orderedInterval (-43218523197 / 1000000000000) (-43218523196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1060079994484503 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (46200411324 / 1000000000000) (46200417805 / 1000000000000), orderedInterval (-16447968847 / 1000000000000) (-16447962366 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1447448603442231 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41050598452 / 1000000000000) (-41050598442 / 1000000000000), orderedInterval (-8553442532 / 1000000000000) (-8553442522 / 1000000000000)))) (orderedInterval (1237656932 / 1000000000000) (1237657086 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (612037470178197 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (9262188468 / 1000000000000) (9262188508 / 1000000000000), orderedInterval (-63865146919 / 1000000000000) (-63865146879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2487898336970037 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21202120252 / 1000000000000) (21202120253 / 1000000000000), orderedInterval (23941595539 / 1000000000000) (23941595540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1661800789777083 / 4000000000000) 1 (IntervalRat.scale (669 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39132412491 / 1000000000000) (39132412709 / 1000000000000), orderedInterval (960076773 / 1000000000000) (960076991 / 1000000000000)))) (orderedInterval (-4023632891 / 1000000000000) (-4023632709 / 1000000000000))) = true
  rfl'

theorem compactCertificate463_chunkChecks1 :
    compactCertificate463.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate463.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate463_chunkChecks1_0
    compactCertificate463_chunkChecks1_1 compactCertificate463_chunkChecks1_2

theorem compactCertificate463_chunkChecks2_0 :
    compactCertificate463.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (669 / 2) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33214254856 / 1000000000000) (33214307356 / 1000000000000), orderedInterval (-28334107993 / 1000000000000) (-28334055493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (985564744145769 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43038167362 / 1000000000000) (43038215940 / 1000000000000), orderedInterval (-27133399483 / 1000000000000) (-27133350906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (318711388551177 / 800000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7630171634 / 1000000000000) (-7630171633 / 1000000000000), orderedInterval (-39230276173 / 1000000000000) (-39230276172 / 1000000000000)))) (orderedInterval (-12705130414 / 1000000000000) (-12705109266 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (287585334308283 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-38658204506 / 1000000000000) (-38658204505 / 1000000000000), orderedInterval (-85523796347 / 1000000000000) (-85523796346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (772494660175551 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-43895773509 / 1000000000000) (-43895672562 / 1000000000000), orderedInterval (37121691181 / 1000000000000) (37121792128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2097473273988867 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-16933882079 / 1000000000000) (-16933882078 / 1000000000000), orderedInterval (-30435680472 / 1000000000000) (-30435680471 / 1000000000000)))) (orderedInterval (-2456524412 / 1000000000000) (-2456523113 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1544989320351771 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-23473482377 / 1000000000000) (-23473482376 / 1000000000000), orderedInterval (-33093834297 / 1000000000000) (-33093834296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2647365533922183 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7656764796 / 1000000000000) (7656764800 / 1000000000000), orderedInterval (-30060167691 / 1000000000000) (-30060167687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1950037470178197 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35240708515 / 1000000000000) (-35240708494 / 1000000000000), orderedInterval (-7960947420 / 1000000000000) (-7960947398 / 1000000000000)))) (orderedInterval (2728993758 / 1000000000000) (2728993818 / 1000000000000))) = true
  rfl'

theorem compactCertificate463_chunkChecks2_1 :
    compactCertificate463.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2991858953894331 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25319722222 / 1000000000000) (25319722224 / 1000000000000), orderedInterval (14476094860 / 1000000000000) (14476094862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1727350572408099 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30478384972 / 1000000000000) (-30478331375 / 1000000000000), orderedInterval (23386499438 / 1000000000000) (23386553035 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3065213902844991 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14821509697 / 1000000000000) (14821509698 / 1000000000000), orderedInterval (24710566009 / 1000000000000) (24710566010 / 1000000000000)))) (orderedInterval (15187402663 / 1000000000000) (15187409889 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2863920437127579 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13828042605 / 1000000000000) (13828042606 / 1000000000000), orderedInterval (26408969716 / 1000000000000) (26408969717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2043828759949707 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (11680106267 / 1000000000000) (11680106315 / 1000000000000), orderedInterval (-33320755977 / 1000000000000) (-33320755929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2317483980526653 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28561396523 / 1000000000000) (28561476704 / 1000000000000), orderedInterval (-16848956993 / 1000000000000) (-16848876812 / 1000000000000)))) (orderedInterval (-982841714 / 1000000000000) (-982840376 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1932076533112557 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36159040 / 1000000000000) (-36159039 / 1000000000000), orderedInterval (36304314686 / 1000000000000) (36304314687 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1707048211007697 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11064976149 / 1000000000000) (11064976150 / 1000000000000), orderedInterval (36991242044 / 1000000000000) (36991242045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (494769106950003 / 800000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11086568231 / 1000000000000) (-11086568230 / 1000000000000), orderedInterval (-30098325917 / 1000000000000) (-30098325916 / 1000000000000)))) (orderedInterval (2012454470 / 1000000000000) (2012454540 / 1000000000000))) = true
  rfl'

theorem compactCertificate463_chunkChecks2_2 :
    compactCertificate463.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1368557388095241 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20330549323 / 1000000000000) (-20330549322 / 1000000000000), orderedInterval (-38014645524 / 1000000000000) (-38014645523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1160141254246401 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45690822860 / 1000000000000) (45690824960 / 1000000000000), orderedInterval (-10438255670 / 1000000000000) (-10438253571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (725962529821803 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3726875330 / 1000000000000) (3726875332 / 1000000000000), orderedInterval (59098544208 / 1000000000000) (59098544210 / 1000000000000)))) (orderedInterval (-1515571315 / 1000000000000) (-1515571151 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (390425062980501 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68001601056 / 1000000000000) (-68001601055 / 1000000000000), orderedInterval (-43218523197 / 1000000000000) (-43218523196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1060079994484503 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (46200411324 / 1000000000000) (46200417805 / 1000000000000), orderedInterval (-16447968847 / 1000000000000) (-16447962366 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1447448603442231 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41050598452 / 1000000000000) (-41050598442 / 1000000000000), orderedInterval (-8553442532 / 1000000000000) (-8553442522 / 1000000000000)))) (orderedInterval (-3134496377 / 1000000000000) (-3134496248 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (612037470178197 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (9262188468 / 1000000000000) (9262188508 / 1000000000000), orderedInterval (-63865146919 / 1000000000000) (-63865146879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2487898336970037 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21202120252 / 1000000000000) (21202120253 / 1000000000000), orderedInterval (23941595539 / 1000000000000) (23941595540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1661800789777083 / 4000000000000) 2 (IntervalRat.scale (669 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39132412491 / 1000000000000) (39132412709 / 1000000000000), orderedInterval (960076773 / 1000000000000) (960076991 / 1000000000000)))) (orderedInterval (17293485501 / 1000000000000) (17293485757 / 1000000000000))) = true
  rfl'

theorem compactCertificate463_chunkChecks2 :
    compactCertificate463.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate463.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate463_chunkChecks2_0
    compactCertificate463_chunkChecks2_1 compactCertificate463_chunkChecks2_2

theorem compactCertificate463_chunkChecks3_0 :
    compactCertificate463.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (669 / 2) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33214254856 / 1000000000000) (33214307356 / 1000000000000), orderedInterval (-28334107993 / 1000000000000) (-28334055493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (985564744145769 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43038167362 / 1000000000000) (43038215940 / 1000000000000), orderedInterval (-27133399483 / 1000000000000) (-27133350906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (318711388551177 / 800000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7630171634 / 1000000000000) (-7630171633 / 1000000000000), orderedInterval (-39230276173 / 1000000000000) (-39230276172 / 1000000000000)))) (orderedInterval (15258675552 / 1000000000000) (15258696640 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (287585334308283 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-38658204506 / 1000000000000) (-38658204505 / 1000000000000), orderedInterval (-85523796347 / 1000000000000) (-85523796346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (772494660175551 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-43895773509 / 1000000000000) (-43895672562 / 1000000000000), orderedInterval (37121691181 / 1000000000000) (37121792128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2097473273988867 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-16933882079 / 1000000000000) (-16933882078 / 1000000000000), orderedInterval (-30435680472 / 1000000000000) (-30435680471 / 1000000000000)))) (orderedInterval (-8597763979 / 1000000000000) (-8597763171 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1544989320351771 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-23473482377 / 1000000000000) (-23473482376 / 1000000000000), orderedInterval (-33093834297 / 1000000000000) (-33093834296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2647365533922183 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7656764796 / 1000000000000) (7656764800 / 1000000000000), orderedInterval (-30060167691 / 1000000000000) (-30060167687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1950037470178197 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35240708515 / 1000000000000) (-35240708494 / 1000000000000), orderedInterval (-7960947420 / 1000000000000) (-7960947398 / 1000000000000)))) (orderedInterval (-6594364667 / 1000000000000) (-6594364558 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate463_chunkChecks3_1 :
    compactCertificate463.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2991858953894331 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25319722222 / 1000000000000) (25319722224 / 1000000000000), orderedInterval (14476094860 / 1000000000000) (14476094862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1727350572408099 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30478384972 / 1000000000000) (-30478331375 / 1000000000000), orderedInterval (23386499438 / 1000000000000) (23386553035 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3065213902844991 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14821509697 / 1000000000000) (14821509698 / 1000000000000), orderedInterval (24710566009 / 1000000000000) (24710566010 / 1000000000000)))) (orderedInterval (-17249213091 / 1000000000000) (-17249203231 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2863920437127579 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13828042605 / 1000000000000) (13828042606 / 1000000000000), orderedInterval (26408969716 / 1000000000000) (26408969717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2043828759949707 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (11680106267 / 1000000000000) (11680106315 / 1000000000000), orderedInterval (-33320755977 / 1000000000000) (-33320755929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2317483980526653 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28561396523 / 1000000000000) (28561476704 / 1000000000000), orderedInterval (-16848956993 / 1000000000000) (-16848876812 / 1000000000000)))) (orderedInterval (15465760835 / 1000000000000) (15465763146 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1932076533112557 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36159040 / 1000000000000) (-36159039 / 1000000000000), orderedInterval (36304314686 / 1000000000000) (36304314687 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1707048211007697 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11064976149 / 1000000000000) (11064976150 / 1000000000000), orderedInterval (36991242044 / 1000000000000) (36991242045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (494769106950003 / 800000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11086568231 / 1000000000000) (-11086568230 / 1000000000000), orderedInterval (-30098325917 / 1000000000000) (-30098325916 / 1000000000000)))) (orderedInterval (7998538725 / 1000000000000) (7998538832 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate463_chunkChecks3_2 :
    compactCertificate463.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1368557388095241 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20330549323 / 1000000000000) (-20330549322 / 1000000000000), orderedInterval (-38014645524 / 1000000000000) (-38014645523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1160141254246401 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45690822860 / 1000000000000) (45690824960 / 1000000000000), orderedInterval (-10438255670 / 1000000000000) (-10438253571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (725962529821803 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3726875330 / 1000000000000) (3726875332 / 1000000000000), orderedInterval (59098544208 / 1000000000000) (59098544210 / 1000000000000)))) (orderedInterval (-7192122764 / 1000000000000) (-7192122614 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (390425062980501 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68001601056 / 1000000000000) (-68001601055 / 1000000000000), orderedInterval (-43218523197 / 1000000000000) (-43218523196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1060079994484503 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (46200411324 / 1000000000000) (46200417805 / 1000000000000), orderedInterval (-16447968847 / 1000000000000) (-16447962366 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1447448603442231 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41050598452 / 1000000000000) (-41050598442 / 1000000000000), orderedInterval (-8553442532 / 1000000000000) (-8553442522 / 1000000000000)))) (orderedInterval (-1025937327 / 1000000000000) (-1025937215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (612037470178197 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (9262188468 / 1000000000000) (9262188508 / 1000000000000), orderedInterval (-63865146919 / 1000000000000) (-63865146879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2487898336970037 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21202120252 / 1000000000000) (21202120253 / 1000000000000), orderedInterval (23941595539 / 1000000000000) (23941595540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1661800789777083 / 4000000000000) 3 (IntervalRat.scale (669 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39132412491 / 1000000000000) (39132412709 / 1000000000000), orderedInterval (960076773 / 1000000000000) (960076991 / 1000000000000)))) (orderedInterval (12859235674 / 1000000000000) (12859236049 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate463_chunkChecks3 :
    compactCertificate463.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate463.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate463_chunkChecks3_0
    compactCertificate463_chunkChecks3_1 compactCertificate463_chunkChecks3_2

theorem compactCertificate463_chunkChecks4_0 :
    compactCertificate463.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (669 / 2) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33214254856 / 1000000000000) (33214307356 / 1000000000000), orderedInterval (-28334107993 / 1000000000000) (-28334055493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (985564744145769 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43038167362 / 1000000000000) (43038215940 / 1000000000000), orderedInterval (-27133399483 / 1000000000000) (-27133350906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (318711388551177 / 800000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7630171634 / 1000000000000) (-7630171633 / 1000000000000), orderedInterval (-39230276173 / 1000000000000) (-39230276172 / 1000000000000)))) (orderedInterval (12290775374 / 1000000000000) (12290796483 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (287585334308283 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-38658204506 / 1000000000000) (-38658204505 / 1000000000000), orderedInterval (-85523796347 / 1000000000000) (-85523796346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (772494660175551 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-43895773509 / 1000000000000) (-43895672562 / 1000000000000), orderedInterval (37121691181 / 1000000000000) (37121792128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2097473273988867 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-16933882079 / 1000000000000) (-16933882078 / 1000000000000), orderedInterval (-30435680472 / 1000000000000) (-30435680471 / 1000000000000)))) (orderedInterval (7144028699 / 1000000000000) (7144029259 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1544989320351771 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-23473482377 / 1000000000000) (-23473482376 / 1000000000000), orderedInterval (-33093834297 / 1000000000000) (-33093834296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2647365533922183 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7656764796 / 1000000000000) (7656764800 / 1000000000000), orderedInterval (-30060167691 / 1000000000000) (-30060167687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1950037470178197 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-35240708515 / 1000000000000) (-35240708494 / 1000000000000), orderedInterval (-7960947420 / 1000000000000) (-7960947398 / 1000000000000)))) (orderedInterval (-7422707062 / 1000000000000) (-7422706862 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate463_chunkChecks4_1 :
    compactCertificate463.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2991858953894331 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25319722222 / 1000000000000) (25319722224 / 1000000000000), orderedInterval (14476094860 / 1000000000000) (14476094862 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1727350572408099 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30478384972 / 1000000000000) (-30478331375 / 1000000000000), orderedInterval (23386499438 / 1000000000000) (23386553035 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3065213902844991 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14821509697 / 1000000000000) (14821509698 / 1000000000000), orderedInterval (24710566009 / 1000000000000) (24710566010 / 1000000000000)))) (orderedInterval (-60611594919 / 1000000000000) (-60611580958 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2863920437127579 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13828042605 / 1000000000000) (13828042606 / 1000000000000), orderedInterval (26408969716 / 1000000000000) (26408969717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2043828759949707 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (11680106267 / 1000000000000) (11680106315 / 1000000000000), orderedInterval (-33320755977 / 1000000000000) (-33320755929 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2317483980526653 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28561396523 / 1000000000000) (28561476704 / 1000000000000), orderedInterval (-16848956993 / 1000000000000) (-16848876812 / 1000000000000)))) (orderedInterval (-619907581 / 1000000000000) (-619903577 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1932076533112557 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36159040 / 1000000000000) (-36159039 / 1000000000000), orderedInterval (36304314686 / 1000000000000) (36304314687 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1707048211007697 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (11064976149 / 1000000000000) (11064976150 / 1000000000000), orderedInterval (36991242044 / 1000000000000) (36991242045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (494769106950003 / 800000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11086568231 / 1000000000000) (-11086568230 / 1000000000000), orderedInterval (-30098325917 / 1000000000000) (-30098325916 / 1000000000000)))) (orderedInterval (-5044482899 / 1000000000000) (-5044482730 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate463_chunkChecks4_2 :
    compactCertificate463.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1368557388095241 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20330549323 / 1000000000000) (-20330549322 / 1000000000000), orderedInterval (-38014645524 / 1000000000000) (-38014645523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1160141254246401 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45690822860 / 1000000000000) (45690824960 / 1000000000000), orderedInterval (-10438255670 / 1000000000000) (-10438253571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (725962529821803 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3726875330 / 1000000000000) (3726875332 / 1000000000000), orderedInterval (59098544208 / 1000000000000) (59098544210 / 1000000000000)))) (orderedInterval (2149772802 / 1000000000000) (2149772941 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (390425062980501 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68001601056 / 1000000000000) (-68001601055 / 1000000000000), orderedInterval (-43218523197 / 1000000000000) (-43218523196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1060079994484503 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (46200411324 / 1000000000000) (46200417805 / 1000000000000), orderedInterval (-16447968847 / 1000000000000) (-16447962366 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1447448603442231 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41050598452 / 1000000000000) (-41050598442 / 1000000000000), orderedInterval (-8553442532 / 1000000000000) (-8553442522 / 1000000000000)))) (orderedInterval (3911012983 / 1000000000000) (3911013082 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (612037470178197 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (9262188468 / 1000000000000) (9262188508 / 1000000000000), orderedInterval (-63865146919 / 1000000000000) (-63865146879 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2487898336970037 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21202120252 / 1000000000000) (21202120253 / 1000000000000), orderedInterval (23941595539 / 1000000000000) (23941595540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1661800789777083 / 4000000000000) 4 (IntervalRat.scale (669 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39132412491 / 1000000000000) (39132412709 / 1000000000000), orderedInterval (960076773 / 1000000000000) (960076991 / 1000000000000)))) (orderedInterval (-38176418886 / 1000000000000) (-38176418311 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate463_chunkChecks4 :
    compactCertificate463.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate463.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate463_chunkChecks4_0
    compactCertificate463_chunkChecks4_1 compactCertificate463_chunkChecks4_2

theorem compactCertificate463_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate463.chunkCheck r b = true :=
  compactCertificate463.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate463_chunkChecks0
    · exact compactCertificate463_chunkChecks1
    · exact compactCertificate463_chunkChecks2
    · exact compactCertificate463_chunkChecks3
    · exact compactCertificate463_chunkChecks4)

theorem compactCertificate463_coefficient0 :
    compactCertificate463.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate463_coefficient1 :
    compactCertificate463.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate463_coefficient2 :
    compactCertificate463.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate463_coefficient3 :
    compactCertificate463.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate463_coefficient4 :
    compactCertificate463.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate463_coefficients : ∀ r : Fin 5,
    compactCertificate463.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate463_coefficient0
  · exact compactCertificate463_coefficient1
  · exact compactCertificate463_coefficient2
  · exact compactCertificate463_coefficient3
  · exact compactCertificate463_coefficient4

theorem compactCertificate463_lower : (1 : ℚ) ≤ compactCertificate463.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate463, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate463_proves {t : ℝ} (ht : t ∈ compactCertificate463.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate463.proves compactCertificate463_states compactCertificate463_chunks
    compactCertificate463_coefficients compactCertificate463_lower ht

end Erdos232
