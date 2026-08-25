/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate510 : CompactCertificate where
  left := 381
  right := 382
  center := 763 / 2
  grid := fun i =>
    match i.val with
    | 0 => 121
    | 1 => 89
    | 2 => 145
    | 3 => 26
    | 4 => 70
    | 5 => 190
    | 6 => 140
    | 7 => 240
    | 8 => 177
    | 9 => 272
    | 10 => 157
    | 11 => 278
    | 12 => 260
    | 13 => 186
    | 14 => 210
    | 15 => 175
    | 16 => 155
    | 17 => 225
    | 18 => 124
    | 19 => 105
    | 20 => 66
    | 21 => 35
    | 22 => 96
    | 23 => 131
    | 24 => 56
    | 25 => 226
    | _ => 151
  point := fun i =>
    match i.val with
    | 0 => 763 / 2
    | 1 => 1124044693248463 / 4000000000000
    | 2 => 363492958840879 / 800000000000
    | 3 => 327993438082541 / 4000000000000
    | 4 => 881036510783177 / 4000000000000
    | 5 => 2392185512785509 / 4000000000000
    | 6 => 1762073021567117 / 4000000000000
    | 7 => 3019342156027841 / 4000000000000
    | 8 => 2224033766436419 / 4000000000000
    | 9 => 3412239733664237 / 4000000000000
    | 10 => 1970057528770373 / 4000000000000
    | 11 => 3495901656010057 / 4000000000000
    | 12 => 3266324803480333 / 4000000000000
    | 13 => 2331003503500189 / 4000000000000
    | 14 => 2643109532349531 / 4000000000000
    | 15 => 2203549170052139 / 4000000000000
    | 16 => 1946902518682919 / 4000000000000
    | 17 => 564288234084981 / 800000000000
    | 18 => 1560850952341807 / 4000000000000
    | 19 => 1323150638251127 / 4000000000000
    | 20 => 827966233563581 / 4000000000000
    | 21 => 445282994101827 / 4000000000000
    | 22 => 1209029948866481 / 4000000000000
    | 23 => 1650827032027537 / 4000000000000
    | 24 => 698033766436419 / 4000000000000
    | 25 => 2837468506888099 / 4000000000000
    | _ => 1895297462780141 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-34134557887 / 1000000000000) (-34134453805 / 1000000000000), orderedInterval (22484891814 / 1000000000000) (22484995896 / 1000000000000))
    | 1 => (orderedInterval (-38638701756 / 1000000000000) (-38638605076 / 1000000000000), orderedInterval (27862833534 / 1000000000000) (27862930215 / 1000000000000))
    | 2 => (orderedInterval (13870651647 / 1000000000000) (13870651780 / 1000000000000), orderedInterval (-34781938691 / 1000000000000) (-34781938558 / 1000000000000))
    | 3 => (orderedInterval (78558692514 / 1000000000000) (78558692515 / 1000000000000), orderedInterval (39424096946 / 1000000000000) (39424096947 / 1000000000000))
    | 4 => (orderedInterval (48679254238 / 1000000000000) (48679254239 / 1000000000000), orderedInterval (22707193271 / 1000000000000) (22707193272 / 1000000000000))
    | 5 => (orderedInterval (30556181163 / 1000000000000) (30556220105 / 1000000000000), orderedInterval (-11463104482 / 1000000000000) (-11463065540 / 1000000000000))
    | 6 => (orderedInterval (37860039170 / 1000000000000) (37860039277 / 1000000000000), orderedInterval (3388856189 / 1000000000000) (3388856296 / 1000000000000))
    | 7 => (orderedInterval (28974547686 / 1000000000000) (28974552709 / 1000000000000), orderedInterval (-1984892158 / 1000000000000) (-1984887135 / 1000000000000))
    | 8 => (orderedInterval (-22608471030 / 1000000000000) (-22608471029 / 1000000000000), orderedInterval (-25155834162 / 1000000000000) (-25155834161 / 1000000000000))
    | 9 => (orderedInterval (-16921648022 / 1000000000000) (-16921647606 / 1000000000000), orderedInterval (21456030950 / 1000000000000) (21456031367 / 1000000000000))
    | 10 => (orderedInterval (-2495976353 / 1000000000000) (-2495976352 / 1000000000000), orderedInterval (-35863355099 / 1000000000000) (-35863355098 / 1000000000000))
    | 11 => (orderedInterval (26586885620 / 1000000000000) (26586886268 / 1000000000000), orderedInterval (4627609936 / 1000000000000) (4627610584 / 1000000000000))
    | 12 => (orderedInterval (14650306630 / 1000000000000) (14650306631 / 1000000000000), orderedInterval (23760433874 / 1000000000000) (23760433875 / 1000000000000))
    | 13 => (orderedInterval (-23714106889 / 1000000000000) (-23714098167 / 1000000000000), orderedInterval (23043815128 / 1000000000000) (23043823850 / 1000000000000))
    | 14 => (orderedInterval (30017223595 / 1000000000000) (30017244224 / 1000000000000), orderedInterval (-7922472639 / 1000000000000) (-7922452010 / 1000000000000))
    | 15 => (orderedInterval (-32237070395 / 1000000000000) (-32237047751 / 1000000000000), orderedInterval (10818028523 / 1000000000000) (10818051167 / 1000000000000))
    | 16 => (orderedInterval (-19330416111 / 1000000000000) (-19330416110 / 1000000000000), orderedInterval (-30546458183 / 1000000000000) (-30546458182 / 1000000000000))
    | 17 => (orderedInterval (19647121507 / 1000000000000) (19647123266 / 1000000000000), orderedInterval (-22741359190 / 1000000000000) (-22741357431 / 1000000000000))
    | 18 => (orderedInterval (40048134066 / 1000000000000) (40048134108 / 1000000000000), orderedInterval (5203597776 / 1000000000000) (5203597817 / 1000000000000))
    | 19 => (orderedInterval (-43472629669 / 1000000000000) (-43472628711 / 1000000000000), orderedInterval (5955157657 / 1000000000000) (5955158616 / 1000000000000))
    | 20 => (orderedInterval (23181128367 / 1000000000000) (23181128368 / 1000000000000), orderedInterval (50324798808 / 1000000000000) (50324798809 / 1000000000000))
    | 21 => (orderedInterval (-63317961668 / 1000000000000) (-63317930802 / 1000000000000), orderedInterval (41631711836 / 1000000000000) (41631742702 / 1000000000000))
    | 22 => (orderedInterval (45556736043 / 1000000000000) (45556736067 / 1000000000000), orderedInterval (5474208684 / 1000000000000) (5474208709 / 1000000000000))
    | 23 => (orderedInterval (-36582943601 / 1000000000000) (-36582924947 / 1000000000000), orderedInterval (14335411624 / 1000000000000) (14335430278 / 1000000000000))
    | 24 => (orderedInterval (-35879205701 / 1000000000000) (-35879192413 / 1000000000000), orderedInterval (48690464546 / 1000000000000) (48690477834 / 1000000000000))
    | 25 => (orderedInterval (4548124477 / 1000000000000) (4548124478 / 1000000000000), orderedInterval (29606966505 / 1000000000000) (29606966506 / 1000000000000))
    | _ => (orderedInterval (-8321118305 / 1000000000000) (-8321118304 / 1000000000000), orderedInterval (-35689079004 / 1000000000000) (-35689079003 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-13075835902 / 1000000000000) (-13075793711 / 1000000000000)
      | 1 => orderedInterval (-1247172290 / 1000000000000) (-1247169476 / 1000000000000)
      | 2 => orderedInterval (-1440093282 / 1000000000000) (-1440093105 / 1000000000000)
      | 3 => orderedInterval (6601323524 / 1000000000000) (6601323842 / 1000000000000)
      | 4 => orderedInterval (-2658861726 / 1000000000000) (-2658860751 / 1000000000000)
      | 5 => orderedInterval (1236996327 / 1000000000000) (1236996670 / 1000000000000)
      | 6 => orderedInterval (-3188177220 / 1000000000000) (-3188177063 / 1000000000000)
      | 7 => orderedInterval (2939307622 / 1000000000000) (2939309668 / 1000000000000)
      | _ => orderedInterval (974745440 / 1000000000000) (974745627 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (6672582884 / 1000000000000) (6672624841 / 1000000000000)
      | 1 => orderedInterval (1664195947 / 1000000000000) (1664200340 / 1000000000000)
      | 2 => orderedInterval (-764933913 / 1000000000000) (-764933569 / 1000000000000)
      | 3 => orderedInterval (-10448318246 / 1000000000000) (-10448317555 / 1000000000000)
      | 4 => orderedInterval (2479911689 / 1000000000000) (2479913204 / 1000000000000)
      | 5 => orderedInterval (1334052210 / 1000000000000) (1334052724 / 1000000000000)
      | 6 => orderedInterval (-254356684 / 1000000000000) (-254356542 / 1000000000000)
      | 7 => orderedInterval (-1511232183 / 1000000000000) (-1511230428 / 1000000000000)
      | _ => orderedInterval (3969688494 / 1000000000000) (3969688680 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (12552993338 / 1000000000000) (12553035237 / 1000000000000)
      | 1 => orderedInterval (4780649363 / 1000000000000) (4780656250 / 1000000000000)
      | 2 => orderedInterval (4661284307 / 1000000000000) (4661284981 / 1000000000000)
      | 3 => orderedInterval (-34533689902 / 1000000000000) (-34533688376 / 1000000000000)
      | 4 => orderedInterval (6893385551 / 1000000000000) (6893387915 / 1000000000000)
      | 5 => orderedInterval (-2747527590 / 1000000000000) (-2747526810 / 1000000000000)
      | 6 => orderedInterval (4627848824 / 1000000000000) (4627848956 / 1000000000000)
      | 7 => orderedInterval (-2727934713 / 1000000000000) (-2727932946 / 1000000000000)
      | _ => orderedInterval (-1093482708 / 1000000000000) (-1093482471 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-5600731362 / 1000000000000) (-5600689585 / 1000000000000)
      | 1 => orderedInterval (-3307105367 / 1000000000000) (-3307094576 / 1000000000000)
      | 2 => orderedInterval (1395645390 / 1000000000000) (1395646712 / 1000000000000)
      | 3 => orderedInterval (40523327017 / 1000000000000) (40523330427 / 1000000000000)
      | 4 => orderedInterval (-3786651653 / 1000000000000) (-3786647958 / 1000000000000)
      | 5 => orderedInterval (-318898518 / 1000000000000) (-318897322 / 1000000000000)
      | 6 => orderedInterval (836238069 / 1000000000000) (836238194 / 1000000000000)
      | 7 => orderedInterval (1478919037 / 1000000000000) (1478920908 / 1000000000000)
      | _ => orderedInterval (2639421379 / 1000000000000) (2639421726 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-11968559898 / 1000000000000) (-11968518098 / 1000000000000)
      | 1 => orderedInterval (-12904952338 / 1000000000000) (-12904935398 / 1000000000000)
      | 2 => orderedInterval (-16169312806 / 1000000000000) (-16169310202 / 1000000000000)
      | 3 => orderedInterval (178543003648 / 1000000000000) (178543011312 / 1000000000000)
      | 4 => orderedInterval (-19107858592 / 1000000000000) (-19107852784 / 1000000000000)
      | 5 => orderedInterval (7192568816 / 1000000000000) (7192570678 / 1000000000000)
      | 6 => orderedInterval (-5556900017 / 1000000000000) (-5556899898 / 1000000000000)
      | 7 => orderedInterval (3433320546 / 1000000000000) (3433322563 / 1000000000000)
      | _ => orderedInterval (-733843026 / 1000000000000) (-733842478 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-9857767507 / 1000000000000) (-9857718299 / 1000000000000)
    | 1 => orderedInterval (3141590198 / 1000000000000) (3141641695 / 1000000000000)
    | 2 => orderedInterval (-7586473530 / 1000000000000) (-7586417264 / 1000000000000)
    | 3 => orderedInterval (33860163992 / 1000000000000) (33860228526 / 1000000000000)
    | _ => orderedInterval (122727466333 / 1000000000000) (122727545695 / 1000000000000)

theorem compactCertificate510_stateChecks0 :
    compactCertificate510.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (763 / 2)) (orderedInterval (-34134557887 / 1000000000000) (-34134453805 / 1000000000000), orderedInterval (22484891814 / 1000000000000) (22484995896 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1124044693248463 / 4000000000000)) (orderedInterval (-38638701756 / 1000000000000) (-38638605076 / 1000000000000), orderedInterval (27862833534 / 1000000000000) (27862930215 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (363492958840879 / 800000000000)) (orderedInterval (13870651647 / 1000000000000) (13870651780 / 1000000000000), orderedInterval (-34781938691 / 1000000000000) (-34781938558 / 1000000000000))) = true
  rfl'

theorem compactCertificate510_stateChecks1 :
    compactCertificate510.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (327993438082541 / 4000000000000)) (orderedInterval (78558692514 / 1000000000000) (78558692515 / 1000000000000), orderedInterval (39424096946 / 1000000000000) (39424096947 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (881036510783177 / 4000000000000)) (orderedInterval (48679254238 / 1000000000000) (48679254239 / 1000000000000), orderedInterval (22707193271 / 1000000000000) (22707193272 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2392185512785509 / 4000000000000)) (orderedInterval (30556181163 / 1000000000000) (30556220105 / 1000000000000), orderedInterval (-11463104482 / 1000000000000) (-11463065540 / 1000000000000))) = true
  rfl'

theorem compactCertificate510_stateChecks2 :
    compactCertificate510.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1762073021567117 / 4000000000000)) (orderedInterval (37860039170 / 1000000000000) (37860039277 / 1000000000000), orderedInterval (3388856189 / 1000000000000) (3388856296 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 240 12 (3019342156027841 / 4000000000000)) (orderedInterval (28974547686 / 1000000000000) (28974552709 / 1000000000000), orderedInterval (-1984892158 / 1000000000000) (-1984887135 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2224033766436419 / 4000000000000)) (orderedInterval (-22608471030 / 1000000000000) (-22608471029 / 1000000000000), orderedInterval (-25155834162 / 1000000000000) (-25155834161 / 1000000000000))) = true
  rfl'

theorem compactCertificate510_stateChecks3 :
    compactCertificate510.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 272 12 (3412239733664237 / 4000000000000)) (orderedInterval (-16921648022 / 1000000000000) (-16921647606 / 1000000000000), orderedInterval (21456030950 / 1000000000000) (21456031367 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1970057528770373 / 4000000000000)) (orderedInterval (-2495976353 / 1000000000000) (-2495976352 / 1000000000000), orderedInterval (-35863355099 / 1000000000000) (-35863355098 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 278 12 (3495901656010057 / 4000000000000)) (orderedInterval (26586885620 / 1000000000000) (26586886268 / 1000000000000), orderedInterval (4627609936 / 1000000000000) (4627610584 / 1000000000000))) = true
  rfl'

theorem compactCertificate510_stateChecks4 :
    compactCertificate510.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 260 12 (3266324803480333 / 4000000000000)) (orderedInterval (14650306630 / 1000000000000) (14650306631 / 1000000000000), orderedInterval (23760433874 / 1000000000000) (23760433875 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2331003503500189 / 4000000000000)) (orderedInterval (-23714106889 / 1000000000000) (-23714098167 / 1000000000000), orderedInterval (23043815128 / 1000000000000) (23043823850 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (2643109532349531 / 4000000000000)) (orderedInterval (30017223595 / 1000000000000) (30017244224 / 1000000000000), orderedInterval (-7922472639 / 1000000000000) (-7922452010 / 1000000000000))) = true
  rfl'

theorem compactCertificate510_stateChecks5 :
    compactCertificate510.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2203549170052139 / 4000000000000)) (orderedInterval (-32237070395 / 1000000000000) (-32237047751 / 1000000000000), orderedInterval (10818028523 / 1000000000000) (10818051167 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1946902518682919 / 4000000000000)) (orderedInterval (-19330416111 / 1000000000000) (-19330416110 / 1000000000000), orderedInterval (-30546458183 / 1000000000000) (-30546458182 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (564288234084981 / 800000000000)) (orderedInterval (19647121507 / 1000000000000) (19647123266 / 1000000000000), orderedInterval (-22741359190 / 1000000000000) (-22741357431 / 1000000000000))) = true
  rfl'

theorem compactCertificate510_stateChecks6 :
    compactCertificate510.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1560850952341807 / 4000000000000)) (orderedInterval (40048134066 / 1000000000000) (40048134108 / 1000000000000), orderedInterval (5203597776 / 1000000000000) (5203597817 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1323150638251127 / 4000000000000)) (orderedInterval (-43472629669 / 1000000000000) (-43472628711 / 1000000000000), orderedInterval (5955157657 / 1000000000000) (5955158616 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (827966233563581 / 4000000000000)) (orderedInterval (23181128367 / 1000000000000) (23181128368 / 1000000000000), orderedInterval (50324798808 / 1000000000000) (50324798809 / 1000000000000))) = true
  rfl'

theorem compactCertificate510_stateChecks7 :
    compactCertificate510.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (445282994101827 / 4000000000000)) (orderedInterval (-63317961668 / 1000000000000) (-63317930802 / 1000000000000), orderedInterval (41631711836 / 1000000000000) (41631742702 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1209029948866481 / 4000000000000)) (orderedInterval (45556736043 / 1000000000000) (45556736067 / 1000000000000), orderedInterval (5474208684 / 1000000000000) (5474208709 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1650827032027537 / 4000000000000)) (orderedInterval (-36582943601 / 1000000000000) (-36582924947 / 1000000000000), orderedInterval (14335411624 / 1000000000000) (14335430278 / 1000000000000))) = true
  rfl'

theorem compactCertificate510_stateChecks8 :
    compactCertificate510.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (698033766436419 / 4000000000000)) (orderedInterval (-35879205701 / 1000000000000) (-35879192413 / 1000000000000), orderedInterval (48690464546 / 1000000000000) (48690477834 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 226 12 (2837468506888099 / 4000000000000)) (orderedInterval (4548124477 / 1000000000000) (4548124478 / 1000000000000), orderedInterval (29606966505 / 1000000000000) (29606966506 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1895297462780141 / 4000000000000)) (orderedInterval (-8321118305 / 1000000000000) (-8321118304 / 1000000000000), orderedInterval (-35689079004 / 1000000000000) (-35689079003 / 1000000000000))) = true
  rfl'

theorem compactCertificate510_states : ∀ j,
    BesselStateValid (compactCertificate510.point j) (compactCertificate510.state j) :=
  compactCertificate510.statesValid_of_checks3 compactCertificate510_stateChecks0
    compactCertificate510_stateChecks1 compactCertificate510_stateChecks2
    compactCertificate510_stateChecks3 compactCertificate510_stateChecks4
    compactCertificate510_stateChecks5 compactCertificate510_stateChecks6
    compactCertificate510_stateChecks7 compactCertificate510_stateChecks8

theorem compactCertificate510_chunkChecks0_0 :
    compactCertificate510.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (763 / 2) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34134557887 / 1000000000000) (-34134453805 / 1000000000000), orderedInterval (22484891814 / 1000000000000) (22484995896 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1124044693248463 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38638701756 / 1000000000000) (-38638605076 / 1000000000000), orderedInterval (27862833534 / 1000000000000) (27862930215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (363492958840879 / 800000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13870651647 / 1000000000000) (13870651780 / 1000000000000), orderedInterval (-34781938691 / 1000000000000) (-34781938558 / 1000000000000)))) (orderedInterval (-13075835902 / 1000000000000) (-13075793711 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (327993438082541 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (78558692514 / 1000000000000) (78558692515 / 1000000000000), orderedInterval (39424096946 / 1000000000000) (39424096947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (881036510783177 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48679254238 / 1000000000000) (48679254239 / 1000000000000), orderedInterval (22707193271 / 1000000000000) (22707193272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2392185512785509 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30556181163 / 1000000000000) (30556220105 / 1000000000000), orderedInterval (-11463104482 / 1000000000000) (-11463065540 / 1000000000000)))) (orderedInterval (-1247172290 / 1000000000000) (-1247169476 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1762073021567117 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37860039170 / 1000000000000) (37860039277 / 1000000000000), orderedInterval (3388856189 / 1000000000000) (3388856296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3019342156027841 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28974547686 / 1000000000000) (28974552709 / 1000000000000), orderedInterval (-1984892158 / 1000000000000) (-1984887135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2224033766436419 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22608471030 / 1000000000000) (-22608471029 / 1000000000000), orderedInterval (-25155834162 / 1000000000000) (-25155834161 / 1000000000000)))) (orderedInterval (-1440093282 / 1000000000000) (-1440093105 / 1000000000000))) = true
  rfl'

theorem compactCertificate510_chunkChecks0_1 :
    compactCertificate510.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3412239733664237 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16921648022 / 1000000000000) (-16921647606 / 1000000000000), orderedInterval (21456030950 / 1000000000000) (21456031367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1970057528770373 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2495976353 / 1000000000000) (-2495976352 / 1000000000000), orderedInterval (-35863355099 / 1000000000000) (-35863355098 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3495901656010057 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26586885620 / 1000000000000) (26586886268 / 1000000000000), orderedInterval (4627609936 / 1000000000000) (4627610584 / 1000000000000)))) (orderedInterval (6601323524 / 1000000000000) (6601323842 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3266324803480333 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14650306630 / 1000000000000) (14650306631 / 1000000000000), orderedInterval (23760433874 / 1000000000000) (23760433875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2331003503500189 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23714106889 / 1000000000000) (-23714098167 / 1000000000000), orderedInterval (23043815128 / 1000000000000) (23043823850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2643109532349531 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30017223595 / 1000000000000) (30017244224 / 1000000000000), orderedInterval (-7922472639 / 1000000000000) (-7922452010 / 1000000000000)))) (orderedInterval (-2658861726 / 1000000000000) (-2658860751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2203549170052139 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32237070395 / 1000000000000) (-32237047751 / 1000000000000), orderedInterval (10818028523 / 1000000000000) (10818051167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1946902518682919 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19330416111 / 1000000000000) (-19330416110 / 1000000000000), orderedInterval (-30546458183 / 1000000000000) (-30546458182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (564288234084981 / 800000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (19647121507 / 1000000000000) (19647123266 / 1000000000000), orderedInterval (-22741359190 / 1000000000000) (-22741357431 / 1000000000000)))) (orderedInterval (1236996327 / 1000000000000) (1236996670 / 1000000000000))) = true
  rfl'

theorem compactCertificate510_chunkChecks0_2 :
    compactCertificate510.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1560850952341807 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40048134066 / 1000000000000) (40048134108 / 1000000000000), orderedInterval (5203597776 / 1000000000000) (5203597817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1323150638251127 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43472629669 / 1000000000000) (-43472628711 / 1000000000000), orderedInterval (5955157657 / 1000000000000) (5955158616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (827966233563581 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (23181128367 / 1000000000000) (23181128368 / 1000000000000), orderedInterval (50324798808 / 1000000000000) (50324798809 / 1000000000000)))) (orderedInterval (-3188177220 / 1000000000000) (-3188177063 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (445282994101827 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63317961668 / 1000000000000) (-63317930802 / 1000000000000), orderedInterval (41631711836 / 1000000000000) (41631742702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1209029948866481 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45556736043 / 1000000000000) (45556736067 / 1000000000000), orderedInterval (5474208684 / 1000000000000) (5474208709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1650827032027537 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36582943601 / 1000000000000) (-36582924947 / 1000000000000), orderedInterval (14335411624 / 1000000000000) (14335430278 / 1000000000000)))) (orderedInterval (2939307622 / 1000000000000) (2939309668 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (698033766436419 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-35879205701 / 1000000000000) (-35879192413 / 1000000000000), orderedInterval (48690464546 / 1000000000000) (48690477834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2837468506888099 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4548124477 / 1000000000000) (4548124478 / 1000000000000), orderedInterval (29606966505 / 1000000000000) (29606966506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1895297462780141 / 4000000000000) 0 (IntervalRat.scale (763 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-8321118305 / 1000000000000) (-8321118304 / 1000000000000), orderedInterval (-35689079004 / 1000000000000) (-35689079003 / 1000000000000)))) (orderedInterval (974745440 / 1000000000000) (974745627 / 1000000000000))) = true
  rfl'

theorem compactCertificate510_chunkChecks0 :
    compactCertificate510.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate510.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate510_chunkChecks0_0
    compactCertificate510_chunkChecks0_1 compactCertificate510_chunkChecks0_2

theorem compactCertificate510_chunkChecks1_0 :
    compactCertificate510.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (763 / 2) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34134557887 / 1000000000000) (-34134453805 / 1000000000000), orderedInterval (22484891814 / 1000000000000) (22484995896 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1124044693248463 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38638701756 / 1000000000000) (-38638605076 / 1000000000000), orderedInterval (27862833534 / 1000000000000) (27862930215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (363492958840879 / 800000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13870651647 / 1000000000000) (13870651780 / 1000000000000), orderedInterval (-34781938691 / 1000000000000) (-34781938558 / 1000000000000)))) (orderedInterval (6672582884 / 1000000000000) (6672624841 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (327993438082541 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (78558692514 / 1000000000000) (78558692515 / 1000000000000), orderedInterval (39424096946 / 1000000000000) (39424096947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (881036510783177 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48679254238 / 1000000000000) (48679254239 / 1000000000000), orderedInterval (22707193271 / 1000000000000) (22707193272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2392185512785509 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30556181163 / 1000000000000) (30556220105 / 1000000000000), orderedInterval (-11463104482 / 1000000000000) (-11463065540 / 1000000000000)))) (orderedInterval (1664195947 / 1000000000000) (1664200340 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1762073021567117 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37860039170 / 1000000000000) (37860039277 / 1000000000000), orderedInterval (3388856189 / 1000000000000) (3388856296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3019342156027841 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28974547686 / 1000000000000) (28974552709 / 1000000000000), orderedInterval (-1984892158 / 1000000000000) (-1984887135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2224033766436419 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22608471030 / 1000000000000) (-22608471029 / 1000000000000), orderedInterval (-25155834162 / 1000000000000) (-25155834161 / 1000000000000)))) (orderedInterval (-764933913 / 1000000000000) (-764933569 / 1000000000000))) = true
  rfl'

theorem compactCertificate510_chunkChecks1_1 :
    compactCertificate510.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3412239733664237 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16921648022 / 1000000000000) (-16921647606 / 1000000000000), orderedInterval (21456030950 / 1000000000000) (21456031367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1970057528770373 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2495976353 / 1000000000000) (-2495976352 / 1000000000000), orderedInterval (-35863355099 / 1000000000000) (-35863355098 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3495901656010057 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26586885620 / 1000000000000) (26586886268 / 1000000000000), orderedInterval (4627609936 / 1000000000000) (4627610584 / 1000000000000)))) (orderedInterval (-10448318246 / 1000000000000) (-10448317555 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3266324803480333 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14650306630 / 1000000000000) (14650306631 / 1000000000000), orderedInterval (23760433874 / 1000000000000) (23760433875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2331003503500189 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23714106889 / 1000000000000) (-23714098167 / 1000000000000), orderedInterval (23043815128 / 1000000000000) (23043823850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2643109532349531 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30017223595 / 1000000000000) (30017244224 / 1000000000000), orderedInterval (-7922472639 / 1000000000000) (-7922452010 / 1000000000000)))) (orderedInterval (2479911689 / 1000000000000) (2479913204 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2203549170052139 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32237070395 / 1000000000000) (-32237047751 / 1000000000000), orderedInterval (10818028523 / 1000000000000) (10818051167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1946902518682919 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19330416111 / 1000000000000) (-19330416110 / 1000000000000), orderedInterval (-30546458183 / 1000000000000) (-30546458182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (564288234084981 / 800000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (19647121507 / 1000000000000) (19647123266 / 1000000000000), orderedInterval (-22741359190 / 1000000000000) (-22741357431 / 1000000000000)))) (orderedInterval (1334052210 / 1000000000000) (1334052724 / 1000000000000))) = true
  rfl'

theorem compactCertificate510_chunkChecks1_2 :
    compactCertificate510.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1560850952341807 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40048134066 / 1000000000000) (40048134108 / 1000000000000), orderedInterval (5203597776 / 1000000000000) (5203597817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1323150638251127 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43472629669 / 1000000000000) (-43472628711 / 1000000000000), orderedInterval (5955157657 / 1000000000000) (5955158616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (827966233563581 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (23181128367 / 1000000000000) (23181128368 / 1000000000000), orderedInterval (50324798808 / 1000000000000) (50324798809 / 1000000000000)))) (orderedInterval (-254356684 / 1000000000000) (-254356542 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (445282994101827 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63317961668 / 1000000000000) (-63317930802 / 1000000000000), orderedInterval (41631711836 / 1000000000000) (41631742702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1209029948866481 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45556736043 / 1000000000000) (45556736067 / 1000000000000), orderedInterval (5474208684 / 1000000000000) (5474208709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1650827032027537 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36582943601 / 1000000000000) (-36582924947 / 1000000000000), orderedInterval (14335411624 / 1000000000000) (14335430278 / 1000000000000)))) (orderedInterval (-1511232183 / 1000000000000) (-1511230428 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (698033766436419 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-35879205701 / 1000000000000) (-35879192413 / 1000000000000), orderedInterval (48690464546 / 1000000000000) (48690477834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2837468506888099 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4548124477 / 1000000000000) (4548124478 / 1000000000000), orderedInterval (29606966505 / 1000000000000) (29606966506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1895297462780141 / 4000000000000) 1 (IntervalRat.scale (763 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-8321118305 / 1000000000000) (-8321118304 / 1000000000000), orderedInterval (-35689079004 / 1000000000000) (-35689079003 / 1000000000000)))) (orderedInterval (3969688494 / 1000000000000) (3969688680 / 1000000000000))) = true
  rfl'

theorem compactCertificate510_chunkChecks1 :
    compactCertificate510.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate510.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate510_chunkChecks1_0
    compactCertificate510_chunkChecks1_1 compactCertificate510_chunkChecks1_2

theorem compactCertificate510_chunkChecks2_0 :
    compactCertificate510.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (763 / 2) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34134557887 / 1000000000000) (-34134453805 / 1000000000000), orderedInterval (22484891814 / 1000000000000) (22484995896 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1124044693248463 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38638701756 / 1000000000000) (-38638605076 / 1000000000000), orderedInterval (27862833534 / 1000000000000) (27862930215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (363492958840879 / 800000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13870651647 / 1000000000000) (13870651780 / 1000000000000), orderedInterval (-34781938691 / 1000000000000) (-34781938558 / 1000000000000)))) (orderedInterval (12552993338 / 1000000000000) (12553035237 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (327993438082541 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (78558692514 / 1000000000000) (78558692515 / 1000000000000), orderedInterval (39424096946 / 1000000000000) (39424096947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (881036510783177 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48679254238 / 1000000000000) (48679254239 / 1000000000000), orderedInterval (22707193271 / 1000000000000) (22707193272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2392185512785509 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30556181163 / 1000000000000) (30556220105 / 1000000000000), orderedInterval (-11463104482 / 1000000000000) (-11463065540 / 1000000000000)))) (orderedInterval (4780649363 / 1000000000000) (4780656250 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1762073021567117 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37860039170 / 1000000000000) (37860039277 / 1000000000000), orderedInterval (3388856189 / 1000000000000) (3388856296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3019342156027841 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28974547686 / 1000000000000) (28974552709 / 1000000000000), orderedInterval (-1984892158 / 1000000000000) (-1984887135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2224033766436419 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22608471030 / 1000000000000) (-22608471029 / 1000000000000), orderedInterval (-25155834162 / 1000000000000) (-25155834161 / 1000000000000)))) (orderedInterval (4661284307 / 1000000000000) (4661284981 / 1000000000000))) = true
  rfl'

theorem compactCertificate510_chunkChecks2_1 :
    compactCertificate510.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3412239733664237 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16921648022 / 1000000000000) (-16921647606 / 1000000000000), orderedInterval (21456030950 / 1000000000000) (21456031367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1970057528770373 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2495976353 / 1000000000000) (-2495976352 / 1000000000000), orderedInterval (-35863355099 / 1000000000000) (-35863355098 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3495901656010057 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26586885620 / 1000000000000) (26586886268 / 1000000000000), orderedInterval (4627609936 / 1000000000000) (4627610584 / 1000000000000)))) (orderedInterval (-34533689902 / 1000000000000) (-34533688376 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3266324803480333 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14650306630 / 1000000000000) (14650306631 / 1000000000000), orderedInterval (23760433874 / 1000000000000) (23760433875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2331003503500189 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23714106889 / 1000000000000) (-23714098167 / 1000000000000), orderedInterval (23043815128 / 1000000000000) (23043823850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2643109532349531 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30017223595 / 1000000000000) (30017244224 / 1000000000000), orderedInterval (-7922472639 / 1000000000000) (-7922452010 / 1000000000000)))) (orderedInterval (6893385551 / 1000000000000) (6893387915 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2203549170052139 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32237070395 / 1000000000000) (-32237047751 / 1000000000000), orderedInterval (10818028523 / 1000000000000) (10818051167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1946902518682919 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19330416111 / 1000000000000) (-19330416110 / 1000000000000), orderedInterval (-30546458183 / 1000000000000) (-30546458182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (564288234084981 / 800000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (19647121507 / 1000000000000) (19647123266 / 1000000000000), orderedInterval (-22741359190 / 1000000000000) (-22741357431 / 1000000000000)))) (orderedInterval (-2747527590 / 1000000000000) (-2747526810 / 1000000000000))) = true
  rfl'

theorem compactCertificate510_chunkChecks2_2 :
    compactCertificate510.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1560850952341807 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40048134066 / 1000000000000) (40048134108 / 1000000000000), orderedInterval (5203597776 / 1000000000000) (5203597817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1323150638251127 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43472629669 / 1000000000000) (-43472628711 / 1000000000000), orderedInterval (5955157657 / 1000000000000) (5955158616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (827966233563581 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (23181128367 / 1000000000000) (23181128368 / 1000000000000), orderedInterval (50324798808 / 1000000000000) (50324798809 / 1000000000000)))) (orderedInterval (4627848824 / 1000000000000) (4627848956 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (445282994101827 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63317961668 / 1000000000000) (-63317930802 / 1000000000000), orderedInterval (41631711836 / 1000000000000) (41631742702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1209029948866481 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45556736043 / 1000000000000) (45556736067 / 1000000000000), orderedInterval (5474208684 / 1000000000000) (5474208709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1650827032027537 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36582943601 / 1000000000000) (-36582924947 / 1000000000000), orderedInterval (14335411624 / 1000000000000) (14335430278 / 1000000000000)))) (orderedInterval (-2727934713 / 1000000000000) (-2727932946 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (698033766436419 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-35879205701 / 1000000000000) (-35879192413 / 1000000000000), orderedInterval (48690464546 / 1000000000000) (48690477834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2837468506888099 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4548124477 / 1000000000000) (4548124478 / 1000000000000), orderedInterval (29606966505 / 1000000000000) (29606966506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1895297462780141 / 4000000000000) 2 (IntervalRat.scale (763 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-8321118305 / 1000000000000) (-8321118304 / 1000000000000), orderedInterval (-35689079004 / 1000000000000) (-35689079003 / 1000000000000)))) (orderedInterval (-1093482708 / 1000000000000) (-1093482471 / 1000000000000))) = true
  rfl'

theorem compactCertificate510_chunkChecks2 :
    compactCertificate510.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate510.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate510_chunkChecks2_0
    compactCertificate510_chunkChecks2_1 compactCertificate510_chunkChecks2_2

theorem compactCertificate510_chunkChecks3_0 :
    compactCertificate510.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (763 / 2) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34134557887 / 1000000000000) (-34134453805 / 1000000000000), orderedInterval (22484891814 / 1000000000000) (22484995896 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1124044693248463 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38638701756 / 1000000000000) (-38638605076 / 1000000000000), orderedInterval (27862833534 / 1000000000000) (27862930215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (363492958840879 / 800000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13870651647 / 1000000000000) (13870651780 / 1000000000000), orderedInterval (-34781938691 / 1000000000000) (-34781938558 / 1000000000000)))) (orderedInterval (-5600731362 / 1000000000000) (-5600689585 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (327993438082541 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (78558692514 / 1000000000000) (78558692515 / 1000000000000), orderedInterval (39424096946 / 1000000000000) (39424096947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (881036510783177 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48679254238 / 1000000000000) (48679254239 / 1000000000000), orderedInterval (22707193271 / 1000000000000) (22707193272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2392185512785509 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30556181163 / 1000000000000) (30556220105 / 1000000000000), orderedInterval (-11463104482 / 1000000000000) (-11463065540 / 1000000000000)))) (orderedInterval (-3307105367 / 1000000000000) (-3307094576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1762073021567117 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37860039170 / 1000000000000) (37860039277 / 1000000000000), orderedInterval (3388856189 / 1000000000000) (3388856296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3019342156027841 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28974547686 / 1000000000000) (28974552709 / 1000000000000), orderedInterval (-1984892158 / 1000000000000) (-1984887135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2224033766436419 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22608471030 / 1000000000000) (-22608471029 / 1000000000000), orderedInterval (-25155834162 / 1000000000000) (-25155834161 / 1000000000000)))) (orderedInterval (1395645390 / 1000000000000) (1395646712 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate510_chunkChecks3_1 :
    compactCertificate510.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3412239733664237 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16921648022 / 1000000000000) (-16921647606 / 1000000000000), orderedInterval (21456030950 / 1000000000000) (21456031367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1970057528770373 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2495976353 / 1000000000000) (-2495976352 / 1000000000000), orderedInterval (-35863355099 / 1000000000000) (-35863355098 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3495901656010057 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26586885620 / 1000000000000) (26586886268 / 1000000000000), orderedInterval (4627609936 / 1000000000000) (4627610584 / 1000000000000)))) (orderedInterval (40523327017 / 1000000000000) (40523330427 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3266324803480333 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14650306630 / 1000000000000) (14650306631 / 1000000000000), orderedInterval (23760433874 / 1000000000000) (23760433875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2331003503500189 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23714106889 / 1000000000000) (-23714098167 / 1000000000000), orderedInterval (23043815128 / 1000000000000) (23043823850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2643109532349531 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30017223595 / 1000000000000) (30017244224 / 1000000000000), orderedInterval (-7922472639 / 1000000000000) (-7922452010 / 1000000000000)))) (orderedInterval (-3786651653 / 1000000000000) (-3786647958 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2203549170052139 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32237070395 / 1000000000000) (-32237047751 / 1000000000000), orderedInterval (10818028523 / 1000000000000) (10818051167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1946902518682919 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19330416111 / 1000000000000) (-19330416110 / 1000000000000), orderedInterval (-30546458183 / 1000000000000) (-30546458182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (564288234084981 / 800000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (19647121507 / 1000000000000) (19647123266 / 1000000000000), orderedInterval (-22741359190 / 1000000000000) (-22741357431 / 1000000000000)))) (orderedInterval (-318898518 / 1000000000000) (-318897322 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate510_chunkChecks3_2 :
    compactCertificate510.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1560850952341807 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40048134066 / 1000000000000) (40048134108 / 1000000000000), orderedInterval (5203597776 / 1000000000000) (5203597817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1323150638251127 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43472629669 / 1000000000000) (-43472628711 / 1000000000000), orderedInterval (5955157657 / 1000000000000) (5955158616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (827966233563581 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (23181128367 / 1000000000000) (23181128368 / 1000000000000), orderedInterval (50324798808 / 1000000000000) (50324798809 / 1000000000000)))) (orderedInterval (836238069 / 1000000000000) (836238194 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (445282994101827 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63317961668 / 1000000000000) (-63317930802 / 1000000000000), orderedInterval (41631711836 / 1000000000000) (41631742702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1209029948866481 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45556736043 / 1000000000000) (45556736067 / 1000000000000), orderedInterval (5474208684 / 1000000000000) (5474208709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1650827032027537 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36582943601 / 1000000000000) (-36582924947 / 1000000000000), orderedInterval (14335411624 / 1000000000000) (14335430278 / 1000000000000)))) (orderedInterval (1478919037 / 1000000000000) (1478920908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (698033766436419 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-35879205701 / 1000000000000) (-35879192413 / 1000000000000), orderedInterval (48690464546 / 1000000000000) (48690477834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2837468506888099 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4548124477 / 1000000000000) (4548124478 / 1000000000000), orderedInterval (29606966505 / 1000000000000) (29606966506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1895297462780141 / 4000000000000) 3 (IntervalRat.scale (763 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-8321118305 / 1000000000000) (-8321118304 / 1000000000000), orderedInterval (-35689079004 / 1000000000000) (-35689079003 / 1000000000000)))) (orderedInterval (2639421379 / 1000000000000) (2639421726 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate510_chunkChecks3 :
    compactCertificate510.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate510.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate510_chunkChecks3_0
    compactCertificate510_chunkChecks3_1 compactCertificate510_chunkChecks3_2

theorem compactCertificate510_chunkChecks4_0 :
    compactCertificate510.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (763 / 2) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34134557887 / 1000000000000) (-34134453805 / 1000000000000), orderedInterval (22484891814 / 1000000000000) (22484995896 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1124044693248463 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38638701756 / 1000000000000) (-38638605076 / 1000000000000), orderedInterval (27862833534 / 1000000000000) (27862930215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (363492958840879 / 800000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13870651647 / 1000000000000) (13870651780 / 1000000000000), orderedInterval (-34781938691 / 1000000000000) (-34781938558 / 1000000000000)))) (orderedInterval (-11968559898 / 1000000000000) (-11968518098 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (327993438082541 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (78558692514 / 1000000000000) (78558692515 / 1000000000000), orderedInterval (39424096946 / 1000000000000) (39424096947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (881036510783177 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48679254238 / 1000000000000) (48679254239 / 1000000000000), orderedInterval (22707193271 / 1000000000000) (22707193272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2392185512785509 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30556181163 / 1000000000000) (30556220105 / 1000000000000), orderedInterval (-11463104482 / 1000000000000) (-11463065540 / 1000000000000)))) (orderedInterval (-12904952338 / 1000000000000) (-12904935398 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1762073021567117 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37860039170 / 1000000000000) (37860039277 / 1000000000000), orderedInterval (3388856189 / 1000000000000) (3388856296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3019342156027841 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28974547686 / 1000000000000) (28974552709 / 1000000000000), orderedInterval (-1984892158 / 1000000000000) (-1984887135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2224033766436419 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22608471030 / 1000000000000) (-22608471029 / 1000000000000), orderedInterval (-25155834162 / 1000000000000) (-25155834161 / 1000000000000)))) (orderedInterval (-16169312806 / 1000000000000) (-16169310202 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate510_chunkChecks4_1 :
    compactCertificate510.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3412239733664237 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-16921648022 / 1000000000000) (-16921647606 / 1000000000000), orderedInterval (21456030950 / 1000000000000) (21456031367 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1970057528770373 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2495976353 / 1000000000000) (-2495976352 / 1000000000000), orderedInterval (-35863355099 / 1000000000000) (-35863355098 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3495901656010057 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26586885620 / 1000000000000) (26586886268 / 1000000000000), orderedInterval (4627609936 / 1000000000000) (4627610584 / 1000000000000)))) (orderedInterval (178543003648 / 1000000000000) (178543011312 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3266324803480333 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (14650306630 / 1000000000000) (14650306631 / 1000000000000), orderedInterval (23760433874 / 1000000000000) (23760433875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2331003503500189 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23714106889 / 1000000000000) (-23714098167 / 1000000000000), orderedInterval (23043815128 / 1000000000000) (23043823850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2643109532349531 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30017223595 / 1000000000000) (30017244224 / 1000000000000), orderedInterval (-7922472639 / 1000000000000) (-7922452010 / 1000000000000)))) (orderedInterval (-19107858592 / 1000000000000) (-19107852784 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2203549170052139 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32237070395 / 1000000000000) (-32237047751 / 1000000000000), orderedInterval (10818028523 / 1000000000000) (10818051167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1946902518682919 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19330416111 / 1000000000000) (-19330416110 / 1000000000000), orderedInterval (-30546458183 / 1000000000000) (-30546458182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (564288234084981 / 800000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (19647121507 / 1000000000000) (19647123266 / 1000000000000), orderedInterval (-22741359190 / 1000000000000) (-22741357431 / 1000000000000)))) (orderedInterval (7192568816 / 1000000000000) (7192570678 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate510_chunkChecks4_2 :
    compactCertificate510.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1560850952341807 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40048134066 / 1000000000000) (40048134108 / 1000000000000), orderedInterval (5203597776 / 1000000000000) (5203597817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1323150638251127 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43472629669 / 1000000000000) (-43472628711 / 1000000000000), orderedInterval (5955157657 / 1000000000000) (5955158616 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (827966233563581 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (23181128367 / 1000000000000) (23181128368 / 1000000000000), orderedInterval (50324798808 / 1000000000000) (50324798809 / 1000000000000)))) (orderedInterval (-5556900017 / 1000000000000) (-5556899898 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (445282994101827 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63317961668 / 1000000000000) (-63317930802 / 1000000000000), orderedInterval (41631711836 / 1000000000000) (41631742702 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1209029948866481 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45556736043 / 1000000000000) (45556736067 / 1000000000000), orderedInterval (5474208684 / 1000000000000) (5474208709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1650827032027537 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36582943601 / 1000000000000) (-36582924947 / 1000000000000), orderedInterval (14335411624 / 1000000000000) (14335430278 / 1000000000000)))) (orderedInterval (3433320546 / 1000000000000) (3433322563 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (698033766436419 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-35879205701 / 1000000000000) (-35879192413 / 1000000000000), orderedInterval (48690464546 / 1000000000000) (48690477834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2837468506888099 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4548124477 / 1000000000000) (4548124478 / 1000000000000), orderedInterval (29606966505 / 1000000000000) (29606966506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1895297462780141 / 4000000000000) 4 (IntervalRat.scale (763 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-8321118305 / 1000000000000) (-8321118304 / 1000000000000), orderedInterval (-35689079004 / 1000000000000) (-35689079003 / 1000000000000)))) (orderedInterval (-733843026 / 1000000000000) (-733842478 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate510_chunkChecks4 :
    compactCertificate510.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate510.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate510_chunkChecks4_0
    compactCertificate510_chunkChecks4_1 compactCertificate510_chunkChecks4_2

theorem compactCertificate510_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate510.chunkCheck r b = true :=
  compactCertificate510.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate510_chunkChecks0
    · exact compactCertificate510_chunkChecks1
    · exact compactCertificate510_chunkChecks2
    · exact compactCertificate510_chunkChecks3
    · exact compactCertificate510_chunkChecks4)

theorem compactCertificate510_coefficient0 :
    compactCertificate510.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate510_coefficient1 :
    compactCertificate510.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate510_coefficient2 :
    compactCertificate510.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate510_coefficient3 :
    compactCertificate510.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate510_coefficient4 :
    compactCertificate510.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate510_coefficients : ∀ r : Fin 5,
    compactCertificate510.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate510_coefficient0
  · exact compactCertificate510_coefficient1
  · exact compactCertificate510_coefficient2
  · exact compactCertificate510_coefficient3
  · exact compactCertificate510_coefficient4

theorem compactCertificate510_lower : (1 : ℚ) ≤ compactCertificate510.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate510, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate510_proves {t : ℝ} (ht : t ∈ compactCertificate510.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate510.proves compactCertificate510_states compactCertificate510_chunks
    compactCertificate510_coefficients compactCertificate510_lower ht

end Erdos232
