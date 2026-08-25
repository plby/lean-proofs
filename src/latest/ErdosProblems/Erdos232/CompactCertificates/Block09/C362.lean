/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate362 : CompactCertificate where
  left := 233
  right := 234
  center := 467 / 2
  grid := fun i =>
    match i.val with
    | 0 => 74
    | 1 => 55
    | 2 => 89
    | 3 => 16
    | 4 => 43
    | 5 => 117
    | 6 => 86
    | 7 => 147
    | 8 => 108
    | 9 => 166
    | 10 => 96
    | 11 => 170
    | 12 => 159
    | 13 => 114
    | 14 => 129
    | 15 => 107
    | 16 => 95
    | 17 => 137
    | 18 => 76
    | 19 => 64
    | 20 => 40
    | 21 => 22
    | 22 => 59
    | 23 => 80
    | 24 => 34
    | 25 => 138
    | _ => 92
  point := fun i =>
    match i.val with
    | 0 => 467 / 2
    | 1 => 687980172669767 / 4000000000000
    | 2 => 222478652396711 / 800000000000
    | 3 => 200750898538069 / 4000000000000
    | 4 => 539245151422993 / 4000000000000
    | 5 => 1464155484234381 / 4000000000000
    | 6 => 1078490302846453 / 4000000000000
    | 7 => 1848011516205769 / 4000000000000
    | 8 => 1361236918644571 / 4000000000000
    | 9 => 2088487490984533 / 4000000000000
    | 10 => 1205788815118957 / 4000000000000
    | 11 => 2139693412000913 / 4000000000000
    | 12 => 1999179139220597 / 4000000000000
    | 13 => 1426708566362501 / 4000000000000
    | 14 => 1617735454268979 / 4000000000000
    | 15 => 1348699164370051 / 4000000000000
    | 16 => 1191616613663071 / 4000000000000
    | 17 => 345376940128029 / 800000000000
    | 18 => 955330792586663 / 4000000000000
    | 19 => 809844492874543 / 4000000000000
    | 20 => 506763081355429 / 4000000000000
    | 21 => 272538870570843 / 4000000000000
    | 22 => 739996049961529 / 4000000000000
    | 23 => 1010401342014233 / 4000000000000
    | 24 => 427236918644571 / 4000000000000
    | 25 => 1736694354805691 / 4000000000000
    | _ => 1160031343536469 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (50765183487 / 1000000000000) (50765185252 / 1000000000000), orderedInterval (-12328095354 / 1000000000000) (-12328093589 / 1000000000000))
    | 1 => (orderedInterval (479488657 / 1000000000000) (479488662 / 1000000000000), orderedInterval (-60838636958 / 1000000000000) (-60838636954 / 1000000000000))
    | 2 => (orderedInterval (31493899039 / 1000000000000) (31493916812 / 1000000000000), orderedInterval (-36075014110 / 1000000000000) (-36074996337 / 1000000000000))
    | 3 => (orderedInterval (72996976481 / 1000000000000) (72996976482 / 1000000000000), orderedInterval (85041781337 / 1000000000000) (85041781338 / 1000000000000))
    | 4 => (orderedInterval (-33383374537 / 1000000000000) (-33383374536 / 1000000000000), orderedInterval (-59941739232 / 1000000000000) (-59941739231 / 1000000000000))
    | 5 => (orderedInterval (28194624418 / 1000000000000) (28194639002 / 1000000000000), orderedInterval (-30767601562 / 1000000000000) (-30767586977 / 1000000000000))
    | 6 => (orderedInterval (11103446138 / 1000000000000) (11103446139 / 1000000000000), orderedInterval (47285526355 / 1000000000000) (47285526356 / 1000000000000))
    | 7 => (orderedInterval (-30701762294 / 1000000000000) (-30701762293 / 1000000000000), orderedInterval (-20832002279 / 1000000000000) (-20832002278 / 1000000000000))
    | 8 => (orderedInterval (42098286764 / 1000000000000) (42098289821 / 1000000000000), orderedInterval (-9983648468 / 1000000000000) (-9983645410 / 1000000000000))
    | 9 => (orderedInterval (34425915409 / 1000000000000) (34425915473 / 1000000000000), orderedInterval (5810769028 / 1000000000000) (5810769091 / 1000000000000))
    | 10 => (orderedInterval (27418118264 / 1000000000000) (27418118265 / 1000000000000), orderedInterval (36834406167 / 1000000000000) (36834406168 / 1000000000000))
    | 11 => (orderedInterval (34420687986 / 1000000000000) (34420689444 / 1000000000000), orderedInterval (-2340782763 / 1000000000000) (-2340781305 / 1000000000000))
    | 12 => (orderedInterval (-31250407676 / 1000000000000) (-31250407675 / 1000000000000), orderedInterval (-17207472699 / 1000000000000) (-17207472698 / 1000000000000))
    | 13 => (orderedInterval (-26544414691 / 1000000000000) (-26544406504 / 1000000000000), orderedInterval (32904476749 / 1000000000000) (32904484936 / 1000000000000))
    | 14 => (orderedInterval (1844205685 / 1000000000000) (1844205687 / 1000000000000), orderedInterval (-39634352356 / 1000000000000) (-39634352355 / 1000000000000))
    | 15 => (orderedInterval (-42221156449 / 1000000000000) (-42221153200 / 1000000000000), orderedInterval (10332583211 / 1000000000000) (10332586460 / 1000000000000))
    | 16 => (orderedInterval (-10890955873 / 1000000000000) (-10890955872 / 1000000000000), orderedInterval (-44908161132 / 1000000000000) (-44908161131 / 1000000000000))
    | 17 => (orderedInterval (-32989894517 / 1000000000000) (-32989805631 / 1000000000000), orderedInterval (19692114787 / 1000000000000) (19692203672 / 1000000000000))
    | 18 => (orderedInterval (39009483551 / 1000000000000) (39009483552 / 1000000000000), orderedInterval (33738539250 / 1000000000000) (33738539251 / 1000000000000))
    | 19 => (orderedInterval (45859340423 / 1000000000000) (45859403544 / 1000000000000), orderedInterval (-32382769522 / 1000000000000) (-32382706402 / 1000000000000))
    | 20 => (orderedInterval (68843657217 / 1000000000000) (68843658211 / 1000000000000), orderedInterval (-17168602670 / 1000000000000) (-17168601676 / 1000000000000))
    | 21 => (orderedInterval (-18896193255 / 1000000000000) (-18896193099 / 1000000000000), orderedInterval (94936923766 / 1000000000000) (94936923921 / 1000000000000))
    | 22 => (orderedInterval (-24441996696 / 1000000000000) (-24441996695 / 1000000000000), orderedInterval (-53261263219 / 1000000000000) (-53261263218 / 1000000000000))
    | 23 => (orderedInterval (44365000045 / 1000000000000) (44365025618 / 1000000000000), orderedInterval (-23582674285 / 1000000000000) (-23582648712 / 1000000000000))
    | 24 => (orderedInterval (54257141208 / 1000000000000) (54257141209 / 1000000000000), orderedInterval (54668756985 / 1000000000000) (54668756986 / 1000000000000))
    | 25 => (orderedInterval (37851191193 / 1000000000000) (37851191235 / 1000000000000), orderedInterval (5750006334 / 1000000000000) (5750006376 / 1000000000000))
    | _ => (orderedInterval (45960371376 / 1000000000000) (45960372911 / 1000000000000), orderedInterval (-9179924626 / 1000000000000) (-9179923091 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (21974107392 / 1000000000000) (21974109151 / 1000000000000)
      | 1 => orderedInterval (-4015197511 / 1000000000000) (-4015196445 / 1000000000000)
      | 2 => orderedInterval (1964397711 / 1000000000000) (1964397799 / 1000000000000)
      | 3 => orderedInterval (807490976 / 1000000000000) (807491288 / 1000000000000)
      | 4 => orderedInterval (-1955282389 / 1000000000000) (-1955281587 / 1000000000000)
      | 5 => orderedInterval (-708974389 / 1000000000000) (-708972053 / 1000000000000)
      | 6 => orderedInterval (-6591737921 / 1000000000000) (-6591734257 / 1000000000000)
      | 7 => orderedInterval (-2496652823 / 1000000000000) (-2496650831 / 1000000000000)
      | _ => orderedInterval (-11377459566 / 1000000000000) (-11377459209 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-7825253555 / 1000000000000) (-7825251595 / 1000000000000)
      | 1 => orderedInterval (1966897903 / 1000000000000) (1966899561 / 1000000000000)
      | 2 => orderedInterval (919678149 / 1000000000000) (919678280 / 1000000000000)
      | 3 => orderedInterval (452230587 / 1000000000000) (452231279 / 1000000000000)
      | 4 => orderedInterval (5765286436 / 1000000000000) (5765287665 / 1000000000000)
      | 5 => orderedInterval (4383297920 / 1000000000000) (4383302215 / 1000000000000)
      | 6 => orderedInterval (-4231778050 / 1000000000000) (-4231774880 / 1000000000000)
      | 7 => orderedInterval (2401006442 / 1000000000000) (2401008588 / 1000000000000)
      | _ => orderedInterval (1419654001 / 1000000000000) (1419654456 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-22711943373 / 1000000000000) (-22711941164 / 1000000000000)
      | 1 => orderedInterval (5359992104 / 1000000000000) (5359994704 / 1000000000000)
      | 2 => orderedInterval (-5872291602 / 1000000000000) (-5872291403 / 1000000000000)
      | 3 => orderedInterval (1517722529 / 1000000000000) (1517724088 / 1000000000000)
      | 4 => orderedInterval (3275503142 / 1000000000000) (3275505029 / 1000000000000)
      | 5 => orderedInterval (2870856608 / 1000000000000) (2870864533 / 1000000000000)
      | 6 => orderedInterval (7835243764 / 1000000000000) (7835246526 / 1000000000000)
      | 7 => orderedInterval (3591019544 / 1000000000000) (3591021873 / 1000000000000)
      | _ => orderedInterval (23880547865 / 1000000000000) (23880548458 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (8786457010 / 1000000000000) (8786459506 / 1000000000000)
      | 1 => orderedInterval (-8018555377 / 1000000000000) (-8018551305 / 1000000000000)
      | 2 => orderedInterval (-4204970945 / 1000000000000) (-4204970641 / 1000000000000)
      | 3 => orderedInterval (9665837403 / 1000000000000) (9665840926 / 1000000000000)
      | 4 => orderedInterval (-15192739922 / 1000000000000) (-15192737028 / 1000000000000)
      | 5 => orderedInterval (-8895189790 / 1000000000000) (-8895175184 / 1000000000000)
      | 6 => orderedInterval (4633490007 / 1000000000000) (4633492403 / 1000000000000)
      | 7 => orderedInterval (-2860867464 / 1000000000000) (-2860864947 / 1000000000000)
      | _ => orderedInterval (-424631325 / 1000000000000) (-424630542 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (23765708545 / 1000000000000) (23765711393 / 1000000000000)
      | 1 => orderedInterval (-12172488322 / 1000000000000) (-12172481925 / 1000000000000)
      | 2 => orderedInterval (19139602597 / 1000000000000) (19139603069 / 1000000000000)
      | 3 => orderedInterval (-12593501419 / 1000000000000) (-12593493402 / 1000000000000)
      | 4 => orderedInterval (-1777952608 / 1000000000000) (-1777948149 / 1000000000000)
      | 5 => orderedInterval (-10263112257 / 1000000000000) (-10263085257 / 1000000000000)
      | 6 => orderedInterval (-8139360067 / 1000000000000) (-8139357975 / 1000000000000)
      | 7 => orderedInterval (-4411102701 / 1000000000000) (-4411099968 / 1000000000000)
      | _ => orderedInterval (-57332726839 / 1000000000000) (-57332725775 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-2399308520 / 1000000000000) (-2399296144 / 1000000000000)
    | 1 => orderedInterval (5251019833 / 1000000000000) (5251035569 / 1000000000000)
    | 2 => orderedInterval (19746650581 / 1000000000000) (19746672644 / 1000000000000)
    | 3 => orderedInterval (-16511170403 / 1000000000000) (-16511136812 / 1000000000000)
    | _ => orderedInterval (-63784933071 / 1000000000000) (-63784877989 / 1000000000000)

theorem compactCertificate362_stateChecks0 :
    compactCertificate362.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (467 / 2)) (orderedInterval (50765183487 / 1000000000000) (50765185252 / 1000000000000), orderedInterval (-12328095354 / 1000000000000) (-12328093589 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (687980172669767 / 4000000000000)) (orderedInterval (479488657 / 1000000000000) (479488662 / 1000000000000), orderedInterval (-60838636958 / 1000000000000) (-60838636954 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (222478652396711 / 800000000000)) (orderedInterval (31493899039 / 1000000000000) (31493916812 / 1000000000000), orderedInterval (-36075014110 / 1000000000000) (-36074996337 / 1000000000000))) = true
  rfl'

theorem compactCertificate362_stateChecks1 :
    compactCertificate362.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (200750898538069 / 4000000000000)) (orderedInterval (72996976481 / 1000000000000) (72996976482 / 1000000000000), orderedInterval (85041781337 / 1000000000000) (85041781338 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (539245151422993 / 4000000000000)) (orderedInterval (-33383374537 / 1000000000000) (-33383374536 / 1000000000000), orderedInterval (-59941739232 / 1000000000000) (-59941739231 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1464155484234381 / 4000000000000)) (orderedInterval (28194624418 / 1000000000000) (28194639002 / 1000000000000), orderedInterval (-30767601562 / 1000000000000) (-30767586977 / 1000000000000))) = true
  rfl'

theorem compactCertificate362_stateChecks2 :
    compactCertificate362.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1078490302846453 / 4000000000000)) (orderedInterval (11103446138 / 1000000000000) (11103446139 / 1000000000000), orderedInterval (47285526355 / 1000000000000) (47285526356 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1848011516205769 / 4000000000000)) (orderedInterval (-30701762294 / 1000000000000) (-30701762293 / 1000000000000), orderedInterval (-20832002279 / 1000000000000) (-20832002278 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1361236918644571 / 4000000000000)) (orderedInterval (42098286764 / 1000000000000) (42098289821 / 1000000000000), orderedInterval (-9983648468 / 1000000000000) (-9983645410 / 1000000000000))) = true
  rfl'

theorem compactCertificate362_stateChecks3 :
    compactCertificate362.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2088487490984533 / 4000000000000)) (orderedInterval (34425915409 / 1000000000000) (34425915473 / 1000000000000), orderedInterval (5810769028 / 1000000000000) (5810769091 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1205788815118957 / 4000000000000)) (orderedInterval (27418118264 / 1000000000000) (27418118265 / 1000000000000), orderedInterval (36834406167 / 1000000000000) (36834406168 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2139693412000913 / 4000000000000)) (orderedInterval (34420687986 / 1000000000000) (34420689444 / 1000000000000), orderedInterval (-2340782763 / 1000000000000) (-2340781305 / 1000000000000))) = true
  rfl'

theorem compactCertificate362_stateChecks4 :
    compactCertificate362.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (1999179139220597 / 4000000000000)) (orderedInterval (-31250407676 / 1000000000000) (-31250407675 / 1000000000000), orderedInterval (-17207472699 / 1000000000000) (-17207472698 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1426708566362501 / 4000000000000)) (orderedInterval (-26544414691 / 1000000000000) (-26544406504 / 1000000000000), orderedInterval (32904476749 / 1000000000000) (32904484936 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1617735454268979 / 4000000000000)) (orderedInterval (1844205685 / 1000000000000) (1844205687 / 1000000000000), orderedInterval (-39634352356 / 1000000000000) (-39634352355 / 1000000000000))) = true
  rfl'

theorem compactCertificate362_stateChecks5 :
    compactCertificate362.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1348699164370051 / 4000000000000)) (orderedInterval (-42221156449 / 1000000000000) (-42221153200 / 1000000000000), orderedInterval (10332583211 / 1000000000000) (10332586460 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1191616613663071 / 4000000000000)) (orderedInterval (-10890955873 / 1000000000000) (-10890955872 / 1000000000000), orderedInterval (-44908161132 / 1000000000000) (-44908161131 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (345376940128029 / 800000000000)) (orderedInterval (-32989894517 / 1000000000000) (-32989805631 / 1000000000000), orderedInterval (19692114787 / 1000000000000) (19692203672 / 1000000000000))) = true
  rfl'

theorem compactCertificate362_stateChecks6 :
    compactCertificate362.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (955330792586663 / 4000000000000)) (orderedInterval (39009483551 / 1000000000000) (39009483552 / 1000000000000), orderedInterval (33738539250 / 1000000000000) (33738539251 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (809844492874543 / 4000000000000)) (orderedInterval (45859340423 / 1000000000000) (45859403544 / 1000000000000), orderedInterval (-32382769522 / 1000000000000) (-32382706402 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (506763081355429 / 4000000000000)) (orderedInterval (68843657217 / 1000000000000) (68843658211 / 1000000000000), orderedInterval (-17168602670 / 1000000000000) (-17168601676 / 1000000000000))) = true
  rfl'

theorem compactCertificate362_stateChecks7 :
    compactCertificate362.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (272538870570843 / 4000000000000)) (orderedInterval (-18896193255 / 1000000000000) (-18896193099 / 1000000000000), orderedInterval (94936923766 / 1000000000000) (94936923921 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (739996049961529 / 4000000000000)) (orderedInterval (-24441996696 / 1000000000000) (-24441996695 / 1000000000000), orderedInterval (-53261263219 / 1000000000000) (-53261263218 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1010401342014233 / 4000000000000)) (orderedInterval (44365000045 / 1000000000000) (44365025618 / 1000000000000), orderedInterval (-23582674285 / 1000000000000) (-23582648712 / 1000000000000))) = true
  rfl'

theorem compactCertificate362_stateChecks8 :
    compactCertificate362.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (427236918644571 / 4000000000000)) (orderedInterval (54257141208 / 1000000000000) (54257141209 / 1000000000000), orderedInterval (54668756985 / 1000000000000) (54668756986 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1736694354805691 / 4000000000000)) (orderedInterval (37851191193 / 1000000000000) (37851191235 / 1000000000000), orderedInterval (5750006334 / 1000000000000) (5750006376 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1160031343536469 / 4000000000000)) (orderedInterval (45960371376 / 1000000000000) (45960372911 / 1000000000000), orderedInterval (-9179924626 / 1000000000000) (-9179923091 / 1000000000000))) = true
  rfl'

theorem compactCertificate362_states : ∀ j,
    BesselStateValid (compactCertificate362.point j) (compactCertificate362.state j) :=
  compactCertificate362.statesValid_of_checks3 compactCertificate362_stateChecks0
    compactCertificate362_stateChecks1 compactCertificate362_stateChecks2
    compactCertificate362_stateChecks3 compactCertificate362_stateChecks4
    compactCertificate362_stateChecks5 compactCertificate362_stateChecks6
    compactCertificate362_stateChecks7 compactCertificate362_stateChecks8

theorem compactCertificate362_chunkChecks0_0 :
    compactCertificate362.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (467 / 2) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (50765183487 / 1000000000000) (50765185252 / 1000000000000), orderedInterval (-12328095354 / 1000000000000) (-12328093589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (687980172669767 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (479488657 / 1000000000000) (479488662 / 1000000000000), orderedInterval (-60838636958 / 1000000000000) (-60838636954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (222478652396711 / 800000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31493899039 / 1000000000000) (31493916812 / 1000000000000), orderedInterval (-36075014110 / 1000000000000) (-36074996337 / 1000000000000)))) (orderedInterval (21974107392 / 1000000000000) (21974109151 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (200750898538069 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72996976481 / 1000000000000) (72996976482 / 1000000000000), orderedInterval (85041781337 / 1000000000000) (85041781338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (539245151422993 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-33383374537 / 1000000000000) (-33383374536 / 1000000000000), orderedInterval (-59941739232 / 1000000000000) (-59941739231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1464155484234381 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28194624418 / 1000000000000) (28194639002 / 1000000000000), orderedInterval (-30767601562 / 1000000000000) (-30767586977 / 1000000000000)))) (orderedInterval (-4015197511 / 1000000000000) (-4015196445 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1078490302846453 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11103446138 / 1000000000000) (11103446139 / 1000000000000), orderedInterval (47285526355 / 1000000000000) (47285526356 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1848011516205769 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30701762294 / 1000000000000) (-30701762293 / 1000000000000), orderedInterval (-20832002279 / 1000000000000) (-20832002278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1361236918644571 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (42098286764 / 1000000000000) (42098289821 / 1000000000000), orderedInterval (-9983648468 / 1000000000000) (-9983645410 / 1000000000000)))) (orderedInterval (1964397711 / 1000000000000) (1964397799 / 1000000000000))) = true
  rfl'

theorem compactCertificate362_chunkChecks0_1 :
    compactCertificate362.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2088487490984533 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34425915409 / 1000000000000) (34425915473 / 1000000000000), orderedInterval (5810769028 / 1000000000000) (5810769091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1205788815118957 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (27418118264 / 1000000000000) (27418118265 / 1000000000000), orderedInterval (36834406167 / 1000000000000) (36834406168 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2139693412000913 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (34420687986 / 1000000000000) (34420689444 / 1000000000000), orderedInterval (-2340782763 / 1000000000000) (-2340781305 / 1000000000000)))) (orderedInterval (807490976 / 1000000000000) (807491288 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1999179139220597 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31250407676 / 1000000000000) (-31250407675 / 1000000000000), orderedInterval (-17207472699 / 1000000000000) (-17207472698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1426708566362501 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26544414691 / 1000000000000) (-26544406504 / 1000000000000), orderedInterval (32904476749 / 1000000000000) (32904484936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1617735454268979 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1844205685 / 1000000000000) (1844205687 / 1000000000000), orderedInterval (-39634352356 / 1000000000000) (-39634352355 / 1000000000000)))) (orderedInterval (-1955282389 / 1000000000000) (-1955281587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1348699164370051 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42221156449 / 1000000000000) (-42221153200 / 1000000000000), orderedInterval (10332583211 / 1000000000000) (10332586460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1191616613663071 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-10890955873 / 1000000000000) (-10890955872 / 1000000000000), orderedInterval (-44908161132 / 1000000000000) (-44908161131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (345376940128029 / 800000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32989894517 / 1000000000000) (-32989805631 / 1000000000000), orderedInterval (19692114787 / 1000000000000) (19692203672 / 1000000000000)))) (orderedInterval (-708974389 / 1000000000000) (-708972053 / 1000000000000))) = true
  rfl'

theorem compactCertificate362_chunkChecks0_2 :
    compactCertificate362.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (955330792586663 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39009483551 / 1000000000000) (39009483552 / 1000000000000), orderedInterval (33738539250 / 1000000000000) (33738539251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (809844492874543 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45859340423 / 1000000000000) (45859403544 / 1000000000000), orderedInterval (-32382769522 / 1000000000000) (-32382706402 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (506763081355429 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (68843657217 / 1000000000000) (68843658211 / 1000000000000), orderedInterval (-17168602670 / 1000000000000) (-17168601676 / 1000000000000)))) (orderedInterval (-6591737921 / 1000000000000) (-6591734257 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (272538870570843 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18896193255 / 1000000000000) (-18896193099 / 1000000000000), orderedInterval (94936923766 / 1000000000000) (94936923921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (739996049961529 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24441996696 / 1000000000000) (-24441996695 / 1000000000000), orderedInterval (-53261263219 / 1000000000000) (-53261263218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1010401342014233 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44365000045 / 1000000000000) (44365025618 / 1000000000000), orderedInterval (-23582674285 / 1000000000000) (-23582648712 / 1000000000000)))) (orderedInterval (-2496652823 / 1000000000000) (-2496650831 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (427236918644571 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54257141208 / 1000000000000) (54257141209 / 1000000000000), orderedInterval (54668756985 / 1000000000000) (54668756986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1736694354805691 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (37851191193 / 1000000000000) (37851191235 / 1000000000000), orderedInterval (5750006334 / 1000000000000) (5750006376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1160031343536469 / 4000000000000) 0 (IntervalRat.scale (467 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45960371376 / 1000000000000) (45960372911 / 1000000000000), orderedInterval (-9179924626 / 1000000000000) (-9179923091 / 1000000000000)))) (orderedInterval (-11377459566 / 1000000000000) (-11377459209 / 1000000000000))) = true
  rfl'

theorem compactCertificate362_chunkChecks0 :
    compactCertificate362.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate362.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate362_chunkChecks0_0
    compactCertificate362_chunkChecks0_1 compactCertificate362_chunkChecks0_2

theorem compactCertificate362_chunkChecks1_0 :
    compactCertificate362.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (467 / 2) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (50765183487 / 1000000000000) (50765185252 / 1000000000000), orderedInterval (-12328095354 / 1000000000000) (-12328093589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (687980172669767 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (479488657 / 1000000000000) (479488662 / 1000000000000), orderedInterval (-60838636958 / 1000000000000) (-60838636954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (222478652396711 / 800000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31493899039 / 1000000000000) (31493916812 / 1000000000000), orderedInterval (-36075014110 / 1000000000000) (-36074996337 / 1000000000000)))) (orderedInterval (-7825253555 / 1000000000000) (-7825251595 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (200750898538069 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72996976481 / 1000000000000) (72996976482 / 1000000000000), orderedInterval (85041781337 / 1000000000000) (85041781338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (539245151422993 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-33383374537 / 1000000000000) (-33383374536 / 1000000000000), orderedInterval (-59941739232 / 1000000000000) (-59941739231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1464155484234381 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28194624418 / 1000000000000) (28194639002 / 1000000000000), orderedInterval (-30767601562 / 1000000000000) (-30767586977 / 1000000000000)))) (orderedInterval (1966897903 / 1000000000000) (1966899561 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1078490302846453 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11103446138 / 1000000000000) (11103446139 / 1000000000000), orderedInterval (47285526355 / 1000000000000) (47285526356 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1848011516205769 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30701762294 / 1000000000000) (-30701762293 / 1000000000000), orderedInterval (-20832002279 / 1000000000000) (-20832002278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1361236918644571 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (42098286764 / 1000000000000) (42098289821 / 1000000000000), orderedInterval (-9983648468 / 1000000000000) (-9983645410 / 1000000000000)))) (orderedInterval (919678149 / 1000000000000) (919678280 / 1000000000000))) = true
  rfl'

theorem compactCertificate362_chunkChecks1_1 :
    compactCertificate362.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2088487490984533 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34425915409 / 1000000000000) (34425915473 / 1000000000000), orderedInterval (5810769028 / 1000000000000) (5810769091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1205788815118957 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (27418118264 / 1000000000000) (27418118265 / 1000000000000), orderedInterval (36834406167 / 1000000000000) (36834406168 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2139693412000913 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (34420687986 / 1000000000000) (34420689444 / 1000000000000), orderedInterval (-2340782763 / 1000000000000) (-2340781305 / 1000000000000)))) (orderedInterval (452230587 / 1000000000000) (452231279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1999179139220597 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31250407676 / 1000000000000) (-31250407675 / 1000000000000), orderedInterval (-17207472699 / 1000000000000) (-17207472698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1426708566362501 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26544414691 / 1000000000000) (-26544406504 / 1000000000000), orderedInterval (32904476749 / 1000000000000) (32904484936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1617735454268979 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1844205685 / 1000000000000) (1844205687 / 1000000000000), orderedInterval (-39634352356 / 1000000000000) (-39634352355 / 1000000000000)))) (orderedInterval (5765286436 / 1000000000000) (5765287665 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1348699164370051 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42221156449 / 1000000000000) (-42221153200 / 1000000000000), orderedInterval (10332583211 / 1000000000000) (10332586460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1191616613663071 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-10890955873 / 1000000000000) (-10890955872 / 1000000000000), orderedInterval (-44908161132 / 1000000000000) (-44908161131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (345376940128029 / 800000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32989894517 / 1000000000000) (-32989805631 / 1000000000000), orderedInterval (19692114787 / 1000000000000) (19692203672 / 1000000000000)))) (orderedInterval (4383297920 / 1000000000000) (4383302215 / 1000000000000))) = true
  rfl'

theorem compactCertificate362_chunkChecks1_2 :
    compactCertificate362.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (955330792586663 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39009483551 / 1000000000000) (39009483552 / 1000000000000), orderedInterval (33738539250 / 1000000000000) (33738539251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (809844492874543 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45859340423 / 1000000000000) (45859403544 / 1000000000000), orderedInterval (-32382769522 / 1000000000000) (-32382706402 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (506763081355429 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (68843657217 / 1000000000000) (68843658211 / 1000000000000), orderedInterval (-17168602670 / 1000000000000) (-17168601676 / 1000000000000)))) (orderedInterval (-4231778050 / 1000000000000) (-4231774880 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (272538870570843 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18896193255 / 1000000000000) (-18896193099 / 1000000000000), orderedInterval (94936923766 / 1000000000000) (94936923921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (739996049961529 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24441996696 / 1000000000000) (-24441996695 / 1000000000000), orderedInterval (-53261263219 / 1000000000000) (-53261263218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1010401342014233 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44365000045 / 1000000000000) (44365025618 / 1000000000000), orderedInterval (-23582674285 / 1000000000000) (-23582648712 / 1000000000000)))) (orderedInterval (2401006442 / 1000000000000) (2401008588 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (427236918644571 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54257141208 / 1000000000000) (54257141209 / 1000000000000), orderedInterval (54668756985 / 1000000000000) (54668756986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1736694354805691 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (37851191193 / 1000000000000) (37851191235 / 1000000000000), orderedInterval (5750006334 / 1000000000000) (5750006376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1160031343536469 / 4000000000000) 1 (IntervalRat.scale (467 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45960371376 / 1000000000000) (45960372911 / 1000000000000), orderedInterval (-9179924626 / 1000000000000) (-9179923091 / 1000000000000)))) (orderedInterval (1419654001 / 1000000000000) (1419654456 / 1000000000000))) = true
  rfl'

theorem compactCertificate362_chunkChecks1 :
    compactCertificate362.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate362.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate362_chunkChecks1_0
    compactCertificate362_chunkChecks1_1 compactCertificate362_chunkChecks1_2

theorem compactCertificate362_chunkChecks2_0 :
    compactCertificate362.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (467 / 2) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (50765183487 / 1000000000000) (50765185252 / 1000000000000), orderedInterval (-12328095354 / 1000000000000) (-12328093589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (687980172669767 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (479488657 / 1000000000000) (479488662 / 1000000000000), orderedInterval (-60838636958 / 1000000000000) (-60838636954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (222478652396711 / 800000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31493899039 / 1000000000000) (31493916812 / 1000000000000), orderedInterval (-36075014110 / 1000000000000) (-36074996337 / 1000000000000)))) (orderedInterval (-22711943373 / 1000000000000) (-22711941164 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (200750898538069 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72996976481 / 1000000000000) (72996976482 / 1000000000000), orderedInterval (85041781337 / 1000000000000) (85041781338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (539245151422993 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-33383374537 / 1000000000000) (-33383374536 / 1000000000000), orderedInterval (-59941739232 / 1000000000000) (-59941739231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1464155484234381 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28194624418 / 1000000000000) (28194639002 / 1000000000000), orderedInterval (-30767601562 / 1000000000000) (-30767586977 / 1000000000000)))) (orderedInterval (5359992104 / 1000000000000) (5359994704 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1078490302846453 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11103446138 / 1000000000000) (11103446139 / 1000000000000), orderedInterval (47285526355 / 1000000000000) (47285526356 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1848011516205769 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30701762294 / 1000000000000) (-30701762293 / 1000000000000), orderedInterval (-20832002279 / 1000000000000) (-20832002278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1361236918644571 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (42098286764 / 1000000000000) (42098289821 / 1000000000000), orderedInterval (-9983648468 / 1000000000000) (-9983645410 / 1000000000000)))) (orderedInterval (-5872291602 / 1000000000000) (-5872291403 / 1000000000000))) = true
  rfl'

theorem compactCertificate362_chunkChecks2_1 :
    compactCertificate362.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2088487490984533 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34425915409 / 1000000000000) (34425915473 / 1000000000000), orderedInterval (5810769028 / 1000000000000) (5810769091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1205788815118957 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (27418118264 / 1000000000000) (27418118265 / 1000000000000), orderedInterval (36834406167 / 1000000000000) (36834406168 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2139693412000913 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (34420687986 / 1000000000000) (34420689444 / 1000000000000), orderedInterval (-2340782763 / 1000000000000) (-2340781305 / 1000000000000)))) (orderedInterval (1517722529 / 1000000000000) (1517724088 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1999179139220597 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31250407676 / 1000000000000) (-31250407675 / 1000000000000), orderedInterval (-17207472699 / 1000000000000) (-17207472698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1426708566362501 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26544414691 / 1000000000000) (-26544406504 / 1000000000000), orderedInterval (32904476749 / 1000000000000) (32904484936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1617735454268979 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1844205685 / 1000000000000) (1844205687 / 1000000000000), orderedInterval (-39634352356 / 1000000000000) (-39634352355 / 1000000000000)))) (orderedInterval (3275503142 / 1000000000000) (3275505029 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1348699164370051 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42221156449 / 1000000000000) (-42221153200 / 1000000000000), orderedInterval (10332583211 / 1000000000000) (10332586460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1191616613663071 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-10890955873 / 1000000000000) (-10890955872 / 1000000000000), orderedInterval (-44908161132 / 1000000000000) (-44908161131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (345376940128029 / 800000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32989894517 / 1000000000000) (-32989805631 / 1000000000000), orderedInterval (19692114787 / 1000000000000) (19692203672 / 1000000000000)))) (orderedInterval (2870856608 / 1000000000000) (2870864533 / 1000000000000))) = true
  rfl'

theorem compactCertificate362_chunkChecks2_2 :
    compactCertificate362.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (955330792586663 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39009483551 / 1000000000000) (39009483552 / 1000000000000), orderedInterval (33738539250 / 1000000000000) (33738539251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (809844492874543 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45859340423 / 1000000000000) (45859403544 / 1000000000000), orderedInterval (-32382769522 / 1000000000000) (-32382706402 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (506763081355429 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (68843657217 / 1000000000000) (68843658211 / 1000000000000), orderedInterval (-17168602670 / 1000000000000) (-17168601676 / 1000000000000)))) (orderedInterval (7835243764 / 1000000000000) (7835246526 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (272538870570843 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18896193255 / 1000000000000) (-18896193099 / 1000000000000), orderedInterval (94936923766 / 1000000000000) (94936923921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (739996049961529 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24441996696 / 1000000000000) (-24441996695 / 1000000000000), orderedInterval (-53261263219 / 1000000000000) (-53261263218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1010401342014233 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44365000045 / 1000000000000) (44365025618 / 1000000000000), orderedInterval (-23582674285 / 1000000000000) (-23582648712 / 1000000000000)))) (orderedInterval (3591019544 / 1000000000000) (3591021873 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (427236918644571 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54257141208 / 1000000000000) (54257141209 / 1000000000000), orderedInterval (54668756985 / 1000000000000) (54668756986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1736694354805691 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (37851191193 / 1000000000000) (37851191235 / 1000000000000), orderedInterval (5750006334 / 1000000000000) (5750006376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1160031343536469 / 4000000000000) 2 (IntervalRat.scale (467 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45960371376 / 1000000000000) (45960372911 / 1000000000000), orderedInterval (-9179924626 / 1000000000000) (-9179923091 / 1000000000000)))) (orderedInterval (23880547865 / 1000000000000) (23880548458 / 1000000000000))) = true
  rfl'

theorem compactCertificate362_chunkChecks2 :
    compactCertificate362.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate362.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate362_chunkChecks2_0
    compactCertificate362_chunkChecks2_1 compactCertificate362_chunkChecks2_2

theorem compactCertificate362_chunkChecks3_0 :
    compactCertificate362.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (467 / 2) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (50765183487 / 1000000000000) (50765185252 / 1000000000000), orderedInterval (-12328095354 / 1000000000000) (-12328093589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (687980172669767 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (479488657 / 1000000000000) (479488662 / 1000000000000), orderedInterval (-60838636958 / 1000000000000) (-60838636954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (222478652396711 / 800000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31493899039 / 1000000000000) (31493916812 / 1000000000000), orderedInterval (-36075014110 / 1000000000000) (-36074996337 / 1000000000000)))) (orderedInterval (8786457010 / 1000000000000) (8786459506 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (200750898538069 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72996976481 / 1000000000000) (72996976482 / 1000000000000), orderedInterval (85041781337 / 1000000000000) (85041781338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (539245151422993 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-33383374537 / 1000000000000) (-33383374536 / 1000000000000), orderedInterval (-59941739232 / 1000000000000) (-59941739231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1464155484234381 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28194624418 / 1000000000000) (28194639002 / 1000000000000), orderedInterval (-30767601562 / 1000000000000) (-30767586977 / 1000000000000)))) (orderedInterval (-8018555377 / 1000000000000) (-8018551305 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1078490302846453 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11103446138 / 1000000000000) (11103446139 / 1000000000000), orderedInterval (47285526355 / 1000000000000) (47285526356 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1848011516205769 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30701762294 / 1000000000000) (-30701762293 / 1000000000000), orderedInterval (-20832002279 / 1000000000000) (-20832002278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1361236918644571 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (42098286764 / 1000000000000) (42098289821 / 1000000000000), orderedInterval (-9983648468 / 1000000000000) (-9983645410 / 1000000000000)))) (orderedInterval (-4204970945 / 1000000000000) (-4204970641 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate362_chunkChecks3_1 :
    compactCertificate362.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2088487490984533 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34425915409 / 1000000000000) (34425915473 / 1000000000000), orderedInterval (5810769028 / 1000000000000) (5810769091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1205788815118957 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (27418118264 / 1000000000000) (27418118265 / 1000000000000), orderedInterval (36834406167 / 1000000000000) (36834406168 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2139693412000913 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (34420687986 / 1000000000000) (34420689444 / 1000000000000), orderedInterval (-2340782763 / 1000000000000) (-2340781305 / 1000000000000)))) (orderedInterval (9665837403 / 1000000000000) (9665840926 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1999179139220597 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31250407676 / 1000000000000) (-31250407675 / 1000000000000), orderedInterval (-17207472699 / 1000000000000) (-17207472698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1426708566362501 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26544414691 / 1000000000000) (-26544406504 / 1000000000000), orderedInterval (32904476749 / 1000000000000) (32904484936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1617735454268979 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1844205685 / 1000000000000) (1844205687 / 1000000000000), orderedInterval (-39634352356 / 1000000000000) (-39634352355 / 1000000000000)))) (orderedInterval (-15192739922 / 1000000000000) (-15192737028 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1348699164370051 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42221156449 / 1000000000000) (-42221153200 / 1000000000000), orderedInterval (10332583211 / 1000000000000) (10332586460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1191616613663071 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-10890955873 / 1000000000000) (-10890955872 / 1000000000000), orderedInterval (-44908161132 / 1000000000000) (-44908161131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (345376940128029 / 800000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32989894517 / 1000000000000) (-32989805631 / 1000000000000), orderedInterval (19692114787 / 1000000000000) (19692203672 / 1000000000000)))) (orderedInterval (-8895189790 / 1000000000000) (-8895175184 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate362_chunkChecks3_2 :
    compactCertificate362.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (955330792586663 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39009483551 / 1000000000000) (39009483552 / 1000000000000), orderedInterval (33738539250 / 1000000000000) (33738539251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (809844492874543 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45859340423 / 1000000000000) (45859403544 / 1000000000000), orderedInterval (-32382769522 / 1000000000000) (-32382706402 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (506763081355429 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (68843657217 / 1000000000000) (68843658211 / 1000000000000), orderedInterval (-17168602670 / 1000000000000) (-17168601676 / 1000000000000)))) (orderedInterval (4633490007 / 1000000000000) (4633492403 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (272538870570843 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18896193255 / 1000000000000) (-18896193099 / 1000000000000), orderedInterval (94936923766 / 1000000000000) (94936923921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (739996049961529 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24441996696 / 1000000000000) (-24441996695 / 1000000000000), orderedInterval (-53261263219 / 1000000000000) (-53261263218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1010401342014233 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44365000045 / 1000000000000) (44365025618 / 1000000000000), orderedInterval (-23582674285 / 1000000000000) (-23582648712 / 1000000000000)))) (orderedInterval (-2860867464 / 1000000000000) (-2860864947 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (427236918644571 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54257141208 / 1000000000000) (54257141209 / 1000000000000), orderedInterval (54668756985 / 1000000000000) (54668756986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1736694354805691 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (37851191193 / 1000000000000) (37851191235 / 1000000000000), orderedInterval (5750006334 / 1000000000000) (5750006376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1160031343536469 / 4000000000000) 3 (IntervalRat.scale (467 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45960371376 / 1000000000000) (45960372911 / 1000000000000), orderedInterval (-9179924626 / 1000000000000) (-9179923091 / 1000000000000)))) (orderedInterval (-424631325 / 1000000000000) (-424630542 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate362_chunkChecks3 :
    compactCertificate362.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate362.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate362_chunkChecks3_0
    compactCertificate362_chunkChecks3_1 compactCertificate362_chunkChecks3_2

theorem compactCertificate362_chunkChecks4_0 :
    compactCertificate362.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (467 / 2) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (50765183487 / 1000000000000) (50765185252 / 1000000000000), orderedInterval (-12328095354 / 1000000000000) (-12328093589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (687980172669767 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (479488657 / 1000000000000) (479488662 / 1000000000000), orderedInterval (-60838636958 / 1000000000000) (-60838636954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (222478652396711 / 800000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31493899039 / 1000000000000) (31493916812 / 1000000000000), orderedInterval (-36075014110 / 1000000000000) (-36074996337 / 1000000000000)))) (orderedInterval (23765708545 / 1000000000000) (23765711393 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (200750898538069 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72996976481 / 1000000000000) (72996976482 / 1000000000000), orderedInterval (85041781337 / 1000000000000) (85041781338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (539245151422993 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-33383374537 / 1000000000000) (-33383374536 / 1000000000000), orderedInterval (-59941739232 / 1000000000000) (-59941739231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1464155484234381 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28194624418 / 1000000000000) (28194639002 / 1000000000000), orderedInterval (-30767601562 / 1000000000000) (-30767586977 / 1000000000000)))) (orderedInterval (-12172488322 / 1000000000000) (-12172481925 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1078490302846453 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (11103446138 / 1000000000000) (11103446139 / 1000000000000), orderedInterval (47285526355 / 1000000000000) (47285526356 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1848011516205769 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30701762294 / 1000000000000) (-30701762293 / 1000000000000), orderedInterval (-20832002279 / 1000000000000) (-20832002278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1361236918644571 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (42098286764 / 1000000000000) (42098289821 / 1000000000000), orderedInterval (-9983648468 / 1000000000000) (-9983645410 / 1000000000000)))) (orderedInterval (19139602597 / 1000000000000) (19139603069 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate362_chunkChecks4_1 :
    compactCertificate362.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2088487490984533 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (34425915409 / 1000000000000) (34425915473 / 1000000000000), orderedInterval (5810769028 / 1000000000000) (5810769091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1205788815118957 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (27418118264 / 1000000000000) (27418118265 / 1000000000000), orderedInterval (36834406167 / 1000000000000) (36834406168 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2139693412000913 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (34420687986 / 1000000000000) (34420689444 / 1000000000000), orderedInterval (-2340782763 / 1000000000000) (-2340781305 / 1000000000000)))) (orderedInterval (-12593501419 / 1000000000000) (-12593493402 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1999179139220597 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31250407676 / 1000000000000) (-31250407675 / 1000000000000), orderedInterval (-17207472699 / 1000000000000) (-17207472698 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1426708566362501 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26544414691 / 1000000000000) (-26544406504 / 1000000000000), orderedInterval (32904476749 / 1000000000000) (32904484936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1617735454268979 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1844205685 / 1000000000000) (1844205687 / 1000000000000), orderedInterval (-39634352356 / 1000000000000) (-39634352355 / 1000000000000)))) (orderedInterval (-1777952608 / 1000000000000) (-1777948149 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1348699164370051 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42221156449 / 1000000000000) (-42221153200 / 1000000000000), orderedInterval (10332583211 / 1000000000000) (10332586460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1191616613663071 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-10890955873 / 1000000000000) (-10890955872 / 1000000000000), orderedInterval (-44908161132 / 1000000000000) (-44908161131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (345376940128029 / 800000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32989894517 / 1000000000000) (-32989805631 / 1000000000000), orderedInterval (19692114787 / 1000000000000) (19692203672 / 1000000000000)))) (orderedInterval (-10263112257 / 1000000000000) (-10263085257 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate362_chunkChecks4_2 :
    compactCertificate362.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (955330792586663 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39009483551 / 1000000000000) (39009483552 / 1000000000000), orderedInterval (33738539250 / 1000000000000) (33738539251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (809844492874543 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45859340423 / 1000000000000) (45859403544 / 1000000000000), orderedInterval (-32382769522 / 1000000000000) (-32382706402 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (506763081355429 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (68843657217 / 1000000000000) (68843658211 / 1000000000000), orderedInterval (-17168602670 / 1000000000000) (-17168601676 / 1000000000000)))) (orderedInterval (-8139360067 / 1000000000000) (-8139357975 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (272538870570843 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-18896193255 / 1000000000000) (-18896193099 / 1000000000000), orderedInterval (94936923766 / 1000000000000) (94936923921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (739996049961529 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-24441996696 / 1000000000000) (-24441996695 / 1000000000000), orderedInterval (-53261263219 / 1000000000000) (-53261263218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1010401342014233 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (44365000045 / 1000000000000) (44365025618 / 1000000000000), orderedInterval (-23582674285 / 1000000000000) (-23582648712 / 1000000000000)))) (orderedInterval (-4411102701 / 1000000000000) (-4411099968 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (427236918644571 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54257141208 / 1000000000000) (54257141209 / 1000000000000), orderedInterval (54668756985 / 1000000000000) (54668756986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1736694354805691 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (37851191193 / 1000000000000) (37851191235 / 1000000000000), orderedInterval (5750006334 / 1000000000000) (5750006376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1160031343536469 / 4000000000000) 4 (IntervalRat.scale (467 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45960371376 / 1000000000000) (45960372911 / 1000000000000), orderedInterval (-9179924626 / 1000000000000) (-9179923091 / 1000000000000)))) (orderedInterval (-57332726839 / 1000000000000) (-57332725775 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate362_chunkChecks4 :
    compactCertificate362.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate362.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate362_chunkChecks4_0
    compactCertificate362_chunkChecks4_1 compactCertificate362_chunkChecks4_2

theorem compactCertificate362_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate362.chunkCheck r b = true :=
  compactCertificate362.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate362_chunkChecks0
    · exact compactCertificate362_chunkChecks1
    · exact compactCertificate362_chunkChecks2
    · exact compactCertificate362_chunkChecks3
    · exact compactCertificate362_chunkChecks4)

theorem compactCertificate362_coefficient0 :
    compactCertificate362.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate362_coefficient1 :
    compactCertificate362.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate362_coefficient2 :
    compactCertificate362.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate362_coefficient3 :
    compactCertificate362.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate362_coefficient4 :
    compactCertificate362.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate362_coefficients : ∀ r : Fin 5,
    compactCertificate362.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate362_coefficient0
  · exact compactCertificate362_coefficient1
  · exact compactCertificate362_coefficient2
  · exact compactCertificate362_coefficient3
  · exact compactCertificate362_coefficient4

theorem compactCertificate362_lower : (1 : ℚ) ≤ compactCertificate362.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate362, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate362_proves {t : ℝ} (ht : t ∈ compactCertificate362.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate362.proves compactCertificate362_states compactCertificate362_chunks
    compactCertificate362_coefficients compactCertificate362_lower ht

end Erdos232
