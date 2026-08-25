/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate365 : CompactCertificate where
  left := 236
  right := 237
  center := 473 / 2
  grid := fun i =>
    match i.val with
    | 0 => 75
    | 1 => 55
    | 2 => 90
    | 3 => 16
    | 4 => 43
    | 5 => 118
    | 6 => 87
    | 7 => 149
    | 8 => 110
    | 9 => 168
    | 10 => 97
    | 11 => 173
    | 12 => 161
    | 13 => 115
    | 14 => 130
    | 15 => 109
    | 16 => 96
    | 17 => 139
    | 18 => 77
    | 19 => 65
    | 20 => 41
    | 21 => 22
    | 22 => 60
    | 23 => 81
    | 24 => 34
    | 25 => 140
    | _ => 94
  point := fun i =>
    match i.val with
    | 0 => 473 / 2
    | 1 => 696819318357173 / 4000000000000
    | 2 => 225337050500309 / 800000000000
    | 3 => 203330139204511 / 4000000000000
    | 4 => 546173354653267 / 4000000000000
    | 5 => 1482966903732039 / 4000000000000
    | 6 => 1092346709307007 / 4000000000000
    | 7 => 1871754704850811 / 4000000000000
    | 8 => 1378726043937649 / 4000000000000
    | 9 => 2115320306714527 / 4000000000000
    | 10 => 1221280748503783 / 4000000000000
    | 11 => 2167184119649747 / 4000000000000
    | 12 => 2024864524306943 / 4000000000000
    | 13 => 1445038869142319 / 4000000000000
    | 14 => 1638520063959801 / 4000000000000
    | 15 => 1366027205025769 / 4000000000000
    | 16 => 1206926463089149 / 4000000000000
    | 17 => 349814331221751 / 800000000000
    | 18 => 967604849878997 / 4000000000000
    | 19 => 820249347172717 / 4000000000000
    | 20 => 513273956062351 / 4000000000000
    | 21 => 276040440642417 / 4000000000000
    | 22 => 749503493858251 / 4000000000000
    | 23 => 1023382943838827 / 4000000000000
    | 24 => 432726043937649 / 4000000000000
    | 25 => 1759007344374929 / 4000000000000
    | _ => 1174935386494111 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-51650771570 / 1000000000000) (-51650771248 / 1000000000000), orderedInterval (5011265004 / 1000000000000) (5011265326 / 1000000000000))
    | 1 => (orderedInterval (-48806884073 / 1000000000000) (-48806818897 / 1000000000000), orderedInterval (35809629538 / 1000000000000) (35809694714 / 1000000000000))
    | 2 => (orderedInterval (-13460980726 / 1000000000000) (-13460980602 / 1000000000000), orderedInterval (45619467359 / 1000000000000) (45619467483 / 1000000000000))
    | 3 => (orderedInterval (109190435158 / 1000000000000) (109190435159 / 1000000000000), orderedInterval (23436608718 / 1000000000000) (23436608719 / 1000000000000))
    | 4 => (orderedInterval (-53582400831 / 1000000000000) (-53582324429 / 1000000000000), orderedInterval (42520200676 / 1000000000000) (42520277079 / 1000000000000))
    | 5 => (orderedInterval (30265170829 / 1000000000000) (30265170830 / 1000000000000), orderedInterval (28264147182 / 1000000000000) (28264147183 / 1000000000000))
    | 6 => (orderedInterval (-25362338217 / 1000000000000) (-25362338216 / 1000000000000), orderedInterval (-41038280533 / 1000000000000) (-41038280532 / 1000000000000))
    | 7 => (orderedInterval (-21625997656 / 1000000000000) (-21625997655 / 1000000000000), orderedInterval (-29856540815 / 1000000000000) (-29856540814 / 1000000000000))
    | 8 => (orderedInterval (-4660016487 / 1000000000000) (-4660016482 / 1000000000000), orderedInterval (42729890584 / 1000000000000) (42729890589 / 1000000000000))
    | 9 => (orderedInterval (33557751275 / 1000000000000) (33557762031 / 1000000000000), orderedInterval (-8846675489 / 1000000000000) (-8846664733 / 1000000000000))
    | 10 => (orderedInterval (-44751551154 / 1000000000000) (-44751551147 / 1000000000000), orderedInterval (-9003339039 / 1000000000000) (-9003339031 / 1000000000000))
    | 11 => (orderedInterval (27153880753 / 1000000000000) (27153912542 / 1000000000000), orderedInterval (-20945953388 / 1000000000000) (-20945921600 / 1000000000000))
    | 12 => (orderedInterval (-33114761054 / 1000000000000) (-33114761051 / 1000000000000), orderedInterval (-12656532147 / 1000000000000) (-12656532145 / 1000000000000))
    | 13 => (orderedInterval (-28969180969 / 1000000000000) (-28969180968 / 1000000000000), orderedInterval (-30340960326 / 1000000000000) (-30340960325 / 1000000000000))
    | 14 => (orderedInterval (35713289311 / 1000000000000) (35713322899 / 1000000000000), orderedInterval (-16737696951 / 1000000000000) (-16737663362 / 1000000000000))
    | 15 => (orderedInterval (6100368565 / 1000000000000) (6100368574 / 1000000000000), orderedInterval (-42751615554 / 1000000000000) (-42751615545 / 1000000000000))
    | 16 => (orderedInterval (36647598776 / 1000000000000) (36647598777 / 1000000000000), orderedInterval (27631151744 / 1000000000000) (27631151745 / 1000000000000))
    | 17 => (orderedInterval (-37402140851 / 1000000000000) (-37402140830 / 1000000000000), orderedInterval (-7505889062 / 1000000000000) (-7505889041 / 1000000000000))
    | 18 => (orderedInterval (-36204455745 / 1000000000000) (-36204455744 / 1000000000000), orderedInterval (-36270344719 / 1000000000000) (-36270344718 / 1000000000000))
    | 19 => (orderedInterval (-55570511410 / 1000000000000) (-55570511214 / 1000000000000), orderedInterval (4188570852 / 1000000000000) (4188571048 / 1000000000000))
    | 20 => (orderedInterval (-20654624159 / 1000000000000) (-20654624158 / 1000000000000), orderedInterval (-67259441408 / 1000000000000) (-67259441407 / 1000000000000))
    | 21 => (orderedInterval (60292659481 / 1000000000000) (60292659482 / 1000000000000), orderedInterval (74328605558 / 1000000000000) (74328605559 / 1000000000000))
    | 22 => (orderedInterval (-19160948684 / 1000000000000) (-19160948245 / 1000000000000), orderedInterval (55100399748 / 1000000000000) (55100400187 / 1000000000000))
    | 23 => (orderedInterval (-41426207798 / 1000000000000) (-41426142109 / 1000000000000), orderedInterval (27868791895 / 1000000000000) (27868857584 / 1000000000000))
    | 24 => (orderedInterval (64132443711 / 1000000000000) (64132474794 / 1000000000000), orderedInterval (-42388460072 / 1000000000000) (-42388428990 / 1000000000000))
    | 25 => (orderedInterval (24915815353 / 1000000000000) (24915815354 / 1000000000000), orderedInterval (28727224906 / 1000000000000) (28727224907 / 1000000000000))
    | _ => (orderedInterval (-33099395939 / 1000000000000) (-33099363511 / 1000000000000), orderedInterval (32794169451 / 1000000000000) (32794201880 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-21717248889 / 1000000000000) (-21717248130 / 1000000000000)
      | 1 => orderedInterval (-5292565958 / 1000000000000) (-5292563140 / 1000000000000)
      | 2 => orderedInterval (554408882 / 1000000000000) (554408896 / 1000000000000)
      | 3 => orderedInterval (-5418446724 / 1000000000000) (-5418440199 / 1000000000000)
      | 4 => orderedInterval (-2322315148 / 1000000000000) (-2322314949 / 1000000000000)
      | 5 => orderedInterval (-2984417811 / 1000000000000) (-2984417787 / 1000000000000)
      | 6 => orderedInterval (8261690413 / 1000000000000) (8261690484 / 1000000000000)
      | 7 => orderedInterval (2496243482 / 1000000000000) (2496248555 / 1000000000000)
      | _ => orderedInterval (4568738349 / 1000000000000) (4568744687 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (5420382128 / 1000000000000) (5420382731 / 1000000000000)
      | 1 => orderedInterval (-2308120192 / 1000000000000) (-2308118548 / 1000000000000)
      | 2 => orderedInterval (3327163129 / 1000000000000) (3327163153 / 1000000000000)
      | 3 => orderedInterval (-4167550646 / 1000000000000) (-4167535825 / 1000000000000)
      | 4 => orderedInterval (-3746887157 / 1000000000000) (-3746886816 / 1000000000000)
      | 5 => orderedInterval (-3085580270 / 1000000000000) (-3085580235 / 1000000000000)
      | 6 => orderedInterval (4538196742 / 1000000000000) (4538196807 / 1000000000000)
      | 7 => orderedInterval (-3701440181 / 1000000000000) (-3701434701 / 1000000000000)
      | _ => orderedInterval (-12107157967 / 1000000000000) (-12107150232 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (21816857070 / 1000000000000) (21816857562 / 1000000000000)
      | 1 => orderedInterval (6003868274 / 1000000000000) (6003869256 / 1000000000000)
      | 2 => orderedInterval (-2386179878 / 1000000000000) (-2386179836 / 1000000000000)
      | 3 => orderedInterval (15099391197 / 1000000000000) (15099424950 / 1000000000000)
      | 4 => orderedInterval (4211044854 / 1000000000000) (4211045442 / 1000000000000)
      | 5 => orderedInterval (6553524328 / 1000000000000) (6553524379 / 1000000000000)
      | 6 => orderedInterval (-8242155904 / 1000000000000) (-8242155843 / 1000000000000)
      | 7 => orderedInterval (-3877935087 / 1000000000000) (-3877929140 / 1000000000000)
      | _ => orderedInterval (-2597255253 / 1000000000000) (-2597245659 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-6734346216 / 1000000000000) (-6734345806 / 1000000000000)
      | 1 => orderedInterval (7418716308 / 1000000000000) (7418716917 / 1000000000000)
      | 2 => orderedInterval (-10319970453 / 1000000000000) (-10319970377 / 1000000000000)
      | 3 => orderedInterval (19596101711 / 1000000000000) (19596178464 / 1000000000000)
      | 4 => orderedInterval (7527536266 / 1000000000000) (7527537281 / 1000000000000)
      | 5 => orderedInterval (5957082258 / 1000000000000) (5957082338 / 1000000000000)
      | 6 => orderedInterval (-5666619939 / 1000000000000) (-5666619880 / 1000000000000)
      | 7 => orderedInterval (3376135310 / 1000000000000) (3376141740 / 1000000000000)
      | _ => orderedInterval (26857142875 / 1000000000000) (26857154801 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-22138456011 / 1000000000000) (-22138455657 / 1000000000000)
      | 1 => orderedInterval (-13275573670 / 1000000000000) (-13275573252 / 1000000000000)
      | 2 => orderedInterval (9802090750 / 1000000000000) (9802090889 / 1000000000000)
      | 3 => orderedInterval (-52125893823 / 1000000000000) (-52125718907 / 1000000000000)
      | 4 => orderedInterval (-4056193720 / 1000000000000) (-4056191958 / 1000000000000)
      | 5 => orderedInterval (-16491504928 / 1000000000000) (-16491504801 / 1000000000000)
      | 6 => orderedInterval (8103320469 / 1000000000000) (8103320526 / 1000000000000)
      | 7 => orderedInterval (4482816900 / 1000000000000) (4482823880 / 1000000000000)
      | _ => orderedInterval (-9677196483 / 1000000000000) (-9677181561 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-21853913404 / 1000000000000) (-21853891583 / 1000000000000)
    | 1 => orderedInterval (-15830994414 / 1000000000000) (-15830963666 / 1000000000000)
    | 2 => orderedInterval (36581159601 / 1000000000000) (36581211111 / 1000000000000)
    | 3 => orderedInterval (48011778120 / 1000000000000) (48011875478 / 1000000000000)
    | _ => orderedInterval (-95376590516 / 1000000000000) (-95376390841 / 1000000000000)

theorem compactCertificate365_stateChecks0 :
    compactCertificate365.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (473 / 2)) (orderedInterval (-51650771570 / 1000000000000) (-51650771248 / 1000000000000), orderedInterval (5011265004 / 1000000000000) (5011265326 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (696819318357173 / 4000000000000)) (orderedInterval (-48806884073 / 1000000000000) (-48806818897 / 1000000000000), orderedInterval (35809629538 / 1000000000000) (35809694714 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (225337050500309 / 800000000000)) (orderedInterval (-13460980726 / 1000000000000) (-13460980602 / 1000000000000), orderedInterval (45619467359 / 1000000000000) (45619467483 / 1000000000000))) = true
  rfl'

theorem compactCertificate365_stateChecks1 :
    compactCertificate365.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (203330139204511 / 4000000000000)) (orderedInterval (109190435158 / 1000000000000) (109190435159 / 1000000000000), orderedInterval (23436608718 / 1000000000000) (23436608719 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (546173354653267 / 4000000000000)) (orderedInterval (-53582400831 / 1000000000000) (-53582324429 / 1000000000000), orderedInterval (42520200676 / 1000000000000) (42520277079 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1482966903732039 / 4000000000000)) (orderedInterval (30265170829 / 1000000000000) (30265170830 / 1000000000000), orderedInterval (28264147182 / 1000000000000) (28264147183 / 1000000000000))) = true
  rfl'

theorem compactCertificate365_stateChecks2 :
    compactCertificate365.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1092346709307007 / 4000000000000)) (orderedInterval (-25362338217 / 1000000000000) (-25362338216 / 1000000000000), orderedInterval (-41038280533 / 1000000000000) (-41038280532 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1871754704850811 / 4000000000000)) (orderedInterval (-21625997656 / 1000000000000) (-21625997655 / 1000000000000), orderedInterval (-29856540815 / 1000000000000) (-29856540814 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1378726043937649 / 4000000000000)) (orderedInterval (-4660016487 / 1000000000000) (-4660016482 / 1000000000000), orderedInterval (42729890584 / 1000000000000) (42729890589 / 1000000000000))) = true
  rfl'

theorem compactCertificate365_stateChecks3 :
    compactCertificate365.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2115320306714527 / 4000000000000)) (orderedInterval (33557751275 / 1000000000000) (33557762031 / 1000000000000), orderedInterval (-8846675489 / 1000000000000) (-8846664733 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1221280748503783 / 4000000000000)) (orderedInterval (-44751551154 / 1000000000000) (-44751551147 / 1000000000000), orderedInterval (-9003339039 / 1000000000000) (-9003339031 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2167184119649747 / 4000000000000)) (orderedInterval (27153880753 / 1000000000000) (27153912542 / 1000000000000), orderedInterval (-20945953388 / 1000000000000) (-20945921600 / 1000000000000))) = true
  rfl'

theorem compactCertificate365_stateChecks4 :
    compactCertificate365.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2024864524306943 / 4000000000000)) (orderedInterval (-33114761054 / 1000000000000) (-33114761051 / 1000000000000), orderedInterval (-12656532147 / 1000000000000) (-12656532145 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1445038869142319 / 4000000000000)) (orderedInterval (-28969180969 / 1000000000000) (-28969180968 / 1000000000000), orderedInterval (-30340960326 / 1000000000000) (-30340960325 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1638520063959801 / 4000000000000)) (orderedInterval (35713289311 / 1000000000000) (35713322899 / 1000000000000), orderedInterval (-16737696951 / 1000000000000) (-16737663362 / 1000000000000))) = true
  rfl'

theorem compactCertificate365_stateChecks5 :
    compactCertificate365.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1366027205025769 / 4000000000000)) (orderedInterval (6100368565 / 1000000000000) (6100368574 / 1000000000000), orderedInterval (-42751615554 / 1000000000000) (-42751615545 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1206926463089149 / 4000000000000)) (orderedInterval (36647598776 / 1000000000000) (36647598777 / 1000000000000), orderedInterval (27631151744 / 1000000000000) (27631151745 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (349814331221751 / 800000000000)) (orderedInterval (-37402140851 / 1000000000000) (-37402140830 / 1000000000000), orderedInterval (-7505889062 / 1000000000000) (-7505889041 / 1000000000000))) = true
  rfl'

theorem compactCertificate365_stateChecks6 :
    compactCertificate365.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (967604849878997 / 4000000000000)) (orderedInterval (-36204455745 / 1000000000000) (-36204455744 / 1000000000000), orderedInterval (-36270344719 / 1000000000000) (-36270344718 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (820249347172717 / 4000000000000)) (orderedInterval (-55570511410 / 1000000000000) (-55570511214 / 1000000000000), orderedInterval (4188570852 / 1000000000000) (4188571048 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (513273956062351 / 4000000000000)) (orderedInterval (-20654624159 / 1000000000000) (-20654624158 / 1000000000000), orderedInterval (-67259441408 / 1000000000000) (-67259441407 / 1000000000000))) = true
  rfl'

theorem compactCertificate365_stateChecks7 :
    compactCertificate365.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (276040440642417 / 4000000000000)) (orderedInterval (60292659481 / 1000000000000) (60292659482 / 1000000000000), orderedInterval (74328605558 / 1000000000000) (74328605559 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (749503493858251 / 4000000000000)) (orderedInterval (-19160948684 / 1000000000000) (-19160948245 / 1000000000000), orderedInterval (55100399748 / 1000000000000) (55100400187 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1023382943838827 / 4000000000000)) (orderedInterval (-41426207798 / 1000000000000) (-41426142109 / 1000000000000), orderedInterval (27868791895 / 1000000000000) (27868857584 / 1000000000000))) = true
  rfl'

theorem compactCertificate365_stateChecks8 :
    compactCertificate365.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (432726043937649 / 4000000000000)) (orderedInterval (64132443711 / 1000000000000) (64132474794 / 1000000000000), orderedInterval (-42388460072 / 1000000000000) (-42388428990 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1759007344374929 / 4000000000000)) (orderedInterval (24915815353 / 1000000000000) (24915815354 / 1000000000000), orderedInterval (28727224906 / 1000000000000) (28727224907 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1174935386494111 / 4000000000000)) (orderedInterval (-33099395939 / 1000000000000) (-33099363511 / 1000000000000), orderedInterval (32794169451 / 1000000000000) (32794201880 / 1000000000000))) = true
  rfl'

theorem compactCertificate365_states : ∀ j,
    BesselStateValid (compactCertificate365.point j) (compactCertificate365.state j) :=
  compactCertificate365.statesValid_of_checks3 compactCertificate365_stateChecks0
    compactCertificate365_stateChecks1 compactCertificate365_stateChecks2
    compactCertificate365_stateChecks3 compactCertificate365_stateChecks4
    compactCertificate365_stateChecks5 compactCertificate365_stateChecks6
    compactCertificate365_stateChecks7 compactCertificate365_stateChecks8

theorem compactCertificate365_chunkChecks0_0 :
    compactCertificate365.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (473 / 2) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-51650771570 / 1000000000000) (-51650771248 / 1000000000000), orderedInterval (5011265004 / 1000000000000) (5011265326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (696819318357173 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48806884073 / 1000000000000) (-48806818897 / 1000000000000), orderedInterval (35809629538 / 1000000000000) (35809694714 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (225337050500309 / 800000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13460980726 / 1000000000000) (-13460980602 / 1000000000000), orderedInterval (45619467359 / 1000000000000) (45619467483 / 1000000000000)))) (orderedInterval (-21717248889 / 1000000000000) (-21717248130 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (203330139204511 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (109190435158 / 1000000000000) (109190435159 / 1000000000000), orderedInterval (23436608718 / 1000000000000) (23436608719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (546173354653267 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53582400831 / 1000000000000) (-53582324429 / 1000000000000), orderedInterval (42520200676 / 1000000000000) (42520277079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1482966903732039 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30265170829 / 1000000000000) (30265170830 / 1000000000000), orderedInterval (28264147182 / 1000000000000) (28264147183 / 1000000000000)))) (orderedInterval (-5292565958 / 1000000000000) (-5292563140 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1092346709307007 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25362338217 / 1000000000000) (-25362338216 / 1000000000000), orderedInterval (-41038280533 / 1000000000000) (-41038280532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1871754704850811 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21625997656 / 1000000000000) (-21625997655 / 1000000000000), orderedInterval (-29856540815 / 1000000000000) (-29856540814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1378726043937649 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4660016487 / 1000000000000) (-4660016482 / 1000000000000), orderedInterval (42729890584 / 1000000000000) (42729890589 / 1000000000000)))) (orderedInterval (554408882 / 1000000000000) (554408896 / 1000000000000))) = true
  rfl'

theorem compactCertificate365_chunkChecks0_1 :
    compactCertificate365.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2115320306714527 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (33557751275 / 1000000000000) (33557762031 / 1000000000000), orderedInterval (-8846675489 / 1000000000000) (-8846664733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1221280748503783 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-44751551154 / 1000000000000) (-44751551147 / 1000000000000), orderedInterval (-9003339039 / 1000000000000) (-9003339031 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2167184119649747 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27153880753 / 1000000000000) (27153912542 / 1000000000000), orderedInterval (-20945953388 / 1000000000000) (-20945921600 / 1000000000000)))) (orderedInterval (-5418446724 / 1000000000000) (-5418440199 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2024864524306943 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33114761054 / 1000000000000) (-33114761051 / 1000000000000), orderedInterval (-12656532147 / 1000000000000) (-12656532145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1445038869142319 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28969180969 / 1000000000000) (-28969180968 / 1000000000000), orderedInterval (-30340960326 / 1000000000000) (-30340960325 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1638520063959801 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (35713289311 / 1000000000000) (35713322899 / 1000000000000), orderedInterval (-16737696951 / 1000000000000) (-16737663362 / 1000000000000)))) (orderedInterval (-2322315148 / 1000000000000) (-2322314949 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1366027205025769 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6100368565 / 1000000000000) (6100368574 / 1000000000000), orderedInterval (-42751615554 / 1000000000000) (-42751615545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1206926463089149 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36647598776 / 1000000000000) (36647598777 / 1000000000000), orderedInterval (27631151744 / 1000000000000) (27631151745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (349814331221751 / 800000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-37402140851 / 1000000000000) (-37402140830 / 1000000000000), orderedInterval (-7505889062 / 1000000000000) (-7505889041 / 1000000000000)))) (orderedInterval (-2984417811 / 1000000000000) (-2984417787 / 1000000000000))) = true
  rfl'

theorem compactCertificate365_chunkChecks0_2 :
    compactCertificate365.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (967604849878997 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36204455745 / 1000000000000) (-36204455744 / 1000000000000), orderedInterval (-36270344719 / 1000000000000) (-36270344718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (820249347172717 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-55570511410 / 1000000000000) (-55570511214 / 1000000000000), orderedInterval (4188570852 / 1000000000000) (4188571048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (513273956062351 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-20654624159 / 1000000000000) (-20654624158 / 1000000000000), orderedInterval (-67259441408 / 1000000000000) (-67259441407 / 1000000000000)))) (orderedInterval (8261690413 / 1000000000000) (8261690484 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (276040440642417 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (60292659481 / 1000000000000) (60292659482 / 1000000000000), orderedInterval (74328605558 / 1000000000000) (74328605559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (749503493858251 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19160948684 / 1000000000000) (-19160948245 / 1000000000000), orderedInterval (55100399748 / 1000000000000) (55100400187 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1023382943838827 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41426207798 / 1000000000000) (-41426142109 / 1000000000000), orderedInterval (27868791895 / 1000000000000) (27868857584 / 1000000000000)))) (orderedInterval (2496243482 / 1000000000000) (2496248555 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (432726043937649 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64132443711 / 1000000000000) (64132474794 / 1000000000000), orderedInterval (-42388460072 / 1000000000000) (-42388428990 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1759007344374929 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24915815353 / 1000000000000) (24915815354 / 1000000000000), orderedInterval (28727224906 / 1000000000000) (28727224907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1174935386494111 / 4000000000000) 0 (IntervalRat.scale (473 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33099395939 / 1000000000000) (-33099363511 / 1000000000000), orderedInterval (32794169451 / 1000000000000) (32794201880 / 1000000000000)))) (orderedInterval (4568738349 / 1000000000000) (4568744687 / 1000000000000))) = true
  rfl'

theorem compactCertificate365_chunkChecks0 :
    compactCertificate365.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate365.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate365_chunkChecks0_0
    compactCertificate365_chunkChecks0_1 compactCertificate365_chunkChecks0_2

theorem compactCertificate365_chunkChecks1_0 :
    compactCertificate365.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (473 / 2) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-51650771570 / 1000000000000) (-51650771248 / 1000000000000), orderedInterval (5011265004 / 1000000000000) (5011265326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (696819318357173 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48806884073 / 1000000000000) (-48806818897 / 1000000000000), orderedInterval (35809629538 / 1000000000000) (35809694714 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (225337050500309 / 800000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13460980726 / 1000000000000) (-13460980602 / 1000000000000), orderedInterval (45619467359 / 1000000000000) (45619467483 / 1000000000000)))) (orderedInterval (5420382128 / 1000000000000) (5420382731 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (203330139204511 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (109190435158 / 1000000000000) (109190435159 / 1000000000000), orderedInterval (23436608718 / 1000000000000) (23436608719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (546173354653267 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53582400831 / 1000000000000) (-53582324429 / 1000000000000), orderedInterval (42520200676 / 1000000000000) (42520277079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1482966903732039 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30265170829 / 1000000000000) (30265170830 / 1000000000000), orderedInterval (28264147182 / 1000000000000) (28264147183 / 1000000000000)))) (orderedInterval (-2308120192 / 1000000000000) (-2308118548 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1092346709307007 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25362338217 / 1000000000000) (-25362338216 / 1000000000000), orderedInterval (-41038280533 / 1000000000000) (-41038280532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1871754704850811 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21625997656 / 1000000000000) (-21625997655 / 1000000000000), orderedInterval (-29856540815 / 1000000000000) (-29856540814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1378726043937649 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4660016487 / 1000000000000) (-4660016482 / 1000000000000), orderedInterval (42729890584 / 1000000000000) (42729890589 / 1000000000000)))) (orderedInterval (3327163129 / 1000000000000) (3327163153 / 1000000000000))) = true
  rfl'

theorem compactCertificate365_chunkChecks1_1 :
    compactCertificate365.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2115320306714527 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (33557751275 / 1000000000000) (33557762031 / 1000000000000), orderedInterval (-8846675489 / 1000000000000) (-8846664733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1221280748503783 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-44751551154 / 1000000000000) (-44751551147 / 1000000000000), orderedInterval (-9003339039 / 1000000000000) (-9003339031 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2167184119649747 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27153880753 / 1000000000000) (27153912542 / 1000000000000), orderedInterval (-20945953388 / 1000000000000) (-20945921600 / 1000000000000)))) (orderedInterval (-4167550646 / 1000000000000) (-4167535825 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2024864524306943 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33114761054 / 1000000000000) (-33114761051 / 1000000000000), orderedInterval (-12656532147 / 1000000000000) (-12656532145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1445038869142319 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28969180969 / 1000000000000) (-28969180968 / 1000000000000), orderedInterval (-30340960326 / 1000000000000) (-30340960325 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1638520063959801 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (35713289311 / 1000000000000) (35713322899 / 1000000000000), orderedInterval (-16737696951 / 1000000000000) (-16737663362 / 1000000000000)))) (orderedInterval (-3746887157 / 1000000000000) (-3746886816 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1366027205025769 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6100368565 / 1000000000000) (6100368574 / 1000000000000), orderedInterval (-42751615554 / 1000000000000) (-42751615545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1206926463089149 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36647598776 / 1000000000000) (36647598777 / 1000000000000), orderedInterval (27631151744 / 1000000000000) (27631151745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (349814331221751 / 800000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-37402140851 / 1000000000000) (-37402140830 / 1000000000000), orderedInterval (-7505889062 / 1000000000000) (-7505889041 / 1000000000000)))) (orderedInterval (-3085580270 / 1000000000000) (-3085580235 / 1000000000000))) = true
  rfl'

theorem compactCertificate365_chunkChecks1_2 :
    compactCertificate365.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (967604849878997 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36204455745 / 1000000000000) (-36204455744 / 1000000000000), orderedInterval (-36270344719 / 1000000000000) (-36270344718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (820249347172717 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-55570511410 / 1000000000000) (-55570511214 / 1000000000000), orderedInterval (4188570852 / 1000000000000) (4188571048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (513273956062351 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-20654624159 / 1000000000000) (-20654624158 / 1000000000000), orderedInterval (-67259441408 / 1000000000000) (-67259441407 / 1000000000000)))) (orderedInterval (4538196742 / 1000000000000) (4538196807 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (276040440642417 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (60292659481 / 1000000000000) (60292659482 / 1000000000000), orderedInterval (74328605558 / 1000000000000) (74328605559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (749503493858251 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19160948684 / 1000000000000) (-19160948245 / 1000000000000), orderedInterval (55100399748 / 1000000000000) (55100400187 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1023382943838827 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41426207798 / 1000000000000) (-41426142109 / 1000000000000), orderedInterval (27868791895 / 1000000000000) (27868857584 / 1000000000000)))) (orderedInterval (-3701440181 / 1000000000000) (-3701434701 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (432726043937649 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64132443711 / 1000000000000) (64132474794 / 1000000000000), orderedInterval (-42388460072 / 1000000000000) (-42388428990 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1759007344374929 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24915815353 / 1000000000000) (24915815354 / 1000000000000), orderedInterval (28727224906 / 1000000000000) (28727224907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1174935386494111 / 4000000000000) 1 (IntervalRat.scale (473 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33099395939 / 1000000000000) (-33099363511 / 1000000000000), orderedInterval (32794169451 / 1000000000000) (32794201880 / 1000000000000)))) (orderedInterval (-12107157967 / 1000000000000) (-12107150232 / 1000000000000))) = true
  rfl'

theorem compactCertificate365_chunkChecks1 :
    compactCertificate365.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate365.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate365_chunkChecks1_0
    compactCertificate365_chunkChecks1_1 compactCertificate365_chunkChecks1_2

theorem compactCertificate365_chunkChecks2_0 :
    compactCertificate365.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (473 / 2) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-51650771570 / 1000000000000) (-51650771248 / 1000000000000), orderedInterval (5011265004 / 1000000000000) (5011265326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (696819318357173 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48806884073 / 1000000000000) (-48806818897 / 1000000000000), orderedInterval (35809629538 / 1000000000000) (35809694714 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (225337050500309 / 800000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13460980726 / 1000000000000) (-13460980602 / 1000000000000), orderedInterval (45619467359 / 1000000000000) (45619467483 / 1000000000000)))) (orderedInterval (21816857070 / 1000000000000) (21816857562 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (203330139204511 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (109190435158 / 1000000000000) (109190435159 / 1000000000000), orderedInterval (23436608718 / 1000000000000) (23436608719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (546173354653267 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53582400831 / 1000000000000) (-53582324429 / 1000000000000), orderedInterval (42520200676 / 1000000000000) (42520277079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1482966903732039 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30265170829 / 1000000000000) (30265170830 / 1000000000000), orderedInterval (28264147182 / 1000000000000) (28264147183 / 1000000000000)))) (orderedInterval (6003868274 / 1000000000000) (6003869256 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1092346709307007 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25362338217 / 1000000000000) (-25362338216 / 1000000000000), orderedInterval (-41038280533 / 1000000000000) (-41038280532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1871754704850811 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21625997656 / 1000000000000) (-21625997655 / 1000000000000), orderedInterval (-29856540815 / 1000000000000) (-29856540814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1378726043937649 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4660016487 / 1000000000000) (-4660016482 / 1000000000000), orderedInterval (42729890584 / 1000000000000) (42729890589 / 1000000000000)))) (orderedInterval (-2386179878 / 1000000000000) (-2386179836 / 1000000000000))) = true
  rfl'

theorem compactCertificate365_chunkChecks2_1 :
    compactCertificate365.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2115320306714527 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (33557751275 / 1000000000000) (33557762031 / 1000000000000), orderedInterval (-8846675489 / 1000000000000) (-8846664733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1221280748503783 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-44751551154 / 1000000000000) (-44751551147 / 1000000000000), orderedInterval (-9003339039 / 1000000000000) (-9003339031 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2167184119649747 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27153880753 / 1000000000000) (27153912542 / 1000000000000), orderedInterval (-20945953388 / 1000000000000) (-20945921600 / 1000000000000)))) (orderedInterval (15099391197 / 1000000000000) (15099424950 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2024864524306943 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33114761054 / 1000000000000) (-33114761051 / 1000000000000), orderedInterval (-12656532147 / 1000000000000) (-12656532145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1445038869142319 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28969180969 / 1000000000000) (-28969180968 / 1000000000000), orderedInterval (-30340960326 / 1000000000000) (-30340960325 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1638520063959801 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (35713289311 / 1000000000000) (35713322899 / 1000000000000), orderedInterval (-16737696951 / 1000000000000) (-16737663362 / 1000000000000)))) (orderedInterval (4211044854 / 1000000000000) (4211045442 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1366027205025769 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6100368565 / 1000000000000) (6100368574 / 1000000000000), orderedInterval (-42751615554 / 1000000000000) (-42751615545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1206926463089149 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36647598776 / 1000000000000) (36647598777 / 1000000000000), orderedInterval (27631151744 / 1000000000000) (27631151745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (349814331221751 / 800000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-37402140851 / 1000000000000) (-37402140830 / 1000000000000), orderedInterval (-7505889062 / 1000000000000) (-7505889041 / 1000000000000)))) (orderedInterval (6553524328 / 1000000000000) (6553524379 / 1000000000000))) = true
  rfl'

theorem compactCertificate365_chunkChecks2_2 :
    compactCertificate365.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (967604849878997 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36204455745 / 1000000000000) (-36204455744 / 1000000000000), orderedInterval (-36270344719 / 1000000000000) (-36270344718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (820249347172717 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-55570511410 / 1000000000000) (-55570511214 / 1000000000000), orderedInterval (4188570852 / 1000000000000) (4188571048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (513273956062351 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-20654624159 / 1000000000000) (-20654624158 / 1000000000000), orderedInterval (-67259441408 / 1000000000000) (-67259441407 / 1000000000000)))) (orderedInterval (-8242155904 / 1000000000000) (-8242155843 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (276040440642417 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (60292659481 / 1000000000000) (60292659482 / 1000000000000), orderedInterval (74328605558 / 1000000000000) (74328605559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (749503493858251 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19160948684 / 1000000000000) (-19160948245 / 1000000000000), orderedInterval (55100399748 / 1000000000000) (55100400187 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1023382943838827 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41426207798 / 1000000000000) (-41426142109 / 1000000000000), orderedInterval (27868791895 / 1000000000000) (27868857584 / 1000000000000)))) (orderedInterval (-3877935087 / 1000000000000) (-3877929140 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (432726043937649 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64132443711 / 1000000000000) (64132474794 / 1000000000000), orderedInterval (-42388460072 / 1000000000000) (-42388428990 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1759007344374929 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24915815353 / 1000000000000) (24915815354 / 1000000000000), orderedInterval (28727224906 / 1000000000000) (28727224907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1174935386494111 / 4000000000000) 2 (IntervalRat.scale (473 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33099395939 / 1000000000000) (-33099363511 / 1000000000000), orderedInterval (32794169451 / 1000000000000) (32794201880 / 1000000000000)))) (orderedInterval (-2597255253 / 1000000000000) (-2597245659 / 1000000000000))) = true
  rfl'

theorem compactCertificate365_chunkChecks2 :
    compactCertificate365.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate365.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate365_chunkChecks2_0
    compactCertificate365_chunkChecks2_1 compactCertificate365_chunkChecks2_2

theorem compactCertificate365_chunkChecks3_0 :
    compactCertificate365.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (473 / 2) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-51650771570 / 1000000000000) (-51650771248 / 1000000000000), orderedInterval (5011265004 / 1000000000000) (5011265326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (696819318357173 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48806884073 / 1000000000000) (-48806818897 / 1000000000000), orderedInterval (35809629538 / 1000000000000) (35809694714 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (225337050500309 / 800000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13460980726 / 1000000000000) (-13460980602 / 1000000000000), orderedInterval (45619467359 / 1000000000000) (45619467483 / 1000000000000)))) (orderedInterval (-6734346216 / 1000000000000) (-6734345806 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (203330139204511 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (109190435158 / 1000000000000) (109190435159 / 1000000000000), orderedInterval (23436608718 / 1000000000000) (23436608719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (546173354653267 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53582400831 / 1000000000000) (-53582324429 / 1000000000000), orderedInterval (42520200676 / 1000000000000) (42520277079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1482966903732039 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30265170829 / 1000000000000) (30265170830 / 1000000000000), orderedInterval (28264147182 / 1000000000000) (28264147183 / 1000000000000)))) (orderedInterval (7418716308 / 1000000000000) (7418716917 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1092346709307007 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25362338217 / 1000000000000) (-25362338216 / 1000000000000), orderedInterval (-41038280533 / 1000000000000) (-41038280532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1871754704850811 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21625997656 / 1000000000000) (-21625997655 / 1000000000000), orderedInterval (-29856540815 / 1000000000000) (-29856540814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1378726043937649 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4660016487 / 1000000000000) (-4660016482 / 1000000000000), orderedInterval (42729890584 / 1000000000000) (42729890589 / 1000000000000)))) (orderedInterval (-10319970453 / 1000000000000) (-10319970377 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate365_chunkChecks3_1 :
    compactCertificate365.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2115320306714527 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (33557751275 / 1000000000000) (33557762031 / 1000000000000), orderedInterval (-8846675489 / 1000000000000) (-8846664733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1221280748503783 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-44751551154 / 1000000000000) (-44751551147 / 1000000000000), orderedInterval (-9003339039 / 1000000000000) (-9003339031 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2167184119649747 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27153880753 / 1000000000000) (27153912542 / 1000000000000), orderedInterval (-20945953388 / 1000000000000) (-20945921600 / 1000000000000)))) (orderedInterval (19596101711 / 1000000000000) (19596178464 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2024864524306943 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33114761054 / 1000000000000) (-33114761051 / 1000000000000), orderedInterval (-12656532147 / 1000000000000) (-12656532145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1445038869142319 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28969180969 / 1000000000000) (-28969180968 / 1000000000000), orderedInterval (-30340960326 / 1000000000000) (-30340960325 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1638520063959801 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (35713289311 / 1000000000000) (35713322899 / 1000000000000), orderedInterval (-16737696951 / 1000000000000) (-16737663362 / 1000000000000)))) (orderedInterval (7527536266 / 1000000000000) (7527537281 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1366027205025769 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6100368565 / 1000000000000) (6100368574 / 1000000000000), orderedInterval (-42751615554 / 1000000000000) (-42751615545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1206926463089149 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36647598776 / 1000000000000) (36647598777 / 1000000000000), orderedInterval (27631151744 / 1000000000000) (27631151745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (349814331221751 / 800000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-37402140851 / 1000000000000) (-37402140830 / 1000000000000), orderedInterval (-7505889062 / 1000000000000) (-7505889041 / 1000000000000)))) (orderedInterval (5957082258 / 1000000000000) (5957082338 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate365_chunkChecks3_2 :
    compactCertificate365.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (967604849878997 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36204455745 / 1000000000000) (-36204455744 / 1000000000000), orderedInterval (-36270344719 / 1000000000000) (-36270344718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (820249347172717 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-55570511410 / 1000000000000) (-55570511214 / 1000000000000), orderedInterval (4188570852 / 1000000000000) (4188571048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (513273956062351 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-20654624159 / 1000000000000) (-20654624158 / 1000000000000), orderedInterval (-67259441408 / 1000000000000) (-67259441407 / 1000000000000)))) (orderedInterval (-5666619939 / 1000000000000) (-5666619880 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (276040440642417 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (60292659481 / 1000000000000) (60292659482 / 1000000000000), orderedInterval (74328605558 / 1000000000000) (74328605559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (749503493858251 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19160948684 / 1000000000000) (-19160948245 / 1000000000000), orderedInterval (55100399748 / 1000000000000) (55100400187 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1023382943838827 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41426207798 / 1000000000000) (-41426142109 / 1000000000000), orderedInterval (27868791895 / 1000000000000) (27868857584 / 1000000000000)))) (orderedInterval (3376135310 / 1000000000000) (3376141740 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (432726043937649 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64132443711 / 1000000000000) (64132474794 / 1000000000000), orderedInterval (-42388460072 / 1000000000000) (-42388428990 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1759007344374929 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24915815353 / 1000000000000) (24915815354 / 1000000000000), orderedInterval (28727224906 / 1000000000000) (28727224907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1174935386494111 / 4000000000000) 3 (IntervalRat.scale (473 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33099395939 / 1000000000000) (-33099363511 / 1000000000000), orderedInterval (32794169451 / 1000000000000) (32794201880 / 1000000000000)))) (orderedInterval (26857142875 / 1000000000000) (26857154801 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate365_chunkChecks3 :
    compactCertificate365.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate365.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate365_chunkChecks3_0
    compactCertificate365_chunkChecks3_1 compactCertificate365_chunkChecks3_2

theorem compactCertificate365_chunkChecks4_0 :
    compactCertificate365.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (473 / 2) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-51650771570 / 1000000000000) (-51650771248 / 1000000000000), orderedInterval (5011265004 / 1000000000000) (5011265326 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (696819318357173 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48806884073 / 1000000000000) (-48806818897 / 1000000000000), orderedInterval (35809629538 / 1000000000000) (35809694714 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (225337050500309 / 800000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13460980726 / 1000000000000) (-13460980602 / 1000000000000), orderedInterval (45619467359 / 1000000000000) (45619467483 / 1000000000000)))) (orderedInterval (-22138456011 / 1000000000000) (-22138455657 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (203330139204511 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (109190435158 / 1000000000000) (109190435159 / 1000000000000), orderedInterval (23436608718 / 1000000000000) (23436608719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (546173354653267 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53582400831 / 1000000000000) (-53582324429 / 1000000000000), orderedInterval (42520200676 / 1000000000000) (42520277079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1482966903732039 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30265170829 / 1000000000000) (30265170830 / 1000000000000), orderedInterval (28264147182 / 1000000000000) (28264147183 / 1000000000000)))) (orderedInterval (-13275573670 / 1000000000000) (-13275573252 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1092346709307007 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-25362338217 / 1000000000000) (-25362338216 / 1000000000000), orderedInterval (-41038280533 / 1000000000000) (-41038280532 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1871754704850811 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21625997656 / 1000000000000) (-21625997655 / 1000000000000), orderedInterval (-29856540815 / 1000000000000) (-29856540814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1378726043937649 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4660016487 / 1000000000000) (-4660016482 / 1000000000000), orderedInterval (42729890584 / 1000000000000) (42729890589 / 1000000000000)))) (orderedInterval (9802090750 / 1000000000000) (9802090889 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate365_chunkChecks4_1 :
    compactCertificate365.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2115320306714527 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (33557751275 / 1000000000000) (33557762031 / 1000000000000), orderedInterval (-8846675489 / 1000000000000) (-8846664733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1221280748503783 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-44751551154 / 1000000000000) (-44751551147 / 1000000000000), orderedInterval (-9003339039 / 1000000000000) (-9003339031 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2167184119649747 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (27153880753 / 1000000000000) (27153912542 / 1000000000000), orderedInterval (-20945953388 / 1000000000000) (-20945921600 / 1000000000000)))) (orderedInterval (-52125893823 / 1000000000000) (-52125718907 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2024864524306943 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-33114761054 / 1000000000000) (-33114761051 / 1000000000000), orderedInterval (-12656532147 / 1000000000000) (-12656532145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1445038869142319 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-28969180969 / 1000000000000) (-28969180968 / 1000000000000), orderedInterval (-30340960326 / 1000000000000) (-30340960325 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1638520063959801 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (35713289311 / 1000000000000) (35713322899 / 1000000000000), orderedInterval (-16737696951 / 1000000000000) (-16737663362 / 1000000000000)))) (orderedInterval (-4056193720 / 1000000000000) (-4056191958 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1366027205025769 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6100368565 / 1000000000000) (6100368574 / 1000000000000), orderedInterval (-42751615554 / 1000000000000) (-42751615545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1206926463089149 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36647598776 / 1000000000000) (36647598777 / 1000000000000), orderedInterval (27631151744 / 1000000000000) (27631151745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (349814331221751 / 800000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-37402140851 / 1000000000000) (-37402140830 / 1000000000000), orderedInterval (-7505889062 / 1000000000000) (-7505889041 / 1000000000000)))) (orderedInterval (-16491504928 / 1000000000000) (-16491504801 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate365_chunkChecks4_2 :
    compactCertificate365.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (967604849878997 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36204455745 / 1000000000000) (-36204455744 / 1000000000000), orderedInterval (-36270344719 / 1000000000000) (-36270344718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (820249347172717 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-55570511410 / 1000000000000) (-55570511214 / 1000000000000), orderedInterval (4188570852 / 1000000000000) (4188571048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (513273956062351 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-20654624159 / 1000000000000) (-20654624158 / 1000000000000), orderedInterval (-67259441408 / 1000000000000) (-67259441407 / 1000000000000)))) (orderedInterval (8103320469 / 1000000000000) (8103320526 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (276040440642417 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (60292659481 / 1000000000000) (60292659482 / 1000000000000), orderedInterval (74328605558 / 1000000000000) (74328605559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (749503493858251 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19160948684 / 1000000000000) (-19160948245 / 1000000000000), orderedInterval (55100399748 / 1000000000000) (55100400187 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1023382943838827 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-41426207798 / 1000000000000) (-41426142109 / 1000000000000), orderedInterval (27868791895 / 1000000000000) (27868857584 / 1000000000000)))) (orderedInterval (4482816900 / 1000000000000) (4482823880 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (432726043937649 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (64132443711 / 1000000000000) (64132474794 / 1000000000000), orderedInterval (-42388460072 / 1000000000000) (-42388428990 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1759007344374929 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (24915815353 / 1000000000000) (24915815354 / 1000000000000), orderedInterval (28727224906 / 1000000000000) (28727224907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1174935386494111 / 4000000000000) 4 (IntervalRat.scale (473 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33099395939 / 1000000000000) (-33099363511 / 1000000000000), orderedInterval (32794169451 / 1000000000000) (32794201880 / 1000000000000)))) (orderedInterval (-9677196483 / 1000000000000) (-9677181561 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate365_chunkChecks4 :
    compactCertificate365.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate365.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate365_chunkChecks4_0
    compactCertificate365_chunkChecks4_1 compactCertificate365_chunkChecks4_2

theorem compactCertificate365_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate365.chunkCheck r b = true :=
  compactCertificate365.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate365_chunkChecks0
    · exact compactCertificate365_chunkChecks1
    · exact compactCertificate365_chunkChecks2
    · exact compactCertificate365_chunkChecks3
    · exact compactCertificate365_chunkChecks4)

theorem compactCertificate365_coefficient0 :
    compactCertificate365.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate365_coefficient1 :
    compactCertificate365.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate365_coefficient2 :
    compactCertificate365.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate365_coefficient3 :
    compactCertificate365.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate365_coefficient4 :
    compactCertificate365.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate365_coefficients : ∀ r : Fin 5,
    compactCertificate365.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate365_coefficient0
  · exact compactCertificate365_coefficient1
  · exact compactCertificate365_coefficient2
  · exact compactCertificate365_coefficient3
  · exact compactCertificate365_coefficient4

theorem compactCertificate365_lower : (1 : ℚ) ≤ compactCertificate365.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate365, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate365_proves {t : ℝ} (ht : t ∈ compactCertificate365.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate365.proves compactCertificate365_states compactCertificate365_chunks
    compactCertificate365_coefficients compactCertificate365_lower ht

end Erdos232
