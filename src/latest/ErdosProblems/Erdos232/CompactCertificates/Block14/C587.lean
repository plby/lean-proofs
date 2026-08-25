/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate587 : CompactCertificate where
  left := 458
  right := 459
  center := 917 / 2
  grid := fun i =>
    match i.val with
    | 0 => 146
    | 1 => 108
    | 2 => 174
    | 3 => 31
    | 4 => 84
    | 5 => 229
    | 6 => 169
    | 7 => 289
    | 8 => 213
    | 9 => 327
    | 10 => 189
    | 11 => 335
    | 12 => 313
    | 13 => 223
    | 14 => 253
    | 15 => 211
    | 16 => 186
    | 17 => 270
    | 18 => 149
    | 19 => 127
    | 20 => 79
    | 21 => 43
    | 22 => 116
    | 23 => 158
    | 24 => 67
    | 25 => 272
    | _ => 181
  point := fun i =>
    match i.val with
    | 0 => 917 / 2
    | 1 => 1350916099225217 / 4000000000000
    | 2 => 436858510166561 / 800000000000
    | 3 => 394193948521219 / 4000000000000
    | 4 => 1058860393693543 / 4000000000000
    | 5 => 2875011946558731 / 4000000000000
    | 6 => 2117720787388003 / 4000000000000
    | 7 => 3628750664583919 / 4000000000000
    | 8 => 2672921315625421 / 4000000000000
    | 9 => 4100948670734083 / 4000000000000
    | 10 => 2367683818980907 / 4000000000000
    | 11 => 4201496485663463 / 4000000000000
    | 12 => 3925583020696547 / 4000000000000
    | 13 => 2801481274848851 / 4000000000000
    | 14 => 3176581181080629 / 4000000000000
    | 15 => 2648302213548901 / 4000000000000
    | 16 => 2339855320618921 / 4000000000000
    | 17 => 678181272157179 / 800000000000
    | 18 => 1875885089511713 / 4000000000000
    | 19 => 1590208565237593 / 4000000000000
    | 20 => 995078684374579 / 4000000000000
    | 21 => 535156625938893 / 4000000000000
    | 22 => 1453054342215679 / 4000000000000
    | 23 => 1984021478858783 / 4000000000000
    | 24 => 838921315625421 / 4000000000000
    | 25 => 3410168572498541 / 4000000000000
    | _ => 2277834565359619 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (21425668292 / 1000000000000) (21425668293 / 1000000000000), orderedInterval (30463102705 / 1000000000000) (30463102706 / 1000000000000))
    | 1 => (orderedInterval (-30470777142 / 1000000000000) (-30470753704 / 1000000000000), orderedInterval (30972984966 / 1000000000000) (30973008404 / 1000000000000))
    | 2 => (orderedInterval (7490723314 / 1000000000000) (7490723315 / 1000000000000), orderedInterval (33305355594 / 1000000000000) (33305355595 / 1000000000000))
    | 3 => (orderedInterval (-74862926750 / 1000000000000) (-74862922983 / 1000000000000), orderedInterval (29627829671 / 1000000000000) (29627833438 / 1000000000000))
    | 4 => (orderedInterval (49009180993 / 1000000000000) (49009181170 / 1000000000000), orderedInterval (-1830438463 / 1000000000000) (-1830438286 / 1000000000000))
    | 5 => (orderedInterval (-3370445848 / 1000000000000) (-3370445847 / 1000000000000), orderedInterval (-29567377711 / 1000000000000) (-29567377710 / 1000000000000))
    | 6 => (orderedInterval (22703084443 / 1000000000000) (22703089172 / 1000000000000), orderedInterval (-26232740013 / 1000000000000) (-26232735285 / 1000000000000))
    | 7 => (orderedInterval (-1394075040 / 1000000000000) (-1394075039 / 1000000000000), orderedInterval (-26453107985 / 1000000000000) (-26453107984 / 1000000000000))
    | 8 => (orderedInterval (4420013374 / 1000000000000) (4420013375 / 1000000000000), orderedInterval (-30550956196 / 1000000000000) (-30550956194 / 1000000000000))
    | 9 => (orderedInterval (23860806333 / 1000000000000) (23860896469 / 1000000000000), orderedInterval (-7195583084 / 1000000000000) (-7195492948 / 1000000000000))
    | 10 => (orderedInterval (28526258936 / 1000000000000) (28526346238 / 1000000000000), orderedInterval (-16203281328 / 1000000000000) (-16203194026 / 1000000000000))
    | 11 => (orderedInterval (23543443534 / 1000000000000) (23543521610 / 1000000000000), orderedInterval (-7207975826 / 1000000000000) (-7207897750 / 1000000000000))
    | 12 => (orderedInterval (23115359173 / 1000000000000) (23115391042 / 1000000000000), orderedInterval (-10706066148 / 1000000000000) (-10706034279 / 1000000000000))
    | 13 => (orderedInterval (-16531993887 / 1000000000000) (-16531993886 / 1000000000000), orderedInterval (-25200679028 / 1000000000000) (-25200679027 / 1000000000000))
    | 14 => (orderedInterval (-3040482724 / 1000000000000) (-3040482723 / 1000000000000), orderedInterval (-28147633694 / 1000000000000) (-28147633693 / 1000000000000))
    | 15 => (orderedInterval (474019303 / 1000000000000) (474019304 / 1000000000000), orderedInterval (-31005633764 / 1000000000000) (-31005633763 / 1000000000000))
    | 16 => (orderedInterval (32578482343 / 1000000000000) (32578482459 / 1000000000000), orderedInterval (5163330734 / 1000000000000) (5163330850 / 1000000000000))
    | 17 => (orderedInterval (7621255088 / 1000000000000) (7621255089 / 1000000000000), orderedInterval (26318300551 / 1000000000000) (26318300552 / 1000000000000))
    | 18 => (orderedInterval (-36700455921 / 1000000000000) (-36700454654 / 1000000000000), orderedInterval (3288313403 / 1000000000000) (3288314670 / 1000000000000))
    | 19 => (orderedInterval (24059403751 / 1000000000000) (24059408383 / 1000000000000), orderedInterval (-32006728763 / 1000000000000) (-32006724131 / 1000000000000))
    | 20 => (orderedInterval (-49558155718 / 1000000000000) (-49558155713 / 1000000000000), orderedInterval (-10052120132 / 1000000000000) (-10052120127 / 1000000000000))
    | 21 => (orderedInterval (33967253716 / 1000000000000) (33967258497 / 1000000000000), orderedInterval (-60165461043 / 1000000000000) (-60165456262 / 1000000000000))
    | 22 => (orderedInterval (-15376375804 / 1000000000000) (-15376375568 / 1000000000000), orderedInterval (38957897545 / 1000000000000) (38957897781 / 1000000000000))
    | 23 => (orderedInterval (14571615366 / 1000000000000) (14571615367 / 1000000000000), orderedInterval (32713925015 / 1000000000000) (32713925016 / 1000000000000))
    | 24 => (orderedInterval (-1565757802 / 1000000000000) (-1565757800 / 1000000000000), orderedInterval (-55068743748 / 1000000000000) (-55068743745 / 1000000000000))
    | 25 => (orderedInterval (-25326198451 / 1000000000000) (-25326112021 / 1000000000000), orderedInterval (10277210018 / 1000000000000) (10277296448 / 1000000000000))
    | _ => (orderedInterval (-33402104548 / 1000000000000) (-33402103167 / 1000000000000), orderedInterval (1525183321 / 1000000000000) (1525184702 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (8648020500 / 1000000000000) (8648020751 / 1000000000000)
      | 1 => orderedInterval (2841224162 / 1000000000000) (2841224265 / 1000000000000)
      | 2 => orderedInterval (149821841 / 1000000000000) (149821868 / 1000000000000)
      | 3 => orderedInterval (1220606964 / 1000000000000) (1220640729 / 1000000000000)
      | 4 => orderedInterval (-1965230299 / 1000000000000) (-1965229668 / 1000000000000)
      | 5 => orderedInterval (-1663750262 / 1000000000000) (-1663750211 / 1000000000000)
      | 6 => orderedInterval (2892984614 / 1000000000000) (2892985194 / 1000000000000)
      | 7 => orderedInterval (-1395119855 / 1000000000000) (-1395119706 / 1000000000000)
      | _ => orderedInterval (8319272170 / 1000000000000) (8319279591 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (14614779287 / 1000000000000) (14614779485 / 1000000000000)
      | 1 => orderedInterval (3187355336 / 1000000000000) (3187355412 / 1000000000000)
      | 2 => orderedInterval (538277366 / 1000000000000) (538277411 / 1000000000000)
      | 3 => orderedInterval (-1038324913 / 1000000000000) (-1038254947 / 1000000000000)
      | 4 => orderedInterval (-2979748304 / 1000000000000) (-2979746983 / 1000000000000)
      | 5 => orderedInterval (351899575 / 1000000000000) (351899647 / 1000000000000)
      | 6 => orderedInterval (855426951 / 1000000000000) (855427492 / 1000000000000)
      | 7 => orderedInterval (-3088317154 / 1000000000000) (-3088317075 / 1000000000000)
      | _ => orderedInterval (-2062840398 / 1000000000000) (-2062826816 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-8993720895 / 1000000000000) (-8993720734 / 1000000000000)
      | 1 => orderedInterval (-1229753137 / 1000000000000) (-1229753046 / 1000000000000)
      | 2 => orderedInterval (-396410348 / 1000000000000) (-396410268 / 1000000000000)
      | 3 => orderedInterval (113639333 / 1000000000000) (113789402 / 1000000000000)
      | 4 => orderedInterval (5519953740 / 1000000000000) (5519956526 / 1000000000000)
      | 5 => orderedInterval (2355407239 / 1000000000000) (2355407345 / 1000000000000)
      | 6 => orderedInterval (-4642341529 / 1000000000000) (-4642341017 / 1000000000000)
      | 7 => orderedInterval (1148091050 / 1000000000000) (1148091111 / 1000000000000)
      | _ => orderedInterval (-16788840115 / 1000000000000) (-16788815098 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-15471938408 / 1000000000000) (-15471938272 / 1000000000000)
      | 1 => orderedInterval (-8078546607 / 1000000000000) (-8078546475 / 1000000000000)
      | 2 => orderedInterval (-4033448705 / 1000000000000) (-4033448560 / 1000000000000)
      | 3 => orderedInterval (607375231 / 1000000000000) (607703750 / 1000000000000)
      | 4 => orderedInterval (5846133656 / 1000000000000) (5846139553 / 1000000000000)
      | 5 => orderedInterval (-2572531110 / 1000000000000) (-2572530950 / 1000000000000)
      | 6 => orderedInterval (-555895381 / 1000000000000) (-555894894 / 1000000000000)
      | 7 => orderedInterval (3583554878 / 1000000000000) (3583554934 / 1000000000000)
      | _ => orderedInterval (5994859596 / 1000000000000) (5994905782 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (9360686498 / 1000000000000) (9360686620 / 1000000000000)
      | 1 => orderedInterval (1682744706 / 1000000000000) (1682744907 / 1000000000000)
      | 2 => orderedInterval (1158557360 / 1000000000000) (1158557629 / 1000000000000)
      | 3 => orderedInterval (-7942905414 / 1000000000000) (-7942175991 / 1000000000000)
      | 4 => orderedInterval (-17157718163 / 1000000000000) (-17157705629 / 1000000000000)
      | 5 => orderedInterval (-2624187404 / 1000000000000) (-2624187155 / 1000000000000)
      | 6 => orderedInterval (5515723552 / 1000000000000) (5515724021 / 1000000000000)
      | 7 => orderedInterval (-1412202991 / 1000000000000) (-1412202934 / 1000000000000)
      | _ => orderedInterval (39530010427 / 1000000000000) (39530095996 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (19047829835 / 1000000000000) (19047872813 / 1000000000000)
    | 1 => orderedInterval (10378507746 / 1000000000000) (10378593626 / 1000000000000)
    | 2 => orderedInterval (-22913974662 / 1000000000000) (-22913795779 / 1000000000000)
    | 3 => orderedInterval (-14680436850 / 1000000000000) (-14680055132 / 1000000000000)
    | _ => orderedInterval (28110708571 / 1000000000000) (28111537464 / 1000000000000)

theorem compactCertificate587_stateChecks0 :
    compactCertificate587.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (917 / 2)) (orderedInterval (21425668292 / 1000000000000) (21425668293 / 1000000000000), orderedInterval (30463102705 / 1000000000000) (30463102706 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1350916099225217 / 4000000000000)) (orderedInterval (-30470777142 / 1000000000000) (-30470753704 / 1000000000000), orderedInterval (30972984966 / 1000000000000) (30973008404 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (436858510166561 / 800000000000)) (orderedInterval (7490723314 / 1000000000000) (7490723315 / 1000000000000), orderedInterval (33305355594 / 1000000000000) (33305355595 / 1000000000000))) = true
  rfl'

theorem compactCertificate587_stateChecks1 :
    compactCertificate587.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (394193948521219 / 4000000000000)) (orderedInterval (-74862926750 / 1000000000000) (-74862922983 / 1000000000000), orderedInterval (29627829671 / 1000000000000) (29627833438 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1058860393693543 / 4000000000000)) (orderedInterval (49009180993 / 1000000000000) (49009181170 / 1000000000000), orderedInterval (-1830438463 / 1000000000000) (-1830438286 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (2875011946558731 / 4000000000000)) (orderedInterval (-3370445848 / 1000000000000) (-3370445847 / 1000000000000), orderedInterval (-29567377711 / 1000000000000) (-29567377710 / 1000000000000))) = true
  rfl'

theorem compactCertificate587_stateChecks2 :
    compactCertificate587.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2117720787388003 / 4000000000000)) (orderedInterval (22703084443 / 1000000000000) (22703089172 / 1000000000000), orderedInterval (-26232740013 / 1000000000000) (-26232735285 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 289 12 (3628750664583919 / 4000000000000)) (orderedInterval (-1394075040 / 1000000000000) (-1394075039 / 1000000000000), orderedInterval (-26453107985 / 1000000000000) (-26453107984 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (2672921315625421 / 4000000000000)) (orderedInterval (4420013374 / 1000000000000) (4420013375 / 1000000000000), orderedInterval (-30550956196 / 1000000000000) (-30550956194 / 1000000000000))) = true
  rfl'

theorem compactCertificate587_stateChecks3 :
    compactCertificate587.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 327 12 (4100948670734083 / 4000000000000)) (orderedInterval (23860806333 / 1000000000000) (23860896469 / 1000000000000), orderedInterval (-7195583084 / 1000000000000) (-7195492948 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2367683818980907 / 4000000000000)) (orderedInterval (28526258936 / 1000000000000) (28526346238 / 1000000000000), orderedInterval (-16203281328 / 1000000000000) (-16203194026 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 335 12 (4201496485663463 / 4000000000000)) (orderedInterval (23543443534 / 1000000000000) (23543521610 / 1000000000000), orderedInterval (-7207975826 / 1000000000000) (-7207897750 / 1000000000000))) = true
  rfl'

theorem compactCertificate587_stateChecks4 :
    compactCertificate587.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 313 12 (3925583020696547 / 4000000000000)) (orderedInterval (23115359173 / 1000000000000) (23115391042 / 1000000000000), orderedInterval (-10706066148 / 1000000000000) (-10706034279 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (2801481274848851 / 4000000000000)) (orderedInterval (-16531993887 / 1000000000000) (-16531993886 / 1000000000000), orderedInterval (-25200679028 / 1000000000000) (-25200679027 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 253 12 (3176581181080629 / 4000000000000)) (orderedInterval (-3040482724 / 1000000000000) (-3040482723 / 1000000000000), orderedInterval (-28147633694 / 1000000000000) (-28147633693 / 1000000000000))) = true
  rfl'

theorem compactCertificate587_stateChecks5 :
    compactCertificate587.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 211 12 (2648302213548901 / 4000000000000)) (orderedInterval (474019303 / 1000000000000) (474019304 / 1000000000000), orderedInterval (-31005633764 / 1000000000000) (-31005633763 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2339855320618921 / 4000000000000)) (orderedInterval (32578482343 / 1000000000000) (32578482459 / 1000000000000), orderedInterval (5163330734 / 1000000000000) (5163330850 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 270 12 (678181272157179 / 800000000000)) (orderedInterval (7621255088 / 1000000000000) (7621255089 / 1000000000000), orderedInterval (26318300551 / 1000000000000) (26318300552 / 1000000000000))) = true
  rfl'

theorem compactCertificate587_stateChecks6 :
    compactCertificate587.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1875885089511713 / 4000000000000)) (orderedInterval (-36700455921 / 1000000000000) (-36700454654 / 1000000000000), orderedInterval (3288313403 / 1000000000000) (3288314670 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1590208565237593 / 4000000000000)) (orderedInterval (24059403751 / 1000000000000) (24059408383 / 1000000000000), orderedInterval (-32006728763 / 1000000000000) (-32006724131 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (995078684374579 / 4000000000000)) (orderedInterval (-49558155718 / 1000000000000) (-49558155713 / 1000000000000), orderedInterval (-10052120132 / 1000000000000) (-10052120127 / 1000000000000))) = true
  rfl'

theorem compactCertificate587_stateChecks7 :
    compactCertificate587.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (535156625938893 / 4000000000000)) (orderedInterval (33967253716 / 1000000000000) (33967258497 / 1000000000000), orderedInterval (-60165461043 / 1000000000000) (-60165456262 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1453054342215679 / 4000000000000)) (orderedInterval (-15376375804 / 1000000000000) (-15376375568 / 1000000000000), orderedInterval (38957897545 / 1000000000000) (38957897781 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1984021478858783 / 4000000000000)) (orderedInterval (14571615366 / 1000000000000) (14571615367 / 1000000000000), orderedInterval (32713925015 / 1000000000000) (32713925016 / 1000000000000))) = true
  rfl'

theorem compactCertificate587_stateChecks8 :
    compactCertificate587.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (838921315625421 / 4000000000000)) (orderedInterval (-1565757802 / 1000000000000) (-1565757800 / 1000000000000), orderedInterval (-55068743748 / 1000000000000) (-55068743745 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 272 12 (3410168572498541 / 4000000000000)) (orderedInterval (-25326198451 / 1000000000000) (-25326112021 / 1000000000000), orderedInterval (10277210018 / 1000000000000) (10277296448 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2277834565359619 / 4000000000000)) (orderedInterval (-33402104548 / 1000000000000) (-33402103167 / 1000000000000), orderedInterval (1525183321 / 1000000000000) (1525184702 / 1000000000000))) = true
  rfl'

theorem compactCertificate587_states : ∀ j,
    BesselStateValid (compactCertificate587.point j) (compactCertificate587.state j) :=
  compactCertificate587.statesValid_of_checks3 compactCertificate587_stateChecks0
    compactCertificate587_stateChecks1 compactCertificate587_stateChecks2
    compactCertificate587_stateChecks3 compactCertificate587_stateChecks4
    compactCertificate587_stateChecks5 compactCertificate587_stateChecks6
    compactCertificate587_stateChecks7 compactCertificate587_stateChecks8

theorem compactCertificate587_chunkChecks0_0 :
    compactCertificate587.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (917 / 2) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (21425668292 / 1000000000000) (21425668293 / 1000000000000), orderedInterval (30463102705 / 1000000000000) (30463102706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1350916099225217 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30470777142 / 1000000000000) (-30470753704 / 1000000000000), orderedInterval (30972984966 / 1000000000000) (30973008404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (436858510166561 / 800000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7490723314 / 1000000000000) (7490723315 / 1000000000000), orderedInterval (33305355594 / 1000000000000) (33305355595 / 1000000000000)))) (orderedInterval (8648020500 / 1000000000000) (8648020751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (394193948521219 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-74862926750 / 1000000000000) (-74862922983 / 1000000000000), orderedInterval (29627829671 / 1000000000000) (29627833438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1058860393693543 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49009180993 / 1000000000000) (49009181170 / 1000000000000), orderedInterval (-1830438463 / 1000000000000) (-1830438286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2875011946558731 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-3370445848 / 1000000000000) (-3370445847 / 1000000000000), orderedInterval (-29567377711 / 1000000000000) (-29567377710 / 1000000000000)))) (orderedInterval (2841224162 / 1000000000000) (2841224265 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2117720787388003 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (22703084443 / 1000000000000) (22703089172 / 1000000000000), orderedInterval (-26232740013 / 1000000000000) (-26232735285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3628750664583919 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1394075040 / 1000000000000) (-1394075039 / 1000000000000), orderedInterval (-26453107985 / 1000000000000) (-26453107984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2672921315625421 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4420013374 / 1000000000000) (4420013375 / 1000000000000), orderedInterval (-30550956196 / 1000000000000) (-30550956194 / 1000000000000)))) (orderedInterval (149821841 / 1000000000000) (149821868 / 1000000000000))) = true
  rfl'

theorem compactCertificate587_chunkChecks0_1 :
    compactCertificate587.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4100948670734083 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23860806333 / 1000000000000) (23860896469 / 1000000000000), orderedInterval (-7195583084 / 1000000000000) (-7195492948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2367683818980907 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28526258936 / 1000000000000) (28526346238 / 1000000000000), orderedInterval (-16203281328 / 1000000000000) (-16203194026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4201496485663463 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23543443534 / 1000000000000) (23543521610 / 1000000000000), orderedInterval (-7207975826 / 1000000000000) (-7207897750 / 1000000000000)))) (orderedInterval (1220606964 / 1000000000000) (1220640729 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3925583020696547 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23115359173 / 1000000000000) (23115391042 / 1000000000000), orderedInterval (-10706066148 / 1000000000000) (-10706034279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2801481274848851 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-16531993887 / 1000000000000) (-16531993886 / 1000000000000), orderedInterval (-25200679028 / 1000000000000) (-25200679027 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3176581181080629 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-3040482724 / 1000000000000) (-3040482723 / 1000000000000), orderedInterval (-28147633694 / 1000000000000) (-28147633693 / 1000000000000)))) (orderedInterval (-1965230299 / 1000000000000) (-1965229668 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2648302213548901 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (474019303 / 1000000000000) (474019304 / 1000000000000), orderedInterval (-31005633764 / 1000000000000) (-31005633763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2339855320618921 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32578482343 / 1000000000000) (32578482459 / 1000000000000), orderedInterval (5163330734 / 1000000000000) (5163330850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (678181272157179 / 800000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7621255088 / 1000000000000) (7621255089 / 1000000000000), orderedInterval (26318300551 / 1000000000000) (26318300552 / 1000000000000)))) (orderedInterval (-1663750262 / 1000000000000) (-1663750211 / 1000000000000))) = true
  rfl'

theorem compactCertificate587_chunkChecks0_2 :
    compactCertificate587.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1875885089511713 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36700455921 / 1000000000000) (-36700454654 / 1000000000000), orderedInterval (3288313403 / 1000000000000) (3288314670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1590208565237593 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (24059403751 / 1000000000000) (24059408383 / 1000000000000), orderedInterval (-32006728763 / 1000000000000) (-32006724131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (995078684374579 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49558155718 / 1000000000000) (-49558155713 / 1000000000000), orderedInterval (-10052120132 / 1000000000000) (-10052120127 / 1000000000000)))) (orderedInterval (2892984614 / 1000000000000) (2892985194 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (535156625938893 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (33967253716 / 1000000000000) (33967258497 / 1000000000000), orderedInterval (-60165461043 / 1000000000000) (-60165456262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1453054342215679 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15376375804 / 1000000000000) (-15376375568 / 1000000000000), orderedInterval (38957897545 / 1000000000000) (38957897781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1984021478858783 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14571615366 / 1000000000000) (14571615367 / 1000000000000), orderedInterval (32713925015 / 1000000000000) (32713925016 / 1000000000000)))) (orderedInterval (-1395119855 / 1000000000000) (-1395119706 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (838921315625421 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1565757802 / 1000000000000) (-1565757800 / 1000000000000), orderedInterval (-55068743748 / 1000000000000) (-55068743745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3410168572498541 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25326198451 / 1000000000000) (-25326112021 / 1000000000000), orderedInterval (10277210018 / 1000000000000) (10277296448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2277834565359619 / 4000000000000) 0 (IntervalRat.scale (917 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33402104548 / 1000000000000) (-33402103167 / 1000000000000), orderedInterval (1525183321 / 1000000000000) (1525184702 / 1000000000000)))) (orderedInterval (8319272170 / 1000000000000) (8319279591 / 1000000000000))) = true
  rfl'

theorem compactCertificate587_chunkChecks0 :
    compactCertificate587.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate587.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate587_chunkChecks0_0
    compactCertificate587_chunkChecks0_1 compactCertificate587_chunkChecks0_2

theorem compactCertificate587_chunkChecks1_0 :
    compactCertificate587.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (917 / 2) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (21425668292 / 1000000000000) (21425668293 / 1000000000000), orderedInterval (30463102705 / 1000000000000) (30463102706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1350916099225217 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30470777142 / 1000000000000) (-30470753704 / 1000000000000), orderedInterval (30972984966 / 1000000000000) (30973008404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (436858510166561 / 800000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7490723314 / 1000000000000) (7490723315 / 1000000000000), orderedInterval (33305355594 / 1000000000000) (33305355595 / 1000000000000)))) (orderedInterval (14614779287 / 1000000000000) (14614779485 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (394193948521219 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-74862926750 / 1000000000000) (-74862922983 / 1000000000000), orderedInterval (29627829671 / 1000000000000) (29627833438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1058860393693543 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49009180993 / 1000000000000) (49009181170 / 1000000000000), orderedInterval (-1830438463 / 1000000000000) (-1830438286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2875011946558731 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-3370445848 / 1000000000000) (-3370445847 / 1000000000000), orderedInterval (-29567377711 / 1000000000000) (-29567377710 / 1000000000000)))) (orderedInterval (3187355336 / 1000000000000) (3187355412 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2117720787388003 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (22703084443 / 1000000000000) (22703089172 / 1000000000000), orderedInterval (-26232740013 / 1000000000000) (-26232735285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3628750664583919 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1394075040 / 1000000000000) (-1394075039 / 1000000000000), orderedInterval (-26453107985 / 1000000000000) (-26453107984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2672921315625421 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4420013374 / 1000000000000) (4420013375 / 1000000000000), orderedInterval (-30550956196 / 1000000000000) (-30550956194 / 1000000000000)))) (orderedInterval (538277366 / 1000000000000) (538277411 / 1000000000000))) = true
  rfl'

theorem compactCertificate587_chunkChecks1_1 :
    compactCertificate587.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4100948670734083 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23860806333 / 1000000000000) (23860896469 / 1000000000000), orderedInterval (-7195583084 / 1000000000000) (-7195492948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2367683818980907 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28526258936 / 1000000000000) (28526346238 / 1000000000000), orderedInterval (-16203281328 / 1000000000000) (-16203194026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4201496485663463 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23543443534 / 1000000000000) (23543521610 / 1000000000000), orderedInterval (-7207975826 / 1000000000000) (-7207897750 / 1000000000000)))) (orderedInterval (-1038324913 / 1000000000000) (-1038254947 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3925583020696547 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23115359173 / 1000000000000) (23115391042 / 1000000000000), orderedInterval (-10706066148 / 1000000000000) (-10706034279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2801481274848851 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-16531993887 / 1000000000000) (-16531993886 / 1000000000000), orderedInterval (-25200679028 / 1000000000000) (-25200679027 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3176581181080629 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-3040482724 / 1000000000000) (-3040482723 / 1000000000000), orderedInterval (-28147633694 / 1000000000000) (-28147633693 / 1000000000000)))) (orderedInterval (-2979748304 / 1000000000000) (-2979746983 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2648302213548901 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (474019303 / 1000000000000) (474019304 / 1000000000000), orderedInterval (-31005633764 / 1000000000000) (-31005633763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2339855320618921 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32578482343 / 1000000000000) (32578482459 / 1000000000000), orderedInterval (5163330734 / 1000000000000) (5163330850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (678181272157179 / 800000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7621255088 / 1000000000000) (7621255089 / 1000000000000), orderedInterval (26318300551 / 1000000000000) (26318300552 / 1000000000000)))) (orderedInterval (351899575 / 1000000000000) (351899647 / 1000000000000))) = true
  rfl'

theorem compactCertificate587_chunkChecks1_2 :
    compactCertificate587.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1875885089511713 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36700455921 / 1000000000000) (-36700454654 / 1000000000000), orderedInterval (3288313403 / 1000000000000) (3288314670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1590208565237593 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (24059403751 / 1000000000000) (24059408383 / 1000000000000), orderedInterval (-32006728763 / 1000000000000) (-32006724131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (995078684374579 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49558155718 / 1000000000000) (-49558155713 / 1000000000000), orderedInterval (-10052120132 / 1000000000000) (-10052120127 / 1000000000000)))) (orderedInterval (855426951 / 1000000000000) (855427492 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (535156625938893 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (33967253716 / 1000000000000) (33967258497 / 1000000000000), orderedInterval (-60165461043 / 1000000000000) (-60165456262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1453054342215679 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15376375804 / 1000000000000) (-15376375568 / 1000000000000), orderedInterval (38957897545 / 1000000000000) (38957897781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1984021478858783 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14571615366 / 1000000000000) (14571615367 / 1000000000000), orderedInterval (32713925015 / 1000000000000) (32713925016 / 1000000000000)))) (orderedInterval (-3088317154 / 1000000000000) (-3088317075 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (838921315625421 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1565757802 / 1000000000000) (-1565757800 / 1000000000000), orderedInterval (-55068743748 / 1000000000000) (-55068743745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3410168572498541 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25326198451 / 1000000000000) (-25326112021 / 1000000000000), orderedInterval (10277210018 / 1000000000000) (10277296448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2277834565359619 / 4000000000000) 1 (IntervalRat.scale (917 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33402104548 / 1000000000000) (-33402103167 / 1000000000000), orderedInterval (1525183321 / 1000000000000) (1525184702 / 1000000000000)))) (orderedInterval (-2062840398 / 1000000000000) (-2062826816 / 1000000000000))) = true
  rfl'

theorem compactCertificate587_chunkChecks1 :
    compactCertificate587.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate587.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate587_chunkChecks1_0
    compactCertificate587_chunkChecks1_1 compactCertificate587_chunkChecks1_2

theorem compactCertificate587_chunkChecks2_0 :
    compactCertificate587.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (917 / 2) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (21425668292 / 1000000000000) (21425668293 / 1000000000000), orderedInterval (30463102705 / 1000000000000) (30463102706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1350916099225217 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30470777142 / 1000000000000) (-30470753704 / 1000000000000), orderedInterval (30972984966 / 1000000000000) (30973008404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (436858510166561 / 800000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7490723314 / 1000000000000) (7490723315 / 1000000000000), orderedInterval (33305355594 / 1000000000000) (33305355595 / 1000000000000)))) (orderedInterval (-8993720895 / 1000000000000) (-8993720734 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (394193948521219 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-74862926750 / 1000000000000) (-74862922983 / 1000000000000), orderedInterval (29627829671 / 1000000000000) (29627833438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1058860393693543 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49009180993 / 1000000000000) (49009181170 / 1000000000000), orderedInterval (-1830438463 / 1000000000000) (-1830438286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2875011946558731 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-3370445848 / 1000000000000) (-3370445847 / 1000000000000), orderedInterval (-29567377711 / 1000000000000) (-29567377710 / 1000000000000)))) (orderedInterval (-1229753137 / 1000000000000) (-1229753046 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2117720787388003 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (22703084443 / 1000000000000) (22703089172 / 1000000000000), orderedInterval (-26232740013 / 1000000000000) (-26232735285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3628750664583919 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1394075040 / 1000000000000) (-1394075039 / 1000000000000), orderedInterval (-26453107985 / 1000000000000) (-26453107984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2672921315625421 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4420013374 / 1000000000000) (4420013375 / 1000000000000), orderedInterval (-30550956196 / 1000000000000) (-30550956194 / 1000000000000)))) (orderedInterval (-396410348 / 1000000000000) (-396410268 / 1000000000000))) = true
  rfl'

theorem compactCertificate587_chunkChecks2_1 :
    compactCertificate587.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4100948670734083 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23860806333 / 1000000000000) (23860896469 / 1000000000000), orderedInterval (-7195583084 / 1000000000000) (-7195492948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2367683818980907 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28526258936 / 1000000000000) (28526346238 / 1000000000000), orderedInterval (-16203281328 / 1000000000000) (-16203194026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4201496485663463 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23543443534 / 1000000000000) (23543521610 / 1000000000000), orderedInterval (-7207975826 / 1000000000000) (-7207897750 / 1000000000000)))) (orderedInterval (113639333 / 1000000000000) (113789402 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3925583020696547 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23115359173 / 1000000000000) (23115391042 / 1000000000000), orderedInterval (-10706066148 / 1000000000000) (-10706034279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2801481274848851 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-16531993887 / 1000000000000) (-16531993886 / 1000000000000), orderedInterval (-25200679028 / 1000000000000) (-25200679027 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3176581181080629 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-3040482724 / 1000000000000) (-3040482723 / 1000000000000), orderedInterval (-28147633694 / 1000000000000) (-28147633693 / 1000000000000)))) (orderedInterval (5519953740 / 1000000000000) (5519956526 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2648302213548901 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (474019303 / 1000000000000) (474019304 / 1000000000000), orderedInterval (-31005633764 / 1000000000000) (-31005633763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2339855320618921 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32578482343 / 1000000000000) (32578482459 / 1000000000000), orderedInterval (5163330734 / 1000000000000) (5163330850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (678181272157179 / 800000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7621255088 / 1000000000000) (7621255089 / 1000000000000), orderedInterval (26318300551 / 1000000000000) (26318300552 / 1000000000000)))) (orderedInterval (2355407239 / 1000000000000) (2355407345 / 1000000000000))) = true
  rfl'

theorem compactCertificate587_chunkChecks2_2 :
    compactCertificate587.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1875885089511713 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36700455921 / 1000000000000) (-36700454654 / 1000000000000), orderedInterval (3288313403 / 1000000000000) (3288314670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1590208565237593 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (24059403751 / 1000000000000) (24059408383 / 1000000000000), orderedInterval (-32006728763 / 1000000000000) (-32006724131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (995078684374579 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49558155718 / 1000000000000) (-49558155713 / 1000000000000), orderedInterval (-10052120132 / 1000000000000) (-10052120127 / 1000000000000)))) (orderedInterval (-4642341529 / 1000000000000) (-4642341017 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (535156625938893 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (33967253716 / 1000000000000) (33967258497 / 1000000000000), orderedInterval (-60165461043 / 1000000000000) (-60165456262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1453054342215679 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15376375804 / 1000000000000) (-15376375568 / 1000000000000), orderedInterval (38957897545 / 1000000000000) (38957897781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1984021478858783 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14571615366 / 1000000000000) (14571615367 / 1000000000000), orderedInterval (32713925015 / 1000000000000) (32713925016 / 1000000000000)))) (orderedInterval (1148091050 / 1000000000000) (1148091111 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (838921315625421 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1565757802 / 1000000000000) (-1565757800 / 1000000000000), orderedInterval (-55068743748 / 1000000000000) (-55068743745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3410168572498541 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25326198451 / 1000000000000) (-25326112021 / 1000000000000), orderedInterval (10277210018 / 1000000000000) (10277296448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2277834565359619 / 4000000000000) 2 (IntervalRat.scale (917 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33402104548 / 1000000000000) (-33402103167 / 1000000000000), orderedInterval (1525183321 / 1000000000000) (1525184702 / 1000000000000)))) (orderedInterval (-16788840115 / 1000000000000) (-16788815098 / 1000000000000))) = true
  rfl'

theorem compactCertificate587_chunkChecks2 :
    compactCertificate587.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate587.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate587_chunkChecks2_0
    compactCertificate587_chunkChecks2_1 compactCertificate587_chunkChecks2_2

theorem compactCertificate587_chunkChecks3_0 :
    compactCertificate587.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (917 / 2) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (21425668292 / 1000000000000) (21425668293 / 1000000000000), orderedInterval (30463102705 / 1000000000000) (30463102706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1350916099225217 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30470777142 / 1000000000000) (-30470753704 / 1000000000000), orderedInterval (30972984966 / 1000000000000) (30973008404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (436858510166561 / 800000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7490723314 / 1000000000000) (7490723315 / 1000000000000), orderedInterval (33305355594 / 1000000000000) (33305355595 / 1000000000000)))) (orderedInterval (-15471938408 / 1000000000000) (-15471938272 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (394193948521219 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-74862926750 / 1000000000000) (-74862922983 / 1000000000000), orderedInterval (29627829671 / 1000000000000) (29627833438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1058860393693543 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49009180993 / 1000000000000) (49009181170 / 1000000000000), orderedInterval (-1830438463 / 1000000000000) (-1830438286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2875011946558731 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-3370445848 / 1000000000000) (-3370445847 / 1000000000000), orderedInterval (-29567377711 / 1000000000000) (-29567377710 / 1000000000000)))) (orderedInterval (-8078546607 / 1000000000000) (-8078546475 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2117720787388003 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (22703084443 / 1000000000000) (22703089172 / 1000000000000), orderedInterval (-26232740013 / 1000000000000) (-26232735285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3628750664583919 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1394075040 / 1000000000000) (-1394075039 / 1000000000000), orderedInterval (-26453107985 / 1000000000000) (-26453107984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2672921315625421 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4420013374 / 1000000000000) (4420013375 / 1000000000000), orderedInterval (-30550956196 / 1000000000000) (-30550956194 / 1000000000000)))) (orderedInterval (-4033448705 / 1000000000000) (-4033448560 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate587_chunkChecks3_1 :
    compactCertificate587.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4100948670734083 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23860806333 / 1000000000000) (23860896469 / 1000000000000), orderedInterval (-7195583084 / 1000000000000) (-7195492948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2367683818980907 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28526258936 / 1000000000000) (28526346238 / 1000000000000), orderedInterval (-16203281328 / 1000000000000) (-16203194026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4201496485663463 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23543443534 / 1000000000000) (23543521610 / 1000000000000), orderedInterval (-7207975826 / 1000000000000) (-7207897750 / 1000000000000)))) (orderedInterval (607375231 / 1000000000000) (607703750 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3925583020696547 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23115359173 / 1000000000000) (23115391042 / 1000000000000), orderedInterval (-10706066148 / 1000000000000) (-10706034279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2801481274848851 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-16531993887 / 1000000000000) (-16531993886 / 1000000000000), orderedInterval (-25200679028 / 1000000000000) (-25200679027 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3176581181080629 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-3040482724 / 1000000000000) (-3040482723 / 1000000000000), orderedInterval (-28147633694 / 1000000000000) (-28147633693 / 1000000000000)))) (orderedInterval (5846133656 / 1000000000000) (5846139553 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2648302213548901 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (474019303 / 1000000000000) (474019304 / 1000000000000), orderedInterval (-31005633764 / 1000000000000) (-31005633763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2339855320618921 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32578482343 / 1000000000000) (32578482459 / 1000000000000), orderedInterval (5163330734 / 1000000000000) (5163330850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (678181272157179 / 800000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7621255088 / 1000000000000) (7621255089 / 1000000000000), orderedInterval (26318300551 / 1000000000000) (26318300552 / 1000000000000)))) (orderedInterval (-2572531110 / 1000000000000) (-2572530950 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate587_chunkChecks3_2 :
    compactCertificate587.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1875885089511713 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36700455921 / 1000000000000) (-36700454654 / 1000000000000), orderedInterval (3288313403 / 1000000000000) (3288314670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1590208565237593 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (24059403751 / 1000000000000) (24059408383 / 1000000000000), orderedInterval (-32006728763 / 1000000000000) (-32006724131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (995078684374579 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49558155718 / 1000000000000) (-49558155713 / 1000000000000), orderedInterval (-10052120132 / 1000000000000) (-10052120127 / 1000000000000)))) (orderedInterval (-555895381 / 1000000000000) (-555894894 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (535156625938893 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (33967253716 / 1000000000000) (33967258497 / 1000000000000), orderedInterval (-60165461043 / 1000000000000) (-60165456262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1453054342215679 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15376375804 / 1000000000000) (-15376375568 / 1000000000000), orderedInterval (38957897545 / 1000000000000) (38957897781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1984021478858783 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14571615366 / 1000000000000) (14571615367 / 1000000000000), orderedInterval (32713925015 / 1000000000000) (32713925016 / 1000000000000)))) (orderedInterval (3583554878 / 1000000000000) (3583554934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (838921315625421 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1565757802 / 1000000000000) (-1565757800 / 1000000000000), orderedInterval (-55068743748 / 1000000000000) (-55068743745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3410168572498541 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25326198451 / 1000000000000) (-25326112021 / 1000000000000), orderedInterval (10277210018 / 1000000000000) (10277296448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2277834565359619 / 4000000000000) 3 (IntervalRat.scale (917 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33402104548 / 1000000000000) (-33402103167 / 1000000000000), orderedInterval (1525183321 / 1000000000000) (1525184702 / 1000000000000)))) (orderedInterval (5994859596 / 1000000000000) (5994905782 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate587_chunkChecks3 :
    compactCertificate587.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate587.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate587_chunkChecks3_0
    compactCertificate587_chunkChecks3_1 compactCertificate587_chunkChecks3_2

theorem compactCertificate587_chunkChecks4_0 :
    compactCertificate587.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (917 / 2) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (21425668292 / 1000000000000) (21425668293 / 1000000000000), orderedInterval (30463102705 / 1000000000000) (30463102706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1350916099225217 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-30470777142 / 1000000000000) (-30470753704 / 1000000000000), orderedInterval (30972984966 / 1000000000000) (30973008404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (436858510166561 / 800000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7490723314 / 1000000000000) (7490723315 / 1000000000000), orderedInterval (33305355594 / 1000000000000) (33305355595 / 1000000000000)))) (orderedInterval (9360686498 / 1000000000000) (9360686620 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (394193948521219 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-74862926750 / 1000000000000) (-74862922983 / 1000000000000), orderedInterval (29627829671 / 1000000000000) (29627833438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1058860393693543 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49009180993 / 1000000000000) (49009181170 / 1000000000000), orderedInterval (-1830438463 / 1000000000000) (-1830438286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2875011946558731 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-3370445848 / 1000000000000) (-3370445847 / 1000000000000), orderedInterval (-29567377711 / 1000000000000) (-29567377710 / 1000000000000)))) (orderedInterval (1682744706 / 1000000000000) (1682744907 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2117720787388003 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (22703084443 / 1000000000000) (22703089172 / 1000000000000), orderedInterval (-26232740013 / 1000000000000) (-26232735285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3628750664583919 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1394075040 / 1000000000000) (-1394075039 / 1000000000000), orderedInterval (-26453107985 / 1000000000000) (-26453107984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2672921315625421 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4420013374 / 1000000000000) (4420013375 / 1000000000000), orderedInterval (-30550956196 / 1000000000000) (-30550956194 / 1000000000000)))) (orderedInterval (1158557360 / 1000000000000) (1158557629 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate587_chunkChecks4_1 :
    compactCertificate587.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4100948670734083 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23860806333 / 1000000000000) (23860896469 / 1000000000000), orderedInterval (-7195583084 / 1000000000000) (-7195492948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2367683818980907 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (28526258936 / 1000000000000) (28526346238 / 1000000000000), orderedInterval (-16203281328 / 1000000000000) (-16203194026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4201496485663463 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23543443534 / 1000000000000) (23543521610 / 1000000000000), orderedInterval (-7207975826 / 1000000000000) (-7207897750 / 1000000000000)))) (orderedInterval (-7942905414 / 1000000000000) (-7942175991 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3925583020696547 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (23115359173 / 1000000000000) (23115391042 / 1000000000000), orderedInterval (-10706066148 / 1000000000000) (-10706034279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2801481274848851 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-16531993887 / 1000000000000) (-16531993886 / 1000000000000), orderedInterval (-25200679028 / 1000000000000) (-25200679027 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3176581181080629 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-3040482724 / 1000000000000) (-3040482723 / 1000000000000), orderedInterval (-28147633694 / 1000000000000) (-28147633693 / 1000000000000)))) (orderedInterval (-17157718163 / 1000000000000) (-17157705629 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2648302213548901 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (474019303 / 1000000000000) (474019304 / 1000000000000), orderedInterval (-31005633764 / 1000000000000) (-31005633763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2339855320618921 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (32578482343 / 1000000000000) (32578482459 / 1000000000000), orderedInterval (5163330734 / 1000000000000) (5163330850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (678181272157179 / 800000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7621255088 / 1000000000000) (7621255089 / 1000000000000), orderedInterval (26318300551 / 1000000000000) (26318300552 / 1000000000000)))) (orderedInterval (-2624187404 / 1000000000000) (-2624187155 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate587_chunkChecks4_2 :
    compactCertificate587.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1875885089511713 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36700455921 / 1000000000000) (-36700454654 / 1000000000000), orderedInterval (3288313403 / 1000000000000) (3288314670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1590208565237593 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (24059403751 / 1000000000000) (24059408383 / 1000000000000), orderedInterval (-32006728763 / 1000000000000) (-32006724131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (995078684374579 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49558155718 / 1000000000000) (-49558155713 / 1000000000000), orderedInterval (-10052120132 / 1000000000000) (-10052120127 / 1000000000000)))) (orderedInterval (5515723552 / 1000000000000) (5515724021 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (535156625938893 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (33967253716 / 1000000000000) (33967258497 / 1000000000000), orderedInterval (-60165461043 / 1000000000000) (-60165456262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1453054342215679 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15376375804 / 1000000000000) (-15376375568 / 1000000000000), orderedInterval (38957897545 / 1000000000000) (38957897781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1984021478858783 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (14571615366 / 1000000000000) (14571615367 / 1000000000000), orderedInterval (32713925015 / 1000000000000) (32713925016 / 1000000000000)))) (orderedInterval (-1412202991 / 1000000000000) (-1412202934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (838921315625421 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-1565757802 / 1000000000000) (-1565757800 / 1000000000000), orderedInterval (-55068743748 / 1000000000000) (-55068743745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3410168572498541 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25326198451 / 1000000000000) (-25326112021 / 1000000000000), orderedInterval (10277210018 / 1000000000000) (10277296448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2277834565359619 / 4000000000000) 4 (IntervalRat.scale (917 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33402104548 / 1000000000000) (-33402103167 / 1000000000000), orderedInterval (1525183321 / 1000000000000) (1525184702 / 1000000000000)))) (orderedInterval (39530010427 / 1000000000000) (39530095996 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate587_chunkChecks4 :
    compactCertificate587.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate587.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate587_chunkChecks4_0
    compactCertificate587_chunkChecks4_1 compactCertificate587_chunkChecks4_2

theorem compactCertificate587_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate587.chunkCheck r b = true :=
  compactCertificate587.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate587_chunkChecks0
    · exact compactCertificate587_chunkChecks1
    · exact compactCertificate587_chunkChecks2
    · exact compactCertificate587_chunkChecks3
    · exact compactCertificate587_chunkChecks4)

theorem compactCertificate587_coefficient0 :
    compactCertificate587.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate587_coefficient1 :
    compactCertificate587.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate587_coefficient2 :
    compactCertificate587.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate587_coefficient3 :
    compactCertificate587.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate587_coefficient4 :
    compactCertificate587.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate587_coefficients : ∀ r : Fin 5,
    compactCertificate587.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate587_coefficient0
  · exact compactCertificate587_coefficient1
  · exact compactCertificate587_coefficient2
  · exact compactCertificate587_coefficient3
  · exact compactCertificate587_coefficient4

theorem compactCertificate587_lower : (1 : ℚ) ≤ compactCertificate587.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate587, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate587_proves {t : ℝ} (ht : t ∈ compactCertificate587.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate587.proves compactCertificate587_states compactCertificate587_chunks
    compactCertificate587_coefficients compactCertificate587_lower ht

end Erdos232
