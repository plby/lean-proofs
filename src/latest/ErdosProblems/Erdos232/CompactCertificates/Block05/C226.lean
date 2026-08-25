/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate226 : CompactCertificate where
  left := 209 / 2
  right := 105
  center := 419 / 4
  grid := fun i =>
    match i.val with
    | 0 => 33
    | 1 => 25
    | 2 => 40
    | 3 => 7
    | 4 => 19
    | 5 => 52
    | 6 => 39
    | 7 => 66
    | 8 => 49
    | 9 => 75
    | 10 => 43
    | 11 => 76
    | 12 => 71
    | 13 => 51
    | 14 => 58
    | 15 => 48
    | 16 => 43
    | 17 => 62
    | 18 => 34
    | 19 => 29
    | 20 => 18
    | 21 => 10
    | 22 => 26
    | 23 => 36
    | 24 => 15
    | 25 => 62
    | _ => 41
  point := fun i =>
    match i.val with
    | 0 => 419 / 4
    | 1 => 617267007170519 / 8000000000000
    | 2 => 199611467567927 / 1600000000000
    | 3 => 180116973206533 / 8000000000000
    | 4 => 483819525580801 / 8000000000000
    | 5 => 1313664128253117 / 8000000000000
    | 6 => 967639051162021 / 8000000000000
    | 7 => 1658066007045433 / 8000000000000
    | 8 => 1221323916299947 / 8000000000000
    | 9 => 1873824965144581 / 8000000000000
    | 10 => 1081853348040349 / 8000000000000
    | 11 => 1919767750810241 / 8000000000000
    | 12 => 1793696058529829 / 8000000000000
    | 13 => 1280066144123957 / 8000000000000
    | 14 => 1451458576742403 / 8000000000000
    | 15 => 1210074839124307 / 8000000000000
    | 16 => 1069137818254447 / 8000000000000
    | 17 => 309877811378253 / 1600000000000
    | 18 => 857138334247991 / 8000000000000
    | 19 => 726605658489151 / 8000000000000
    | 20 => 454676083700053 / 8000000000000
    | 21 => 244526309998251 / 8000000000000
    | 22 => 663936498787753 / 8000000000000
    | 23 => 906548527417481 / 8000000000000
    | 24 => 383323916299947 / 8000000000000
    | 25 => 1558190438251787 / 8000000000000
    | _ => 1040798999875333 / 8000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-74683758824 / 1000000000000) (-74683757250 / 1000000000000), orderedInterval (22712553503 / 1000000000000) (22712555077 / 1000000000000))
    | 1 => (orderedInterval (51112797247 / 1000000000000) (51112811902 / 1000000000000), orderedInterval (-75420249491 / 1000000000000) (-75420234836 / 1000000000000))
    | 2 => (orderedInterval (-8703472323 / 1000000000000) (-8703472287 / 1000000000000), orderedInterval (70937353986 / 1000000000000) (70937354022 / 1000000000000))
    | 3 => (orderedInterval (-162155095043 / 1000000000000) (-162155095042 / 1000000000000), orderedInterval (-40848195222 / 1000000000000) (-40848195221 / 1000000000000))
    | 4 => (orderedInterval (-102597298118 / 1000000000000) (-102597298093 / 1000000000000), orderedInterval (818982401 / 1000000000000) (818982425 / 1000000000000))
    | 5 => (orderedInterval (62156214496 / 1000000000000) (62156214618 / 1000000000000), orderedInterval (-3863165484 / 1000000000000) (-3863165362 / 1000000000000))
    | 6 => (orderedInterval (51169279956 / 1000000000000) (51169345295 / 1000000000000), orderedInterval (-51640962678 / 1000000000000) (-51640897338 / 1000000000000))
    | 7 => (orderedInterval (35616153246 / 1000000000000) (35616153247 / 1000000000000), orderedInterval (42377202285 / 1000000000000) (42377202286 / 1000000000000))
    | 8 => (orderedInterval (30275284056 / 1000000000000) (30275287295 / 1000000000000), orderedInterval (-57138180188 / 1000000000000) (-57138176949 / 1000000000000))
    | 9 => (orderedInterval (29714509661 / 1000000000000) (29714516983 / 1000000000000), orderedInterval (-42900304984 / 1000000000000) (-42900297662 / 1000000000000))
    | 10 => (orderedInterval (-54904452320 / 1000000000000) (-54904452319 / 1000000000000), orderedInterval (-40944486333 / 1000000000000) (-40944486332 / 1000000000000))
    | 11 => (orderedInterval (46945256486 / 1000000000000) (46945269697 / 1000000000000), orderedInterval (-21288425163 / 1000000000000) (-21288411951 / 1000000000000))
    | 12 => (orderedInterval (-49622140902 / 1000000000000) (-49622133571 / 1000000000000), orderedInterval (19527232669 / 1000000000000) (19527240000 / 1000000000000))
    | 13 => (orderedInterval (-34126204326 / 1000000000000) (-34126204325 / 1000000000000), orderedInterval (-52941248175 / 1000000000000) (-52941248174 / 1000000000000))
    | 14 => (orderedInterval (275882130 / 1000000000000) (275882134 / 1000000000000), orderedInterval (59234301570 / 1000000000000) (59234301573 / 1000000000000))
    | 15 => (orderedInterval (61513671124 / 1000000000000) (61513671125 / 1000000000000), orderedInterval (20408455200 / 1000000000000) (20408455201 / 1000000000000))
    | 16 => (orderedInterval (42414255237 / 1000000000000) (42414275942 / 1000000000000), orderedInterval (-54607298640 / 1000000000000) (-54607277934 / 1000000000000))
    | 17 => (orderedInterval (-18054592893 / 1000000000000) (-18054592543 / 1000000000000), orderedInterval (54462743612 / 1000000000000) (54462743961 / 1000000000000))
    | 18 => (orderedInterval (69124068184 / 1000000000000) (69124068185 / 1000000000000), orderedInterval (33789590441 / 1000000000000) (33789590442 / 1000000000000))
    | 19 => (orderedInterval (-40397807831 / 1000000000000) (-40397807830 / 1000000000000), orderedInterval (-73107829437 / 1000000000000) (-73107829436 / 1000000000000))
    | 20 => (orderedInterval (92788991881 / 1000000000000) (92788991882 / 1000000000000), orderedInterval (50088166091 / 1000000000000) (50088166092 / 1000000000000))
    | 21 => (orderedInterval (-9924496042 / 1000000000000) (-9924496010 / 1000000000000), orderedInterval (144148808285 / 1000000000000) (144148808317 / 1000000000000))
    | 22 => (orderedInterval (75842164250 / 1000000000000) (75842180458 / 1000000000000), orderedInterval (-44260415203 / 1000000000000) (-44260398995 / 1000000000000))
    | 23 => (orderedInterval (63293345118 / 1000000000000) (63293345119 / 1000000000000), orderedInterval (39869139284 / 1000000000000) (39869139285 / 1000000000000))
    | 24 => (orderedInterval (-115262352318 / 1000000000000) (-115262352295 / 1000000000000), orderedInterval (1616844566 / 1000000000000) (1616844589 / 1000000000000))
    | 25 => (orderedInterval (40199576536 / 1000000000000) (40199576537 / 1000000000000), orderedInterval (40547787134 / 1000000000000) (40547787135 / 1000000000000))
    | _ => (orderedInterval (-61110997527 / 1000000000000) (-61110980059 / 1000000000000), orderedInterval (34275174779 / 1000000000000) (34275192248 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-29636485114 / 1000000000000) (-29636484343 / 1000000000000)
      | 1 => orderedInterval (-6405401666 / 1000000000000) (-6405401643 / 1000000000000)
      | 2 => orderedInterval (-366850787 / 1000000000000) (-366850702 / 1000000000000)
      | 3 => orderedInterval (-2674334213 / 1000000000000) (-2674330992 / 1000000000000)
      | 4 => orderedInterval (-2332635171 / 1000000000000) (-2332635025 / 1000000000000)
      | 5 => orderedInterval (-2179157394 / 1000000000000) (-2179156189 / 1000000000000)
      | 6 => orderedInterval (-5745131154 / 1000000000000) (-5745131127 / 1000000000000)
      | 7 => orderedInterval (-6388094557 / 1000000000000) (-6388094175 / 1000000000000)
      | _ => orderedInterval (7498884705 / 1000000000000) (7498888012 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (13442557911 / 1000000000000) (13442558647 / 1000000000000)
      | 1 => orderedInterval (543035193 / 1000000000000) (543035222 / 1000000000000)
      | 2 => orderedInterval (-4598778131 / 1000000000000) (-4598778006 / 1000000000000)
      | 3 => orderedInterval (6195949158 / 1000000000000) (6195956457 / 1000000000000)
      | 4 => orderedInterval (-8920978019 / 1000000000000) (-8920977714 / 1000000000000)
      | 5 => orderedInterval (6905477202 / 1000000000000) (6905478746 / 1000000000000)
      | 6 => orderedInterval (-1053496059 / 1000000000000) (-1053496034 / 1000000000000)
      | 7 => orderedInterval (-3286594074 / 1000000000000) (-3286593770 / 1000000000000)
      | _ => orderedInterval (-14120089110 / 1000000000000) (-14120084997 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (29939743968 / 1000000000000) (29939744686 / 1000000000000)
      | 1 => orderedInterval (12020752592 / 1000000000000) (12020752635 / 1000000000000)
      | 2 => orderedInterval (2790358037 / 1000000000000) (2790358223 / 1000000000000)
      | 3 => orderedInterval (-1903679858 / 1000000000000) (-1903663243 / 1000000000000)
      | 4 => orderedInterval (3514910175 / 1000000000000) (3514910819 / 1000000000000)
      | 5 => orderedInterval (3984014057 / 1000000000000) (3984016053 / 1000000000000)
      | 6 => orderedInterval (8964770092 / 1000000000000) (8964770116 / 1000000000000)
      | 7 => orderedInterval (6772606736 / 1000000000000) (6772606982 / 1000000000000)
      | _ => orderedInterval (-6093225849 / 1000000000000) (-6093220693 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-16038661672 / 1000000000000) (-16038660971 / 1000000000000)
      | 1 => orderedInterval (-1182825683 / 1000000000000) (-1182825619 / 1000000000000)
      | 2 => orderedInterval (14372428920 / 1000000000000) (14372429198 / 1000000000000)
      | 3 => orderedInterval (-42295142088 / 1000000000000) (-42295104401 / 1000000000000)
      | 4 => orderedInterval (22823783999 / 1000000000000) (22823785361 / 1000000000000)
      | 5 => orderedInterval (-16050253337 / 1000000000000) (-16050250767 / 1000000000000)
      | 6 => orderedInterval (2737855091 / 1000000000000) (2737855114 / 1000000000000)
      | 7 => orderedInterval (3370151263 / 1000000000000) (3370151461 / 1000000000000)
      | _ => orderedInterval (33596127682 / 1000000000000) (33596134103 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-30180506205 / 1000000000000) (-30180505510 / 1000000000000)
      | 1 => orderedInterval (-27072865375 / 1000000000000) (-27072865275 / 1000000000000)
      | 2 => orderedInterval (-13809305265 / 1000000000000) (-13809304845 / 1000000000000)
      | 3 => orderedInterval (41322278949 / 1000000000000) (41322364805 / 1000000000000)
      | 4 => orderedInterval (786200158 / 1000000000000) (786203061 / 1000000000000)
      | 5 => orderedInterval (-8437693810 / 1000000000000) (-8437690465 / 1000000000000)
      | 6 => orderedInterval (-10594478930 / 1000000000000) (-10594478906 / 1000000000000)
      | 7 => orderedInterval (-7383850337 / 1000000000000) (-7383850175 / 1000000000000)
      | _ => orderedInterval (-12505246025 / 1000000000000) (-12505237957 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-48229205351 / 1000000000000) (-48229196184 / 1000000000000)
    | 1 => orderedInterval (-4892915929 / 1000000000000) (-4892901449 / 1000000000000)
    | 2 => orderedInterval (59990249950 / 1000000000000) (59990275578 / 1000000000000)
    | 3 => orderedInterval (1333464175 / 1000000000000) (1333513479 / 1000000000000)
    | _ => orderedInterval (-67875466840 / 1000000000000) (-67875365267 / 1000000000000)

theorem compactCertificate226_stateChecks0 :
    compactCertificate226.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (419 / 4)) (orderedInterval (-74683758824 / 1000000000000) (-74683757250 / 1000000000000), orderedInterval (22712553503 / 1000000000000) (22712555077 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (617267007170519 / 8000000000000)) (orderedInterval (51112797247 / 1000000000000) (51112811902 / 1000000000000), orderedInterval (-75420249491 / 1000000000000) (-75420234836 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (199611467567927 / 1600000000000)) (orderedInterval (-8703472323 / 1000000000000) (-8703472287 / 1000000000000), orderedInterval (70937353986 / 1000000000000) (70937354022 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState041, besselGridState043, besselGridState048, besselGridState049, besselGridState051, besselGridState052, besselGridState058, besselGridState062, besselGridState066, besselGridState071, besselGridState075, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate226_stateChecks1 :
    compactCertificate226.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 7 12 (180116973206533 / 8000000000000)) (orderedInterval (-162155095043 / 1000000000000) (-162155095042 / 1000000000000), orderedInterval (-40848195222 / 1000000000000) (-40848195221 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (483819525580801 / 8000000000000)) (orderedInterval (-102597298118 / 1000000000000) (-102597298093 / 1000000000000), orderedInterval (818982401 / 1000000000000) (818982425 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (1313664128253117 / 8000000000000)) (orderedInterval (62156214496 / 1000000000000) (62156214618 / 1000000000000), orderedInterval (-3863165484 / 1000000000000) (-3863165362 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState041, besselGridState043, besselGridState048, besselGridState049, besselGridState051, besselGridState052, besselGridState058, besselGridState062, besselGridState066, besselGridState071, besselGridState075, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate226_stateChecks2 :
    compactCertificate226.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (967639051162021 / 8000000000000)) (orderedInterval (51169279956 / 1000000000000) (51169345295 / 1000000000000), orderedInterval (-51640962678 / 1000000000000) (-51640897338 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (1658066007045433 / 8000000000000)) (orderedInterval (35616153246 / 1000000000000) (35616153247 / 1000000000000), orderedInterval (42377202285 / 1000000000000) (42377202286 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (1221323916299947 / 8000000000000)) (orderedInterval (30275284056 / 1000000000000) (30275287295 / 1000000000000), orderedInterval (-57138180188 / 1000000000000) (-57138176949 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState041, besselGridState043, besselGridState048, besselGridState049, besselGridState051, besselGridState052, besselGridState058, besselGridState062, besselGridState066, besselGridState071, besselGridState075, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate226_stateChecks3 :
    compactCertificate226.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (1873824965144581 / 8000000000000)) (orderedInterval (29714509661 / 1000000000000) (29714516983 / 1000000000000), orderedInterval (-42900304984 / 1000000000000) (-42900297662 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (1081853348040349 / 8000000000000)) (orderedInterval (-54904452320 / 1000000000000) (-54904452319 / 1000000000000), orderedInterval (-40944486333 / 1000000000000) (-40944486332 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (1919767750810241 / 8000000000000)) (orderedInterval (46945256486 / 1000000000000) (46945269697 / 1000000000000), orderedInterval (-21288425163 / 1000000000000) (-21288411951 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState041, besselGridState043, besselGridState048, besselGridState049, besselGridState051, besselGridState052, besselGridState058, besselGridState062, besselGridState066, besselGridState071, besselGridState075, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate226_stateChecks4 :
    compactCertificate226.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (1793696058529829 / 8000000000000)) (orderedInterval (-49622140902 / 1000000000000) (-49622133571 / 1000000000000), orderedInterval (19527232669 / 1000000000000) (19527240000 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (1280066144123957 / 8000000000000)) (orderedInterval (-34126204326 / 1000000000000) (-34126204325 / 1000000000000), orderedInterval (-52941248175 / 1000000000000) (-52941248174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (1451458576742403 / 8000000000000)) (orderedInterval (275882130 / 1000000000000) (275882134 / 1000000000000), orderedInterval (59234301570 / 1000000000000) (59234301573 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState041, besselGridState043, besselGridState048, besselGridState049, besselGridState051, besselGridState052, besselGridState058, besselGridState062, besselGridState066, besselGridState071, besselGridState075, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate226_stateChecks5 :
    compactCertificate226.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (1210074839124307 / 8000000000000)) (orderedInterval (61513671124 / 1000000000000) (61513671125 / 1000000000000), orderedInterval (20408455200 / 1000000000000) (20408455201 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (1069137818254447 / 8000000000000)) (orderedInterval (42414255237 / 1000000000000) (42414275942 / 1000000000000), orderedInterval (-54607298640 / 1000000000000) (-54607277934 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (309877811378253 / 1600000000000)) (orderedInterval (-18054592893 / 1000000000000) (-18054592543 / 1000000000000), orderedInterval (54462743612 / 1000000000000) (54462743961 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState041, besselGridState043, besselGridState048, besselGridState049, besselGridState051, besselGridState052, besselGridState058, besselGridState062, besselGridState066, besselGridState071, besselGridState075, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate226_stateChecks6 :
    compactCertificate226.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (857138334247991 / 8000000000000)) (orderedInterval (69124068184 / 1000000000000) (69124068185 / 1000000000000), orderedInterval (33789590441 / 1000000000000) (33789590442 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (726605658489151 / 8000000000000)) (orderedInterval (-40397807831 / 1000000000000) (-40397807830 / 1000000000000), orderedInterval (-73107829437 / 1000000000000) (-73107829436 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (454676083700053 / 8000000000000)) (orderedInterval (92788991881 / 1000000000000) (92788991882 / 1000000000000), orderedInterval (50088166091 / 1000000000000) (50088166092 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState041, besselGridState043, besselGridState048, besselGridState049, besselGridState051, besselGridState052, besselGridState058, besselGridState062, besselGridState066, besselGridState071, besselGridState075, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate226_stateChecks7 :
    compactCertificate226.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (244526309998251 / 8000000000000)) (orderedInterval (-9924496042 / 1000000000000) (-9924496010 / 1000000000000), orderedInterval (144148808285 / 1000000000000) (144148808317 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (663936498787753 / 8000000000000)) (orderedInterval (75842164250 / 1000000000000) (75842180458 / 1000000000000), orderedInterval (-44260415203 / 1000000000000) (-44260398995 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (906548527417481 / 8000000000000)) (orderedInterval (63293345118 / 1000000000000) (63293345119 / 1000000000000), orderedInterval (39869139284 / 1000000000000) (39869139285 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState041, besselGridState043, besselGridState048, besselGridState049, besselGridState051, besselGridState052, besselGridState058, besselGridState062, besselGridState066, besselGridState071, besselGridState075, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate226_stateChecks8 :
    compactCertificate226.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (383323916299947 / 8000000000000)) (orderedInterval (-115262352318 / 1000000000000) (-115262352295 / 1000000000000), orderedInterval (1616844566 / 1000000000000) (1616844589 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (1558190438251787 / 8000000000000)) (orderedInterval (40199576536 / 1000000000000) (40199576537 / 1000000000000), orderedInterval (40547787134 / 1000000000000) (40547787135 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (1040798999875333 / 8000000000000)) (orderedInterval (-61110997527 / 1000000000000) (-61110980059 / 1000000000000), orderedInterval (34275174779 / 1000000000000) (34275192248 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState007, besselGridState010, besselGridState015, besselGridState018, besselGridState019, besselGridState025, besselGridState026, besselGridState029, besselGridState033, besselGridState034, besselGridState036, besselGridState039, besselGridState040, besselGridState041, besselGridState043, besselGridState048, besselGridState049, besselGridState051, besselGridState052, besselGridState058, besselGridState062, besselGridState066, besselGridState071, besselGridState075, besselGridState076, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate226_states : ∀ j,
    BesselStateValid (compactCertificate226.point j) (compactCertificate226.state j) :=
  compactCertificate226.statesValid_of_checks3 compactCertificate226_stateChecks0
    compactCertificate226_stateChecks1 compactCertificate226_stateChecks2
    compactCertificate226_stateChecks3 compactCertificate226_stateChecks4
    compactCertificate226_stateChecks5 compactCertificate226_stateChecks6
    compactCertificate226_stateChecks7 compactCertificate226_stateChecks8

theorem compactCertificate226_chunkChecks0_0 :
    compactCertificate226.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (419 / 4) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-74683758824 / 1000000000000) (-74683757250 / 1000000000000), orderedInterval (22712553503 / 1000000000000) (22712555077 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (617267007170519 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51112797247 / 1000000000000) (51112811902 / 1000000000000), orderedInterval (-75420249491 / 1000000000000) (-75420234836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (199611467567927 / 1600000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8703472323 / 1000000000000) (-8703472287 / 1000000000000), orderedInterval (70937353986 / 1000000000000) (70937354022 / 1000000000000)))) (orderedInterval (-29636485114 / 1000000000000) (-29636484343 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (180116973206533 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-162155095043 / 1000000000000) (-162155095042 / 1000000000000), orderedInterval (-40848195222 / 1000000000000) (-40848195221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (483819525580801 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-102597298118 / 1000000000000) (-102597298093 / 1000000000000), orderedInterval (818982401 / 1000000000000) (818982425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1313664128253117 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (62156214496 / 1000000000000) (62156214618 / 1000000000000), orderedInterval (-3863165484 / 1000000000000) (-3863165362 / 1000000000000)))) (orderedInterval (-6405401666 / 1000000000000) (-6405401643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (967639051162021 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51169279956 / 1000000000000) (51169345295 / 1000000000000), orderedInterval (-51640962678 / 1000000000000) (-51640897338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1658066007045433 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35616153246 / 1000000000000) (35616153247 / 1000000000000), orderedInterval (42377202285 / 1000000000000) (42377202286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1221323916299947 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30275284056 / 1000000000000) (30275287295 / 1000000000000), orderedInterval (-57138180188 / 1000000000000) (-57138176949 / 1000000000000)))) (orderedInterval (-366850787 / 1000000000000) (-366850702 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate226_chunkChecks0_1 :
    compactCertificate226.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1873824965144581 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29714509661 / 1000000000000) (29714516983 / 1000000000000), orderedInterval (-42900304984 / 1000000000000) (-42900297662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1081853348040349 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-54904452320 / 1000000000000) (-54904452319 / 1000000000000), orderedInterval (-40944486333 / 1000000000000) (-40944486332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1919767750810241 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (46945256486 / 1000000000000) (46945269697 / 1000000000000), orderedInterval (-21288425163 / 1000000000000) (-21288411951 / 1000000000000)))) (orderedInterval (-2674334213 / 1000000000000) (-2674330992 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1793696058529829 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-49622140902 / 1000000000000) (-49622133571 / 1000000000000), orderedInterval (19527232669 / 1000000000000) (19527240000 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1280066144123957 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34126204326 / 1000000000000) (-34126204325 / 1000000000000), orderedInterval (-52941248175 / 1000000000000) (-52941248174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1451458576742403 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (275882130 / 1000000000000) (275882134 / 1000000000000), orderedInterval (59234301570 / 1000000000000) (59234301573 / 1000000000000)))) (orderedInterval (-2332635171 / 1000000000000) (-2332635025 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1210074839124307 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (61513671124 / 1000000000000) (61513671125 / 1000000000000), orderedInterval (20408455200 / 1000000000000) (20408455201 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1069137818254447 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42414255237 / 1000000000000) (42414275942 / 1000000000000), orderedInterval (-54607298640 / 1000000000000) (-54607277934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (309877811378253 / 1600000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-18054592893 / 1000000000000) (-18054592543 / 1000000000000), orderedInterval (54462743612 / 1000000000000) (54462743961 / 1000000000000)))) (orderedInterval (-2179157394 / 1000000000000) (-2179156189 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate226_chunkChecks0_2 :
    compactCertificate226.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (857138334247991 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (69124068184 / 1000000000000) (69124068185 / 1000000000000), orderedInterval (33789590441 / 1000000000000) (33789590442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (726605658489151 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40397807831 / 1000000000000) (-40397807830 / 1000000000000), orderedInterval (-73107829437 / 1000000000000) (-73107829436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (454676083700053 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (92788991881 / 1000000000000) (92788991882 / 1000000000000), orderedInterval (50088166091 / 1000000000000) (50088166092 / 1000000000000)))) (orderedInterval (-5745131154 / 1000000000000) (-5745131127 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (244526309998251 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-9924496042 / 1000000000000) (-9924496010 / 1000000000000), orderedInterval (144148808285 / 1000000000000) (144148808317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (663936498787753 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (75842164250 / 1000000000000) (75842180458 / 1000000000000), orderedInterval (-44260415203 / 1000000000000) (-44260398995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (906548527417481 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (63293345118 / 1000000000000) (63293345119 / 1000000000000), orderedInterval (39869139284 / 1000000000000) (39869139285 / 1000000000000)))) (orderedInterval (-6388094557 / 1000000000000) (-6388094175 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (383323916299947 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-115262352318 / 1000000000000) (-115262352295 / 1000000000000), orderedInterval (1616844566 / 1000000000000) (1616844589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1558190438251787 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40199576536 / 1000000000000) (40199576537 / 1000000000000), orderedInterval (40547787134 / 1000000000000) (40547787135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1040798999875333 / 8000000000000) 0 (IntervalRat.scale (419 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-61110997527 / 1000000000000) (-61110980059 / 1000000000000), orderedInterval (34275174779 / 1000000000000) (34275192248 / 1000000000000)))) (orderedInterval (7498884705 / 1000000000000) (7498888012 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate226_chunkChecks0 :
    compactCertificate226.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate226.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate226_chunkChecks0_0
    compactCertificate226_chunkChecks0_1 compactCertificate226_chunkChecks0_2

theorem compactCertificate226_chunkChecks1_0 :
    compactCertificate226.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (419 / 4) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-74683758824 / 1000000000000) (-74683757250 / 1000000000000), orderedInterval (22712553503 / 1000000000000) (22712555077 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (617267007170519 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51112797247 / 1000000000000) (51112811902 / 1000000000000), orderedInterval (-75420249491 / 1000000000000) (-75420234836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (199611467567927 / 1600000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8703472323 / 1000000000000) (-8703472287 / 1000000000000), orderedInterval (70937353986 / 1000000000000) (70937354022 / 1000000000000)))) (orderedInterval (13442557911 / 1000000000000) (13442558647 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (180116973206533 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-162155095043 / 1000000000000) (-162155095042 / 1000000000000), orderedInterval (-40848195222 / 1000000000000) (-40848195221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (483819525580801 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-102597298118 / 1000000000000) (-102597298093 / 1000000000000), orderedInterval (818982401 / 1000000000000) (818982425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1313664128253117 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (62156214496 / 1000000000000) (62156214618 / 1000000000000), orderedInterval (-3863165484 / 1000000000000) (-3863165362 / 1000000000000)))) (orderedInterval (543035193 / 1000000000000) (543035222 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (967639051162021 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51169279956 / 1000000000000) (51169345295 / 1000000000000), orderedInterval (-51640962678 / 1000000000000) (-51640897338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1658066007045433 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35616153246 / 1000000000000) (35616153247 / 1000000000000), orderedInterval (42377202285 / 1000000000000) (42377202286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1221323916299947 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30275284056 / 1000000000000) (30275287295 / 1000000000000), orderedInterval (-57138180188 / 1000000000000) (-57138176949 / 1000000000000)))) (orderedInterval (-4598778131 / 1000000000000) (-4598778006 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate226_chunkChecks1_1 :
    compactCertificate226.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1873824965144581 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29714509661 / 1000000000000) (29714516983 / 1000000000000), orderedInterval (-42900304984 / 1000000000000) (-42900297662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1081853348040349 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-54904452320 / 1000000000000) (-54904452319 / 1000000000000), orderedInterval (-40944486333 / 1000000000000) (-40944486332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1919767750810241 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (46945256486 / 1000000000000) (46945269697 / 1000000000000), orderedInterval (-21288425163 / 1000000000000) (-21288411951 / 1000000000000)))) (orderedInterval (6195949158 / 1000000000000) (6195956457 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1793696058529829 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-49622140902 / 1000000000000) (-49622133571 / 1000000000000), orderedInterval (19527232669 / 1000000000000) (19527240000 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1280066144123957 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34126204326 / 1000000000000) (-34126204325 / 1000000000000), orderedInterval (-52941248175 / 1000000000000) (-52941248174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1451458576742403 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (275882130 / 1000000000000) (275882134 / 1000000000000), orderedInterval (59234301570 / 1000000000000) (59234301573 / 1000000000000)))) (orderedInterval (-8920978019 / 1000000000000) (-8920977714 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1210074839124307 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (61513671124 / 1000000000000) (61513671125 / 1000000000000), orderedInterval (20408455200 / 1000000000000) (20408455201 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1069137818254447 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42414255237 / 1000000000000) (42414275942 / 1000000000000), orderedInterval (-54607298640 / 1000000000000) (-54607277934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (309877811378253 / 1600000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-18054592893 / 1000000000000) (-18054592543 / 1000000000000), orderedInterval (54462743612 / 1000000000000) (54462743961 / 1000000000000)))) (orderedInterval (6905477202 / 1000000000000) (6905478746 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate226_chunkChecks1_2 :
    compactCertificate226.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (857138334247991 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (69124068184 / 1000000000000) (69124068185 / 1000000000000), orderedInterval (33789590441 / 1000000000000) (33789590442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (726605658489151 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40397807831 / 1000000000000) (-40397807830 / 1000000000000), orderedInterval (-73107829437 / 1000000000000) (-73107829436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (454676083700053 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (92788991881 / 1000000000000) (92788991882 / 1000000000000), orderedInterval (50088166091 / 1000000000000) (50088166092 / 1000000000000)))) (orderedInterval (-1053496059 / 1000000000000) (-1053496034 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (244526309998251 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-9924496042 / 1000000000000) (-9924496010 / 1000000000000), orderedInterval (144148808285 / 1000000000000) (144148808317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (663936498787753 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (75842164250 / 1000000000000) (75842180458 / 1000000000000), orderedInterval (-44260415203 / 1000000000000) (-44260398995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (906548527417481 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (63293345118 / 1000000000000) (63293345119 / 1000000000000), orderedInterval (39869139284 / 1000000000000) (39869139285 / 1000000000000)))) (orderedInterval (-3286594074 / 1000000000000) (-3286593770 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (383323916299947 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-115262352318 / 1000000000000) (-115262352295 / 1000000000000), orderedInterval (1616844566 / 1000000000000) (1616844589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1558190438251787 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40199576536 / 1000000000000) (40199576537 / 1000000000000), orderedInterval (40547787134 / 1000000000000) (40547787135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1040798999875333 / 8000000000000) 1 (IntervalRat.scale (419 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-61110997527 / 1000000000000) (-61110980059 / 1000000000000), orderedInterval (34275174779 / 1000000000000) (34275192248 / 1000000000000)))) (orderedInterval (-14120089110 / 1000000000000) (-14120084997 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate226_chunkChecks1 :
    compactCertificate226.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate226.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate226_chunkChecks1_0
    compactCertificate226_chunkChecks1_1 compactCertificate226_chunkChecks1_2

theorem compactCertificate226_chunkChecks2_0 :
    compactCertificate226.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (419 / 4) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-74683758824 / 1000000000000) (-74683757250 / 1000000000000), orderedInterval (22712553503 / 1000000000000) (22712555077 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (617267007170519 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51112797247 / 1000000000000) (51112811902 / 1000000000000), orderedInterval (-75420249491 / 1000000000000) (-75420234836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (199611467567927 / 1600000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8703472323 / 1000000000000) (-8703472287 / 1000000000000), orderedInterval (70937353986 / 1000000000000) (70937354022 / 1000000000000)))) (orderedInterval (29939743968 / 1000000000000) (29939744686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (180116973206533 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-162155095043 / 1000000000000) (-162155095042 / 1000000000000), orderedInterval (-40848195222 / 1000000000000) (-40848195221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (483819525580801 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-102597298118 / 1000000000000) (-102597298093 / 1000000000000), orderedInterval (818982401 / 1000000000000) (818982425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1313664128253117 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (62156214496 / 1000000000000) (62156214618 / 1000000000000), orderedInterval (-3863165484 / 1000000000000) (-3863165362 / 1000000000000)))) (orderedInterval (12020752592 / 1000000000000) (12020752635 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (967639051162021 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51169279956 / 1000000000000) (51169345295 / 1000000000000), orderedInterval (-51640962678 / 1000000000000) (-51640897338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1658066007045433 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35616153246 / 1000000000000) (35616153247 / 1000000000000), orderedInterval (42377202285 / 1000000000000) (42377202286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1221323916299947 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30275284056 / 1000000000000) (30275287295 / 1000000000000), orderedInterval (-57138180188 / 1000000000000) (-57138176949 / 1000000000000)))) (orderedInterval (2790358037 / 1000000000000) (2790358223 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate226_chunkChecks2_1 :
    compactCertificate226.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1873824965144581 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29714509661 / 1000000000000) (29714516983 / 1000000000000), orderedInterval (-42900304984 / 1000000000000) (-42900297662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1081853348040349 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-54904452320 / 1000000000000) (-54904452319 / 1000000000000), orderedInterval (-40944486333 / 1000000000000) (-40944486332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1919767750810241 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (46945256486 / 1000000000000) (46945269697 / 1000000000000), orderedInterval (-21288425163 / 1000000000000) (-21288411951 / 1000000000000)))) (orderedInterval (-1903679858 / 1000000000000) (-1903663243 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1793696058529829 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-49622140902 / 1000000000000) (-49622133571 / 1000000000000), orderedInterval (19527232669 / 1000000000000) (19527240000 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1280066144123957 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34126204326 / 1000000000000) (-34126204325 / 1000000000000), orderedInterval (-52941248175 / 1000000000000) (-52941248174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1451458576742403 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (275882130 / 1000000000000) (275882134 / 1000000000000), orderedInterval (59234301570 / 1000000000000) (59234301573 / 1000000000000)))) (orderedInterval (3514910175 / 1000000000000) (3514910819 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1210074839124307 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (61513671124 / 1000000000000) (61513671125 / 1000000000000), orderedInterval (20408455200 / 1000000000000) (20408455201 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1069137818254447 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42414255237 / 1000000000000) (42414275942 / 1000000000000), orderedInterval (-54607298640 / 1000000000000) (-54607277934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (309877811378253 / 1600000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-18054592893 / 1000000000000) (-18054592543 / 1000000000000), orderedInterval (54462743612 / 1000000000000) (54462743961 / 1000000000000)))) (orderedInterval (3984014057 / 1000000000000) (3984016053 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate226_chunkChecks2_2 :
    compactCertificate226.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (857138334247991 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (69124068184 / 1000000000000) (69124068185 / 1000000000000), orderedInterval (33789590441 / 1000000000000) (33789590442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (726605658489151 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40397807831 / 1000000000000) (-40397807830 / 1000000000000), orderedInterval (-73107829437 / 1000000000000) (-73107829436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (454676083700053 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (92788991881 / 1000000000000) (92788991882 / 1000000000000), orderedInterval (50088166091 / 1000000000000) (50088166092 / 1000000000000)))) (orderedInterval (8964770092 / 1000000000000) (8964770116 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (244526309998251 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-9924496042 / 1000000000000) (-9924496010 / 1000000000000), orderedInterval (144148808285 / 1000000000000) (144148808317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (663936498787753 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (75842164250 / 1000000000000) (75842180458 / 1000000000000), orderedInterval (-44260415203 / 1000000000000) (-44260398995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (906548527417481 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (63293345118 / 1000000000000) (63293345119 / 1000000000000), orderedInterval (39869139284 / 1000000000000) (39869139285 / 1000000000000)))) (orderedInterval (6772606736 / 1000000000000) (6772606982 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (383323916299947 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-115262352318 / 1000000000000) (-115262352295 / 1000000000000), orderedInterval (1616844566 / 1000000000000) (1616844589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1558190438251787 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40199576536 / 1000000000000) (40199576537 / 1000000000000), orderedInterval (40547787134 / 1000000000000) (40547787135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1040798999875333 / 8000000000000) 2 (IntervalRat.scale (419 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-61110997527 / 1000000000000) (-61110980059 / 1000000000000), orderedInterval (34275174779 / 1000000000000) (34275192248 / 1000000000000)))) (orderedInterval (-6093225849 / 1000000000000) (-6093220693 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate226_chunkChecks2 :
    compactCertificate226.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate226.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate226_chunkChecks2_0
    compactCertificate226_chunkChecks2_1 compactCertificate226_chunkChecks2_2

theorem compactCertificate226_chunkChecks3_0 :
    compactCertificate226.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (419 / 4) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-74683758824 / 1000000000000) (-74683757250 / 1000000000000), orderedInterval (22712553503 / 1000000000000) (22712555077 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (617267007170519 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51112797247 / 1000000000000) (51112811902 / 1000000000000), orderedInterval (-75420249491 / 1000000000000) (-75420234836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (199611467567927 / 1600000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8703472323 / 1000000000000) (-8703472287 / 1000000000000), orderedInterval (70937353986 / 1000000000000) (70937354022 / 1000000000000)))) (orderedInterval (-16038661672 / 1000000000000) (-16038660971 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (180116973206533 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-162155095043 / 1000000000000) (-162155095042 / 1000000000000), orderedInterval (-40848195222 / 1000000000000) (-40848195221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (483819525580801 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-102597298118 / 1000000000000) (-102597298093 / 1000000000000), orderedInterval (818982401 / 1000000000000) (818982425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1313664128253117 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (62156214496 / 1000000000000) (62156214618 / 1000000000000), orderedInterval (-3863165484 / 1000000000000) (-3863165362 / 1000000000000)))) (orderedInterval (-1182825683 / 1000000000000) (-1182825619 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (967639051162021 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51169279956 / 1000000000000) (51169345295 / 1000000000000), orderedInterval (-51640962678 / 1000000000000) (-51640897338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1658066007045433 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35616153246 / 1000000000000) (35616153247 / 1000000000000), orderedInterval (42377202285 / 1000000000000) (42377202286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1221323916299947 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30275284056 / 1000000000000) (30275287295 / 1000000000000), orderedInterval (-57138180188 / 1000000000000) (-57138176949 / 1000000000000)))) (orderedInterval (14372428920 / 1000000000000) (14372429198 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate226_chunkChecks3_1 :
    compactCertificate226.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1873824965144581 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29714509661 / 1000000000000) (29714516983 / 1000000000000), orderedInterval (-42900304984 / 1000000000000) (-42900297662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1081853348040349 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-54904452320 / 1000000000000) (-54904452319 / 1000000000000), orderedInterval (-40944486333 / 1000000000000) (-40944486332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1919767750810241 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (46945256486 / 1000000000000) (46945269697 / 1000000000000), orderedInterval (-21288425163 / 1000000000000) (-21288411951 / 1000000000000)))) (orderedInterval (-42295142088 / 1000000000000) (-42295104401 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1793696058529829 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-49622140902 / 1000000000000) (-49622133571 / 1000000000000), orderedInterval (19527232669 / 1000000000000) (19527240000 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1280066144123957 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34126204326 / 1000000000000) (-34126204325 / 1000000000000), orderedInterval (-52941248175 / 1000000000000) (-52941248174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1451458576742403 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (275882130 / 1000000000000) (275882134 / 1000000000000), orderedInterval (59234301570 / 1000000000000) (59234301573 / 1000000000000)))) (orderedInterval (22823783999 / 1000000000000) (22823785361 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1210074839124307 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (61513671124 / 1000000000000) (61513671125 / 1000000000000), orderedInterval (20408455200 / 1000000000000) (20408455201 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1069137818254447 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42414255237 / 1000000000000) (42414275942 / 1000000000000), orderedInterval (-54607298640 / 1000000000000) (-54607277934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (309877811378253 / 1600000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-18054592893 / 1000000000000) (-18054592543 / 1000000000000), orderedInterval (54462743612 / 1000000000000) (54462743961 / 1000000000000)))) (orderedInterval (-16050253337 / 1000000000000) (-16050250767 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate226_chunkChecks3_2 :
    compactCertificate226.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (857138334247991 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (69124068184 / 1000000000000) (69124068185 / 1000000000000), orderedInterval (33789590441 / 1000000000000) (33789590442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (726605658489151 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40397807831 / 1000000000000) (-40397807830 / 1000000000000), orderedInterval (-73107829437 / 1000000000000) (-73107829436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (454676083700053 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (92788991881 / 1000000000000) (92788991882 / 1000000000000), orderedInterval (50088166091 / 1000000000000) (50088166092 / 1000000000000)))) (orderedInterval (2737855091 / 1000000000000) (2737855114 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (244526309998251 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-9924496042 / 1000000000000) (-9924496010 / 1000000000000), orderedInterval (144148808285 / 1000000000000) (144148808317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (663936498787753 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (75842164250 / 1000000000000) (75842180458 / 1000000000000), orderedInterval (-44260415203 / 1000000000000) (-44260398995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (906548527417481 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (63293345118 / 1000000000000) (63293345119 / 1000000000000), orderedInterval (39869139284 / 1000000000000) (39869139285 / 1000000000000)))) (orderedInterval (3370151263 / 1000000000000) (3370151461 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (383323916299947 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-115262352318 / 1000000000000) (-115262352295 / 1000000000000), orderedInterval (1616844566 / 1000000000000) (1616844589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1558190438251787 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40199576536 / 1000000000000) (40199576537 / 1000000000000), orderedInterval (40547787134 / 1000000000000) (40547787135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1040798999875333 / 8000000000000) 3 (IntervalRat.scale (419 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-61110997527 / 1000000000000) (-61110980059 / 1000000000000), orderedInterval (34275174779 / 1000000000000) (34275192248 / 1000000000000)))) (orderedInterval (33596127682 / 1000000000000) (33596134103 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate226_chunkChecks3 :
    compactCertificate226.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate226.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate226_chunkChecks3_0
    compactCertificate226_chunkChecks3_1 compactCertificate226_chunkChecks3_2

theorem compactCertificate226_chunkChecks4_0 :
    compactCertificate226.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (419 / 4) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-74683758824 / 1000000000000) (-74683757250 / 1000000000000), orderedInterval (22712553503 / 1000000000000) (22712555077 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (617267007170519 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51112797247 / 1000000000000) (51112811902 / 1000000000000), orderedInterval (-75420249491 / 1000000000000) (-75420234836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (199611467567927 / 1600000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8703472323 / 1000000000000) (-8703472287 / 1000000000000), orderedInterval (70937353986 / 1000000000000) (70937354022 / 1000000000000)))) (orderedInterval (-30180506205 / 1000000000000) (-30180505510 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (180116973206533 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-162155095043 / 1000000000000) (-162155095042 / 1000000000000), orderedInterval (-40848195222 / 1000000000000) (-40848195221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (483819525580801 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-102597298118 / 1000000000000) (-102597298093 / 1000000000000), orderedInterval (818982401 / 1000000000000) (818982425 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1313664128253117 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (62156214496 / 1000000000000) (62156214618 / 1000000000000), orderedInterval (-3863165484 / 1000000000000) (-3863165362 / 1000000000000)))) (orderedInterval (-27072865375 / 1000000000000) (-27072865275 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (967639051162021 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51169279956 / 1000000000000) (51169345295 / 1000000000000), orderedInterval (-51640962678 / 1000000000000) (-51640897338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1658066007045433 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35616153246 / 1000000000000) (35616153247 / 1000000000000), orderedInterval (42377202285 / 1000000000000) (42377202286 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1221323916299947 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30275284056 / 1000000000000) (30275287295 / 1000000000000), orderedInterval (-57138180188 / 1000000000000) (-57138176949 / 1000000000000)))) (orderedInterval (-13809305265 / 1000000000000) (-13809304845 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate226_chunkChecks4_1 :
    compactCertificate226.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1873824965144581 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29714509661 / 1000000000000) (29714516983 / 1000000000000), orderedInterval (-42900304984 / 1000000000000) (-42900297662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1081853348040349 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-54904452320 / 1000000000000) (-54904452319 / 1000000000000), orderedInterval (-40944486333 / 1000000000000) (-40944486332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1919767750810241 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (46945256486 / 1000000000000) (46945269697 / 1000000000000), orderedInterval (-21288425163 / 1000000000000) (-21288411951 / 1000000000000)))) (orderedInterval (41322278949 / 1000000000000) (41322364805 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1793696058529829 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-49622140902 / 1000000000000) (-49622133571 / 1000000000000), orderedInterval (19527232669 / 1000000000000) (19527240000 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1280066144123957 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34126204326 / 1000000000000) (-34126204325 / 1000000000000), orderedInterval (-52941248175 / 1000000000000) (-52941248174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1451458576742403 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (275882130 / 1000000000000) (275882134 / 1000000000000), orderedInterval (59234301570 / 1000000000000) (59234301573 / 1000000000000)))) (orderedInterval (786200158 / 1000000000000) (786203061 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1210074839124307 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (61513671124 / 1000000000000) (61513671125 / 1000000000000), orderedInterval (20408455200 / 1000000000000) (20408455201 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1069137818254447 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42414255237 / 1000000000000) (42414275942 / 1000000000000), orderedInterval (-54607298640 / 1000000000000) (-54607277934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (309877811378253 / 1600000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-18054592893 / 1000000000000) (-18054592543 / 1000000000000), orderedInterval (54462743612 / 1000000000000) (54462743961 / 1000000000000)))) (orderedInterval (-8437693810 / 1000000000000) (-8437690465 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate226_chunkChecks4_2 :
    compactCertificate226.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (857138334247991 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (69124068184 / 1000000000000) (69124068185 / 1000000000000), orderedInterval (33789590441 / 1000000000000) (33789590442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (726605658489151 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40397807831 / 1000000000000) (-40397807830 / 1000000000000), orderedInterval (-73107829437 / 1000000000000) (-73107829436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (454676083700053 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (92788991881 / 1000000000000) (92788991882 / 1000000000000), orderedInterval (50088166091 / 1000000000000) (50088166092 / 1000000000000)))) (orderedInterval (-10594478930 / 1000000000000) (-10594478906 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (244526309998251 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-9924496042 / 1000000000000) (-9924496010 / 1000000000000), orderedInterval (144148808285 / 1000000000000) (144148808317 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (663936498787753 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (75842164250 / 1000000000000) (75842180458 / 1000000000000), orderedInterval (-44260415203 / 1000000000000) (-44260398995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (906548527417481 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (63293345118 / 1000000000000) (63293345119 / 1000000000000), orderedInterval (39869139284 / 1000000000000) (39869139285 / 1000000000000)))) (orderedInterval (-7383850337 / 1000000000000) (-7383850175 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (383323916299947 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-115262352318 / 1000000000000) (-115262352295 / 1000000000000), orderedInterval (1616844566 / 1000000000000) (1616844589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1558190438251787 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40199576536 / 1000000000000) (40199576537 / 1000000000000), orderedInterval (40547787134 / 1000000000000) (40547787135 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1040798999875333 / 8000000000000) 4 (IntervalRat.scale (419 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-61110997527 / 1000000000000) (-61110980059 / 1000000000000), orderedInterval (34275174779 / 1000000000000) (34275192248 / 1000000000000)))) (orderedInterval (-12505246025 / 1000000000000) (-12505237957 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate226_chunkChecks4 :
    compactCertificate226.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate226.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate226_chunkChecks4_0
    compactCertificate226_chunkChecks4_1 compactCertificate226_chunkChecks4_2

theorem compactCertificate226_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate226.chunkCheck r b = true :=
  compactCertificate226.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate226_chunkChecks0
    · exact compactCertificate226_chunkChecks1
    · exact compactCertificate226_chunkChecks2
    · exact compactCertificate226_chunkChecks3
    · exact compactCertificate226_chunkChecks4)

theorem compactCertificate226_coefficient0 :
    compactCertificate226.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate226, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate226_coefficient1 :
    compactCertificate226.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate226, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate226_coefficient2 :
    compactCertificate226.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate226, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate226_coefficient3 :
    compactCertificate226.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate226, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate226_coefficient4 :
    compactCertificate226.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate226, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate226_coefficients : ∀ r : Fin 5,
    compactCertificate226.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate226_coefficient0
  · exact compactCertificate226_coefficient1
  · exact compactCertificate226_coefficient2
  · exact compactCertificate226_coefficient3
  · exact compactCertificate226_coefficient4

theorem compactCertificate226_lower : (1 : ℚ) ≤ compactCertificate226.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate226, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate226_proves {t : ℝ} (ht : t ∈ compactCertificate226.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate226.proves compactCertificate226_states compactCertificate226_chunks
    compactCertificate226_coefficients compactCertificate226_lower ht

end Erdos232
