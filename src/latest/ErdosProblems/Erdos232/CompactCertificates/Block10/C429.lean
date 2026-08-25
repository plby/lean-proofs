/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate429 : CompactCertificate where
  left := 300
  right := 301
  center := 601 / 2
  grid := fun i =>
    match i.val with
    | 0 => 96
    | 1 => 70
    | 2 => 114
    | 3 => 21
    | 4 => 55
    | 5 => 150
    | 6 => 111
    | 7 => 189
    | 8 => 139
    | 9 => 214
    | 10 => 124
    | 11 => 219
    | 12 => 205
    | 13 => 146
    | 14 => 166
    | 15 => 138
    | 16 => 122
    | 17 => 177
    | 18 => 98
    | 19 => 83
    | 20 => 52
    | 21 => 28
    | 22 => 76
    | 23 => 104
    | 24 => 44
    | 25 => 178
    | _ => 119
  point := fun i =>
    match i.val with
    | 0 => 601 / 2
    | 1 => 885387759688501 / 4000000000000
    | 2 => 286316210043733 / 800000000000
    | 3 => 258353940088607 / 4000000000000
    | 4 => 693975023565779 / 4000000000000
    | 5 => 1884277186348743 / 4000000000000
    | 6 => 1387950047132159 / 4000000000000
    | 7 => 2378276062611707 / 4000000000000
    | 8 => 1751827383523313 / 4000000000000
    | 9 => 2687753708954399 / 4000000000000
    | 10 => 1551775327380071 / 4000000000000
    | 11 => 2753652549491539 / 4000000000000
    | 12 => 2572819406148991 / 4000000000000
    | 13 => 1836085328445103 / 4000000000000
    | 14 => 2081925070697337 / 4000000000000
    | 15 => 1735692072347753 / 4000000000000
    | 16 => 1533536584178813 / 4000000000000
    | 17 => 444478674554487 / 800000000000
    | 18 => 1229451405448789 / 4000000000000
    | 19 => 1042219572200429 / 4000000000000
    | 20 => 652172616476687 / 4000000000000
    | 21 => 350740602169329 / 4000000000000
    | 22 => 952328963654987 / 4000000000000
    | 23 => 1300323782763499 / 4000000000000
    | 24 => 549827383523313 / 4000000000000
    | 25 => 2235017788518673 / 4000000000000
    | _ => 1492888302923807 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-13949560091 / 1000000000000) (-13949559946 / 1000000000000), orderedInterval (43886032803 / 1000000000000) (43886032947 / 1000000000000))
    | 1 => (orderedInterval (42709934319 / 1000000000000) (42710027625 / 1000000000000), orderedInterval (-32530651213 / 1000000000000) (-32530557907 / 1000000000000))
    | 2 => (orderedInterval (21638751020 / 1000000000000) (21638751021 / 1000000000000), orderedInterval (36171333050 / 1000000000000) (36171333051 / 1000000000000))
    | 3 => (orderedInterval (56179602711 / 1000000000000) (56179618834 / 1000000000000), orderedInterval (-82291526248 / 1000000000000) (-82291510125 / 1000000000000))
    | 4 => (orderedInterval (-60381993334 / 1000000000000) (-60381993317 / 1000000000000), orderedInterval (-4664384720 / 1000000000000) (-4664384703 / 1000000000000))
    | 5 => (orderedInterval (21226023152 / 1000000000000) (21226023153 / 1000000000000), orderedInterval (29992328378 / 1000000000000) (29992328379 / 1000000000000))
    | 6 => (orderedInterval (34697110394 / 1000000000000) (34697208145 / 1000000000000), orderedInterval (-25166007729 / 1000000000000) (-25165909978 / 1000000000000))
    | 7 => (orderedInterval (-32713720035 / 1000000000000) (-32713718801 / 1000000000000), orderedInterval (760280041 / 1000000000000) (760281275 / 1000000000000))
    | 8 => (orderedInterval (-33643970517 / 1000000000000) (-33643909695 / 1000000000000), orderedInterval (17974312782 / 1000000000000) (17974373604 / 1000000000000))
    | 9 => (orderedInterval (12630027335 / 1000000000000) (12630027336 / 1000000000000), orderedInterval (28060518889 / 1000000000000) (28060518890 / 1000000000000))
    | 10 => (orderedInterval (-29854329858 / 1000000000000) (-29854300260 / 1000000000000), orderedInterval (27419658411 / 1000000000000) (27419688009 / 1000000000000))
    | 11 => (orderedInterval (-28226692160 / 1000000000000) (-28226692151 / 1000000000000), orderedInterval (-11293993791 / 1000000000000) (-11293993782 / 1000000000000))
    | 12 => (orderedInterval (1146122929 / 1000000000000) (1146122930 / 1000000000000), orderedInterval (-31440496248 / 1000000000000) (-31440496247 / 1000000000000))
    | 13 => (orderedInterval (33743575316 / 1000000000000) (33743575317 / 1000000000000), orderedInterval (15720062299 / 1000000000000) (15720062300 / 1000000000000))
    | 14 => (orderedInterval (-8243766453 / 1000000000000) (-8243766443 / 1000000000000), orderedInterval (33995822768 / 1000000000000) (33995822778 / 1000000000000))
    | 15 => (orderedInterval (35242747861 / 1000000000000) (35242747863 / 1000000000000), orderedInterval (14961861014 / 1000000000000) (14961861016 / 1000000000000))
    | 16 => (orderedInterval (31790986527 / 1000000000000) (31790986528 / 1000000000000), orderedInterval (25450890660 / 1000000000000) (25450890661 / 1000000000000))
    | 17 => (orderedInterval (-10700031406 / 1000000000000) (-10700031405 / 1000000000000), orderedInterval (-32104807357 / 1000000000000) (-32104807356 / 1000000000000))
    | 18 => (orderedInterval (12216450866 / 1000000000000) (12216450867 / 1000000000000), orderedInterval (43820663883 / 1000000000000) (43820663884 / 1000000000000))
    | 19 => (orderedInterval (-27403107550 / 1000000000000) (-27403107549 / 1000000000000), orderedInterval (-41086136363 / 1000000000000) (-41086136362 / 1000000000000))
    | 20 => (orderedInterval (28018664588 / 1000000000000) (28018664589 / 1000000000000), orderedInterval (55767227446 / 1000000000000) (55767227447 / 1000000000000))
    | 21 => (orderedInterval (41188481336 / 1000000000000) (41188481337 / 1000000000000), orderedInterval (74356452242 / 1000000000000) (74356452243 / 1000000000000))
    | 22 => (orderedInterval (5474742429 / 1000000000000) (5474742430 / 1000000000000), orderedInterval (51408167666 / 1000000000000) (51408167667 / 1000000000000))
    | 23 => (orderedInterval (-33527596636 / 1000000000000) (-33527544571 / 1000000000000), orderedInterval (28934822231 / 1000000000000) (28934874296 / 1000000000000))
    | 24 => (orderedInterval (766134466 / 1000000000000) (766134471 / 1000000000000), orderedInterval (68047629893 / 1000000000000) (68047629897 / 1000000000000))
    | 25 => (orderedInterval (11133373541 / 1000000000000) (11133373542 / 1000000000000), orderedInterval (31855434370 / 1000000000000) (31855434371 / 1000000000000))
    | _ => (orderedInterval (-6482599241 / 1000000000000) (-6482599240 / 1000000000000), orderedInterval (-40780005296 / 1000000000000) (-40780005295 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-3861356990 / 1000000000000) (-3861356042 / 1000000000000)
      | 1 => orderedInterval (-4323111421 / 1000000000000) (-4323111208 / 1000000000000)
      | 2 => orderedInterval (195913579 / 1000000000000) (195915104 / 1000000000000)
      | 3 => orderedInterval (-8468754196 / 1000000000000) (-8468751882 / 1000000000000)
      | 4 => orderedInterval (3211916324 / 1000000000000) (3211916360 / 1000000000000)
      | 5 => orderedInterval (-1686283979 / 1000000000000) (-1686283950 / 1000000000000)
      | 6 => orderedInterval (509851701 / 1000000000000) (509851777 / 1000000000000)
      | 7 => orderedInterval (1684758259 / 1000000000000) (1684762285 / 1000000000000)
      | _ => orderedInterval (314649659 / 1000000000000) (314649743 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (19699593585 / 1000000000000) (19699594306 / 1000000000000)
      | 1 => orderedInterval (-3248816789 / 1000000000000) (-3248816710 / 1000000000000)
      | 2 => orderedInterval (586713301 / 1000000000000) (586715548 / 1000000000000)
      | 3 => orderedInterval (-12204367929 / 1000000000000) (-12204364847 / 1000000000000)
      | 4 => orderedInterval (3187653454 / 1000000000000) (3187653512 / 1000000000000)
      | 5 => orderedInterval (-3128532157 / 1000000000000) (-3128532115 / 1000000000000)
      | 6 => orderedInterval (-4165208811 / 1000000000000) (-4165208741 / 1000000000000)
      | 7 => orderedInterval (-3723605421 / 1000000000000) (-3723601072 / 1000000000000)
      | _ => orderedInterval (4869091660 / 1000000000000) (4869091778 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (3446465187 / 1000000000000) (3446465747 / 1000000000000)
      | 1 => orderedInterval (4481988840 / 1000000000000) (4481988906 / 1000000000000)
      | 2 => orderedInterval (-2225011231 / 1000000000000) (-2225007900 / 1000000000000)
      | 3 => orderedInterval (36007054736 / 1000000000000) (36007058937 / 1000000000000)
      | 4 => orderedInterval (-7486374108 / 1000000000000) (-7486374011 / 1000000000000)
      | 5 => orderedInterval (3059649335 / 1000000000000) (3059649398 / 1000000000000)
      | 6 => orderedInterval (622820770 / 1000000000000) (622820837 / 1000000000000)
      | 7 => orderedInterval (-2851969623 / 1000000000000) (-2851964907 / 1000000000000)
      | _ => orderedInterval (1239971693 / 1000000000000) (1239971867 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-20870887721 / 1000000000000) (-20870887283 / 1000000000000)
      | 1 => orderedInterval (8222633023 / 1000000000000) (8222633111 / 1000000000000)
      | 2 => orderedInterval (-1155739765 / 1000000000000) (-1155734813 / 1000000000000)
      | 3 => orderedInterval (70557209635 / 1000000000000) (70557215543 / 1000000000000)
      | 4 => orderedInterval (-9945612384 / 1000000000000) (-9945612220 / 1000000000000)
      | 5 => orderedInterval (7689673432 / 1000000000000) (7689673529 / 1000000000000)
      | 6 => orderedInterval (5689670839 / 1000000000000) (5689670904 / 1000000000000)
      | 7 => orderedInterval (3431040540 / 1000000000000) (3431045641 / 1000000000000)
      | _ => orderedInterval (1967908508 / 1000000000000) (1967908775 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-2718098500 / 1000000000000) (-2718098146 / 1000000000000)
      | 1 => orderedInterval (-9413411603 / 1000000000000) (-9413411471 / 1000000000000)
      | 2 => orderedInterval (11803460829 / 1000000000000) (11803468252 / 1000000000000)
      | 3 => orderedInterval (-173239297831 / 1000000000000) (-173239289094 / 1000000000000)
      | 4 => orderedInterval (17379881219 / 1000000000000) (17379881503 / 1000000000000)
      | 5 => orderedInterval (-6303390399 / 1000000000000) (-6303390246 / 1000000000000)
      | 6 => orderedInterval (-1220108571 / 1000000000000) (-1220108506 / 1000000000000)
      | 7 => orderedInterval (3441838486 / 1000000000000) (3441844020 / 1000000000000)
      | _ => orderedInterval (-7952088982 / 1000000000000) (-7952088553 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-12422417064 / 1000000000000) (-12422407813 / 1000000000000)
    | 1 => orderedInterval (1872520893 / 1000000000000) (1872531659 / 1000000000000)
    | 2 => orderedInterval (36294595599 / 1000000000000) (36294608874 / 1000000000000)
    | 3 => orderedInterval (65585896107 / 1000000000000) (65585913187 / 1000000000000)
    | _ => orderedInterval (-168221215352 / 1000000000000) (-168221192241 / 1000000000000)

theorem compactCertificate429_stateChecks0 :
    compactCertificate429.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (601 / 2)) (orderedInterval (-13949560091 / 1000000000000) (-13949559946 / 1000000000000), orderedInterval (43886032803 / 1000000000000) (43886032947 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (885387759688501 / 4000000000000)) (orderedInterval (42709934319 / 1000000000000) (42710027625 / 1000000000000), orderedInterval (-32530651213 / 1000000000000) (-32530557907 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (286316210043733 / 800000000000)) (orderedInterval (21638751020 / 1000000000000) (21638751021 / 1000000000000), orderedInterval (36171333050 / 1000000000000) (36171333051 / 1000000000000))) = true
  rfl'

theorem compactCertificate429_stateChecks1 :
    compactCertificate429.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (258353940088607 / 4000000000000)) (orderedInterval (56179602711 / 1000000000000) (56179618834 / 1000000000000), orderedInterval (-82291526248 / 1000000000000) (-82291510125 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (693975023565779 / 4000000000000)) (orderedInterval (-60381993334 / 1000000000000) (-60381993317 / 1000000000000), orderedInterval (-4664384720 / 1000000000000) (-4664384703 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1884277186348743 / 4000000000000)) (orderedInterval (21226023152 / 1000000000000) (21226023153 / 1000000000000), orderedInterval (29992328378 / 1000000000000) (29992328379 / 1000000000000))) = true
  rfl'

theorem compactCertificate429_stateChecks2 :
    compactCertificate429.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1387950047132159 / 4000000000000)) (orderedInterval (34697110394 / 1000000000000) (34697208145 / 1000000000000), orderedInterval (-25166007729 / 1000000000000) (-25165909978 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2378276062611707 / 4000000000000)) (orderedInterval (-32713720035 / 1000000000000) (-32713718801 / 1000000000000), orderedInterval (760280041 / 1000000000000) (760281275 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1751827383523313 / 4000000000000)) (orderedInterval (-33643970517 / 1000000000000) (-33643909695 / 1000000000000), orderedInterval (17974312782 / 1000000000000) (17974373604 / 1000000000000))) = true
  rfl'

theorem compactCertificate429_stateChecks3 :
    compactCertificate429.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 214 12 (2687753708954399 / 4000000000000)) (orderedInterval (12630027335 / 1000000000000) (12630027336 / 1000000000000), orderedInterval (28060518889 / 1000000000000) (28060518890 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1551775327380071 / 4000000000000)) (orderedInterval (-29854329858 / 1000000000000) (-29854300260 / 1000000000000), orderedInterval (27419658411 / 1000000000000) (27419688009 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 219 12 (2753652549491539 / 4000000000000)) (orderedInterval (-28226692160 / 1000000000000) (-28226692151 / 1000000000000), orderedInterval (-11293993791 / 1000000000000) (-11293993782 / 1000000000000))) = true
  rfl'

theorem compactCertificate429_stateChecks4 :
    compactCertificate429.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (2572819406148991 / 4000000000000)) (orderedInterval (1146122929 / 1000000000000) (1146122930 / 1000000000000), orderedInterval (-31440496248 / 1000000000000) (-31440496247 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1836085328445103 / 4000000000000)) (orderedInterval (33743575316 / 1000000000000) (33743575317 / 1000000000000), orderedInterval (15720062299 / 1000000000000) (15720062300 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2081925070697337 / 4000000000000)) (orderedInterval (-8243766453 / 1000000000000) (-8243766443 / 1000000000000), orderedInterval (33995822768 / 1000000000000) (33995822778 / 1000000000000))) = true
  rfl'

theorem compactCertificate429_stateChecks5 :
    compactCertificate429.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1735692072347753 / 4000000000000)) (orderedInterval (35242747861 / 1000000000000) (35242747863 / 1000000000000), orderedInterval (14961861014 / 1000000000000) (14961861016 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1533536584178813 / 4000000000000)) (orderedInterval (31790986527 / 1000000000000) (31790986528 / 1000000000000), orderedInterval (25450890660 / 1000000000000) (25450890661 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (444478674554487 / 800000000000)) (orderedInterval (-10700031406 / 1000000000000) (-10700031405 / 1000000000000), orderedInterval (-32104807357 / 1000000000000) (-32104807356 / 1000000000000))) = true
  rfl'

theorem compactCertificate429_stateChecks6 :
    compactCertificate429.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1229451405448789 / 4000000000000)) (orderedInterval (12216450866 / 1000000000000) (12216450867 / 1000000000000), orderedInterval (43820663883 / 1000000000000) (43820663884 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1042219572200429 / 4000000000000)) (orderedInterval (-27403107550 / 1000000000000) (-27403107549 / 1000000000000), orderedInterval (-41086136363 / 1000000000000) (-41086136362 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (652172616476687 / 4000000000000)) (orderedInterval (28018664588 / 1000000000000) (28018664589 / 1000000000000), orderedInterval (55767227446 / 1000000000000) (55767227447 / 1000000000000))) = true
  rfl'

theorem compactCertificate429_stateChecks7 :
    compactCertificate429.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (350740602169329 / 4000000000000)) (orderedInterval (41188481336 / 1000000000000) (41188481337 / 1000000000000), orderedInterval (74356452242 / 1000000000000) (74356452243 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (952328963654987 / 4000000000000)) (orderedInterval (5474742429 / 1000000000000) (5474742430 / 1000000000000), orderedInterval (51408167666 / 1000000000000) (51408167667 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1300323782763499 / 4000000000000)) (orderedInterval (-33527596636 / 1000000000000) (-33527544571 / 1000000000000), orderedInterval (28934822231 / 1000000000000) (28934874296 / 1000000000000))) = true
  rfl'

theorem compactCertificate429_stateChecks8 :
    compactCertificate429.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (549827383523313 / 4000000000000)) (orderedInterval (766134466 / 1000000000000) (766134471 / 1000000000000), orderedInterval (68047629893 / 1000000000000) (68047629897 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2235017788518673 / 4000000000000)) (orderedInterval (11133373541 / 1000000000000) (11133373542 / 1000000000000), orderedInterval (31855434370 / 1000000000000) (31855434371 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1492888302923807 / 4000000000000)) (orderedInterval (-6482599241 / 1000000000000) (-6482599240 / 1000000000000), orderedInterval (-40780005296 / 1000000000000) (-40780005295 / 1000000000000))) = true
  rfl'

theorem compactCertificate429_states : ∀ j,
    BesselStateValid (compactCertificate429.point j) (compactCertificate429.state j) :=
  compactCertificate429.statesValid_of_checks3 compactCertificate429_stateChecks0
    compactCertificate429_stateChecks1 compactCertificate429_stateChecks2
    compactCertificate429_stateChecks3 compactCertificate429_stateChecks4
    compactCertificate429_stateChecks5 compactCertificate429_stateChecks6
    compactCertificate429_stateChecks7 compactCertificate429_stateChecks8

theorem compactCertificate429_chunkChecks0_0 :
    compactCertificate429.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (601 / 2) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-13949560091 / 1000000000000) (-13949559946 / 1000000000000), orderedInterval (43886032803 / 1000000000000) (43886032947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (885387759688501 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42709934319 / 1000000000000) (42710027625 / 1000000000000), orderedInterval (-32530651213 / 1000000000000) (-32530557907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (286316210043733 / 800000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21638751020 / 1000000000000) (21638751021 / 1000000000000), orderedInterval (36171333050 / 1000000000000) (36171333051 / 1000000000000)))) (orderedInterval (-3861356990 / 1000000000000) (-3861356042 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (258353940088607 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (56179602711 / 1000000000000) (56179618834 / 1000000000000), orderedInterval (-82291526248 / 1000000000000) (-82291510125 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (693975023565779 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-60381993334 / 1000000000000) (-60381993317 / 1000000000000), orderedInterval (-4664384720 / 1000000000000) (-4664384703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1884277186348743 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21226023152 / 1000000000000) (21226023153 / 1000000000000), orderedInterval (29992328378 / 1000000000000) (29992328379 / 1000000000000)))) (orderedInterval (-4323111421 / 1000000000000) (-4323111208 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1387950047132159 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34697110394 / 1000000000000) (34697208145 / 1000000000000), orderedInterval (-25166007729 / 1000000000000) (-25165909978 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2378276062611707 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32713720035 / 1000000000000) (-32713718801 / 1000000000000), orderedInterval (760280041 / 1000000000000) (760281275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1751827383523313 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33643970517 / 1000000000000) (-33643909695 / 1000000000000), orderedInterval (17974312782 / 1000000000000) (17974373604 / 1000000000000)))) (orderedInterval (195913579 / 1000000000000) (195915104 / 1000000000000))) = true
  rfl'

theorem compactCertificate429_chunkChecks0_1 :
    compactCertificate429.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2687753708954399 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12630027335 / 1000000000000) (12630027336 / 1000000000000), orderedInterval (28060518889 / 1000000000000) (28060518890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1551775327380071 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29854329858 / 1000000000000) (-29854300260 / 1000000000000), orderedInterval (27419658411 / 1000000000000) (27419688009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2753652549491539 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28226692160 / 1000000000000) (-28226692151 / 1000000000000), orderedInterval (-11293993791 / 1000000000000) (-11293993782 / 1000000000000)))) (orderedInterval (-8468754196 / 1000000000000) (-8468751882 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2572819406148991 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (1146122929 / 1000000000000) (1146122930 / 1000000000000), orderedInterval (-31440496248 / 1000000000000) (-31440496247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1836085328445103 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33743575316 / 1000000000000) (33743575317 / 1000000000000), orderedInterval (15720062299 / 1000000000000) (15720062300 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2081925070697337 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8243766453 / 1000000000000) (-8243766443 / 1000000000000), orderedInterval (33995822768 / 1000000000000) (33995822778 / 1000000000000)))) (orderedInterval (3211916324 / 1000000000000) (3211916360 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1735692072347753 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (35242747861 / 1000000000000) (35242747863 / 1000000000000), orderedInterval (14961861014 / 1000000000000) (14961861016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1533536584178813 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31790986527 / 1000000000000) (31790986528 / 1000000000000), orderedInterval (25450890660 / 1000000000000) (25450890661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (444478674554487 / 800000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10700031406 / 1000000000000) (-10700031405 / 1000000000000), orderedInterval (-32104807357 / 1000000000000) (-32104807356 / 1000000000000)))) (orderedInterval (-1686283979 / 1000000000000) (-1686283950 / 1000000000000))) = true
  rfl'

theorem compactCertificate429_chunkChecks0_2 :
    compactCertificate429.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1229451405448789 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (12216450866 / 1000000000000) (12216450867 / 1000000000000), orderedInterval (43820663883 / 1000000000000) (43820663884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1042219572200429 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-27403107550 / 1000000000000) (-27403107549 / 1000000000000), orderedInterval (-41086136363 / 1000000000000) (-41086136362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (652172616476687 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28018664588 / 1000000000000) (28018664589 / 1000000000000), orderedInterval (55767227446 / 1000000000000) (55767227447 / 1000000000000)))) (orderedInterval (509851701 / 1000000000000) (509851777 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (350740602169329 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41188481336 / 1000000000000) (41188481337 / 1000000000000), orderedInterval (74356452242 / 1000000000000) (74356452243 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (952328963654987 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (5474742429 / 1000000000000) (5474742430 / 1000000000000), orderedInterval (51408167666 / 1000000000000) (51408167667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1300323782763499 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33527596636 / 1000000000000) (-33527544571 / 1000000000000), orderedInterval (28934822231 / 1000000000000) (28934874296 / 1000000000000)))) (orderedInterval (1684758259 / 1000000000000) (1684762285 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (549827383523313 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (766134466 / 1000000000000) (766134471 / 1000000000000), orderedInterval (68047629893 / 1000000000000) (68047629897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2235017788518673 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (11133373541 / 1000000000000) (11133373542 / 1000000000000), orderedInterval (31855434370 / 1000000000000) (31855434371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1492888302923807 / 4000000000000) 0 (IntervalRat.scale (601 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-6482599241 / 1000000000000) (-6482599240 / 1000000000000), orderedInterval (-40780005296 / 1000000000000) (-40780005295 / 1000000000000)))) (orderedInterval (314649659 / 1000000000000) (314649743 / 1000000000000))) = true
  rfl'

theorem compactCertificate429_chunkChecks0 :
    compactCertificate429.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate429.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate429_chunkChecks0_0
    compactCertificate429_chunkChecks0_1 compactCertificate429_chunkChecks0_2

theorem compactCertificate429_chunkChecks1_0 :
    compactCertificate429.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (601 / 2) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-13949560091 / 1000000000000) (-13949559946 / 1000000000000), orderedInterval (43886032803 / 1000000000000) (43886032947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (885387759688501 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42709934319 / 1000000000000) (42710027625 / 1000000000000), orderedInterval (-32530651213 / 1000000000000) (-32530557907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (286316210043733 / 800000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21638751020 / 1000000000000) (21638751021 / 1000000000000), orderedInterval (36171333050 / 1000000000000) (36171333051 / 1000000000000)))) (orderedInterval (19699593585 / 1000000000000) (19699594306 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (258353940088607 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (56179602711 / 1000000000000) (56179618834 / 1000000000000), orderedInterval (-82291526248 / 1000000000000) (-82291510125 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (693975023565779 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-60381993334 / 1000000000000) (-60381993317 / 1000000000000), orderedInterval (-4664384720 / 1000000000000) (-4664384703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1884277186348743 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21226023152 / 1000000000000) (21226023153 / 1000000000000), orderedInterval (29992328378 / 1000000000000) (29992328379 / 1000000000000)))) (orderedInterval (-3248816789 / 1000000000000) (-3248816710 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1387950047132159 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34697110394 / 1000000000000) (34697208145 / 1000000000000), orderedInterval (-25166007729 / 1000000000000) (-25165909978 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2378276062611707 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32713720035 / 1000000000000) (-32713718801 / 1000000000000), orderedInterval (760280041 / 1000000000000) (760281275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1751827383523313 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33643970517 / 1000000000000) (-33643909695 / 1000000000000), orderedInterval (17974312782 / 1000000000000) (17974373604 / 1000000000000)))) (orderedInterval (586713301 / 1000000000000) (586715548 / 1000000000000))) = true
  rfl'

theorem compactCertificate429_chunkChecks1_1 :
    compactCertificate429.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2687753708954399 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12630027335 / 1000000000000) (12630027336 / 1000000000000), orderedInterval (28060518889 / 1000000000000) (28060518890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1551775327380071 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29854329858 / 1000000000000) (-29854300260 / 1000000000000), orderedInterval (27419658411 / 1000000000000) (27419688009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2753652549491539 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28226692160 / 1000000000000) (-28226692151 / 1000000000000), orderedInterval (-11293993791 / 1000000000000) (-11293993782 / 1000000000000)))) (orderedInterval (-12204367929 / 1000000000000) (-12204364847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2572819406148991 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (1146122929 / 1000000000000) (1146122930 / 1000000000000), orderedInterval (-31440496248 / 1000000000000) (-31440496247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1836085328445103 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33743575316 / 1000000000000) (33743575317 / 1000000000000), orderedInterval (15720062299 / 1000000000000) (15720062300 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2081925070697337 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8243766453 / 1000000000000) (-8243766443 / 1000000000000), orderedInterval (33995822768 / 1000000000000) (33995822778 / 1000000000000)))) (orderedInterval (3187653454 / 1000000000000) (3187653512 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1735692072347753 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (35242747861 / 1000000000000) (35242747863 / 1000000000000), orderedInterval (14961861014 / 1000000000000) (14961861016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1533536584178813 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31790986527 / 1000000000000) (31790986528 / 1000000000000), orderedInterval (25450890660 / 1000000000000) (25450890661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (444478674554487 / 800000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10700031406 / 1000000000000) (-10700031405 / 1000000000000), orderedInterval (-32104807357 / 1000000000000) (-32104807356 / 1000000000000)))) (orderedInterval (-3128532157 / 1000000000000) (-3128532115 / 1000000000000))) = true
  rfl'

theorem compactCertificate429_chunkChecks1_2 :
    compactCertificate429.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1229451405448789 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (12216450866 / 1000000000000) (12216450867 / 1000000000000), orderedInterval (43820663883 / 1000000000000) (43820663884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1042219572200429 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-27403107550 / 1000000000000) (-27403107549 / 1000000000000), orderedInterval (-41086136363 / 1000000000000) (-41086136362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (652172616476687 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28018664588 / 1000000000000) (28018664589 / 1000000000000), orderedInterval (55767227446 / 1000000000000) (55767227447 / 1000000000000)))) (orderedInterval (-4165208811 / 1000000000000) (-4165208741 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (350740602169329 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41188481336 / 1000000000000) (41188481337 / 1000000000000), orderedInterval (74356452242 / 1000000000000) (74356452243 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (952328963654987 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (5474742429 / 1000000000000) (5474742430 / 1000000000000), orderedInterval (51408167666 / 1000000000000) (51408167667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1300323782763499 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33527596636 / 1000000000000) (-33527544571 / 1000000000000), orderedInterval (28934822231 / 1000000000000) (28934874296 / 1000000000000)))) (orderedInterval (-3723605421 / 1000000000000) (-3723601072 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (549827383523313 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (766134466 / 1000000000000) (766134471 / 1000000000000), orderedInterval (68047629893 / 1000000000000) (68047629897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2235017788518673 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (11133373541 / 1000000000000) (11133373542 / 1000000000000), orderedInterval (31855434370 / 1000000000000) (31855434371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1492888302923807 / 4000000000000) 1 (IntervalRat.scale (601 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-6482599241 / 1000000000000) (-6482599240 / 1000000000000), orderedInterval (-40780005296 / 1000000000000) (-40780005295 / 1000000000000)))) (orderedInterval (4869091660 / 1000000000000) (4869091778 / 1000000000000))) = true
  rfl'

theorem compactCertificate429_chunkChecks1 :
    compactCertificate429.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate429.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate429_chunkChecks1_0
    compactCertificate429_chunkChecks1_1 compactCertificate429_chunkChecks1_2

theorem compactCertificate429_chunkChecks2_0 :
    compactCertificate429.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (601 / 2) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-13949560091 / 1000000000000) (-13949559946 / 1000000000000), orderedInterval (43886032803 / 1000000000000) (43886032947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (885387759688501 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42709934319 / 1000000000000) (42710027625 / 1000000000000), orderedInterval (-32530651213 / 1000000000000) (-32530557907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (286316210043733 / 800000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21638751020 / 1000000000000) (21638751021 / 1000000000000), orderedInterval (36171333050 / 1000000000000) (36171333051 / 1000000000000)))) (orderedInterval (3446465187 / 1000000000000) (3446465747 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (258353940088607 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (56179602711 / 1000000000000) (56179618834 / 1000000000000), orderedInterval (-82291526248 / 1000000000000) (-82291510125 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (693975023565779 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-60381993334 / 1000000000000) (-60381993317 / 1000000000000), orderedInterval (-4664384720 / 1000000000000) (-4664384703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1884277186348743 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21226023152 / 1000000000000) (21226023153 / 1000000000000), orderedInterval (29992328378 / 1000000000000) (29992328379 / 1000000000000)))) (orderedInterval (4481988840 / 1000000000000) (4481988906 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1387950047132159 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34697110394 / 1000000000000) (34697208145 / 1000000000000), orderedInterval (-25166007729 / 1000000000000) (-25165909978 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2378276062611707 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32713720035 / 1000000000000) (-32713718801 / 1000000000000), orderedInterval (760280041 / 1000000000000) (760281275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1751827383523313 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33643970517 / 1000000000000) (-33643909695 / 1000000000000), orderedInterval (17974312782 / 1000000000000) (17974373604 / 1000000000000)))) (orderedInterval (-2225011231 / 1000000000000) (-2225007900 / 1000000000000))) = true
  rfl'

theorem compactCertificate429_chunkChecks2_1 :
    compactCertificate429.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2687753708954399 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12630027335 / 1000000000000) (12630027336 / 1000000000000), orderedInterval (28060518889 / 1000000000000) (28060518890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1551775327380071 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29854329858 / 1000000000000) (-29854300260 / 1000000000000), orderedInterval (27419658411 / 1000000000000) (27419688009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2753652549491539 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28226692160 / 1000000000000) (-28226692151 / 1000000000000), orderedInterval (-11293993791 / 1000000000000) (-11293993782 / 1000000000000)))) (orderedInterval (36007054736 / 1000000000000) (36007058937 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2572819406148991 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (1146122929 / 1000000000000) (1146122930 / 1000000000000), orderedInterval (-31440496248 / 1000000000000) (-31440496247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1836085328445103 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33743575316 / 1000000000000) (33743575317 / 1000000000000), orderedInterval (15720062299 / 1000000000000) (15720062300 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2081925070697337 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8243766453 / 1000000000000) (-8243766443 / 1000000000000), orderedInterval (33995822768 / 1000000000000) (33995822778 / 1000000000000)))) (orderedInterval (-7486374108 / 1000000000000) (-7486374011 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1735692072347753 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (35242747861 / 1000000000000) (35242747863 / 1000000000000), orderedInterval (14961861014 / 1000000000000) (14961861016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1533536584178813 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31790986527 / 1000000000000) (31790986528 / 1000000000000), orderedInterval (25450890660 / 1000000000000) (25450890661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (444478674554487 / 800000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10700031406 / 1000000000000) (-10700031405 / 1000000000000), orderedInterval (-32104807357 / 1000000000000) (-32104807356 / 1000000000000)))) (orderedInterval (3059649335 / 1000000000000) (3059649398 / 1000000000000))) = true
  rfl'

theorem compactCertificate429_chunkChecks2_2 :
    compactCertificate429.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1229451405448789 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (12216450866 / 1000000000000) (12216450867 / 1000000000000), orderedInterval (43820663883 / 1000000000000) (43820663884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1042219572200429 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-27403107550 / 1000000000000) (-27403107549 / 1000000000000), orderedInterval (-41086136363 / 1000000000000) (-41086136362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (652172616476687 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28018664588 / 1000000000000) (28018664589 / 1000000000000), orderedInterval (55767227446 / 1000000000000) (55767227447 / 1000000000000)))) (orderedInterval (622820770 / 1000000000000) (622820837 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (350740602169329 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41188481336 / 1000000000000) (41188481337 / 1000000000000), orderedInterval (74356452242 / 1000000000000) (74356452243 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (952328963654987 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (5474742429 / 1000000000000) (5474742430 / 1000000000000), orderedInterval (51408167666 / 1000000000000) (51408167667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1300323782763499 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33527596636 / 1000000000000) (-33527544571 / 1000000000000), orderedInterval (28934822231 / 1000000000000) (28934874296 / 1000000000000)))) (orderedInterval (-2851969623 / 1000000000000) (-2851964907 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (549827383523313 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (766134466 / 1000000000000) (766134471 / 1000000000000), orderedInterval (68047629893 / 1000000000000) (68047629897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2235017788518673 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (11133373541 / 1000000000000) (11133373542 / 1000000000000), orderedInterval (31855434370 / 1000000000000) (31855434371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1492888302923807 / 4000000000000) 2 (IntervalRat.scale (601 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-6482599241 / 1000000000000) (-6482599240 / 1000000000000), orderedInterval (-40780005296 / 1000000000000) (-40780005295 / 1000000000000)))) (orderedInterval (1239971693 / 1000000000000) (1239971867 / 1000000000000))) = true
  rfl'

theorem compactCertificate429_chunkChecks2 :
    compactCertificate429.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate429.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate429_chunkChecks2_0
    compactCertificate429_chunkChecks2_1 compactCertificate429_chunkChecks2_2

theorem compactCertificate429_chunkChecks3_0 :
    compactCertificate429.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (601 / 2) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-13949560091 / 1000000000000) (-13949559946 / 1000000000000), orderedInterval (43886032803 / 1000000000000) (43886032947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (885387759688501 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42709934319 / 1000000000000) (42710027625 / 1000000000000), orderedInterval (-32530651213 / 1000000000000) (-32530557907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (286316210043733 / 800000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21638751020 / 1000000000000) (21638751021 / 1000000000000), orderedInterval (36171333050 / 1000000000000) (36171333051 / 1000000000000)))) (orderedInterval (-20870887721 / 1000000000000) (-20870887283 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (258353940088607 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (56179602711 / 1000000000000) (56179618834 / 1000000000000), orderedInterval (-82291526248 / 1000000000000) (-82291510125 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (693975023565779 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-60381993334 / 1000000000000) (-60381993317 / 1000000000000), orderedInterval (-4664384720 / 1000000000000) (-4664384703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1884277186348743 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21226023152 / 1000000000000) (21226023153 / 1000000000000), orderedInterval (29992328378 / 1000000000000) (29992328379 / 1000000000000)))) (orderedInterval (8222633023 / 1000000000000) (8222633111 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1387950047132159 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34697110394 / 1000000000000) (34697208145 / 1000000000000), orderedInterval (-25166007729 / 1000000000000) (-25165909978 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2378276062611707 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32713720035 / 1000000000000) (-32713718801 / 1000000000000), orderedInterval (760280041 / 1000000000000) (760281275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1751827383523313 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33643970517 / 1000000000000) (-33643909695 / 1000000000000), orderedInterval (17974312782 / 1000000000000) (17974373604 / 1000000000000)))) (orderedInterval (-1155739765 / 1000000000000) (-1155734813 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate429_chunkChecks3_1 :
    compactCertificate429.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2687753708954399 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12630027335 / 1000000000000) (12630027336 / 1000000000000), orderedInterval (28060518889 / 1000000000000) (28060518890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1551775327380071 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29854329858 / 1000000000000) (-29854300260 / 1000000000000), orderedInterval (27419658411 / 1000000000000) (27419688009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2753652549491539 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28226692160 / 1000000000000) (-28226692151 / 1000000000000), orderedInterval (-11293993791 / 1000000000000) (-11293993782 / 1000000000000)))) (orderedInterval (70557209635 / 1000000000000) (70557215543 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2572819406148991 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (1146122929 / 1000000000000) (1146122930 / 1000000000000), orderedInterval (-31440496248 / 1000000000000) (-31440496247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1836085328445103 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33743575316 / 1000000000000) (33743575317 / 1000000000000), orderedInterval (15720062299 / 1000000000000) (15720062300 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2081925070697337 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8243766453 / 1000000000000) (-8243766443 / 1000000000000), orderedInterval (33995822768 / 1000000000000) (33995822778 / 1000000000000)))) (orderedInterval (-9945612384 / 1000000000000) (-9945612220 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1735692072347753 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (35242747861 / 1000000000000) (35242747863 / 1000000000000), orderedInterval (14961861014 / 1000000000000) (14961861016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1533536584178813 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31790986527 / 1000000000000) (31790986528 / 1000000000000), orderedInterval (25450890660 / 1000000000000) (25450890661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (444478674554487 / 800000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10700031406 / 1000000000000) (-10700031405 / 1000000000000), orderedInterval (-32104807357 / 1000000000000) (-32104807356 / 1000000000000)))) (orderedInterval (7689673432 / 1000000000000) (7689673529 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate429_chunkChecks3_2 :
    compactCertificate429.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1229451405448789 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (12216450866 / 1000000000000) (12216450867 / 1000000000000), orderedInterval (43820663883 / 1000000000000) (43820663884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1042219572200429 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-27403107550 / 1000000000000) (-27403107549 / 1000000000000), orderedInterval (-41086136363 / 1000000000000) (-41086136362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (652172616476687 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28018664588 / 1000000000000) (28018664589 / 1000000000000), orderedInterval (55767227446 / 1000000000000) (55767227447 / 1000000000000)))) (orderedInterval (5689670839 / 1000000000000) (5689670904 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (350740602169329 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41188481336 / 1000000000000) (41188481337 / 1000000000000), orderedInterval (74356452242 / 1000000000000) (74356452243 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (952328963654987 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (5474742429 / 1000000000000) (5474742430 / 1000000000000), orderedInterval (51408167666 / 1000000000000) (51408167667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1300323782763499 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33527596636 / 1000000000000) (-33527544571 / 1000000000000), orderedInterval (28934822231 / 1000000000000) (28934874296 / 1000000000000)))) (orderedInterval (3431040540 / 1000000000000) (3431045641 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (549827383523313 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (766134466 / 1000000000000) (766134471 / 1000000000000), orderedInterval (68047629893 / 1000000000000) (68047629897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2235017788518673 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (11133373541 / 1000000000000) (11133373542 / 1000000000000), orderedInterval (31855434370 / 1000000000000) (31855434371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1492888302923807 / 4000000000000) 3 (IntervalRat.scale (601 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-6482599241 / 1000000000000) (-6482599240 / 1000000000000), orderedInterval (-40780005296 / 1000000000000) (-40780005295 / 1000000000000)))) (orderedInterval (1967908508 / 1000000000000) (1967908775 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate429_chunkChecks3 :
    compactCertificate429.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate429.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate429_chunkChecks3_0
    compactCertificate429_chunkChecks3_1 compactCertificate429_chunkChecks3_2

theorem compactCertificate429_chunkChecks4_0 :
    compactCertificate429.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (601 / 2) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-13949560091 / 1000000000000) (-13949559946 / 1000000000000), orderedInterval (43886032803 / 1000000000000) (43886032947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (885387759688501 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42709934319 / 1000000000000) (42710027625 / 1000000000000), orderedInterval (-32530651213 / 1000000000000) (-32530557907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (286316210043733 / 800000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21638751020 / 1000000000000) (21638751021 / 1000000000000), orderedInterval (36171333050 / 1000000000000) (36171333051 / 1000000000000)))) (orderedInterval (-2718098500 / 1000000000000) (-2718098146 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (258353940088607 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (56179602711 / 1000000000000) (56179618834 / 1000000000000), orderedInterval (-82291526248 / 1000000000000) (-82291510125 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (693975023565779 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-60381993334 / 1000000000000) (-60381993317 / 1000000000000), orderedInterval (-4664384720 / 1000000000000) (-4664384703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1884277186348743 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (21226023152 / 1000000000000) (21226023153 / 1000000000000), orderedInterval (29992328378 / 1000000000000) (29992328379 / 1000000000000)))) (orderedInterval (-9413411603 / 1000000000000) (-9413411471 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1387950047132159 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34697110394 / 1000000000000) (34697208145 / 1000000000000), orderedInterval (-25166007729 / 1000000000000) (-25165909978 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2378276062611707 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32713720035 / 1000000000000) (-32713718801 / 1000000000000), orderedInterval (760280041 / 1000000000000) (760281275 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1751827383523313 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33643970517 / 1000000000000) (-33643909695 / 1000000000000), orderedInterval (17974312782 / 1000000000000) (17974373604 / 1000000000000)))) (orderedInterval (11803460829 / 1000000000000) (11803468252 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate429_chunkChecks4_1 :
    compactCertificate429.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2687753708954399 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12630027335 / 1000000000000) (12630027336 / 1000000000000), orderedInterval (28060518889 / 1000000000000) (28060518890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1551775327380071 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29854329858 / 1000000000000) (-29854300260 / 1000000000000), orderedInterval (27419658411 / 1000000000000) (27419688009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2753652549491539 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28226692160 / 1000000000000) (-28226692151 / 1000000000000), orderedInterval (-11293993791 / 1000000000000) (-11293993782 / 1000000000000)))) (orderedInterval (-173239297831 / 1000000000000) (-173239289094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2572819406148991 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (1146122929 / 1000000000000) (1146122930 / 1000000000000), orderedInterval (-31440496248 / 1000000000000) (-31440496247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1836085328445103 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33743575316 / 1000000000000) (33743575317 / 1000000000000), orderedInterval (15720062299 / 1000000000000) (15720062300 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2081925070697337 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-8243766453 / 1000000000000) (-8243766443 / 1000000000000), orderedInterval (33995822768 / 1000000000000) (33995822778 / 1000000000000)))) (orderedInterval (17379881219 / 1000000000000) (17379881503 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1735692072347753 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (35242747861 / 1000000000000) (35242747863 / 1000000000000), orderedInterval (14961861014 / 1000000000000) (14961861016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1533536584178813 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31790986527 / 1000000000000) (31790986528 / 1000000000000), orderedInterval (25450890660 / 1000000000000) (25450890661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (444478674554487 / 800000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10700031406 / 1000000000000) (-10700031405 / 1000000000000), orderedInterval (-32104807357 / 1000000000000) (-32104807356 / 1000000000000)))) (orderedInterval (-6303390399 / 1000000000000) (-6303390246 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate429_chunkChecks4_2 :
    compactCertificate429.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1229451405448789 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (12216450866 / 1000000000000) (12216450867 / 1000000000000), orderedInterval (43820663883 / 1000000000000) (43820663884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1042219572200429 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-27403107550 / 1000000000000) (-27403107549 / 1000000000000), orderedInterval (-41086136363 / 1000000000000) (-41086136362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (652172616476687 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (28018664588 / 1000000000000) (28018664589 / 1000000000000), orderedInterval (55767227446 / 1000000000000) (55767227447 / 1000000000000)))) (orderedInterval (-1220108571 / 1000000000000) (-1220108506 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (350740602169329 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41188481336 / 1000000000000) (41188481337 / 1000000000000), orderedInterval (74356452242 / 1000000000000) (74356452243 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (952328963654987 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (5474742429 / 1000000000000) (5474742430 / 1000000000000), orderedInterval (51408167666 / 1000000000000) (51408167667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1300323782763499 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33527596636 / 1000000000000) (-33527544571 / 1000000000000), orderedInterval (28934822231 / 1000000000000) (28934874296 / 1000000000000)))) (orderedInterval (3441838486 / 1000000000000) (3441844020 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (549827383523313 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (766134466 / 1000000000000) (766134471 / 1000000000000), orderedInterval (68047629893 / 1000000000000) (68047629897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2235017788518673 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (11133373541 / 1000000000000) (11133373542 / 1000000000000), orderedInterval (31855434370 / 1000000000000) (31855434371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1492888302923807 / 4000000000000) 4 (IntervalRat.scale (601 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-6482599241 / 1000000000000) (-6482599240 / 1000000000000), orderedInterval (-40780005296 / 1000000000000) (-40780005295 / 1000000000000)))) (orderedInterval (-7952088982 / 1000000000000) (-7952088553 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate429_chunkChecks4 :
    compactCertificate429.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate429.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate429_chunkChecks4_0
    compactCertificate429_chunkChecks4_1 compactCertificate429_chunkChecks4_2

theorem compactCertificate429_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate429.chunkCheck r b = true :=
  compactCertificate429.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate429_chunkChecks0
    · exact compactCertificate429_chunkChecks1
    · exact compactCertificate429_chunkChecks2
    · exact compactCertificate429_chunkChecks3
    · exact compactCertificate429_chunkChecks4)

theorem compactCertificate429_coefficient0 :
    compactCertificate429.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate429_coefficient1 :
    compactCertificate429.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate429_coefficient2 :
    compactCertificate429.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate429_coefficient3 :
    compactCertificate429.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate429_coefficient4 :
    compactCertificate429.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate429_coefficients : ∀ r : Fin 5,
    compactCertificate429.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate429_coefficient0
  · exact compactCertificate429_coefficient1
  · exact compactCertificate429_coefficient2
  · exact compactCertificate429_coefficient3
  · exact compactCertificate429_coefficient4

theorem compactCertificate429_lower : (1 : ℚ) ≤ compactCertificate429.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate429, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate429_proves {t : ℝ} (ht : t ∈ compactCertificate429.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate429.proves compactCertificate429_states compactCertificate429_chunks
    compactCertificate429_coefficients compactCertificate429_lower ht

end Erdos232
