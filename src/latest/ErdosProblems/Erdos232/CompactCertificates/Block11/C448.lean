/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate448 : CompactCertificate where
  left := 319
  right := 320
  center := 639 / 2
  grid := fun i =>
    match i.val with
    | 0 => 102
    | 1 => 75
    | 2 => 121
    | 3 => 22
    | 4 => 59
    | 5 => 160
    | 6 => 117
    | 7 => 201
    | 8 => 148
    | 9 => 228
    | 10 => 131
    | 11 => 233
    | 12 => 218
    | 13 => 155
    | 14 => 176
    | 15 => 147
    | 16 => 130
    | 17 => 188
    | 18 => 104
    | 19 => 88
    | 20 => 55
    | 21 => 30
    | 22 => 81
    | 23 => 110
    | 24 => 47
    | 25 => 189
    | _ => 126
  point := fun i =>
    match i.val with
    | 0 => 639 / 2
    | 1 => 941369015708739 / 4000000000000
    | 2 => 304419398033187 / 800000000000
    | 3 => 274689130976073 / 4000000000000
    | 4 => 737853644024181 / 4000000000000
    | 5 => 2003416176500577 / 4000000000000
    | 6 => 1475707288049001 / 4000000000000
    | 7 => 2528649590696973 / 4000000000000
    | 8 => 1862591843712807 / 4000000000000
    | 9 => 2857694875244361 / 4000000000000
    | 10 => 1649890905483969 / 4000000000000
    | 11 => 2927760364600821 / 4000000000000
    | 12 => 2735493511695849 / 4000000000000
    | 13 => 1952177246050617 / 4000000000000
    | 14 => 2213560932072543 / 4000000000000
    | 15 => 1845436329833967 / 4000000000000
    | 16 => 1630498963877307 / 4000000000000
    | 17 => 472582151481393 / 800000000000
    | 18 => 1307187101633571 / 4000000000000
    | 19 => 1108116982755531 / 4000000000000
    | 20 => 693408156287193 / 4000000000000
    | 21 => 372917212622631 / 4000000000000
    | 22 => 1012542775000893 / 4000000000000
    | 23 => 1382540594319261 / 4000000000000
    | 24 => 584591843712807 / 4000000000000
    | 25 => 2376333389123847 / 4000000000000
    | _ => 1587280574988873 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-6998968127 / 1000000000000) (-6998968114 / 1000000000000), orderedInterval (44096856763 / 1000000000000) (44096856777 / 1000000000000))
    | 1 => (orderedInterval (-25284516558 / 1000000000000) (-25284516557 / 1000000000000), orderedInterval (-45397101992 / 1000000000000) (-45397101991 / 1000000000000))
    | 2 => (orderedInterval (-37765500788 / 1000000000000) (-37765500787 / 1000000000000), orderedInterval (-15659388649 / 1000000000000) (-15659388648 / 1000000000000))
    | 3 => (orderedInterval (32183337069 / 1000000000000) (32183337070 / 1000000000000), orderedInterval (90511634986 / 1000000000000) (90511634987 / 1000000000000))
    | 4 => (orderedInterval (6205867411 / 1000000000000) (6205867429 / 1000000000000), orderedInterval (-58435120629 / 1000000000000) (-58435120611 / 1000000000000))
    | 5 => (orderedInterval (-30297637382 / 1000000000000) (-30297544845 / 1000000000000), orderedInterval (18821794106 / 1000000000000) (18821886643 / 1000000000000))
    | 6 => (orderedInterval (-34866124173 / 1000000000000) (-34866030959 / 1000000000000), orderedInterval (22629387168 / 1000000000000) (22629480381 / 1000000000000))
    | 7 => (orderedInterval (-31623969097 / 1000000000000) (-31623968668 / 1000000000000), orderedInterval (-2616062741 / 1000000000000) (-2616062312 / 1000000000000))
    | 8 => (orderedInterval (36814022740 / 1000000000000) (36814022862 / 1000000000000), orderedInterval (3409618935 / 1000000000000) (3409619057 / 1000000000000))
    | 9 => (orderedInterval (-26245256956 / 1000000000000) (-26245196432 / 1000000000000), orderedInterval (14240975422 / 1000000000000) (14241035946 / 1000000000000))
    | 10 => (orderedInterval (-38910816079 / 1000000000000) (-38910814455 / 1000000000000), orderedInterval (5466582921 / 1000000000000) (5466584546 / 1000000000000))
    | 11 => (orderedInterval (-19760019661 / 1000000000000) (-19760019660 / 1000000000000), orderedInterval (-21879696241 / 1000000000000) (-21879696240 / 1000000000000))
    | 12 => (orderedInterval (-6318628970 / 1000000000000) (-6318628968 / 1000000000000), orderedInterval (29853876767 / 1000000000000) (29853876769 / 1000000000000))
    | 13 => (orderedInterval (-34375489514 / 1000000000000) (-34375474473 / 1000000000000), orderedInterval (11114737640 / 1000000000000) (11114752681 / 1000000000000))
    | 14 => (orderedInterval (32241322266 / 1000000000000) (32241322275 / 1000000000000), orderedInterval (10501592137 / 1000000000000) (10501592146 / 1000000000000))
    | 15 => (orderedInterval (-12040282474 / 1000000000000) (-12040282473 / 1000000000000), orderedInterval (-35128257124 / 1000000000000) (-35128257123 / 1000000000000))
    | 16 => (orderedInterval (110160494 / 1000000000000) (110160496 / 1000000000000), orderedInterval (39519076267 / 1000000000000) (39519076269 / 1000000000000))
    | 17 => (orderedInterval (25581100834 / 1000000000000) (25581100835 / 1000000000000), orderedInterval (20552471653 / 1000000000000) (20552471654 / 1000000000000))
    | 18 => (orderedInterval (33337785368 / 1000000000000) (33337785369 / 1000000000000), orderedInterval (28873928580 / 1000000000000) (28873928581 / 1000000000000))
    | 19 => (orderedInterval (46815925583 / 1000000000000) (46815925587 / 1000000000000), orderedInterval (10225179739 / 1000000000000) (10225179744 / 1000000000000))
    | 20 => (orderedInterval (-59117416381 / 1000000000000) (-59117416378 / 1000000000000), orderedInterval (-13153427547 / 1000000000000) (-13153427545 / 1000000000000))
    | 21 => (orderedInterval (-19194138370 / 1000000000000) (-19194138150 / 1000000000000), orderedInterval (80478368540 / 1000000000000) (80478368760 / 1000000000000))
    | 22 => (orderedInterval (26144133640 / 1000000000000) (26144137242 / 1000000000000), orderedInterval (-42846749829 / 1000000000000) (-42846746227 / 1000000000000))
    | 23 => (orderedInterval (32100595358 / 1000000000000) (32100595359 / 1000000000000), orderedInterval (28439266836 / 1000000000000) (28439266837 / 1000000000000))
    | 24 => (orderedInterval (43635746684 / 1000000000000) (43635780896 / 1000000000000), orderedInterval (-49666148032 / 1000000000000) (-49666113820 / 1000000000000))
    | 25 => (orderedInterval (-29284825140 / 1000000000000) (-29284825138 / 1000000000000), orderedInterval (-14604053688 / 1000000000000) (-14604053687 / 1000000000000))
    | _ => (orderedInterval (39304245818 / 1000000000000) (39304248585 / 1000000000000), orderedInterval (-7761725562 / 1000000000000) (-7761722794 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-5225871245 / 1000000000000) (-5225871217 / 1000000000000)
      | 1 => orderedInterval (2031262232 / 1000000000000) (2031268850 / 1000000000000)
      | 2 => orderedInterval (1865132007 / 1000000000000) (1865132042 / 1000000000000)
      | 3 => orderedInterval (-1028520037 / 1000000000000) (-1028509035 / 1000000000000)
      | 4 => orderedInterval (-3299733737 / 1000000000000) (-3299732276 / 1000000000000)
      | 5 => orderedInterval (509635883 / 1000000000000) (509635915 / 1000000000000)
      | 6 => orderedInterval (-9904822793 / 1000000000000) (-9904822712 / 1000000000000)
      | 7 => orderedInterval (-2698859801 / 1000000000000) (-2698859677 / 1000000000000)
      | _ => orderedInterval (-4727632304 / 1000000000000) (-4727631489 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (16072438897 / 1000000000000) (16072438928 / 1000000000000)
      | 1 => orderedInterval (-3540419129 / 1000000000000) (-3540408772 / 1000000000000)
      | 2 => orderedInterval (279750280 / 1000000000000) (279750342 / 1000000000000)
      | 3 => orderedInterval (-12260816950 / 1000000000000) (-12260792484 / 1000000000000)
      | 4 => orderedInterval (359839293 / 1000000000000) (359841528 / 1000000000000)
      | 5 => orderedInterval (-2498142735 / 1000000000000) (-2498142690 / 1000000000000)
      | 6 => orderedInterval (-5456310063 / 1000000000000) (-5456309988 / 1000000000000)
      | 7 => orderedInterval (-2021315493 / 1000000000000) (-2021315392 / 1000000000000)
      | _ => orderedInterval (3882246562 / 1000000000000) (3882247427 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (5995196253 / 1000000000000) (5995196287 / 1000000000000)
      | 1 => orderedInterval (-5341242106 / 1000000000000) (-5341225846 / 1000000000000)
      | 2 => orderedInterval (-5709316122 / 1000000000000) (-5709316008 / 1000000000000)
      | 3 => orderedInterval (-3731824072 / 1000000000000) (-3731769460 / 1000000000000)
      | 4 => orderedInterval (7550569704 / 1000000000000) (7550573133 / 1000000000000)
      | 5 => orderedInterval (-1931032911 / 1000000000000) (-1931032844 / 1000000000000)
      | 6 => orderedInterval (8152499292 / 1000000000000) (8152499363 / 1000000000000)
      | 7 => orderedInterval (3227563412 / 1000000000000) (3227563498 / 1000000000000)
      | _ => orderedInterval (3066599591 / 1000000000000) (3066600622 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-15775582473 / 1000000000000) (-15775582433 / 1000000000000)
      | 1 => orderedInterval (5591559790 / 1000000000000) (5591585273 / 1000000000000)
      | 2 => orderedInterval (-862243701 / 1000000000000) (-862243488 / 1000000000000)
      | 3 => orderedInterval (64826931364 / 1000000000000) (64827053264 / 1000000000000)
      | 4 => orderedInterval (1791626093 / 1000000000000) (1791631347 / 1000000000000)
      | 5 => orderedInterval (2597926901 / 1000000000000) (2597927003 / 1000000000000)
      | 6 => orderedInterval (5360409408 / 1000000000000) (5360409477 / 1000000000000)
      | 7 => orderedInterval (2302723987 / 1000000000000) (2302724064 / 1000000000000)
      | _ => orderedInterval (-10413536870 / 1000000000000) (-10413535569 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-7203716715 / 1000000000000) (-7203716670 / 1000000000000)
      | 1 => orderedInterval (12996314070 / 1000000000000) (12996354095 / 1000000000000)
      | 2 => orderedInterval (18968778529 / 1000000000000) (18968778933 / 1000000000000)
      | 3 => orderedInterval (30802565701 / 1000000000000) (30802838389 / 1000000000000)
      | 4 => orderedInterval (-16783150297 / 1000000000000) (-16783142219 / 1000000000000)
      | 5 => orderedInterval (7016569037 / 1000000000000) (7016569199 / 1000000000000)
      | 6 => orderedInterval (-7532325482 / 1000000000000) (-7532325413 / 1000000000000)
      | 7 => orderedInterval (-3614906859 / 1000000000000) (-3614906789 / 1000000000000)
      | _ => orderedInterval (11024747397 / 1000000000000) (11024749104 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-22479409795 / 1000000000000) (-22479389599 / 1000000000000)
    | 1 => orderedInterval (-5182729338 / 1000000000000) (-5182691101 / 1000000000000)
    | 2 => orderedInterval (11279013041 / 1000000000000) (11279088745 / 1000000000000)
    | 3 => orderedInterval (55419814499 / 1000000000000) (55419968938 / 1000000000000)
    | _ => orderedInterval (45674875381 / 1000000000000) (45675198629 / 1000000000000)

theorem compactCertificate448_stateChecks0 :
    compactCertificate448.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (639 / 2)) (orderedInterval (-6998968127 / 1000000000000) (-6998968114 / 1000000000000), orderedInterval (44096856763 / 1000000000000) (44096856777 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (941369015708739 / 4000000000000)) (orderedInterval (-25284516558 / 1000000000000) (-25284516557 / 1000000000000), orderedInterval (-45397101992 / 1000000000000) (-45397101991 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (304419398033187 / 800000000000)) (orderedInterval (-37765500788 / 1000000000000) (-37765500787 / 1000000000000), orderedInterval (-15659388649 / 1000000000000) (-15659388648 / 1000000000000))) = true
  rfl'

theorem compactCertificate448_stateChecks1 :
    compactCertificate448.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (274689130976073 / 4000000000000)) (orderedInterval (32183337069 / 1000000000000) (32183337070 / 1000000000000), orderedInterval (90511634986 / 1000000000000) (90511634987 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (737853644024181 / 4000000000000)) (orderedInterval (6205867411 / 1000000000000) (6205867429 / 1000000000000), orderedInterval (-58435120629 / 1000000000000) (-58435120611 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2003416176500577 / 4000000000000)) (orderedInterval (-30297637382 / 1000000000000) (-30297544845 / 1000000000000), orderedInterval (18821794106 / 1000000000000) (18821886643 / 1000000000000))) = true
  rfl'

theorem compactCertificate448_stateChecks2 :
    compactCertificate448.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1475707288049001 / 4000000000000)) (orderedInterval (-34866124173 / 1000000000000) (-34866030959 / 1000000000000), orderedInterval (22629387168 / 1000000000000) (22629480381 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (2528649590696973 / 4000000000000)) (orderedInterval (-31623969097 / 1000000000000) (-31623968668 / 1000000000000), orderedInterval (-2616062741 / 1000000000000) (-2616062312 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1862591843712807 / 4000000000000)) (orderedInterval (36814022740 / 1000000000000) (36814022862 / 1000000000000), orderedInterval (3409618935 / 1000000000000) (3409619057 / 1000000000000))) = true
  rfl'

theorem compactCertificate448_stateChecks3 :
    compactCertificate448.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (2857694875244361 / 4000000000000)) (orderedInterval (-26245256956 / 1000000000000) (-26245196432 / 1000000000000), orderedInterval (14240975422 / 1000000000000) (14241035946 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1649890905483969 / 4000000000000)) (orderedInterval (-38910816079 / 1000000000000) (-38910814455 / 1000000000000), orderedInterval (5466582921 / 1000000000000) (5466584546 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 233 12 (2927760364600821 / 4000000000000)) (orderedInterval (-19760019661 / 1000000000000) (-19760019660 / 1000000000000), orderedInterval (-21879696241 / 1000000000000) (-21879696240 / 1000000000000))) = true
  rfl'

theorem compactCertificate448_stateChecks4 :
    compactCertificate448.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (2735493511695849 / 4000000000000)) (orderedInterval (-6318628970 / 1000000000000) (-6318628968 / 1000000000000), orderedInterval (29853876767 / 1000000000000) (29853876769 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1952177246050617 / 4000000000000)) (orderedInterval (-34375489514 / 1000000000000) (-34375474473 / 1000000000000), orderedInterval (11114737640 / 1000000000000) (11114752681 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (2213560932072543 / 4000000000000)) (orderedInterval (32241322266 / 1000000000000) (32241322275 / 1000000000000), orderedInterval (10501592137 / 1000000000000) (10501592146 / 1000000000000))) = true
  rfl'

theorem compactCertificate448_stateChecks5 :
    compactCertificate448.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1845436329833967 / 4000000000000)) (orderedInterval (-12040282474 / 1000000000000) (-12040282473 / 1000000000000), orderedInterval (-35128257124 / 1000000000000) (-35128257123 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1630498963877307 / 4000000000000)) (orderedInterval (110160494 / 1000000000000) (110160496 / 1000000000000), orderedInterval (39519076267 / 1000000000000) (39519076269 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (472582151481393 / 800000000000)) (orderedInterval (25581100834 / 1000000000000) (25581100835 / 1000000000000), orderedInterval (20552471653 / 1000000000000) (20552471654 / 1000000000000))) = true
  rfl'

theorem compactCertificate448_stateChecks6 :
    compactCertificate448.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1307187101633571 / 4000000000000)) (orderedInterval (33337785368 / 1000000000000) (33337785369 / 1000000000000), orderedInterval (28873928580 / 1000000000000) (28873928581 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1108116982755531 / 4000000000000)) (orderedInterval (46815925583 / 1000000000000) (46815925587 / 1000000000000), orderedInterval (10225179739 / 1000000000000) (10225179744 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (693408156287193 / 4000000000000)) (orderedInterval (-59117416381 / 1000000000000) (-59117416378 / 1000000000000), orderedInterval (-13153427547 / 1000000000000) (-13153427545 / 1000000000000))) = true
  rfl'

theorem compactCertificate448_stateChecks7 :
    compactCertificate448.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (372917212622631 / 4000000000000)) (orderedInterval (-19194138370 / 1000000000000) (-19194138150 / 1000000000000), orderedInterval (80478368540 / 1000000000000) (80478368760 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1012542775000893 / 4000000000000)) (orderedInterval (26144133640 / 1000000000000) (26144137242 / 1000000000000), orderedInterval (-42846749829 / 1000000000000) (-42846746227 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1382540594319261 / 4000000000000)) (orderedInterval (32100595358 / 1000000000000) (32100595359 / 1000000000000), orderedInterval (28439266836 / 1000000000000) (28439266837 / 1000000000000))) = true
  rfl'

theorem compactCertificate448_stateChecks8 :
    compactCertificate448.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (584591843712807 / 4000000000000)) (orderedInterval (43635746684 / 1000000000000) (43635780896 / 1000000000000), orderedInterval (-49666148032 / 1000000000000) (-49666113820 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2376333389123847 / 4000000000000)) (orderedInterval (-29284825140 / 1000000000000) (-29284825138 / 1000000000000), orderedInterval (-14604053688 / 1000000000000) (-14604053687 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1587280574988873 / 4000000000000)) (orderedInterval (39304245818 / 1000000000000) (39304248585 / 1000000000000), orderedInterval (-7761725562 / 1000000000000) (-7761722794 / 1000000000000))) = true
  rfl'

theorem compactCertificate448_states : ∀ j,
    BesselStateValid (compactCertificate448.point j) (compactCertificate448.state j) :=
  compactCertificate448.statesValid_of_checks3 compactCertificate448_stateChecks0
    compactCertificate448_stateChecks1 compactCertificate448_stateChecks2
    compactCertificate448_stateChecks3 compactCertificate448_stateChecks4
    compactCertificate448_stateChecks5 compactCertificate448_stateChecks6
    compactCertificate448_stateChecks7 compactCertificate448_stateChecks8

theorem compactCertificate448_chunkChecks0_0 :
    compactCertificate448.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (639 / 2) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6998968127 / 1000000000000) (-6998968114 / 1000000000000), orderedInterval (44096856763 / 1000000000000) (44096856777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (941369015708739 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25284516558 / 1000000000000) (-25284516557 / 1000000000000), orderedInterval (-45397101992 / 1000000000000) (-45397101991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (304419398033187 / 800000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37765500788 / 1000000000000) (-37765500787 / 1000000000000), orderedInterval (-15659388649 / 1000000000000) (-15659388648 / 1000000000000)))) (orderedInterval (-5225871245 / 1000000000000) (-5225871217 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (274689130976073 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (32183337069 / 1000000000000) (32183337070 / 1000000000000), orderedInterval (90511634986 / 1000000000000) (90511634987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (737853644024181 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (6205867411 / 1000000000000) (6205867429 / 1000000000000), orderedInterval (-58435120629 / 1000000000000) (-58435120611 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2003416176500577 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30297637382 / 1000000000000) (-30297544845 / 1000000000000), orderedInterval (18821794106 / 1000000000000) (18821886643 / 1000000000000)))) (orderedInterval (2031262232 / 1000000000000) (2031268850 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1475707288049001 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34866124173 / 1000000000000) (-34866030959 / 1000000000000), orderedInterval (22629387168 / 1000000000000) (22629480381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2528649590696973 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31623969097 / 1000000000000) (-31623968668 / 1000000000000), orderedInterval (-2616062741 / 1000000000000) (-2616062312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1862591843712807 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36814022740 / 1000000000000) (36814022862 / 1000000000000), orderedInterval (3409618935 / 1000000000000) (3409619057 / 1000000000000)))) (orderedInterval (1865132007 / 1000000000000) (1865132042 / 1000000000000))) = true
  rfl'

theorem compactCertificate448_chunkChecks0_1 :
    compactCertificate448.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2857694875244361 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26245256956 / 1000000000000) (-26245196432 / 1000000000000), orderedInterval (14240975422 / 1000000000000) (14241035946 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1649890905483969 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-38910816079 / 1000000000000) (-38910814455 / 1000000000000), orderedInterval (5466582921 / 1000000000000) (5466584546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2927760364600821 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19760019661 / 1000000000000) (-19760019660 / 1000000000000), orderedInterval (-21879696241 / 1000000000000) (-21879696240 / 1000000000000)))) (orderedInterval (-1028520037 / 1000000000000) (-1028509035 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2735493511695849 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6318628970 / 1000000000000) (-6318628968 / 1000000000000), orderedInterval (29853876767 / 1000000000000) (29853876769 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1952177246050617 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34375489514 / 1000000000000) (-34375474473 / 1000000000000), orderedInterval (11114737640 / 1000000000000) (11114752681 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2213560932072543 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32241322266 / 1000000000000) (32241322275 / 1000000000000), orderedInterval (10501592137 / 1000000000000) (10501592146 / 1000000000000)))) (orderedInterval (-3299733737 / 1000000000000) (-3299732276 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1845436329833967 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12040282474 / 1000000000000) (-12040282473 / 1000000000000), orderedInterval (-35128257124 / 1000000000000) (-35128257123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1630498963877307 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (110160494 / 1000000000000) (110160496 / 1000000000000), orderedInterval (39519076267 / 1000000000000) (39519076269 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (472582151481393 / 800000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25581100834 / 1000000000000) (25581100835 / 1000000000000), orderedInterval (20552471653 / 1000000000000) (20552471654 / 1000000000000)))) (orderedInterval (509635883 / 1000000000000) (509635915 / 1000000000000))) = true
  rfl'

theorem compactCertificate448_chunkChecks0_2 :
    compactCertificate448.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1307187101633571 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33337785368 / 1000000000000) (33337785369 / 1000000000000), orderedInterval (28873928580 / 1000000000000) (28873928581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1108116982755531 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46815925583 / 1000000000000) (46815925587 / 1000000000000), orderedInterval (10225179739 / 1000000000000) (10225179744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (693408156287193 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-59117416381 / 1000000000000) (-59117416378 / 1000000000000), orderedInterval (-13153427547 / 1000000000000) (-13153427545 / 1000000000000)))) (orderedInterval (-9904822793 / 1000000000000) (-9904822712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (372917212622631 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19194138370 / 1000000000000) (-19194138150 / 1000000000000), orderedInterval (80478368540 / 1000000000000) (80478368760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1012542775000893 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (26144133640 / 1000000000000) (26144137242 / 1000000000000), orderedInterval (-42846749829 / 1000000000000) (-42846746227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1382540594319261 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32100595358 / 1000000000000) (32100595359 / 1000000000000), orderedInterval (28439266836 / 1000000000000) (28439266837 / 1000000000000)))) (orderedInterval (-2698859801 / 1000000000000) (-2698859677 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (584591843712807 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (43635746684 / 1000000000000) (43635780896 / 1000000000000), orderedInterval (-49666148032 / 1000000000000) (-49666113820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2376333389123847 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29284825140 / 1000000000000) (-29284825138 / 1000000000000), orderedInterval (-14604053688 / 1000000000000) (-14604053687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1587280574988873 / 4000000000000) 0 (IntervalRat.scale (639 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39304245818 / 1000000000000) (39304248585 / 1000000000000), orderedInterval (-7761725562 / 1000000000000) (-7761722794 / 1000000000000)))) (orderedInterval (-4727632304 / 1000000000000) (-4727631489 / 1000000000000))) = true
  rfl'

theorem compactCertificate448_chunkChecks0 :
    compactCertificate448.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate448.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate448_chunkChecks0_0
    compactCertificate448_chunkChecks0_1 compactCertificate448_chunkChecks0_2

theorem compactCertificate448_chunkChecks1_0 :
    compactCertificate448.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (639 / 2) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6998968127 / 1000000000000) (-6998968114 / 1000000000000), orderedInterval (44096856763 / 1000000000000) (44096856777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (941369015708739 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25284516558 / 1000000000000) (-25284516557 / 1000000000000), orderedInterval (-45397101992 / 1000000000000) (-45397101991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (304419398033187 / 800000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37765500788 / 1000000000000) (-37765500787 / 1000000000000), orderedInterval (-15659388649 / 1000000000000) (-15659388648 / 1000000000000)))) (orderedInterval (16072438897 / 1000000000000) (16072438928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (274689130976073 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (32183337069 / 1000000000000) (32183337070 / 1000000000000), orderedInterval (90511634986 / 1000000000000) (90511634987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (737853644024181 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (6205867411 / 1000000000000) (6205867429 / 1000000000000), orderedInterval (-58435120629 / 1000000000000) (-58435120611 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2003416176500577 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30297637382 / 1000000000000) (-30297544845 / 1000000000000), orderedInterval (18821794106 / 1000000000000) (18821886643 / 1000000000000)))) (orderedInterval (-3540419129 / 1000000000000) (-3540408772 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1475707288049001 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34866124173 / 1000000000000) (-34866030959 / 1000000000000), orderedInterval (22629387168 / 1000000000000) (22629480381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2528649590696973 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31623969097 / 1000000000000) (-31623968668 / 1000000000000), orderedInterval (-2616062741 / 1000000000000) (-2616062312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1862591843712807 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36814022740 / 1000000000000) (36814022862 / 1000000000000), orderedInterval (3409618935 / 1000000000000) (3409619057 / 1000000000000)))) (orderedInterval (279750280 / 1000000000000) (279750342 / 1000000000000))) = true
  rfl'

theorem compactCertificate448_chunkChecks1_1 :
    compactCertificate448.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2857694875244361 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26245256956 / 1000000000000) (-26245196432 / 1000000000000), orderedInterval (14240975422 / 1000000000000) (14241035946 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1649890905483969 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-38910816079 / 1000000000000) (-38910814455 / 1000000000000), orderedInterval (5466582921 / 1000000000000) (5466584546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2927760364600821 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19760019661 / 1000000000000) (-19760019660 / 1000000000000), orderedInterval (-21879696241 / 1000000000000) (-21879696240 / 1000000000000)))) (orderedInterval (-12260816950 / 1000000000000) (-12260792484 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2735493511695849 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6318628970 / 1000000000000) (-6318628968 / 1000000000000), orderedInterval (29853876767 / 1000000000000) (29853876769 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1952177246050617 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34375489514 / 1000000000000) (-34375474473 / 1000000000000), orderedInterval (11114737640 / 1000000000000) (11114752681 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2213560932072543 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32241322266 / 1000000000000) (32241322275 / 1000000000000), orderedInterval (10501592137 / 1000000000000) (10501592146 / 1000000000000)))) (orderedInterval (359839293 / 1000000000000) (359841528 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1845436329833967 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12040282474 / 1000000000000) (-12040282473 / 1000000000000), orderedInterval (-35128257124 / 1000000000000) (-35128257123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1630498963877307 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (110160494 / 1000000000000) (110160496 / 1000000000000), orderedInterval (39519076267 / 1000000000000) (39519076269 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (472582151481393 / 800000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25581100834 / 1000000000000) (25581100835 / 1000000000000), orderedInterval (20552471653 / 1000000000000) (20552471654 / 1000000000000)))) (orderedInterval (-2498142735 / 1000000000000) (-2498142690 / 1000000000000))) = true
  rfl'

theorem compactCertificate448_chunkChecks1_2 :
    compactCertificate448.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1307187101633571 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33337785368 / 1000000000000) (33337785369 / 1000000000000), orderedInterval (28873928580 / 1000000000000) (28873928581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1108116982755531 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46815925583 / 1000000000000) (46815925587 / 1000000000000), orderedInterval (10225179739 / 1000000000000) (10225179744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (693408156287193 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-59117416381 / 1000000000000) (-59117416378 / 1000000000000), orderedInterval (-13153427547 / 1000000000000) (-13153427545 / 1000000000000)))) (orderedInterval (-5456310063 / 1000000000000) (-5456309988 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (372917212622631 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19194138370 / 1000000000000) (-19194138150 / 1000000000000), orderedInterval (80478368540 / 1000000000000) (80478368760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1012542775000893 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (26144133640 / 1000000000000) (26144137242 / 1000000000000), orderedInterval (-42846749829 / 1000000000000) (-42846746227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1382540594319261 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32100595358 / 1000000000000) (32100595359 / 1000000000000), orderedInterval (28439266836 / 1000000000000) (28439266837 / 1000000000000)))) (orderedInterval (-2021315493 / 1000000000000) (-2021315392 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (584591843712807 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (43635746684 / 1000000000000) (43635780896 / 1000000000000), orderedInterval (-49666148032 / 1000000000000) (-49666113820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2376333389123847 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29284825140 / 1000000000000) (-29284825138 / 1000000000000), orderedInterval (-14604053688 / 1000000000000) (-14604053687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1587280574988873 / 4000000000000) 1 (IntervalRat.scale (639 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39304245818 / 1000000000000) (39304248585 / 1000000000000), orderedInterval (-7761725562 / 1000000000000) (-7761722794 / 1000000000000)))) (orderedInterval (3882246562 / 1000000000000) (3882247427 / 1000000000000))) = true
  rfl'

theorem compactCertificate448_chunkChecks1 :
    compactCertificate448.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate448.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate448_chunkChecks1_0
    compactCertificate448_chunkChecks1_1 compactCertificate448_chunkChecks1_2

theorem compactCertificate448_chunkChecks2_0 :
    compactCertificate448.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (639 / 2) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6998968127 / 1000000000000) (-6998968114 / 1000000000000), orderedInterval (44096856763 / 1000000000000) (44096856777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (941369015708739 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25284516558 / 1000000000000) (-25284516557 / 1000000000000), orderedInterval (-45397101992 / 1000000000000) (-45397101991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (304419398033187 / 800000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37765500788 / 1000000000000) (-37765500787 / 1000000000000), orderedInterval (-15659388649 / 1000000000000) (-15659388648 / 1000000000000)))) (orderedInterval (5995196253 / 1000000000000) (5995196287 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (274689130976073 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (32183337069 / 1000000000000) (32183337070 / 1000000000000), orderedInterval (90511634986 / 1000000000000) (90511634987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (737853644024181 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (6205867411 / 1000000000000) (6205867429 / 1000000000000), orderedInterval (-58435120629 / 1000000000000) (-58435120611 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2003416176500577 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30297637382 / 1000000000000) (-30297544845 / 1000000000000), orderedInterval (18821794106 / 1000000000000) (18821886643 / 1000000000000)))) (orderedInterval (-5341242106 / 1000000000000) (-5341225846 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1475707288049001 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34866124173 / 1000000000000) (-34866030959 / 1000000000000), orderedInterval (22629387168 / 1000000000000) (22629480381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2528649590696973 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31623969097 / 1000000000000) (-31623968668 / 1000000000000), orderedInterval (-2616062741 / 1000000000000) (-2616062312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1862591843712807 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36814022740 / 1000000000000) (36814022862 / 1000000000000), orderedInterval (3409618935 / 1000000000000) (3409619057 / 1000000000000)))) (orderedInterval (-5709316122 / 1000000000000) (-5709316008 / 1000000000000))) = true
  rfl'

theorem compactCertificate448_chunkChecks2_1 :
    compactCertificate448.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2857694875244361 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26245256956 / 1000000000000) (-26245196432 / 1000000000000), orderedInterval (14240975422 / 1000000000000) (14241035946 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1649890905483969 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-38910816079 / 1000000000000) (-38910814455 / 1000000000000), orderedInterval (5466582921 / 1000000000000) (5466584546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2927760364600821 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19760019661 / 1000000000000) (-19760019660 / 1000000000000), orderedInterval (-21879696241 / 1000000000000) (-21879696240 / 1000000000000)))) (orderedInterval (-3731824072 / 1000000000000) (-3731769460 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2735493511695849 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6318628970 / 1000000000000) (-6318628968 / 1000000000000), orderedInterval (29853876767 / 1000000000000) (29853876769 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1952177246050617 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34375489514 / 1000000000000) (-34375474473 / 1000000000000), orderedInterval (11114737640 / 1000000000000) (11114752681 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2213560932072543 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32241322266 / 1000000000000) (32241322275 / 1000000000000), orderedInterval (10501592137 / 1000000000000) (10501592146 / 1000000000000)))) (orderedInterval (7550569704 / 1000000000000) (7550573133 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1845436329833967 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12040282474 / 1000000000000) (-12040282473 / 1000000000000), orderedInterval (-35128257124 / 1000000000000) (-35128257123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1630498963877307 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (110160494 / 1000000000000) (110160496 / 1000000000000), orderedInterval (39519076267 / 1000000000000) (39519076269 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (472582151481393 / 800000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25581100834 / 1000000000000) (25581100835 / 1000000000000), orderedInterval (20552471653 / 1000000000000) (20552471654 / 1000000000000)))) (orderedInterval (-1931032911 / 1000000000000) (-1931032844 / 1000000000000))) = true
  rfl'

theorem compactCertificate448_chunkChecks2_2 :
    compactCertificate448.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1307187101633571 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33337785368 / 1000000000000) (33337785369 / 1000000000000), orderedInterval (28873928580 / 1000000000000) (28873928581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1108116982755531 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46815925583 / 1000000000000) (46815925587 / 1000000000000), orderedInterval (10225179739 / 1000000000000) (10225179744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (693408156287193 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-59117416381 / 1000000000000) (-59117416378 / 1000000000000), orderedInterval (-13153427547 / 1000000000000) (-13153427545 / 1000000000000)))) (orderedInterval (8152499292 / 1000000000000) (8152499363 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (372917212622631 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19194138370 / 1000000000000) (-19194138150 / 1000000000000), orderedInterval (80478368540 / 1000000000000) (80478368760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1012542775000893 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (26144133640 / 1000000000000) (26144137242 / 1000000000000), orderedInterval (-42846749829 / 1000000000000) (-42846746227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1382540594319261 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32100595358 / 1000000000000) (32100595359 / 1000000000000), orderedInterval (28439266836 / 1000000000000) (28439266837 / 1000000000000)))) (orderedInterval (3227563412 / 1000000000000) (3227563498 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (584591843712807 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (43635746684 / 1000000000000) (43635780896 / 1000000000000), orderedInterval (-49666148032 / 1000000000000) (-49666113820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2376333389123847 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29284825140 / 1000000000000) (-29284825138 / 1000000000000), orderedInterval (-14604053688 / 1000000000000) (-14604053687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1587280574988873 / 4000000000000) 2 (IntervalRat.scale (639 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39304245818 / 1000000000000) (39304248585 / 1000000000000), orderedInterval (-7761725562 / 1000000000000) (-7761722794 / 1000000000000)))) (orderedInterval (3066599591 / 1000000000000) (3066600622 / 1000000000000))) = true
  rfl'

theorem compactCertificate448_chunkChecks2 :
    compactCertificate448.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate448.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate448_chunkChecks2_0
    compactCertificate448_chunkChecks2_1 compactCertificate448_chunkChecks2_2

theorem compactCertificate448_chunkChecks3_0 :
    compactCertificate448.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (639 / 2) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6998968127 / 1000000000000) (-6998968114 / 1000000000000), orderedInterval (44096856763 / 1000000000000) (44096856777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (941369015708739 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25284516558 / 1000000000000) (-25284516557 / 1000000000000), orderedInterval (-45397101992 / 1000000000000) (-45397101991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (304419398033187 / 800000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37765500788 / 1000000000000) (-37765500787 / 1000000000000), orderedInterval (-15659388649 / 1000000000000) (-15659388648 / 1000000000000)))) (orderedInterval (-15775582473 / 1000000000000) (-15775582433 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (274689130976073 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (32183337069 / 1000000000000) (32183337070 / 1000000000000), orderedInterval (90511634986 / 1000000000000) (90511634987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (737853644024181 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (6205867411 / 1000000000000) (6205867429 / 1000000000000), orderedInterval (-58435120629 / 1000000000000) (-58435120611 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2003416176500577 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30297637382 / 1000000000000) (-30297544845 / 1000000000000), orderedInterval (18821794106 / 1000000000000) (18821886643 / 1000000000000)))) (orderedInterval (5591559790 / 1000000000000) (5591585273 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1475707288049001 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34866124173 / 1000000000000) (-34866030959 / 1000000000000), orderedInterval (22629387168 / 1000000000000) (22629480381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2528649590696973 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31623969097 / 1000000000000) (-31623968668 / 1000000000000), orderedInterval (-2616062741 / 1000000000000) (-2616062312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1862591843712807 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36814022740 / 1000000000000) (36814022862 / 1000000000000), orderedInterval (3409618935 / 1000000000000) (3409619057 / 1000000000000)))) (orderedInterval (-862243701 / 1000000000000) (-862243488 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate448_chunkChecks3_1 :
    compactCertificate448.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2857694875244361 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26245256956 / 1000000000000) (-26245196432 / 1000000000000), orderedInterval (14240975422 / 1000000000000) (14241035946 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1649890905483969 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-38910816079 / 1000000000000) (-38910814455 / 1000000000000), orderedInterval (5466582921 / 1000000000000) (5466584546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2927760364600821 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19760019661 / 1000000000000) (-19760019660 / 1000000000000), orderedInterval (-21879696241 / 1000000000000) (-21879696240 / 1000000000000)))) (orderedInterval (64826931364 / 1000000000000) (64827053264 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2735493511695849 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6318628970 / 1000000000000) (-6318628968 / 1000000000000), orderedInterval (29853876767 / 1000000000000) (29853876769 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1952177246050617 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34375489514 / 1000000000000) (-34375474473 / 1000000000000), orderedInterval (11114737640 / 1000000000000) (11114752681 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2213560932072543 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32241322266 / 1000000000000) (32241322275 / 1000000000000), orderedInterval (10501592137 / 1000000000000) (10501592146 / 1000000000000)))) (orderedInterval (1791626093 / 1000000000000) (1791631347 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1845436329833967 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12040282474 / 1000000000000) (-12040282473 / 1000000000000), orderedInterval (-35128257124 / 1000000000000) (-35128257123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1630498963877307 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (110160494 / 1000000000000) (110160496 / 1000000000000), orderedInterval (39519076267 / 1000000000000) (39519076269 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (472582151481393 / 800000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25581100834 / 1000000000000) (25581100835 / 1000000000000), orderedInterval (20552471653 / 1000000000000) (20552471654 / 1000000000000)))) (orderedInterval (2597926901 / 1000000000000) (2597927003 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate448_chunkChecks3_2 :
    compactCertificate448.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1307187101633571 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33337785368 / 1000000000000) (33337785369 / 1000000000000), orderedInterval (28873928580 / 1000000000000) (28873928581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1108116982755531 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46815925583 / 1000000000000) (46815925587 / 1000000000000), orderedInterval (10225179739 / 1000000000000) (10225179744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (693408156287193 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-59117416381 / 1000000000000) (-59117416378 / 1000000000000), orderedInterval (-13153427547 / 1000000000000) (-13153427545 / 1000000000000)))) (orderedInterval (5360409408 / 1000000000000) (5360409477 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (372917212622631 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19194138370 / 1000000000000) (-19194138150 / 1000000000000), orderedInterval (80478368540 / 1000000000000) (80478368760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1012542775000893 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (26144133640 / 1000000000000) (26144137242 / 1000000000000), orderedInterval (-42846749829 / 1000000000000) (-42846746227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1382540594319261 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32100595358 / 1000000000000) (32100595359 / 1000000000000), orderedInterval (28439266836 / 1000000000000) (28439266837 / 1000000000000)))) (orderedInterval (2302723987 / 1000000000000) (2302724064 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (584591843712807 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (43635746684 / 1000000000000) (43635780896 / 1000000000000), orderedInterval (-49666148032 / 1000000000000) (-49666113820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2376333389123847 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29284825140 / 1000000000000) (-29284825138 / 1000000000000), orderedInterval (-14604053688 / 1000000000000) (-14604053687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1587280574988873 / 4000000000000) 3 (IntervalRat.scale (639 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39304245818 / 1000000000000) (39304248585 / 1000000000000), orderedInterval (-7761725562 / 1000000000000) (-7761722794 / 1000000000000)))) (orderedInterval (-10413536870 / 1000000000000) (-10413535569 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate448_chunkChecks3 :
    compactCertificate448.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate448.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate448_chunkChecks3_0
    compactCertificate448_chunkChecks3_1 compactCertificate448_chunkChecks3_2

theorem compactCertificate448_chunkChecks4_0 :
    compactCertificate448.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (639 / 2) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6998968127 / 1000000000000) (-6998968114 / 1000000000000), orderedInterval (44096856763 / 1000000000000) (44096856777 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (941369015708739 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-25284516558 / 1000000000000) (-25284516557 / 1000000000000), orderedInterval (-45397101992 / 1000000000000) (-45397101991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (304419398033187 / 800000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37765500788 / 1000000000000) (-37765500787 / 1000000000000), orderedInterval (-15659388649 / 1000000000000) (-15659388648 / 1000000000000)))) (orderedInterval (-7203716715 / 1000000000000) (-7203716670 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (274689130976073 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (32183337069 / 1000000000000) (32183337070 / 1000000000000), orderedInterval (90511634986 / 1000000000000) (90511634987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (737853644024181 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (6205867411 / 1000000000000) (6205867429 / 1000000000000), orderedInterval (-58435120629 / 1000000000000) (-58435120611 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2003416176500577 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30297637382 / 1000000000000) (-30297544845 / 1000000000000), orderedInterval (18821794106 / 1000000000000) (18821886643 / 1000000000000)))) (orderedInterval (12996314070 / 1000000000000) (12996354095 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1475707288049001 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34866124173 / 1000000000000) (-34866030959 / 1000000000000), orderedInterval (22629387168 / 1000000000000) (22629480381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2528649590696973 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31623969097 / 1000000000000) (-31623968668 / 1000000000000), orderedInterval (-2616062741 / 1000000000000) (-2616062312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1862591843712807 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36814022740 / 1000000000000) (36814022862 / 1000000000000), orderedInterval (3409618935 / 1000000000000) (3409619057 / 1000000000000)))) (orderedInterval (18968778529 / 1000000000000) (18968778933 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate448_chunkChecks4_1 :
    compactCertificate448.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2857694875244361 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-26245256956 / 1000000000000) (-26245196432 / 1000000000000), orderedInterval (14240975422 / 1000000000000) (14241035946 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1649890905483969 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-38910816079 / 1000000000000) (-38910814455 / 1000000000000), orderedInterval (5466582921 / 1000000000000) (5466584546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2927760364600821 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19760019661 / 1000000000000) (-19760019660 / 1000000000000), orderedInterval (-21879696241 / 1000000000000) (-21879696240 / 1000000000000)))) (orderedInterval (30802565701 / 1000000000000) (30802838389 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2735493511695849 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6318628970 / 1000000000000) (-6318628968 / 1000000000000), orderedInterval (29853876767 / 1000000000000) (29853876769 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1952177246050617 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-34375489514 / 1000000000000) (-34375474473 / 1000000000000), orderedInterval (11114737640 / 1000000000000) (11114752681 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2213560932072543 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32241322266 / 1000000000000) (32241322275 / 1000000000000), orderedInterval (10501592137 / 1000000000000) (10501592146 / 1000000000000)))) (orderedInterval (-16783150297 / 1000000000000) (-16783142219 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1845436329833967 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12040282474 / 1000000000000) (-12040282473 / 1000000000000), orderedInterval (-35128257124 / 1000000000000) (-35128257123 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1630498963877307 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (110160494 / 1000000000000) (110160496 / 1000000000000), orderedInterval (39519076267 / 1000000000000) (39519076269 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (472582151481393 / 800000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25581100834 / 1000000000000) (25581100835 / 1000000000000), orderedInterval (20552471653 / 1000000000000) (20552471654 / 1000000000000)))) (orderedInterval (7016569037 / 1000000000000) (7016569199 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate448_chunkChecks4_2 :
    compactCertificate448.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1307187101633571 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33337785368 / 1000000000000) (33337785369 / 1000000000000), orderedInterval (28873928580 / 1000000000000) (28873928581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1108116982755531 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46815925583 / 1000000000000) (46815925587 / 1000000000000), orderedInterval (10225179739 / 1000000000000) (10225179744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (693408156287193 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-59117416381 / 1000000000000) (-59117416378 / 1000000000000), orderedInterval (-13153427547 / 1000000000000) (-13153427545 / 1000000000000)))) (orderedInterval (-7532325482 / 1000000000000) (-7532325413 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (372917212622631 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19194138370 / 1000000000000) (-19194138150 / 1000000000000), orderedInterval (80478368540 / 1000000000000) (80478368760 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1012542775000893 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (26144133640 / 1000000000000) (26144137242 / 1000000000000), orderedInterval (-42846749829 / 1000000000000) (-42846746227 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1382540594319261 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (32100595358 / 1000000000000) (32100595359 / 1000000000000), orderedInterval (28439266836 / 1000000000000) (28439266837 / 1000000000000)))) (orderedInterval (-3614906859 / 1000000000000) (-3614906789 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (584591843712807 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (43635746684 / 1000000000000) (43635780896 / 1000000000000), orderedInterval (-49666148032 / 1000000000000) (-49666113820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2376333389123847 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29284825140 / 1000000000000) (-29284825138 / 1000000000000), orderedInterval (-14604053688 / 1000000000000) (-14604053687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1587280574988873 / 4000000000000) 4 (IntervalRat.scale (639 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39304245818 / 1000000000000) (39304248585 / 1000000000000), orderedInterval (-7761725562 / 1000000000000) (-7761722794 / 1000000000000)))) (orderedInterval (11024747397 / 1000000000000) (11024749104 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate448_chunkChecks4 :
    compactCertificate448.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate448.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate448_chunkChecks4_0
    compactCertificate448_chunkChecks4_1 compactCertificate448_chunkChecks4_2

theorem compactCertificate448_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate448.chunkCheck r b = true :=
  compactCertificate448.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate448_chunkChecks0
    · exact compactCertificate448_chunkChecks1
    · exact compactCertificate448_chunkChecks2
    · exact compactCertificate448_chunkChecks3
    · exact compactCertificate448_chunkChecks4)

theorem compactCertificate448_coefficient0 :
    compactCertificate448.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate448_coefficient1 :
    compactCertificate448.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate448_coefficient2 :
    compactCertificate448.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate448_coefficient3 :
    compactCertificate448.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate448_coefficient4 :
    compactCertificate448.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate448_coefficients : ∀ r : Fin 5,
    compactCertificate448.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate448_coefficient0
  · exact compactCertificate448_coefficient1
  · exact compactCertificate448_coefficient2
  · exact compactCertificate448_coefficient3
  · exact compactCertificate448_coefficient4

theorem compactCertificate448_lower : (1 : ℚ) ≤ compactCertificate448.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate448, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate448_proves {t : ℝ} (ht : t ∈ compactCertificate448.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate448.proves compactCertificate448_states compactCertificate448_chunks
    compactCertificate448_coefficients compactCertificate448_lower ht

end Erdos232
