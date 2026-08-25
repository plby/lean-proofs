/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate600 : CompactCertificate where
  left := 471
  right := 472
  center := 943 / 2
  grid := fun i =>
    match i.val with
    | 0 => 150
    | 1 => 111
    | 2 => 179
    | 3 => 32
    | 4 => 87
    | 5 => 235
    | 6 => 173
    | 7 => 297
    | 8 => 219
    | 9 => 336
    | 10 => 194
    | 11 => 344
    | 12 => 321
    | 13 => 229
    | 14 => 260
    | 15 => 217
    | 16 => 192
    | 17 => 278
    | 18 => 154
    | 19 => 130
    | 20 => 81
    | 21 => 44
    | 22 => 119
    | 23 => 162
    | 24 => 69
    | 25 => 279
    | _ => 186
  point := fun i =>
    match i.val with
    | 0 => 943 / 2
    | 1 => 1389219063870643 / 4000000000000
    | 2 => 449244901948819 / 800000000000
    | 3 => 405370658075801 / 4000000000000
    | 4 => 1088882607691397 / 4000000000000
    | 5 => 2956528097715249 / 4000000000000
    | 6 => 2177765215383737 / 4000000000000
    | 7 => 3731637815379101 / 4000000000000
    | 8 => 2748707525228759 / 4000000000000
    | 9 => 4217224205564057 / 4000000000000
    | 10 => 2434815530315153 / 4000000000000
    | 11 => 4320622885475077 / 4000000000000
    | 12 => 4036886356070713 / 4000000000000
    | 13 => 2880912586894729 / 4000000000000
    | 14 => 3266647823074191 / 4000000000000
    | 15 => 2723390389723679 / 4000000000000
    | 16 => 2406198001465259 / 4000000000000
    | 17 => 697409966896641 / 800000000000
    | 18 => 1929072671111827 / 4000000000000
    | 19 => 1635296267196347 / 4000000000000
    | 20 => 1023292474771241 / 4000000000000
    | 21 => 550330096249047 / 4000000000000
    | 22 => 1494253265768141 / 4000000000000
    | 23 => 2040275086765357 / 4000000000000
    | 24 => 862707525228759 / 4000000000000
    | 25 => 3506858193965239 / 4000000000000
    | _ => 2342418751509401 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (31804465964 / 1000000000000) (31804465965 / 1000000000000), orderedInterval (18369440480 / 1000000000000) (18369440481 / 1000000000000))
    | 1 => (orderedInterval (25118983598 / 1000000000000) (25118988605 / 1000000000000), orderedInterval (-34706993059 / 1000000000000) (-34706988052 / 1000000000000))
    | 2 => (orderedInterval (127339330 / 1000000000000) (127339331 / 1000000000000), orderedInterval (-33669907157 / 1000000000000) (-33669907156 / 1000000000000))
    | 3 => (orderedInterval (79232760691 / 1000000000000) (79232760739 / 1000000000000), orderedInterval (-2377557895 / 1000000000000) (-2377557846 / 1000000000000))
    | 4 => (orderedInterval (14889106817 / 1000000000000) (14889107006 / 1000000000000), orderedInterval (-46037503199 / 1000000000000) (-46037503010 / 1000000000000))
    | 5 => (orderedInterval (-29271610320 / 1000000000000) (-29271605480 / 1000000000000), orderedInterval (2136405519 / 1000000000000) (2136410360 / 1000000000000))
    | 6 => (orderedInterval (-33757579928 / 1000000000000) (-33757575607 / 1000000000000), orderedInterval (5483874183 / 1000000000000) (5483878504 / 1000000000000))
    | 7 => (orderedInterval (-15636032641 / 1000000000000) (-15636032640 / 1000000000000), orderedInterval (-20918087248 / 1000000000000) (-20918087247 / 1000000000000))
    | 8 => (orderedInterval (1420708499 / 1000000000000) (1420708500 / 1000000000000), orderedInterval (-30405139377 / 1000000000000) (-30405139376 / 1000000000000))
    | 9 => (orderedInterval (-11430016874 / 1000000000000) (-11430016868 / 1000000000000), orderedInterval (21758190512 / 1000000000000) (21758190519 / 1000000000000))
    | 10 => (orderedInterval (650004777 / 1000000000000) (650004778 / 1000000000000), orderedInterval (32332715914 / 1000000000000) (32332715915 / 1000000000000))
    | 11 => (orderedInterval (5608615788 / 1000000000000) (5608615789 / 1000000000000), orderedInterval (23617760633 / 1000000000000) (23617760634 / 1000000000000))
    | 12 => (orderedInterval (-25112897932 / 1000000000000) (-25112889850 / 1000000000000), orderedInterval (-368674957 / 1000000000000) (-368666874 / 1000000000000))
    | 13 => (orderedInterval (-29725949319 / 1000000000000) (-29725946896 / 1000000000000), orderedInterval (551517934 / 1000000000000) (551520357 / 1000000000000))
    | 14 => (orderedInterval (16519156082 / 1000000000000) (16519156083 / 1000000000000), orderedInterval (22498916319 / 1000000000000) (22498916320 / 1000000000000))
    | 15 => (orderedInterval (2833418353 / 1000000000000) (2833418354 / 1000000000000), orderedInterval (-30448953210 / 1000000000000) (-30448953209 / 1000000000000))
    | 16 => (orderedInterval (-24463872651 / 1000000000000) (-24463859500 / 1000000000000), orderedInterval (21463720128 / 1000000000000) (21463733280 / 1000000000000))
    | 17 => (orderedInterval (-19666485306 / 1000000000000) (-19666483153 / 1000000000000), orderedInterval (18544947142 / 1000000000000) (18544949294 / 1000000000000))
    | 18 => (orderedInterval (-24817773081 / 1000000000000) (-24817764118 / 1000000000000), orderedInterval (26561209096 / 1000000000000) (26561218059 / 1000000000000))
    | 19 => (orderedInterval (36809647569 / 1000000000000) (36809647571 / 1000000000000), orderedInterval (14176316512 / 1000000000000) (14176316514 / 1000000000000))
    | 20 => (orderedInterval (-42045897482 / 1000000000000) (-42045843526 / 1000000000000), orderedInterval (26927225294 / 1000000000000) (26927279251 / 1000000000000))
    | 21 => (orderedInterval (9285803473 / 1000000000000) (9285803474 / 1000000000000), orderedInterval (67353108415 / 1000000000000) (67353108417 / 1000000000000))
    | 22 => (orderedInterval (-19749986926 / 1000000000000) (-19749986925 / 1000000000000), orderedInterval (-36224366231 / 1000000000000) (-36224366230 / 1000000000000))
    | 23 => (orderedInterval (33245385227 / 1000000000000) (33245408187 / 1000000000000), orderedInterval (-11984540544 / 1000000000000) (-11984517584 / 1000000000000))
    | 24 => (orderedInterval (16480246962 / 1000000000000) (16480247221 / 1000000000000), orderedInterval (-51808247701 / 1000000000000) (-51808247442 / 1000000000000))
    | 25 => (orderedInterval (-22608718800 / 1000000000000) (-22608718798 / 1000000000000), orderedInterval (-14649587903 / 1000000000000) (-14649587900 / 1000000000000))
    | _ => (orderedInterval (29202030944 / 1000000000000) (29202139165 / 1000000000000), orderedInterval (-15333583399 / 1000000000000) (-15333475178 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (12847709526 / 1000000000000) (12847709606 / 1000000000000)
      | 1 => orderedInterval (1764915905 / 1000000000000) (1764916313 / 1000000000000)
      | 2 => orderedInterval (516613514 / 1000000000000) (516613541 / 1000000000000)
      | 3 => orderedInterval (2876433683 / 1000000000000) (2876433871 / 1000000000000)
      | 4 => orderedInterval (-2441202275 / 1000000000000) (-2441201844 / 1000000000000)
      | 5 => orderedInterval (929165037 / 1000000000000) (929165890 / 1000000000000)
      | 6 => orderedInterval (515932831 / 1000000000000) (515936139 / 1000000000000)
      | 7 => orderedInterval (-2271288764 / 1000000000000) (-2271286948 / 1000000000000)
      | _ => orderedInterval (-3539357798 / 1000000000000) (-3539337360 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (4689624210 / 1000000000000) (4689624282 / 1000000000000)
      | 1 => orderedInterval (-1203014010 / 1000000000000) (-1203013402 / 1000000000000)
      | 2 => orderedInterval (205622737 / 1000000000000) (205622783 / 1000000000000)
      | 3 => orderedInterval (2139127554 / 1000000000000) (2139127944 / 1000000000000)
      | 4 => orderedInterval (-103295861 / 1000000000000) (-103295107 / 1000000000000)
      | 5 => orderedInterval (-1196912737 / 1000000000000) (-1196911610 / 1000000000000)
      | 6 => orderedInterval (-4564017782 / 1000000000000) (-4564015253 / 1000000000000)
      | 7 => orderedInterval (1281823123 / 1000000000000) (1281825078 / 1000000000000)
      | _ => orderedInterval (5647698493 / 1000000000000) (5647723897 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-12753717342 / 1000000000000) (-12753717274 / 1000000000000)
      | 1 => orderedInterval (-5252625557 / 1000000000000) (-5252624619 / 1000000000000)
      | 2 => orderedInterval (-1961415740 / 1000000000000) (-1961415658 / 1000000000000)
      | 3 => orderedInterval (-14424052193 / 1000000000000) (-14424051357 / 1000000000000)
      | 4 => orderedInterval (4732837430 / 1000000000000) (4732838786 / 1000000000000)
      | 5 => orderedInterval (-623130009 / 1000000000000) (-623128496 / 1000000000000)
      | 6 => orderedInterval (-2172512361 / 1000000000000) (-2172510235 / 1000000000000)
      | 7 => orderedInterval (2712394572 / 1000000000000) (2712396686 / 1000000000000)
      | _ => orderedInterval (2056093745 / 1000000000000) (2056125392 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-3786771142 / 1000000000000) (-3786771073 / 1000000000000)
      | 1 => orderedInterval (919444082 / 1000000000000) (919445544 / 1000000000000)
      | 2 => orderedInterval (-2718663031 / 1000000000000) (-2718662882 / 1000000000000)
      | 3 => orderedInterval (-2264990317 / 1000000000000) (-2264988483 / 1000000000000)
      | 4 => orderedInterval (330426690 / 1000000000000) (330429196 / 1000000000000)
      | 5 => orderedInterval (609678956 / 1000000000000) (609681020 / 1000000000000)
      | 6 => orderedInterval (4932226898 / 1000000000000) (4932228818 / 1000000000000)
      | 7 => orderedInterval (-1546381937 / 1000000000000) (-1546379653 / 1000000000000)
      | _ => orderedInterval (-13152761592 / 1000000000000) (-13152722205 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (12706121157 / 1000000000000) (12706121230 / 1000000000000)
      | 1 => orderedInterval (12621139327 / 1000000000000) (12621141617 / 1000000000000)
      | 2 => orderedInterval (7557867984 / 1000000000000) (7557868260 / 1000000000000)
      | 3 => orderedInterval (72878067768 / 1000000000000) (72878071838 / 1000000000000)
      | 4 => orderedInterval (-6541637830 / 1000000000000) (-6541633066 / 1000000000000)
      | 5 => orderedInterval (-2035478785 / 1000000000000) (-2035475902 / 1000000000000)
      | 6 => orderedInterval (3026129845 / 1000000000000) (3026131673 / 1000000000000)
      | 7 => orderedInterval (-3307665935 / 1000000000000) (-3307663461 / 1000000000000)
      | _ => orderedInterval (9022126729 / 1000000000000) (9022175882 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (11198921659 / 1000000000000) (11198949208 / 1000000000000)
    | 1 => orderedInterval (6896655727 / 1000000000000) (6896688612 / 1000000000000)
    | 2 => orderedInterval (-27686127455 / 1000000000000) (-27686086775 / 1000000000000)
    | 3 => orderedInterval (-16677791393 / 1000000000000) (-16677739718 / 1000000000000)
    | _ => orderedInterval (105926670260 / 1000000000000) (105926738071 / 1000000000000)

theorem compactCertificate600_stateChecks0 :
    compactCertificate600.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (943 / 2)) (orderedInterval (31804465964 / 1000000000000) (31804465965 / 1000000000000), orderedInterval (18369440480 / 1000000000000) (18369440481 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1389219063870643 / 4000000000000)) (orderedInterval (25118983598 / 1000000000000) (25118988605 / 1000000000000), orderedInterval (-34706993059 / 1000000000000) (-34706988052 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (449244901948819 / 800000000000)) (orderedInterval (127339330 / 1000000000000) (127339331 / 1000000000000), orderedInterval (-33669907157 / 1000000000000) (-33669907156 / 1000000000000))) = true
  rfl'

theorem compactCertificate600_stateChecks1 :
    compactCertificate600.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (405370658075801 / 4000000000000)) (orderedInterval (79232760691 / 1000000000000) (79232760739 / 1000000000000), orderedInterval (-2377557895 / 1000000000000) (-2377557846 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1088882607691397 / 4000000000000)) (orderedInterval (14889106817 / 1000000000000) (14889107006 / 1000000000000), orderedInterval (-46037503199 / 1000000000000) (-46037503010 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 235 12 (2956528097715249 / 4000000000000)) (orderedInterval (-29271610320 / 1000000000000) (-29271605480 / 1000000000000), orderedInterval (2136405519 / 1000000000000) (2136410360 / 1000000000000))) = true
  rfl'

theorem compactCertificate600_stateChecks2 :
    compactCertificate600.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2177765215383737 / 4000000000000)) (orderedInterval (-33757579928 / 1000000000000) (-33757575607 / 1000000000000), orderedInterval (5483874183 / 1000000000000) (5483878504 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 297 12 (3731637815379101 / 4000000000000)) (orderedInterval (-15636032641 / 1000000000000) (-15636032640 / 1000000000000), orderedInterval (-20918087248 / 1000000000000) (-20918087247 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 219 12 (2748707525228759 / 4000000000000)) (orderedInterval (1420708499 / 1000000000000) (1420708500 / 1000000000000), orderedInterval (-30405139377 / 1000000000000) (-30405139376 / 1000000000000))) = true
  rfl'

theorem compactCertificate600_stateChecks3 :
    compactCertificate600.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 336 12 (4217224205564057 / 4000000000000)) (orderedInterval (-11430016874 / 1000000000000) (-11430016868 / 1000000000000), orderedInterval (21758190512 / 1000000000000) (21758190519 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (2434815530315153 / 4000000000000)) (orderedInterval (650004777 / 1000000000000) (650004778 / 1000000000000), orderedInterval (32332715914 / 1000000000000) (32332715915 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 344 12 (4320622885475077 / 4000000000000)) (orderedInterval (5608615788 / 1000000000000) (5608615789 / 1000000000000), orderedInterval (23617760633 / 1000000000000) (23617760634 / 1000000000000))) = true
  rfl'

theorem compactCertificate600_stateChecks4 :
    compactCertificate600.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 321 12 (4036886356070713 / 4000000000000)) (orderedInterval (-25112897932 / 1000000000000) (-25112889850 / 1000000000000), orderedInterval (-368674957 / 1000000000000) (-368666874 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (2880912586894729 / 4000000000000)) (orderedInterval (-29725949319 / 1000000000000) (-29725946896 / 1000000000000), orderedInterval (551517934 / 1000000000000) (551520357 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 260 12 (3266647823074191 / 4000000000000)) (orderedInterval (16519156082 / 1000000000000) (16519156083 / 1000000000000), orderedInterval (22498916319 / 1000000000000) (22498916320 / 1000000000000))) = true
  rfl'

theorem compactCertificate600_stateChecks5 :
    compactCertificate600.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 217 12 (2723390389723679 / 4000000000000)) (orderedInterval (2833418353 / 1000000000000) (2833418354 / 1000000000000), orderedInterval (-30448953210 / 1000000000000) (-30448953209 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2406198001465259 / 4000000000000)) (orderedInterval (-24463872651 / 1000000000000) (-24463859500 / 1000000000000), orderedInterval (21463720128 / 1000000000000) (21463733280 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 278 12 (697409966896641 / 800000000000)) (orderedInterval (-19666485306 / 1000000000000) (-19666483153 / 1000000000000), orderedInterval (18544947142 / 1000000000000) (18544949294 / 1000000000000))) = true
  rfl'

theorem compactCertificate600_stateChecks6 :
    compactCertificate600.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1929072671111827 / 4000000000000)) (orderedInterval (-24817773081 / 1000000000000) (-24817764118 / 1000000000000), orderedInterval (26561209096 / 1000000000000) (26561218059 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1635296267196347 / 4000000000000)) (orderedInterval (36809647569 / 1000000000000) (36809647571 / 1000000000000), orderedInterval (14176316512 / 1000000000000) (14176316514 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1023292474771241 / 4000000000000)) (orderedInterval (-42045897482 / 1000000000000) (-42045843526 / 1000000000000), orderedInterval (26927225294 / 1000000000000) (26927279251 / 1000000000000))) = true
  rfl'

theorem compactCertificate600_stateChecks7 :
    compactCertificate600.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (550330096249047 / 4000000000000)) (orderedInterval (9285803473 / 1000000000000) (9285803474 / 1000000000000), orderedInterval (67353108415 / 1000000000000) (67353108417 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1494253265768141 / 4000000000000)) (orderedInterval (-19749986926 / 1000000000000) (-19749986925 / 1000000000000), orderedInterval (-36224366231 / 1000000000000) (-36224366230 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2040275086765357 / 4000000000000)) (orderedInterval (33245385227 / 1000000000000) (33245408187 / 1000000000000), orderedInterval (-11984540544 / 1000000000000) (-11984517584 / 1000000000000))) = true
  rfl'

theorem compactCertificate600_stateChecks8 :
    compactCertificate600.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (862707525228759 / 4000000000000)) (orderedInterval (16480246962 / 1000000000000) (16480247221 / 1000000000000), orderedInterval (-51808247701 / 1000000000000) (-51808247442 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 279 12 (3506858193965239 / 4000000000000)) (orderedInterval (-22608718800 / 1000000000000) (-22608718798 / 1000000000000), orderedInterval (-14649587903 / 1000000000000) (-14649587900 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2342418751509401 / 4000000000000)) (orderedInterval (29202030944 / 1000000000000) (29202139165 / 1000000000000), orderedInterval (-15333583399 / 1000000000000) (-15333475178 / 1000000000000))) = true
  rfl'

theorem compactCertificate600_states : ∀ j,
    BesselStateValid (compactCertificate600.point j) (compactCertificate600.state j) :=
  compactCertificate600.statesValid_of_checks3 compactCertificate600_stateChecks0
    compactCertificate600_stateChecks1 compactCertificate600_stateChecks2
    compactCertificate600_stateChecks3 compactCertificate600_stateChecks4
    compactCertificate600_stateChecks5 compactCertificate600_stateChecks6
    compactCertificate600_stateChecks7 compactCertificate600_stateChecks8

theorem compactCertificate600_chunkChecks0_0 :
    compactCertificate600.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (943 / 2) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (31804465964 / 1000000000000) (31804465965 / 1000000000000), orderedInterval (18369440480 / 1000000000000) (18369440481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1389219063870643 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (25118983598 / 1000000000000) (25118988605 / 1000000000000), orderedInterval (-34706993059 / 1000000000000) (-34706988052 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (449244901948819 / 800000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (127339330 / 1000000000000) (127339331 / 1000000000000), orderedInterval (-33669907157 / 1000000000000) (-33669907156 / 1000000000000)))) (orderedInterval (12847709526 / 1000000000000) (12847709606 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (405370658075801 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79232760691 / 1000000000000) (79232760739 / 1000000000000), orderedInterval (-2377557895 / 1000000000000) (-2377557846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1088882607691397 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14889106817 / 1000000000000) (14889107006 / 1000000000000), orderedInterval (-46037503199 / 1000000000000) (-46037503010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2956528097715249 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29271610320 / 1000000000000) (-29271605480 / 1000000000000), orderedInterval (2136405519 / 1000000000000) (2136410360 / 1000000000000)))) (orderedInterval (1764915905 / 1000000000000) (1764916313 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2177765215383737 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33757579928 / 1000000000000) (-33757575607 / 1000000000000), orderedInterval (5483874183 / 1000000000000) (5483878504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3731637815379101 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15636032641 / 1000000000000) (-15636032640 / 1000000000000), orderedInterval (-20918087248 / 1000000000000) (-20918087247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2748707525228759 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1420708499 / 1000000000000) (1420708500 / 1000000000000), orderedInterval (-30405139377 / 1000000000000) (-30405139376 / 1000000000000)))) (orderedInterval (516613514 / 1000000000000) (516613541 / 1000000000000))) = true
  rfl'

theorem compactCertificate600_chunkChecks0_1 :
    compactCertificate600.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4217224205564057 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11430016874 / 1000000000000) (-11430016868 / 1000000000000), orderedInterval (21758190512 / 1000000000000) (21758190519 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2434815530315153 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (650004777 / 1000000000000) (650004778 / 1000000000000), orderedInterval (32332715914 / 1000000000000) (32332715915 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4320622885475077 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5608615788 / 1000000000000) (5608615789 / 1000000000000), orderedInterval (23617760633 / 1000000000000) (23617760634 / 1000000000000)))) (orderedInterval (2876433683 / 1000000000000) (2876433871 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4036886356070713 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25112897932 / 1000000000000) (-25112889850 / 1000000000000), orderedInterval (-368674957 / 1000000000000) (-368666874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2880912586894729 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29725949319 / 1000000000000) (-29725946896 / 1000000000000), orderedInterval (551517934 / 1000000000000) (551520357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3266647823074191 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (16519156082 / 1000000000000) (16519156083 / 1000000000000), orderedInterval (22498916319 / 1000000000000) (22498916320 / 1000000000000)))) (orderedInterval (-2441202275 / 1000000000000) (-2441201844 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2723390389723679 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2833418353 / 1000000000000) (2833418354 / 1000000000000), orderedInterval (-30448953210 / 1000000000000) (-30448953209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2406198001465259 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24463872651 / 1000000000000) (-24463859500 / 1000000000000), orderedInterval (21463720128 / 1000000000000) (21463733280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (697409966896641 / 800000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19666485306 / 1000000000000) (-19666483153 / 1000000000000), orderedInterval (18544947142 / 1000000000000) (18544949294 / 1000000000000)))) (orderedInterval (929165037 / 1000000000000) (929165890 / 1000000000000))) = true
  rfl'

theorem compactCertificate600_chunkChecks0_2 :
    compactCertificate600.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1929072671111827 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24817773081 / 1000000000000) (-24817764118 / 1000000000000), orderedInterval (26561209096 / 1000000000000) (26561218059 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1635296267196347 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (36809647569 / 1000000000000) (36809647571 / 1000000000000), orderedInterval (14176316512 / 1000000000000) (14176316514 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1023292474771241 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-42045897482 / 1000000000000) (-42045843526 / 1000000000000), orderedInterval (26927225294 / 1000000000000) (26927279251 / 1000000000000)))) (orderedInterval (515932831 / 1000000000000) (515936139 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (550330096249047 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (9285803473 / 1000000000000) (9285803474 / 1000000000000), orderedInterval (67353108415 / 1000000000000) (67353108417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1494253265768141 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19749986926 / 1000000000000) (-19749986925 / 1000000000000), orderedInterval (-36224366231 / 1000000000000) (-36224366230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2040275086765357 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33245385227 / 1000000000000) (33245408187 / 1000000000000), orderedInterval (-11984540544 / 1000000000000) (-11984517584 / 1000000000000)))) (orderedInterval (-2271288764 / 1000000000000) (-2271286948 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (862707525228759 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16480246962 / 1000000000000) (16480247221 / 1000000000000), orderedInterval (-51808247701 / 1000000000000) (-51808247442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3506858193965239 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22608718800 / 1000000000000) (-22608718798 / 1000000000000), orderedInterval (-14649587903 / 1000000000000) (-14649587900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2342418751509401 / 4000000000000) 0 (IntervalRat.scale (943 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29202030944 / 1000000000000) (29202139165 / 1000000000000), orderedInterval (-15333583399 / 1000000000000) (-15333475178 / 1000000000000)))) (orderedInterval (-3539357798 / 1000000000000) (-3539337360 / 1000000000000))) = true
  rfl'

theorem compactCertificate600_chunkChecks0 :
    compactCertificate600.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate600.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate600_chunkChecks0_0
    compactCertificate600_chunkChecks0_1 compactCertificate600_chunkChecks0_2

theorem compactCertificate600_chunkChecks1_0 :
    compactCertificate600.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (943 / 2) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (31804465964 / 1000000000000) (31804465965 / 1000000000000), orderedInterval (18369440480 / 1000000000000) (18369440481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1389219063870643 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (25118983598 / 1000000000000) (25118988605 / 1000000000000), orderedInterval (-34706993059 / 1000000000000) (-34706988052 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (449244901948819 / 800000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (127339330 / 1000000000000) (127339331 / 1000000000000), orderedInterval (-33669907157 / 1000000000000) (-33669907156 / 1000000000000)))) (orderedInterval (4689624210 / 1000000000000) (4689624282 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (405370658075801 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79232760691 / 1000000000000) (79232760739 / 1000000000000), orderedInterval (-2377557895 / 1000000000000) (-2377557846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1088882607691397 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14889106817 / 1000000000000) (14889107006 / 1000000000000), orderedInterval (-46037503199 / 1000000000000) (-46037503010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2956528097715249 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29271610320 / 1000000000000) (-29271605480 / 1000000000000), orderedInterval (2136405519 / 1000000000000) (2136410360 / 1000000000000)))) (orderedInterval (-1203014010 / 1000000000000) (-1203013402 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2177765215383737 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33757579928 / 1000000000000) (-33757575607 / 1000000000000), orderedInterval (5483874183 / 1000000000000) (5483878504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3731637815379101 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15636032641 / 1000000000000) (-15636032640 / 1000000000000), orderedInterval (-20918087248 / 1000000000000) (-20918087247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2748707525228759 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1420708499 / 1000000000000) (1420708500 / 1000000000000), orderedInterval (-30405139377 / 1000000000000) (-30405139376 / 1000000000000)))) (orderedInterval (205622737 / 1000000000000) (205622783 / 1000000000000))) = true
  rfl'

theorem compactCertificate600_chunkChecks1_1 :
    compactCertificate600.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4217224205564057 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11430016874 / 1000000000000) (-11430016868 / 1000000000000), orderedInterval (21758190512 / 1000000000000) (21758190519 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2434815530315153 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (650004777 / 1000000000000) (650004778 / 1000000000000), orderedInterval (32332715914 / 1000000000000) (32332715915 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4320622885475077 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5608615788 / 1000000000000) (5608615789 / 1000000000000), orderedInterval (23617760633 / 1000000000000) (23617760634 / 1000000000000)))) (orderedInterval (2139127554 / 1000000000000) (2139127944 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4036886356070713 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25112897932 / 1000000000000) (-25112889850 / 1000000000000), orderedInterval (-368674957 / 1000000000000) (-368666874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2880912586894729 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29725949319 / 1000000000000) (-29725946896 / 1000000000000), orderedInterval (551517934 / 1000000000000) (551520357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3266647823074191 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (16519156082 / 1000000000000) (16519156083 / 1000000000000), orderedInterval (22498916319 / 1000000000000) (22498916320 / 1000000000000)))) (orderedInterval (-103295861 / 1000000000000) (-103295107 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2723390389723679 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2833418353 / 1000000000000) (2833418354 / 1000000000000), orderedInterval (-30448953210 / 1000000000000) (-30448953209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2406198001465259 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24463872651 / 1000000000000) (-24463859500 / 1000000000000), orderedInterval (21463720128 / 1000000000000) (21463733280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (697409966896641 / 800000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19666485306 / 1000000000000) (-19666483153 / 1000000000000), orderedInterval (18544947142 / 1000000000000) (18544949294 / 1000000000000)))) (orderedInterval (-1196912737 / 1000000000000) (-1196911610 / 1000000000000))) = true
  rfl'

theorem compactCertificate600_chunkChecks1_2 :
    compactCertificate600.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1929072671111827 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24817773081 / 1000000000000) (-24817764118 / 1000000000000), orderedInterval (26561209096 / 1000000000000) (26561218059 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1635296267196347 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (36809647569 / 1000000000000) (36809647571 / 1000000000000), orderedInterval (14176316512 / 1000000000000) (14176316514 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1023292474771241 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-42045897482 / 1000000000000) (-42045843526 / 1000000000000), orderedInterval (26927225294 / 1000000000000) (26927279251 / 1000000000000)))) (orderedInterval (-4564017782 / 1000000000000) (-4564015253 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (550330096249047 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (9285803473 / 1000000000000) (9285803474 / 1000000000000), orderedInterval (67353108415 / 1000000000000) (67353108417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1494253265768141 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19749986926 / 1000000000000) (-19749986925 / 1000000000000), orderedInterval (-36224366231 / 1000000000000) (-36224366230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2040275086765357 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33245385227 / 1000000000000) (33245408187 / 1000000000000), orderedInterval (-11984540544 / 1000000000000) (-11984517584 / 1000000000000)))) (orderedInterval (1281823123 / 1000000000000) (1281825078 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (862707525228759 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16480246962 / 1000000000000) (16480247221 / 1000000000000), orderedInterval (-51808247701 / 1000000000000) (-51808247442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3506858193965239 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22608718800 / 1000000000000) (-22608718798 / 1000000000000), orderedInterval (-14649587903 / 1000000000000) (-14649587900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2342418751509401 / 4000000000000) 1 (IntervalRat.scale (943 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29202030944 / 1000000000000) (29202139165 / 1000000000000), orderedInterval (-15333583399 / 1000000000000) (-15333475178 / 1000000000000)))) (orderedInterval (5647698493 / 1000000000000) (5647723897 / 1000000000000))) = true
  rfl'

theorem compactCertificate600_chunkChecks1 :
    compactCertificate600.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate600.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate600_chunkChecks1_0
    compactCertificate600_chunkChecks1_1 compactCertificate600_chunkChecks1_2

theorem compactCertificate600_chunkChecks2_0 :
    compactCertificate600.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (943 / 2) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (31804465964 / 1000000000000) (31804465965 / 1000000000000), orderedInterval (18369440480 / 1000000000000) (18369440481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1389219063870643 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (25118983598 / 1000000000000) (25118988605 / 1000000000000), orderedInterval (-34706993059 / 1000000000000) (-34706988052 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (449244901948819 / 800000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (127339330 / 1000000000000) (127339331 / 1000000000000), orderedInterval (-33669907157 / 1000000000000) (-33669907156 / 1000000000000)))) (orderedInterval (-12753717342 / 1000000000000) (-12753717274 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (405370658075801 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79232760691 / 1000000000000) (79232760739 / 1000000000000), orderedInterval (-2377557895 / 1000000000000) (-2377557846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1088882607691397 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14889106817 / 1000000000000) (14889107006 / 1000000000000), orderedInterval (-46037503199 / 1000000000000) (-46037503010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2956528097715249 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29271610320 / 1000000000000) (-29271605480 / 1000000000000), orderedInterval (2136405519 / 1000000000000) (2136410360 / 1000000000000)))) (orderedInterval (-5252625557 / 1000000000000) (-5252624619 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2177765215383737 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33757579928 / 1000000000000) (-33757575607 / 1000000000000), orderedInterval (5483874183 / 1000000000000) (5483878504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3731637815379101 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15636032641 / 1000000000000) (-15636032640 / 1000000000000), orderedInterval (-20918087248 / 1000000000000) (-20918087247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2748707525228759 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1420708499 / 1000000000000) (1420708500 / 1000000000000), orderedInterval (-30405139377 / 1000000000000) (-30405139376 / 1000000000000)))) (orderedInterval (-1961415740 / 1000000000000) (-1961415658 / 1000000000000))) = true
  rfl'

theorem compactCertificate600_chunkChecks2_1 :
    compactCertificate600.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4217224205564057 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11430016874 / 1000000000000) (-11430016868 / 1000000000000), orderedInterval (21758190512 / 1000000000000) (21758190519 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2434815530315153 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (650004777 / 1000000000000) (650004778 / 1000000000000), orderedInterval (32332715914 / 1000000000000) (32332715915 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4320622885475077 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5608615788 / 1000000000000) (5608615789 / 1000000000000), orderedInterval (23617760633 / 1000000000000) (23617760634 / 1000000000000)))) (orderedInterval (-14424052193 / 1000000000000) (-14424051357 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4036886356070713 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25112897932 / 1000000000000) (-25112889850 / 1000000000000), orderedInterval (-368674957 / 1000000000000) (-368666874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2880912586894729 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29725949319 / 1000000000000) (-29725946896 / 1000000000000), orderedInterval (551517934 / 1000000000000) (551520357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3266647823074191 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (16519156082 / 1000000000000) (16519156083 / 1000000000000), orderedInterval (22498916319 / 1000000000000) (22498916320 / 1000000000000)))) (orderedInterval (4732837430 / 1000000000000) (4732838786 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2723390389723679 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2833418353 / 1000000000000) (2833418354 / 1000000000000), orderedInterval (-30448953210 / 1000000000000) (-30448953209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2406198001465259 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24463872651 / 1000000000000) (-24463859500 / 1000000000000), orderedInterval (21463720128 / 1000000000000) (21463733280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (697409966896641 / 800000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19666485306 / 1000000000000) (-19666483153 / 1000000000000), orderedInterval (18544947142 / 1000000000000) (18544949294 / 1000000000000)))) (orderedInterval (-623130009 / 1000000000000) (-623128496 / 1000000000000))) = true
  rfl'

theorem compactCertificate600_chunkChecks2_2 :
    compactCertificate600.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1929072671111827 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24817773081 / 1000000000000) (-24817764118 / 1000000000000), orderedInterval (26561209096 / 1000000000000) (26561218059 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1635296267196347 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (36809647569 / 1000000000000) (36809647571 / 1000000000000), orderedInterval (14176316512 / 1000000000000) (14176316514 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1023292474771241 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-42045897482 / 1000000000000) (-42045843526 / 1000000000000), orderedInterval (26927225294 / 1000000000000) (26927279251 / 1000000000000)))) (orderedInterval (-2172512361 / 1000000000000) (-2172510235 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (550330096249047 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (9285803473 / 1000000000000) (9285803474 / 1000000000000), orderedInterval (67353108415 / 1000000000000) (67353108417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1494253265768141 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19749986926 / 1000000000000) (-19749986925 / 1000000000000), orderedInterval (-36224366231 / 1000000000000) (-36224366230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2040275086765357 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33245385227 / 1000000000000) (33245408187 / 1000000000000), orderedInterval (-11984540544 / 1000000000000) (-11984517584 / 1000000000000)))) (orderedInterval (2712394572 / 1000000000000) (2712396686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (862707525228759 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16480246962 / 1000000000000) (16480247221 / 1000000000000), orderedInterval (-51808247701 / 1000000000000) (-51808247442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3506858193965239 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22608718800 / 1000000000000) (-22608718798 / 1000000000000), orderedInterval (-14649587903 / 1000000000000) (-14649587900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2342418751509401 / 4000000000000) 2 (IntervalRat.scale (943 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29202030944 / 1000000000000) (29202139165 / 1000000000000), orderedInterval (-15333583399 / 1000000000000) (-15333475178 / 1000000000000)))) (orderedInterval (2056093745 / 1000000000000) (2056125392 / 1000000000000))) = true
  rfl'

theorem compactCertificate600_chunkChecks2 :
    compactCertificate600.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate600.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate600_chunkChecks2_0
    compactCertificate600_chunkChecks2_1 compactCertificate600_chunkChecks2_2

theorem compactCertificate600_chunkChecks3_0 :
    compactCertificate600.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (943 / 2) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (31804465964 / 1000000000000) (31804465965 / 1000000000000), orderedInterval (18369440480 / 1000000000000) (18369440481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1389219063870643 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (25118983598 / 1000000000000) (25118988605 / 1000000000000), orderedInterval (-34706993059 / 1000000000000) (-34706988052 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (449244901948819 / 800000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (127339330 / 1000000000000) (127339331 / 1000000000000), orderedInterval (-33669907157 / 1000000000000) (-33669907156 / 1000000000000)))) (orderedInterval (-3786771142 / 1000000000000) (-3786771073 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (405370658075801 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79232760691 / 1000000000000) (79232760739 / 1000000000000), orderedInterval (-2377557895 / 1000000000000) (-2377557846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1088882607691397 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14889106817 / 1000000000000) (14889107006 / 1000000000000), orderedInterval (-46037503199 / 1000000000000) (-46037503010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2956528097715249 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29271610320 / 1000000000000) (-29271605480 / 1000000000000), orderedInterval (2136405519 / 1000000000000) (2136410360 / 1000000000000)))) (orderedInterval (919444082 / 1000000000000) (919445544 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2177765215383737 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33757579928 / 1000000000000) (-33757575607 / 1000000000000), orderedInterval (5483874183 / 1000000000000) (5483878504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3731637815379101 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15636032641 / 1000000000000) (-15636032640 / 1000000000000), orderedInterval (-20918087248 / 1000000000000) (-20918087247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2748707525228759 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1420708499 / 1000000000000) (1420708500 / 1000000000000), orderedInterval (-30405139377 / 1000000000000) (-30405139376 / 1000000000000)))) (orderedInterval (-2718663031 / 1000000000000) (-2718662882 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate600_chunkChecks3_1 :
    compactCertificate600.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4217224205564057 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11430016874 / 1000000000000) (-11430016868 / 1000000000000), orderedInterval (21758190512 / 1000000000000) (21758190519 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2434815530315153 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (650004777 / 1000000000000) (650004778 / 1000000000000), orderedInterval (32332715914 / 1000000000000) (32332715915 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4320622885475077 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5608615788 / 1000000000000) (5608615789 / 1000000000000), orderedInterval (23617760633 / 1000000000000) (23617760634 / 1000000000000)))) (orderedInterval (-2264990317 / 1000000000000) (-2264988483 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4036886356070713 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25112897932 / 1000000000000) (-25112889850 / 1000000000000), orderedInterval (-368674957 / 1000000000000) (-368666874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2880912586894729 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29725949319 / 1000000000000) (-29725946896 / 1000000000000), orderedInterval (551517934 / 1000000000000) (551520357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3266647823074191 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (16519156082 / 1000000000000) (16519156083 / 1000000000000), orderedInterval (22498916319 / 1000000000000) (22498916320 / 1000000000000)))) (orderedInterval (330426690 / 1000000000000) (330429196 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2723390389723679 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2833418353 / 1000000000000) (2833418354 / 1000000000000), orderedInterval (-30448953210 / 1000000000000) (-30448953209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2406198001465259 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24463872651 / 1000000000000) (-24463859500 / 1000000000000), orderedInterval (21463720128 / 1000000000000) (21463733280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (697409966896641 / 800000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19666485306 / 1000000000000) (-19666483153 / 1000000000000), orderedInterval (18544947142 / 1000000000000) (18544949294 / 1000000000000)))) (orderedInterval (609678956 / 1000000000000) (609681020 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate600_chunkChecks3_2 :
    compactCertificate600.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1929072671111827 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24817773081 / 1000000000000) (-24817764118 / 1000000000000), orderedInterval (26561209096 / 1000000000000) (26561218059 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1635296267196347 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (36809647569 / 1000000000000) (36809647571 / 1000000000000), orderedInterval (14176316512 / 1000000000000) (14176316514 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1023292474771241 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-42045897482 / 1000000000000) (-42045843526 / 1000000000000), orderedInterval (26927225294 / 1000000000000) (26927279251 / 1000000000000)))) (orderedInterval (4932226898 / 1000000000000) (4932228818 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (550330096249047 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (9285803473 / 1000000000000) (9285803474 / 1000000000000), orderedInterval (67353108415 / 1000000000000) (67353108417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1494253265768141 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19749986926 / 1000000000000) (-19749986925 / 1000000000000), orderedInterval (-36224366231 / 1000000000000) (-36224366230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2040275086765357 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33245385227 / 1000000000000) (33245408187 / 1000000000000), orderedInterval (-11984540544 / 1000000000000) (-11984517584 / 1000000000000)))) (orderedInterval (-1546381937 / 1000000000000) (-1546379653 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (862707525228759 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16480246962 / 1000000000000) (16480247221 / 1000000000000), orderedInterval (-51808247701 / 1000000000000) (-51808247442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3506858193965239 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22608718800 / 1000000000000) (-22608718798 / 1000000000000), orderedInterval (-14649587903 / 1000000000000) (-14649587900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2342418751509401 / 4000000000000) 3 (IntervalRat.scale (943 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29202030944 / 1000000000000) (29202139165 / 1000000000000), orderedInterval (-15333583399 / 1000000000000) (-15333475178 / 1000000000000)))) (orderedInterval (-13152761592 / 1000000000000) (-13152722205 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate600_chunkChecks3 :
    compactCertificate600.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate600.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate600_chunkChecks3_0
    compactCertificate600_chunkChecks3_1 compactCertificate600_chunkChecks3_2

theorem compactCertificate600_chunkChecks4_0 :
    compactCertificate600.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (943 / 2) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (31804465964 / 1000000000000) (31804465965 / 1000000000000), orderedInterval (18369440480 / 1000000000000) (18369440481 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1389219063870643 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (25118983598 / 1000000000000) (25118988605 / 1000000000000), orderedInterval (-34706993059 / 1000000000000) (-34706988052 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (449244901948819 / 800000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (127339330 / 1000000000000) (127339331 / 1000000000000), orderedInterval (-33669907157 / 1000000000000) (-33669907156 / 1000000000000)))) (orderedInterval (12706121157 / 1000000000000) (12706121230 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (405370658075801 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (79232760691 / 1000000000000) (79232760739 / 1000000000000), orderedInterval (-2377557895 / 1000000000000) (-2377557846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1088882607691397 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (14889106817 / 1000000000000) (14889107006 / 1000000000000), orderedInterval (-46037503199 / 1000000000000) (-46037503010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2956528097715249 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29271610320 / 1000000000000) (-29271605480 / 1000000000000), orderedInterval (2136405519 / 1000000000000) (2136410360 / 1000000000000)))) (orderedInterval (12621139327 / 1000000000000) (12621141617 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2177765215383737 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33757579928 / 1000000000000) (-33757575607 / 1000000000000), orderedInterval (5483874183 / 1000000000000) (5483878504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3731637815379101 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15636032641 / 1000000000000) (-15636032640 / 1000000000000), orderedInterval (-20918087248 / 1000000000000) (-20918087247 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2748707525228759 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1420708499 / 1000000000000) (1420708500 / 1000000000000), orderedInterval (-30405139377 / 1000000000000) (-30405139376 / 1000000000000)))) (orderedInterval (7557867984 / 1000000000000) (7557868260 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate600_chunkChecks4_1 :
    compactCertificate600.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4217224205564057 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11430016874 / 1000000000000) (-11430016868 / 1000000000000), orderedInterval (21758190512 / 1000000000000) (21758190519 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2434815530315153 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (650004777 / 1000000000000) (650004778 / 1000000000000), orderedInterval (32332715914 / 1000000000000) (32332715915 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4320622885475077 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5608615788 / 1000000000000) (5608615789 / 1000000000000), orderedInterval (23617760633 / 1000000000000) (23617760634 / 1000000000000)))) (orderedInterval (72878067768 / 1000000000000) (72878071838 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4036886356070713 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25112897932 / 1000000000000) (-25112889850 / 1000000000000), orderedInterval (-368674957 / 1000000000000) (-368666874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2880912586894729 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-29725949319 / 1000000000000) (-29725946896 / 1000000000000), orderedInterval (551517934 / 1000000000000) (551520357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3266647823074191 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (16519156082 / 1000000000000) (16519156083 / 1000000000000), orderedInterval (22498916319 / 1000000000000) (22498916320 / 1000000000000)))) (orderedInterval (-6541637830 / 1000000000000) (-6541633066 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2723390389723679 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (2833418353 / 1000000000000) (2833418354 / 1000000000000), orderedInterval (-30448953210 / 1000000000000) (-30448953209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2406198001465259 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24463872651 / 1000000000000) (-24463859500 / 1000000000000), orderedInterval (21463720128 / 1000000000000) (21463733280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (697409966896641 / 800000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19666485306 / 1000000000000) (-19666483153 / 1000000000000), orderedInterval (18544947142 / 1000000000000) (18544949294 / 1000000000000)))) (orderedInterval (-2035478785 / 1000000000000) (-2035475902 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate600_chunkChecks4_2 :
    compactCertificate600.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1929072671111827 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-24817773081 / 1000000000000) (-24817764118 / 1000000000000), orderedInterval (26561209096 / 1000000000000) (26561218059 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1635296267196347 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (36809647569 / 1000000000000) (36809647571 / 1000000000000), orderedInterval (14176316512 / 1000000000000) (14176316514 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1023292474771241 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-42045897482 / 1000000000000) (-42045843526 / 1000000000000), orderedInterval (26927225294 / 1000000000000) (26927279251 / 1000000000000)))) (orderedInterval (3026129845 / 1000000000000) (3026131673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (550330096249047 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (9285803473 / 1000000000000) (9285803474 / 1000000000000), orderedInterval (67353108415 / 1000000000000) (67353108417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1494253265768141 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19749986926 / 1000000000000) (-19749986925 / 1000000000000), orderedInterval (-36224366231 / 1000000000000) (-36224366230 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2040275086765357 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (33245385227 / 1000000000000) (33245408187 / 1000000000000), orderedInterval (-11984540544 / 1000000000000) (-11984517584 / 1000000000000)))) (orderedInterval (-3307665935 / 1000000000000) (-3307663461 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (862707525228759 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16480246962 / 1000000000000) (16480247221 / 1000000000000), orderedInterval (-51808247701 / 1000000000000) (-51808247442 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3506858193965239 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22608718800 / 1000000000000) (-22608718798 / 1000000000000), orderedInterval (-14649587903 / 1000000000000) (-14649587900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2342418751509401 / 4000000000000) 4 (IntervalRat.scale (943 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29202030944 / 1000000000000) (29202139165 / 1000000000000), orderedInterval (-15333583399 / 1000000000000) (-15333475178 / 1000000000000)))) (orderedInterval (9022126729 / 1000000000000) (9022175882 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate600_chunkChecks4 :
    compactCertificate600.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate600.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate600_chunkChecks4_0
    compactCertificate600_chunkChecks4_1 compactCertificate600_chunkChecks4_2

theorem compactCertificate600_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate600.chunkCheck r b = true :=
  compactCertificate600.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate600_chunkChecks0
    · exact compactCertificate600_chunkChecks1
    · exact compactCertificate600_chunkChecks2
    · exact compactCertificate600_chunkChecks3
    · exact compactCertificate600_chunkChecks4)

theorem compactCertificate600_coefficient0 :
    compactCertificate600.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate600_coefficient1 :
    compactCertificate600.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate600_coefficient2 :
    compactCertificate600.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate600_coefficient3 :
    compactCertificate600.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate600_coefficient4 :
    compactCertificate600.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate600_coefficients : ∀ r : Fin 5,
    compactCertificate600.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate600_coefficient0
  · exact compactCertificate600_coefficient1
  · exact compactCertificate600_coefficient2
  · exact compactCertificate600_coefficient3
  · exact compactCertificate600_coefficient4

theorem compactCertificate600_lower : (1 : ℚ) ≤ compactCertificate600.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate600, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate600_proves {t : ℝ} (ht : t ∈ compactCertificate600.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate600.proves compactCertificate600_states compactCertificate600_chunks
    compactCertificate600_coefficients compactCertificate600_lower ht

end Erdos232
