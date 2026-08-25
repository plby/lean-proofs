/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate306 : CompactCertificate where
  left := 179
  right := 180
  center := 359 / 2
  grid := fun i =>
    match i.val with
    | 0 => 57
    | 1 => 42
    | 2 => 68
    | 3 => 12
    | 4 => 33
    | 5 => 90
    | 6 => 66
    | 7 => 113
    | 8 => 83
    | 9 => 128
    | 10 => 74
    | 11 => 131
    | 12 => 122
    | 13 => 87
    | 14 => 99
    | 15 => 83
    | 16 => 73
    | 17 => 106
    | 18 => 58
    | 19 => 50
    | 20 => 31
    | 21 => 17
    | 22 => 45
    | 23 => 62
    | 24 => 26
    | 25 => 106
    | _ => 71
  point := fun i =>
    match i.val with
    | 0 => 359 / 2
    | 1 => 528875550296459 / 4000000000000
    | 2 => 171027486531947 / 800000000000
    | 3 => 154324566542113 / 4000000000000
    | 4 => 414537493278061 / 4000000000000
    | 5 => 1125549933276537 / 4000000000000
    | 6 => 829074986556481 / 4000000000000
    | 7 => 1420634120595013 / 4000000000000
    | 8 => 1046432663369167 / 4000000000000
    | 9 => 1605496807844641 / 4000000000000
    | 10 => 926934014192089 / 4000000000000
    | 11 => 1644860674321901 / 4000000000000
    | 12 => 1536842207666369 / 4000000000000
    | 13 => 1096763116325777 / 4000000000000
    | 14 => 1243612479834183 / 4000000000000
    | 15 => 1036794432567127 / 4000000000000
    | 16 => 916039323993667 / 4000000000000
    | 17 => 265503900441033 / 800000000000
    | 18 => 734397761324651 / 4000000000000
    | 19 => 622557115507411 / 4000000000000
    | 20 => 389567336630833 / 4000000000000
    | 21 => 209510609282511 / 4000000000000
    | 22 => 568862059820533 / 4000000000000
    | 23 => 776732509171541 / 4000000000000
    | 24 => 328432663369167 / 4000000000000
    | 25 => 1335060542559407 / 4000000000000
    | _ => 891758570298913 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-55801164524 / 1000000000000) (-55801164523 / 1000000000000), orderedInterval (-20649563104 / 1000000000000) (-20649563103 / 1000000000000))
    | 1 => (orderedInterval (60411189255 / 1000000000000) (60411189256 / 1000000000000), orderedInterval (33908969297 / 1000000000000) (33908969298 / 1000000000000))
    | 2 => (orderedInterval (44096219122 / 1000000000000) (44096219123 / 1000000000000), orderedInterval (32043103059 / 1000000000000) (32043103060 / 1000000000000))
    | 3 => (orderedInterval (127890281250 / 1000000000000) (127890281334 / 1000000000000), orderedInterval (-13637030531 / 1000000000000) (-13637030447 / 1000000000000))
    | 4 => (orderedInterval (-53195064288 / 1000000000000) (-53195064287 / 1000000000000), orderedInterval (-57304031402 / 1000000000000) (-57304031401 / 1000000000000))
    | 5 => (orderedInterval (-25703682973 / 1000000000000) (-25703679039 / 1000000000000), orderedInterval (40067581064 / 1000000000000) (40067584997 / 1000000000000))
    | 6 => (orderedInterval (36058952993 / 1000000000000) (36058952994 / 1000000000000), orderedInterval (41998920102 / 1000000000000) (41998920103 / 1000000000000))
    | 7 => (orderedInterval (-34280100623 / 1000000000000) (-34280100622 / 1000000000000), orderedInterval (-24798647446 / 1000000000000) (-24798647445 / 1000000000000))
    | 8 => (orderedInterval (-49209175770 / 1000000000000) (-49209175493 / 1000000000000), orderedInterval (3549263105 / 1000000000000) (3549263381 / 1000000000000))
    | 9 => (orderedInterval (1410696671 / 1000000000000) (1410696672 / 1000000000000), orderedInterval (39799141374 / 1000000000000) (39799141375 / 1000000000000))
    | 10 => (orderedInterval (2122487162 / 1000000000000) (2122487164 / 1000000000000), orderedInterval (52366288842 / 1000000000000) (52366288843 / 1000000000000))
    | 11 => (orderedInterval (-17171896438 / 1000000000000) (-17171896437 / 1000000000000), orderedInterval (-35380665854 / 1000000000000) (-35380665853 / 1000000000000))
    | 12 => (orderedInterval (40245421485 / 1000000000000) (40245423070 / 1000000000000), orderedInterval (-6156480465 / 1000000000000) (-6156478881 / 1000000000000))
    | 13 => (orderedInterval (-48005567763 / 1000000000000) (-48005567393 / 1000000000000), orderedInterval (4243846740 / 1000000000000) (4243847110 / 1000000000000))
    | 14 => (orderedInterval (-28115898805 / 1000000000000) (-28115898804 / 1000000000000), orderedInterval (-35411004762 / 1000000000000) (-35411004761 / 1000000000000))
    | 15 => (orderedInterval (34452326776 / 1000000000000) (34452357825 / 1000000000000), orderedInterval (-35691524506 / 1000000000000) (-35691493457 / 1000000000000))
    | 16 => (orderedInterval (-23332250342 / 1000000000000) (-23332250341 / 1000000000000), orderedInterval (-47230025117 / 1000000000000) (-47230025116 / 1000000000000))
    | 17 => (orderedInterval (-14767820953 / 1000000000000) (-14767820762 / 1000000000000), orderedInterval (41254961781 / 1000000000000) (41254961972 / 1000000000000))
    | 18 => (orderedInterval (48566882506 / 1000000000000) (48566934749 / 1000000000000), orderedInterval (-33429271700 / 1000000000000) (-33429219457 / 1000000000000))
    | 19 => (orderedInterval (-38997694405 / 1000000000000) (-38997676794 / 1000000000000), orderedInterval (50815902709 / 1000000000000) (50815920320 / 1000000000000))
    | 20 => (orderedInterval (-57236377554 / 1000000000000) (-57236377553 / 1000000000000), orderedInterval (-56808545350 / 1000000000000) (-56808545349 / 1000000000000))
    | 21 => (orderedInterval (26891364345 / 1000000000000) (26891364677 / 1000000000000), orderedInterval (-107176083172 / 1000000000000) (-107176082839 / 1000000000000))
    | 22 => (orderedInterval (-66795188434 / 1000000000000) (-66795188331 / 1000000000000), orderedInterval (4084408120 / 1000000000000) (4084408223 / 1000000000000))
    | 23 => (orderedInterval (10765102657 / 1000000000000) (10765102658 / 1000000000000), orderedInterval (56209041213 / 1000000000000) (56209041214 / 1000000000000))
    | 24 => (orderedInterval (82403201935 / 1000000000000) (82403201936 / 1000000000000), orderedInterval (30530987532 / 1000000000000) (30530987533 / 1000000000000))
    | 25 => (orderedInterval (43654685781 / 1000000000000) (43654685899 / 1000000000000), orderedInterval (1220969922 / 1000000000000) (1220970040 / 1000000000000))
    | _ => (orderedInterval (-33242594371 / 1000000000000) (-33242594370 / 1000000000000), orderedInterval (-41764441633 / 1000000000000) (-41764441632 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-18967096699 / 1000000000000) (-18967096685 / 1000000000000)
      | 1 => orderedInterval (-1502498250 / 1000000000000) (-1502497947 / 1000000000000)
      | 2 => orderedInterval (-131953236 / 1000000000000) (-131953219 / 1000000000000)
      | 3 => orderedInterval (-2534491224 / 1000000000000) (-2534491152 / 1000000000000)
      | 4 => orderedInterval (-5123815524 / 1000000000000) (-5123815438 / 1000000000000)
      | 5 => orderedInterval (1354956696 / 1000000000000) (1354957077 / 1000000000000)
      | 6 => orderedInterval (-7421564812 / 1000000000000) (-7421555416 / 1000000000000)
      | 7 => orderedInterval (193795711 / 1000000000000) (193795741 / 1000000000000)
      | _ => orderedInterval (3180377028 / 1000000000000) (3180377088 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-5712558395 / 1000000000000) (-5712558380 / 1000000000000)
      | 1 => orderedInterval (-5641361087 / 1000000000000) (-5641360624 / 1000000000000)
      | 2 => orderedInterval (1638425828 / 1000000000000) (1638425856 / 1000000000000)
      | 3 => orderedInterval (-22326345519 / 1000000000000) (-22326345371 / 1000000000000)
      | 4 => orderedInterval (1161292096 / 1000000000000) (1161292246 / 1000000000000)
      | 5 => orderedInterval (4806147126 / 1000000000000) (4806147679 / 1000000000000)
      | 6 => orderedInterval (1969855338 / 1000000000000) (1969864788 / 1000000000000)
      | 7 => orderedInterval (-4156118332 / 1000000000000) (-4156118308 / 1000000000000)
      | _ => orderedInterval (9631869607 / 1000000000000) (9631869696 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (18173550709 / 1000000000000) (18173550726 / 1000000000000)
      | 1 => orderedInterval (-3747428626 / 1000000000000) (-3747427902 / 1000000000000)
      | 2 => orderedInterval (-1622281226 / 1000000000000) (-1622281179 / 1000000000000)
      | 3 => orderedInterval (13926879861 / 1000000000000) (13926880179 / 1000000000000)
      | 4 => orderedInterval (13487674443 / 1000000000000) (13487674714 / 1000000000000)
      | 5 => orderedInterval (-1737136413 / 1000000000000) (-1737135608 / 1000000000000)
      | 6 => orderedInterval (7002341461 / 1000000000000) (7002351042 / 1000000000000)
      | 7 => orderedInterval (79725261 / 1000000000000) (79725283 / 1000000000000)
      | _ => orderedInterval (2507281676 / 1000000000000) (2507281813 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (4780426802 / 1000000000000) (4780426822 / 1000000000000)
      | 1 => orderedInterval (11394764918 / 1000000000000) (11394766050 / 1000000000000)
      | 2 => orderedInterval (-6181235680 / 1000000000000) (-6181235602 / 1000000000000)
      | 3 => orderedInterval (131109593199 / 1000000000000) (131109593896 / 1000000000000)
      | 4 => orderedInterval (-3526545411 / 1000000000000) (-3526544907 / 1000000000000)
      | 5 => orderedInterval (-11038325339 / 1000000000000) (-11038324167 / 1000000000000)
      | 6 => orderedInterval (-3588372121 / 1000000000000) (-3588362441 / 1000000000000)
      | 7 => orderedInterval (5450106124 / 1000000000000) (5450106146 / 1000000000000)
      | _ => orderedInterval (-14405401242 / 1000000000000) (-14405401020 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-16798114021 / 1000000000000) (-16798113998 / 1000000000000)
      | 1 => orderedInterval (10688917394 / 1000000000000) (10688919173 / 1000000000000)
      | 2 => orderedInterval (10907830350 / 1000000000000) (10907830487 / 1000000000000)
      | 3 => orderedInterval (-74526152115 / 1000000000000) (-74526150568 / 1000000000000)
      | 4 => orderedInterval (-38645653006 / 1000000000000) (-38645652041 / 1000000000000)
      | 5 => orderedInterval (971689891 / 1000000000000) (971691611 / 1000000000000)
      | 6 => orderedInterval (-7373244059 / 1000000000000) (-7373234208 / 1000000000000)
      | 7 => orderedInterval (-597158613 / 1000000000000) (-597158590 / 1000000000000)
      | _ => orderedInterval (-27454736904 / 1000000000000) (-27454736532 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-30952290310 / 1000000000000) (-30952279951 / 1000000000000)
    | 1 => orderedInterval (-18628793338 / 1000000000000) (-18628782418 / 1000000000000)
    | 2 => orderedInterval (48070607146 / 1000000000000) (48070619068 / 1000000000000)
    | 3 => orderedInterval (113995011250 / 1000000000000) (113995024777 / 1000000000000)
    | _ => orderedInterval (-142826621083 / 1000000000000) (-142826604666 / 1000000000000)

theorem compactCertificate306_stateChecks0 :
    compactCertificate306.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (359 / 2)) (orderedInterval (-55801164524 / 1000000000000) (-55801164523 / 1000000000000), orderedInterval (-20649563104 / 1000000000000) (-20649563103 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (528875550296459 / 4000000000000)) (orderedInterval (60411189255 / 1000000000000) (60411189256 / 1000000000000), orderedInterval (33908969297 / 1000000000000) (33908969298 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (171027486531947 / 800000000000)) (orderedInterval (44096219122 / 1000000000000) (44096219123 / 1000000000000), orderedInterval (32043103059 / 1000000000000) (32043103060 / 1000000000000))) = true
  rfl'

theorem compactCertificate306_stateChecks1 :
    compactCertificate306.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (154324566542113 / 4000000000000)) (orderedInterval (127890281250 / 1000000000000) (127890281334 / 1000000000000), orderedInterval (-13637030531 / 1000000000000) (-13637030447 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (414537493278061 / 4000000000000)) (orderedInterval (-53195064288 / 1000000000000) (-53195064287 / 1000000000000), orderedInterval (-57304031402 / 1000000000000) (-57304031401 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1125549933276537 / 4000000000000)) (orderedInterval (-25703682973 / 1000000000000) (-25703679039 / 1000000000000), orderedInterval (40067581064 / 1000000000000) (40067584997 / 1000000000000))) = true
  rfl'

theorem compactCertificate306_stateChecks2 :
    compactCertificate306.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (829074986556481 / 4000000000000)) (orderedInterval (36058952993 / 1000000000000) (36058952994 / 1000000000000), orderedInterval (41998920102 / 1000000000000) (41998920103 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1420634120595013 / 4000000000000)) (orderedInterval (-34280100623 / 1000000000000) (-34280100622 / 1000000000000), orderedInterval (-24798647446 / 1000000000000) (-24798647445 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1046432663369167 / 4000000000000)) (orderedInterval (-49209175770 / 1000000000000) (-49209175493 / 1000000000000), orderedInterval (3549263105 / 1000000000000) (3549263381 / 1000000000000))) = true
  rfl'

theorem compactCertificate306_stateChecks3 :
    compactCertificate306.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1605496807844641 / 4000000000000)) (orderedInterval (1410696671 / 1000000000000) (1410696672 / 1000000000000), orderedInterval (39799141374 / 1000000000000) (39799141375 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (926934014192089 / 4000000000000)) (orderedInterval (2122487162 / 1000000000000) (2122487164 / 1000000000000), orderedInterval (52366288842 / 1000000000000) (52366288843 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1644860674321901 / 4000000000000)) (orderedInterval (-17171896438 / 1000000000000) (-17171896437 / 1000000000000), orderedInterval (-35380665854 / 1000000000000) (-35380665853 / 1000000000000))) = true
  rfl'

theorem compactCertificate306_stateChecks4 :
    compactCertificate306.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1536842207666369 / 4000000000000)) (orderedInterval (40245421485 / 1000000000000) (40245423070 / 1000000000000), orderedInterval (-6156480465 / 1000000000000) (-6156478881 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1096763116325777 / 4000000000000)) (orderedInterval (-48005567763 / 1000000000000) (-48005567393 / 1000000000000), orderedInterval (4243846740 / 1000000000000) (4243847110 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1243612479834183 / 4000000000000)) (orderedInterval (-28115898805 / 1000000000000) (-28115898804 / 1000000000000), orderedInterval (-35411004762 / 1000000000000) (-35411004761 / 1000000000000))) = true
  rfl'

theorem compactCertificate306_stateChecks5 :
    compactCertificate306.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1036794432567127 / 4000000000000)) (orderedInterval (34452326776 / 1000000000000) (34452357825 / 1000000000000), orderedInterval (-35691524506 / 1000000000000) (-35691493457 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (916039323993667 / 4000000000000)) (orderedInterval (-23332250342 / 1000000000000) (-23332250341 / 1000000000000), orderedInterval (-47230025117 / 1000000000000) (-47230025116 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (265503900441033 / 800000000000)) (orderedInterval (-14767820953 / 1000000000000) (-14767820762 / 1000000000000), orderedInterval (41254961781 / 1000000000000) (41254961972 / 1000000000000))) = true
  rfl'

theorem compactCertificate306_stateChecks6 :
    compactCertificate306.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (734397761324651 / 4000000000000)) (orderedInterval (48566882506 / 1000000000000) (48566934749 / 1000000000000), orderedInterval (-33429271700 / 1000000000000) (-33429219457 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (622557115507411 / 4000000000000)) (orderedInterval (-38997694405 / 1000000000000) (-38997676794 / 1000000000000), orderedInterval (50815902709 / 1000000000000) (50815920320 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (389567336630833 / 4000000000000)) (orderedInterval (-57236377554 / 1000000000000) (-57236377553 / 1000000000000), orderedInterval (-56808545350 / 1000000000000) (-56808545349 / 1000000000000))) = true
  rfl'

theorem compactCertificate306_stateChecks7 :
    compactCertificate306.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (209510609282511 / 4000000000000)) (orderedInterval (26891364345 / 1000000000000) (26891364677 / 1000000000000), orderedInterval (-107176083172 / 1000000000000) (-107176082839 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (568862059820533 / 4000000000000)) (orderedInterval (-66795188434 / 1000000000000) (-66795188331 / 1000000000000), orderedInterval (4084408120 / 1000000000000) (4084408223 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (776732509171541 / 4000000000000)) (orderedInterval (10765102657 / 1000000000000) (10765102658 / 1000000000000), orderedInterval (56209041213 / 1000000000000) (56209041214 / 1000000000000))) = true
  rfl'

theorem compactCertificate306_stateChecks8 :
    compactCertificate306.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (328432663369167 / 4000000000000)) (orderedInterval (82403201935 / 1000000000000) (82403201936 / 1000000000000), orderedInterval (30530987532 / 1000000000000) (30530987533 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1335060542559407 / 4000000000000)) (orderedInterval (43654685781 / 1000000000000) (43654685899 / 1000000000000), orderedInterval (1220969922 / 1000000000000) (1220970040 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (891758570298913 / 4000000000000)) (orderedInterval (-33242594371 / 1000000000000) (-33242594370 / 1000000000000), orderedInterval (-41764441633 / 1000000000000) (-41764441632 / 1000000000000))) = true
  rfl'

theorem compactCertificate306_states : ∀ j,
    BesselStateValid (compactCertificate306.point j) (compactCertificate306.state j) :=
  compactCertificate306.statesValid_of_checks3 compactCertificate306_stateChecks0
    compactCertificate306_stateChecks1 compactCertificate306_stateChecks2
    compactCertificate306_stateChecks3 compactCertificate306_stateChecks4
    compactCertificate306_stateChecks5 compactCertificate306_stateChecks6
    compactCertificate306_stateChecks7 compactCertificate306_stateChecks8

theorem compactCertificate306_chunkChecks0_0 :
    compactCertificate306.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (359 / 2) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55801164524 / 1000000000000) (-55801164523 / 1000000000000), orderedInterval (-20649563104 / 1000000000000) (-20649563103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (528875550296459 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60411189255 / 1000000000000) (60411189256 / 1000000000000), orderedInterval (33908969297 / 1000000000000) (33908969298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (171027486531947 / 800000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (44096219122 / 1000000000000) (44096219123 / 1000000000000), orderedInterval (32043103059 / 1000000000000) (32043103060 / 1000000000000)))) (orderedInterval (-18967096699 / 1000000000000) (-18967096685 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (154324566542113 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (127890281250 / 1000000000000) (127890281334 / 1000000000000), orderedInterval (-13637030531 / 1000000000000) (-13637030447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (414537493278061 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53195064288 / 1000000000000) (-53195064287 / 1000000000000), orderedInterval (-57304031402 / 1000000000000) (-57304031401 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1125549933276537 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25703682973 / 1000000000000) (-25703679039 / 1000000000000), orderedInterval (40067581064 / 1000000000000) (40067584997 / 1000000000000)))) (orderedInterval (-1502498250 / 1000000000000) (-1502497947 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (829074986556481 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36058952993 / 1000000000000) (36058952994 / 1000000000000), orderedInterval (41998920102 / 1000000000000) (41998920103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1420634120595013 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34280100623 / 1000000000000) (-34280100622 / 1000000000000), orderedInterval (-24798647446 / 1000000000000) (-24798647445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1046432663369167 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-49209175770 / 1000000000000) (-49209175493 / 1000000000000), orderedInterval (3549263105 / 1000000000000) (3549263381 / 1000000000000)))) (orderedInterval (-131953236 / 1000000000000) (-131953219 / 1000000000000))) = true
  rfl'

theorem compactCertificate306_chunkChecks0_1 :
    compactCertificate306.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1605496807844641 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1410696671 / 1000000000000) (1410696672 / 1000000000000), orderedInterval (39799141374 / 1000000000000) (39799141375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (926934014192089 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (2122487162 / 1000000000000) (2122487164 / 1000000000000), orderedInterval (52366288842 / 1000000000000) (52366288843 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1644860674321901 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17171896438 / 1000000000000) (-17171896437 / 1000000000000), orderedInterval (-35380665854 / 1000000000000) (-35380665853 / 1000000000000)))) (orderedInterval (-2534491224 / 1000000000000) (-2534491152 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1536842207666369 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (40245421485 / 1000000000000) (40245423070 / 1000000000000), orderedInterval (-6156480465 / 1000000000000) (-6156478881 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1096763116325777 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-48005567763 / 1000000000000) (-48005567393 / 1000000000000), orderedInterval (4243846740 / 1000000000000) (4243847110 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1243612479834183 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28115898805 / 1000000000000) (-28115898804 / 1000000000000), orderedInterval (-35411004762 / 1000000000000) (-35411004761 / 1000000000000)))) (orderedInterval (-5123815524 / 1000000000000) (-5123815438 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1036794432567127 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34452326776 / 1000000000000) (34452357825 / 1000000000000), orderedInterval (-35691524506 / 1000000000000) (-35691493457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (916039323993667 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-23332250342 / 1000000000000) (-23332250341 / 1000000000000), orderedInterval (-47230025117 / 1000000000000) (-47230025116 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (265503900441033 / 800000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-14767820953 / 1000000000000) (-14767820762 / 1000000000000), orderedInterval (41254961781 / 1000000000000) (41254961972 / 1000000000000)))) (orderedInterval (1354956696 / 1000000000000) (1354957077 / 1000000000000))) = true
  rfl'

theorem compactCertificate306_chunkChecks0_2 :
    compactCertificate306.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (734397761324651 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48566882506 / 1000000000000) (48566934749 / 1000000000000), orderedInterval (-33429271700 / 1000000000000) (-33429219457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (622557115507411 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38997694405 / 1000000000000) (-38997676794 / 1000000000000), orderedInterval (50815902709 / 1000000000000) (50815920320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (389567336630833 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57236377554 / 1000000000000) (-57236377553 / 1000000000000), orderedInterval (-56808545350 / 1000000000000) (-56808545349 / 1000000000000)))) (orderedInterval (-7421564812 / 1000000000000) (-7421555416 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (209510609282511 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (26891364345 / 1000000000000) (26891364677 / 1000000000000), orderedInterval (-107176083172 / 1000000000000) (-107176082839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (568862059820533 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-66795188434 / 1000000000000) (-66795188331 / 1000000000000), orderedInterval (4084408120 / 1000000000000) (4084408223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (776732509171541 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (10765102657 / 1000000000000) (10765102658 / 1000000000000), orderedInterval (56209041213 / 1000000000000) (56209041214 / 1000000000000)))) (orderedInterval (193795711 / 1000000000000) (193795741 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (328432663369167 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82403201935 / 1000000000000) (82403201936 / 1000000000000), orderedInterval (30530987532 / 1000000000000) (30530987533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1335060542559407 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (43654685781 / 1000000000000) (43654685899 / 1000000000000), orderedInterval (1220969922 / 1000000000000) (1220970040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (891758570298913 / 4000000000000) 0 (IntervalRat.scale (359 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33242594371 / 1000000000000) (-33242594370 / 1000000000000), orderedInterval (-41764441633 / 1000000000000) (-41764441632 / 1000000000000)))) (orderedInterval (3180377028 / 1000000000000) (3180377088 / 1000000000000))) = true
  rfl'

theorem compactCertificate306_chunkChecks0 :
    compactCertificate306.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate306.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate306_chunkChecks0_0
    compactCertificate306_chunkChecks0_1 compactCertificate306_chunkChecks0_2

theorem compactCertificate306_chunkChecks1_0 :
    compactCertificate306.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (359 / 2) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55801164524 / 1000000000000) (-55801164523 / 1000000000000), orderedInterval (-20649563104 / 1000000000000) (-20649563103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (528875550296459 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60411189255 / 1000000000000) (60411189256 / 1000000000000), orderedInterval (33908969297 / 1000000000000) (33908969298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (171027486531947 / 800000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (44096219122 / 1000000000000) (44096219123 / 1000000000000), orderedInterval (32043103059 / 1000000000000) (32043103060 / 1000000000000)))) (orderedInterval (-5712558395 / 1000000000000) (-5712558380 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (154324566542113 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (127890281250 / 1000000000000) (127890281334 / 1000000000000), orderedInterval (-13637030531 / 1000000000000) (-13637030447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (414537493278061 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53195064288 / 1000000000000) (-53195064287 / 1000000000000), orderedInterval (-57304031402 / 1000000000000) (-57304031401 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1125549933276537 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25703682973 / 1000000000000) (-25703679039 / 1000000000000), orderedInterval (40067581064 / 1000000000000) (40067584997 / 1000000000000)))) (orderedInterval (-5641361087 / 1000000000000) (-5641360624 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (829074986556481 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36058952993 / 1000000000000) (36058952994 / 1000000000000), orderedInterval (41998920102 / 1000000000000) (41998920103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1420634120595013 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34280100623 / 1000000000000) (-34280100622 / 1000000000000), orderedInterval (-24798647446 / 1000000000000) (-24798647445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1046432663369167 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-49209175770 / 1000000000000) (-49209175493 / 1000000000000), orderedInterval (3549263105 / 1000000000000) (3549263381 / 1000000000000)))) (orderedInterval (1638425828 / 1000000000000) (1638425856 / 1000000000000))) = true
  rfl'

theorem compactCertificate306_chunkChecks1_1 :
    compactCertificate306.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1605496807844641 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1410696671 / 1000000000000) (1410696672 / 1000000000000), orderedInterval (39799141374 / 1000000000000) (39799141375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (926934014192089 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (2122487162 / 1000000000000) (2122487164 / 1000000000000), orderedInterval (52366288842 / 1000000000000) (52366288843 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1644860674321901 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17171896438 / 1000000000000) (-17171896437 / 1000000000000), orderedInterval (-35380665854 / 1000000000000) (-35380665853 / 1000000000000)))) (orderedInterval (-22326345519 / 1000000000000) (-22326345371 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1536842207666369 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (40245421485 / 1000000000000) (40245423070 / 1000000000000), orderedInterval (-6156480465 / 1000000000000) (-6156478881 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1096763116325777 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-48005567763 / 1000000000000) (-48005567393 / 1000000000000), orderedInterval (4243846740 / 1000000000000) (4243847110 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1243612479834183 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28115898805 / 1000000000000) (-28115898804 / 1000000000000), orderedInterval (-35411004762 / 1000000000000) (-35411004761 / 1000000000000)))) (orderedInterval (1161292096 / 1000000000000) (1161292246 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1036794432567127 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34452326776 / 1000000000000) (34452357825 / 1000000000000), orderedInterval (-35691524506 / 1000000000000) (-35691493457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (916039323993667 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-23332250342 / 1000000000000) (-23332250341 / 1000000000000), orderedInterval (-47230025117 / 1000000000000) (-47230025116 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (265503900441033 / 800000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-14767820953 / 1000000000000) (-14767820762 / 1000000000000), orderedInterval (41254961781 / 1000000000000) (41254961972 / 1000000000000)))) (orderedInterval (4806147126 / 1000000000000) (4806147679 / 1000000000000))) = true
  rfl'

theorem compactCertificate306_chunkChecks1_2 :
    compactCertificate306.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (734397761324651 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48566882506 / 1000000000000) (48566934749 / 1000000000000), orderedInterval (-33429271700 / 1000000000000) (-33429219457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (622557115507411 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38997694405 / 1000000000000) (-38997676794 / 1000000000000), orderedInterval (50815902709 / 1000000000000) (50815920320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (389567336630833 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57236377554 / 1000000000000) (-57236377553 / 1000000000000), orderedInterval (-56808545350 / 1000000000000) (-56808545349 / 1000000000000)))) (orderedInterval (1969855338 / 1000000000000) (1969864788 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (209510609282511 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (26891364345 / 1000000000000) (26891364677 / 1000000000000), orderedInterval (-107176083172 / 1000000000000) (-107176082839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (568862059820533 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-66795188434 / 1000000000000) (-66795188331 / 1000000000000), orderedInterval (4084408120 / 1000000000000) (4084408223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (776732509171541 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (10765102657 / 1000000000000) (10765102658 / 1000000000000), orderedInterval (56209041213 / 1000000000000) (56209041214 / 1000000000000)))) (orderedInterval (-4156118332 / 1000000000000) (-4156118308 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (328432663369167 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82403201935 / 1000000000000) (82403201936 / 1000000000000), orderedInterval (30530987532 / 1000000000000) (30530987533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1335060542559407 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (43654685781 / 1000000000000) (43654685899 / 1000000000000), orderedInterval (1220969922 / 1000000000000) (1220970040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (891758570298913 / 4000000000000) 1 (IntervalRat.scale (359 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33242594371 / 1000000000000) (-33242594370 / 1000000000000), orderedInterval (-41764441633 / 1000000000000) (-41764441632 / 1000000000000)))) (orderedInterval (9631869607 / 1000000000000) (9631869696 / 1000000000000))) = true
  rfl'

theorem compactCertificate306_chunkChecks1 :
    compactCertificate306.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate306.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate306_chunkChecks1_0
    compactCertificate306_chunkChecks1_1 compactCertificate306_chunkChecks1_2

theorem compactCertificate306_chunkChecks2_0 :
    compactCertificate306.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (359 / 2) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55801164524 / 1000000000000) (-55801164523 / 1000000000000), orderedInterval (-20649563104 / 1000000000000) (-20649563103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (528875550296459 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60411189255 / 1000000000000) (60411189256 / 1000000000000), orderedInterval (33908969297 / 1000000000000) (33908969298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (171027486531947 / 800000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (44096219122 / 1000000000000) (44096219123 / 1000000000000), orderedInterval (32043103059 / 1000000000000) (32043103060 / 1000000000000)))) (orderedInterval (18173550709 / 1000000000000) (18173550726 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (154324566542113 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (127890281250 / 1000000000000) (127890281334 / 1000000000000), orderedInterval (-13637030531 / 1000000000000) (-13637030447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (414537493278061 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53195064288 / 1000000000000) (-53195064287 / 1000000000000), orderedInterval (-57304031402 / 1000000000000) (-57304031401 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1125549933276537 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25703682973 / 1000000000000) (-25703679039 / 1000000000000), orderedInterval (40067581064 / 1000000000000) (40067584997 / 1000000000000)))) (orderedInterval (-3747428626 / 1000000000000) (-3747427902 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (829074986556481 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36058952993 / 1000000000000) (36058952994 / 1000000000000), orderedInterval (41998920102 / 1000000000000) (41998920103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1420634120595013 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34280100623 / 1000000000000) (-34280100622 / 1000000000000), orderedInterval (-24798647446 / 1000000000000) (-24798647445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1046432663369167 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-49209175770 / 1000000000000) (-49209175493 / 1000000000000), orderedInterval (3549263105 / 1000000000000) (3549263381 / 1000000000000)))) (orderedInterval (-1622281226 / 1000000000000) (-1622281179 / 1000000000000))) = true
  rfl'

theorem compactCertificate306_chunkChecks2_1 :
    compactCertificate306.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1605496807844641 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1410696671 / 1000000000000) (1410696672 / 1000000000000), orderedInterval (39799141374 / 1000000000000) (39799141375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (926934014192089 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (2122487162 / 1000000000000) (2122487164 / 1000000000000), orderedInterval (52366288842 / 1000000000000) (52366288843 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1644860674321901 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17171896438 / 1000000000000) (-17171896437 / 1000000000000), orderedInterval (-35380665854 / 1000000000000) (-35380665853 / 1000000000000)))) (orderedInterval (13926879861 / 1000000000000) (13926880179 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1536842207666369 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (40245421485 / 1000000000000) (40245423070 / 1000000000000), orderedInterval (-6156480465 / 1000000000000) (-6156478881 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1096763116325777 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-48005567763 / 1000000000000) (-48005567393 / 1000000000000), orderedInterval (4243846740 / 1000000000000) (4243847110 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1243612479834183 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28115898805 / 1000000000000) (-28115898804 / 1000000000000), orderedInterval (-35411004762 / 1000000000000) (-35411004761 / 1000000000000)))) (orderedInterval (13487674443 / 1000000000000) (13487674714 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1036794432567127 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34452326776 / 1000000000000) (34452357825 / 1000000000000), orderedInterval (-35691524506 / 1000000000000) (-35691493457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (916039323993667 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-23332250342 / 1000000000000) (-23332250341 / 1000000000000), orderedInterval (-47230025117 / 1000000000000) (-47230025116 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (265503900441033 / 800000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-14767820953 / 1000000000000) (-14767820762 / 1000000000000), orderedInterval (41254961781 / 1000000000000) (41254961972 / 1000000000000)))) (orderedInterval (-1737136413 / 1000000000000) (-1737135608 / 1000000000000))) = true
  rfl'

theorem compactCertificate306_chunkChecks2_2 :
    compactCertificate306.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (734397761324651 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48566882506 / 1000000000000) (48566934749 / 1000000000000), orderedInterval (-33429271700 / 1000000000000) (-33429219457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (622557115507411 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38997694405 / 1000000000000) (-38997676794 / 1000000000000), orderedInterval (50815902709 / 1000000000000) (50815920320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (389567336630833 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57236377554 / 1000000000000) (-57236377553 / 1000000000000), orderedInterval (-56808545350 / 1000000000000) (-56808545349 / 1000000000000)))) (orderedInterval (7002341461 / 1000000000000) (7002351042 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (209510609282511 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (26891364345 / 1000000000000) (26891364677 / 1000000000000), orderedInterval (-107176083172 / 1000000000000) (-107176082839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (568862059820533 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-66795188434 / 1000000000000) (-66795188331 / 1000000000000), orderedInterval (4084408120 / 1000000000000) (4084408223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (776732509171541 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (10765102657 / 1000000000000) (10765102658 / 1000000000000), orderedInterval (56209041213 / 1000000000000) (56209041214 / 1000000000000)))) (orderedInterval (79725261 / 1000000000000) (79725283 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (328432663369167 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82403201935 / 1000000000000) (82403201936 / 1000000000000), orderedInterval (30530987532 / 1000000000000) (30530987533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1335060542559407 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (43654685781 / 1000000000000) (43654685899 / 1000000000000), orderedInterval (1220969922 / 1000000000000) (1220970040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (891758570298913 / 4000000000000) 2 (IntervalRat.scale (359 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33242594371 / 1000000000000) (-33242594370 / 1000000000000), orderedInterval (-41764441633 / 1000000000000) (-41764441632 / 1000000000000)))) (orderedInterval (2507281676 / 1000000000000) (2507281813 / 1000000000000))) = true
  rfl'

theorem compactCertificate306_chunkChecks2 :
    compactCertificate306.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate306.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate306_chunkChecks2_0
    compactCertificate306_chunkChecks2_1 compactCertificate306_chunkChecks2_2

theorem compactCertificate306_chunkChecks3_0 :
    compactCertificate306.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (359 / 2) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55801164524 / 1000000000000) (-55801164523 / 1000000000000), orderedInterval (-20649563104 / 1000000000000) (-20649563103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (528875550296459 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60411189255 / 1000000000000) (60411189256 / 1000000000000), orderedInterval (33908969297 / 1000000000000) (33908969298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (171027486531947 / 800000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (44096219122 / 1000000000000) (44096219123 / 1000000000000), orderedInterval (32043103059 / 1000000000000) (32043103060 / 1000000000000)))) (orderedInterval (4780426802 / 1000000000000) (4780426822 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (154324566542113 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (127890281250 / 1000000000000) (127890281334 / 1000000000000), orderedInterval (-13637030531 / 1000000000000) (-13637030447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (414537493278061 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53195064288 / 1000000000000) (-53195064287 / 1000000000000), orderedInterval (-57304031402 / 1000000000000) (-57304031401 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1125549933276537 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25703682973 / 1000000000000) (-25703679039 / 1000000000000), orderedInterval (40067581064 / 1000000000000) (40067584997 / 1000000000000)))) (orderedInterval (11394764918 / 1000000000000) (11394766050 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (829074986556481 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36058952993 / 1000000000000) (36058952994 / 1000000000000), orderedInterval (41998920102 / 1000000000000) (41998920103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1420634120595013 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34280100623 / 1000000000000) (-34280100622 / 1000000000000), orderedInterval (-24798647446 / 1000000000000) (-24798647445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1046432663369167 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-49209175770 / 1000000000000) (-49209175493 / 1000000000000), orderedInterval (3549263105 / 1000000000000) (3549263381 / 1000000000000)))) (orderedInterval (-6181235680 / 1000000000000) (-6181235602 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate306_chunkChecks3_1 :
    compactCertificate306.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1605496807844641 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1410696671 / 1000000000000) (1410696672 / 1000000000000), orderedInterval (39799141374 / 1000000000000) (39799141375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (926934014192089 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (2122487162 / 1000000000000) (2122487164 / 1000000000000), orderedInterval (52366288842 / 1000000000000) (52366288843 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1644860674321901 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17171896438 / 1000000000000) (-17171896437 / 1000000000000), orderedInterval (-35380665854 / 1000000000000) (-35380665853 / 1000000000000)))) (orderedInterval (131109593199 / 1000000000000) (131109593896 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1536842207666369 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (40245421485 / 1000000000000) (40245423070 / 1000000000000), orderedInterval (-6156480465 / 1000000000000) (-6156478881 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1096763116325777 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-48005567763 / 1000000000000) (-48005567393 / 1000000000000), orderedInterval (4243846740 / 1000000000000) (4243847110 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1243612479834183 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28115898805 / 1000000000000) (-28115898804 / 1000000000000), orderedInterval (-35411004762 / 1000000000000) (-35411004761 / 1000000000000)))) (orderedInterval (-3526545411 / 1000000000000) (-3526544907 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1036794432567127 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34452326776 / 1000000000000) (34452357825 / 1000000000000), orderedInterval (-35691524506 / 1000000000000) (-35691493457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (916039323993667 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-23332250342 / 1000000000000) (-23332250341 / 1000000000000), orderedInterval (-47230025117 / 1000000000000) (-47230025116 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (265503900441033 / 800000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-14767820953 / 1000000000000) (-14767820762 / 1000000000000), orderedInterval (41254961781 / 1000000000000) (41254961972 / 1000000000000)))) (orderedInterval (-11038325339 / 1000000000000) (-11038324167 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate306_chunkChecks3_2 :
    compactCertificate306.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (734397761324651 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48566882506 / 1000000000000) (48566934749 / 1000000000000), orderedInterval (-33429271700 / 1000000000000) (-33429219457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (622557115507411 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38997694405 / 1000000000000) (-38997676794 / 1000000000000), orderedInterval (50815902709 / 1000000000000) (50815920320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (389567336630833 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57236377554 / 1000000000000) (-57236377553 / 1000000000000), orderedInterval (-56808545350 / 1000000000000) (-56808545349 / 1000000000000)))) (orderedInterval (-3588372121 / 1000000000000) (-3588362441 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (209510609282511 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (26891364345 / 1000000000000) (26891364677 / 1000000000000), orderedInterval (-107176083172 / 1000000000000) (-107176082839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (568862059820533 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-66795188434 / 1000000000000) (-66795188331 / 1000000000000), orderedInterval (4084408120 / 1000000000000) (4084408223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (776732509171541 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (10765102657 / 1000000000000) (10765102658 / 1000000000000), orderedInterval (56209041213 / 1000000000000) (56209041214 / 1000000000000)))) (orderedInterval (5450106124 / 1000000000000) (5450106146 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (328432663369167 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82403201935 / 1000000000000) (82403201936 / 1000000000000), orderedInterval (30530987532 / 1000000000000) (30530987533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1335060542559407 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (43654685781 / 1000000000000) (43654685899 / 1000000000000), orderedInterval (1220969922 / 1000000000000) (1220970040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (891758570298913 / 4000000000000) 3 (IntervalRat.scale (359 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33242594371 / 1000000000000) (-33242594370 / 1000000000000), orderedInterval (-41764441633 / 1000000000000) (-41764441632 / 1000000000000)))) (orderedInterval (-14405401242 / 1000000000000) (-14405401020 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate306_chunkChecks3 :
    compactCertificate306.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate306.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate306_chunkChecks3_0
    compactCertificate306_chunkChecks3_1 compactCertificate306_chunkChecks3_2

theorem compactCertificate306_chunkChecks4_0 :
    compactCertificate306.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (359 / 2) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55801164524 / 1000000000000) (-55801164523 / 1000000000000), orderedInterval (-20649563104 / 1000000000000) (-20649563103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (528875550296459 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60411189255 / 1000000000000) (60411189256 / 1000000000000), orderedInterval (33908969297 / 1000000000000) (33908969298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (171027486531947 / 800000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (44096219122 / 1000000000000) (44096219123 / 1000000000000), orderedInterval (32043103059 / 1000000000000) (32043103060 / 1000000000000)))) (orderedInterval (-16798114021 / 1000000000000) (-16798113998 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (154324566542113 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (127890281250 / 1000000000000) (127890281334 / 1000000000000), orderedInterval (-13637030531 / 1000000000000) (-13637030447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (414537493278061 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53195064288 / 1000000000000) (-53195064287 / 1000000000000), orderedInterval (-57304031402 / 1000000000000) (-57304031401 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1125549933276537 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25703682973 / 1000000000000) (-25703679039 / 1000000000000), orderedInterval (40067581064 / 1000000000000) (40067584997 / 1000000000000)))) (orderedInterval (10688917394 / 1000000000000) (10688919173 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (829074986556481 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36058952993 / 1000000000000) (36058952994 / 1000000000000), orderedInterval (41998920102 / 1000000000000) (41998920103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1420634120595013 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34280100623 / 1000000000000) (-34280100622 / 1000000000000), orderedInterval (-24798647446 / 1000000000000) (-24798647445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1046432663369167 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-49209175770 / 1000000000000) (-49209175493 / 1000000000000), orderedInterval (3549263105 / 1000000000000) (3549263381 / 1000000000000)))) (orderedInterval (10907830350 / 1000000000000) (10907830487 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate306_chunkChecks4_1 :
    compactCertificate306.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1605496807844641 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1410696671 / 1000000000000) (1410696672 / 1000000000000), orderedInterval (39799141374 / 1000000000000) (39799141375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (926934014192089 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (2122487162 / 1000000000000) (2122487164 / 1000000000000), orderedInterval (52366288842 / 1000000000000) (52366288843 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1644860674321901 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17171896438 / 1000000000000) (-17171896437 / 1000000000000), orderedInterval (-35380665854 / 1000000000000) (-35380665853 / 1000000000000)))) (orderedInterval (-74526152115 / 1000000000000) (-74526150568 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1536842207666369 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (40245421485 / 1000000000000) (40245423070 / 1000000000000), orderedInterval (-6156480465 / 1000000000000) (-6156478881 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1096763116325777 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-48005567763 / 1000000000000) (-48005567393 / 1000000000000), orderedInterval (4243846740 / 1000000000000) (4243847110 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1243612479834183 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28115898805 / 1000000000000) (-28115898804 / 1000000000000), orderedInterval (-35411004762 / 1000000000000) (-35411004761 / 1000000000000)))) (orderedInterval (-38645653006 / 1000000000000) (-38645652041 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1036794432567127 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34452326776 / 1000000000000) (34452357825 / 1000000000000), orderedInterval (-35691524506 / 1000000000000) (-35691493457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (916039323993667 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-23332250342 / 1000000000000) (-23332250341 / 1000000000000), orderedInterval (-47230025117 / 1000000000000) (-47230025116 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (265503900441033 / 800000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-14767820953 / 1000000000000) (-14767820762 / 1000000000000), orderedInterval (41254961781 / 1000000000000) (41254961972 / 1000000000000)))) (orderedInterval (971689891 / 1000000000000) (971691611 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate306_chunkChecks4_2 :
    compactCertificate306.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (734397761324651 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48566882506 / 1000000000000) (48566934749 / 1000000000000), orderedInterval (-33429271700 / 1000000000000) (-33429219457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (622557115507411 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-38997694405 / 1000000000000) (-38997676794 / 1000000000000), orderedInterval (50815902709 / 1000000000000) (50815920320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (389567336630833 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57236377554 / 1000000000000) (-57236377553 / 1000000000000), orderedInterval (-56808545350 / 1000000000000) (-56808545349 / 1000000000000)))) (orderedInterval (-7373244059 / 1000000000000) (-7373234208 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (209510609282511 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (26891364345 / 1000000000000) (26891364677 / 1000000000000), orderedInterval (-107176083172 / 1000000000000) (-107176082839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (568862059820533 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-66795188434 / 1000000000000) (-66795188331 / 1000000000000), orderedInterval (4084408120 / 1000000000000) (4084408223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (776732509171541 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (10765102657 / 1000000000000) (10765102658 / 1000000000000), orderedInterval (56209041213 / 1000000000000) (56209041214 / 1000000000000)))) (orderedInterval (-597158613 / 1000000000000) (-597158590 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (328432663369167 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82403201935 / 1000000000000) (82403201936 / 1000000000000), orderedInterval (30530987532 / 1000000000000) (30530987533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1335060542559407 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (43654685781 / 1000000000000) (43654685899 / 1000000000000), orderedInterval (1220969922 / 1000000000000) (1220970040 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (891758570298913 / 4000000000000) 4 (IntervalRat.scale (359 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-33242594371 / 1000000000000) (-33242594370 / 1000000000000), orderedInterval (-41764441633 / 1000000000000) (-41764441632 / 1000000000000)))) (orderedInterval (-27454736904 / 1000000000000) (-27454736532 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate306_chunkChecks4 :
    compactCertificate306.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate306.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate306_chunkChecks4_0
    compactCertificate306_chunkChecks4_1 compactCertificate306_chunkChecks4_2

theorem compactCertificate306_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate306.chunkCheck r b = true :=
  compactCertificate306.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate306_chunkChecks0
    · exact compactCertificate306_chunkChecks1
    · exact compactCertificate306_chunkChecks2
    · exact compactCertificate306_chunkChecks3
    · exact compactCertificate306_chunkChecks4)

theorem compactCertificate306_coefficient0 :
    compactCertificate306.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate306_coefficient1 :
    compactCertificate306.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate306_coefficient2 :
    compactCertificate306.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate306_coefficient3 :
    compactCertificate306.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate306_coefficient4 :
    compactCertificate306.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate306_coefficients : ∀ r : Fin 5,
    compactCertificate306.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate306_coefficient0
  · exact compactCertificate306_coefficient1
  · exact compactCertificate306_coefficient2
  · exact compactCertificate306_coefficient3
  · exact compactCertificate306_coefficient4

theorem compactCertificate306_lower : (1 : ℚ) ≤ compactCertificate306.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate306, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate306_proves {t : ℝ} (ht : t ∈ compactCertificate306.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate306.proves compactCertificate306_states compactCertificate306_chunks
    compactCertificate306_coefficients compactCertificate306_lower ht

end Erdos232
