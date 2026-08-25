/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate396 : CompactCertificate where
  left := 267
  right := 268
  center := 535 / 2
  grid := fun i =>
    match i.val with
    | 0 => 85
    | 1 => 63
    | 2 => 101
    | 3 => 18
    | 4 => 49
    | 5 => 134
    | 6 => 98
    | 7 => 169
    | 8 => 124
    | 9 => 190
    | 10 => 110
    | 11 => 195
    | 12 => 182
    | 13 => 130
    | 14 => 148
    | 15 => 123
    | 16 => 109
    | 17 => 158
    | 18 => 87
    | 19 => 74
    | 20 => 46
    | 21 => 25
    | 22 => 67
    | 23 => 92
    | 24 => 39
    | 25 => 158
    | _ => 106
  point := fun i =>
    match i.val with
    | 0 => 535 / 2
    | 1 => 157631431425407 / 800000000000
    | 2 => 50974766180831 / 160000000000
    | 3 => 45996458551549 / 800000000000
    | 4 => 123552957606553 / 800000000000
    | 5 => 335470314374901 / 800000000000
    | 6 => 247105915213213 / 800000000000
    | 7 => 423420197503249 / 800000000000
    | 8 => 311889401059891 / 800000000000
    | 9 => 478518547184893 / 800000000000
    | 10 => 276272812029397 / 800000000000
    | 11 => 490250953070873 / 800000000000
    | 12 => 458056034039837 / 800000000000
    | 13 => 326890399573421 / 800000000000
    | 14 => 370658872819659 / 800000000000
    | 15 => 309016725026971 / 800000000000
    | 16 => 273025648098391 / 800000000000
    | 17 => 79133474504709 / 160000000000
    | 18 => 218887355046623 / 800000000000
    | 19 => 185553234984103 / 800000000000
    | 20 => 116110598940109 / 800000000000
    | 21 => 62444666276403 / 800000000000
    | 22 => 169549416158209 / 800000000000
    | 23 => 231505232538593 / 800000000000
    | 24 => 97889401059891 / 800000000000
    | 25 => 397914980651411 / 800000000000
    | _ => 265788766077949 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-46288461462 / 1000000000000) (-46288461461 / 1000000000000), orderedInterval (-15316791363 / 1000000000000) (-15316791361 / 1000000000000))
    | 1 => (orderedInterval (5464448594 / 1000000000000) (5464448608 / 1000000000000), orderedInterval (-56591937062 / 1000000000000) (-56591937048 / 1000000000000))
    | 2 => (orderedInterval (-39107786207 / 1000000000000) (-39107745144 / 1000000000000), orderedInterval (21713340427 / 1000000000000) (21713381489 / 1000000000000))
    | 3 => (orderedInterval (103891115903 / 1000000000000) (103891116137 / 1000000000000), orderedInterval (-17598889023 / 1000000000000) (-17598888789 / 1000000000000))
    | 4 => (orderedInterval (-61648517185 / 1000000000000) (-61648517183 / 1000000000000), orderedInterval (-17731598630 / 1000000000000) (-17731598628 / 1000000000000))
    | 5 => (orderedInterval (-29283384854 / 1000000000000) (-29283353601 / 1000000000000), orderedInterval (25737794355 / 1000000000000) (25737825608 / 1000000000000))
    | 6 => (orderedInterval (44299382581 / 1000000000000) (44299384854 / 1000000000000), orderedInterval (-10001702842 / 1000000000000) (-10001700569 / 1000000000000))
    | 7 => (orderedInterval (26480157481 / 1000000000000) (26480179592 / 1000000000000), orderedInterval (-22421783894 / 1000000000000) (-22421761783 / 1000000000000))
    | 8 => (orderedInterval (35815894483 / 1000000000000) (35815894484 / 1000000000000), orderedInterval (18666579861 / 1000000000000) (18666579862 / 1000000000000))
    | 9 => (orderedInterval (29233055425 / 1000000000000) (29233149711 / 1000000000000), orderedInterval (-14506997472 / 1000000000000) (-14506903185 / 1000000000000))
    | 10 => (orderedInterval (22473244426 / 1000000000000) (22473244427 / 1000000000000), orderedInterval (36551703472 / 1000000000000) (36551703473 / 1000000000000))
    | 11 => (orderedInterval (-26916293340 / 1000000000000) (-26916293339 / 1000000000000), orderedInterval (-17708244413 / 1000000000000) (-17708244412 / 1000000000000))
    | 12 => (orderedInterval (33341075589 / 1000000000000) (33341076575 / 1000000000000), orderedInterval (-514700333 / 1000000000000) (-514699347 / 1000000000000))
    | 13 => (orderedInterval (33021865050 / 1000000000000) (33021865051 / 1000000000000), orderedInterval (21582675890 / 1000000000000) (21582675891 / 1000000000000))
    | 14 => (orderedInterval (-27774701125 / 1000000000000) (-27774676469 / 1000000000000), orderedInterval (24577770044 / 1000000000000) (24577794700 / 1000000000000))
    | 15 => (orderedInterval (-24247089726 / 1000000000000) (-24247089725 / 1000000000000), orderedInterval (-32529270551 / 1000000000000) (-32529270550 / 1000000000000))
    | 16 => (orderedInterval (15477427077 / 1000000000000) (15477427318 / 1000000000000), orderedInterval (-40344232142 / 1000000000000) (-40344231900 / 1000000000000))
    | 17 => (orderedInterval (-30233836417 / 1000000000000) (-30233751490 / 1000000000000), orderedInterval (19346294709 / 1000000000000) (19346379636 / 1000000000000))
    | 18 => (orderedInterval (-42441381143 / 1000000000000) (-42441381142 / 1000000000000), orderedInterval (-22845694334 / 1000000000000) (-22845694333 / 1000000000000))
    | 19 => (orderedInterval (12887759461 / 1000000000000) (12887759462 / 1000000000000), orderedInterval (50752662723 / 1000000000000) (50752662724 / 1000000000000))
    | 20 => (orderedInterval (65369538322 / 1000000000000) (65369538326 / 1000000000000), orderedInterval (10409554578 / 1000000000000) (10409554582 / 1000000000000))
    | 21 => (orderedInterval (-26672150132 / 1000000000000) (-26672150131 / 1000000000000), orderedInterval (-86111761652 / 1000000000000) (-86111761651 / 1000000000000))
    | 22 => (orderedInterval (-43159906704 / 1000000000000) (-43159805389 / 1000000000000), orderedInterval (33881112176 / 1000000000000) (33881213491 / 1000000000000))
    | 23 => (orderedInterval (42617662463 / 1000000000000) (42617662464 / 1000000000000), orderedInterval (19513730739 / 1000000000000) (19513730740 / 1000000000000))
    | 24 => (orderedInterval (-42145346621 / 1000000000000) (-42145346620 / 1000000000000), orderedInterval (-58364538180 / 1000000000000) (-58364538179 / 1000000000000))
    | 25 => (orderedInterval (34780503527 / 1000000000000) (34780510988 / 1000000000000), orderedInterval (-8415114053 / 1000000000000) (-8415106592 / 1000000000000))
    | _ => (orderedInterval (532202161 / 1000000000000) (532202163 / 1000000000000), orderedInterval (43770039979 / 1000000000000) (43770039981 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-20591097131 / 1000000000000) (-20591094701 / 1000000000000)
      | 1 => orderedInterval (-1296296874 / 1000000000000) (-1296294617 / 1000000000000)
      | 2 => orderedInterval (48844811 / 1000000000000) (48845509 / 1000000000000)
      | 3 => orderedInterval (-7355605005 / 1000000000000) (-7355588145 / 1000000000000)
      | 4 => orderedInterval (2661288722 / 1000000000000) (2661288897 / 1000000000000)
      | 5 => orderedInterval (-1939824774 / 1000000000000) (-1939822559 / 1000000000000)
      | 6 => orderedInterval (8184732456 / 1000000000000) (8184732524 / 1000000000000)
      | 7 => orderedInterval (-1794504588 / 1000000000000) (-1794502257 / 1000000000000)
      | _ => orderedInterval (-3185116653 / 1000000000000) (-3185115971 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-4941938837 / 1000000000000) (-4941935945 / 1000000000000)
      | 1 => orderedInterval (-3201004125 / 1000000000000) (-3201000605 / 1000000000000)
      | 2 => orderedInterval (2025848786 / 1000000000000) (2025850162 / 1000000000000)
      | 3 => orderedInterval (3493226820 / 1000000000000) (3493264503 / 1000000000000)
      | 4 => orderedInterval (2922016488 / 1000000000000) (2922016795 / 1000000000000)
      | 5 => orderedInterval (3318993976 / 1000000000000) (3318998052 / 1000000000000)
      | 6 => orderedInterval (1429400997 / 1000000000000) (1429401060 / 1000000000000)
      | 7 => orderedInterval (-1762864681 / 1000000000000) (-1762862830 / 1000000000000)
      | _ => orderedInterval (-9087088810 / 1000000000000) (-9087087575 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (21593222842 / 1000000000000) (21593226296 / 1000000000000)
      | 1 => orderedInterval (-4301401096 / 1000000000000) (-4301395572 / 1000000000000)
      | 2 => orderedInterval (1351285040 / 1000000000000) (1351287762 / 1000000000000)
      | 3 => orderedInterval (43264799179 / 1000000000000) (43264883559 / 1000000000000)
      | 4 => orderedInterval (-4961096511 / 1000000000000) (-4961095968 / 1000000000000)
      | 5 => orderedInterval (4659390186 / 1000000000000) (4659397713 / 1000000000000)
      | 6 => orderedInterval (-7182981663 / 1000000000000) (-7182981603 / 1000000000000)
      | 7 => orderedInterval (3172387270 / 1000000000000) (3172388749 / 1000000000000)
      | _ => orderedInterval (10029814609 / 1000000000000) (10029816867 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (4048412723 / 1000000000000) (4048416836 / 1000000000000)
      | 1 => orderedInterval (7187264730 / 1000000000000) (7187273386 / 1000000000000)
      | 2 => orderedInterval (-6758514315 / 1000000000000) (-6758508938 / 1000000000000)
      | 3 => orderedInterval (-4542577054 / 1000000000000) (-4542388396 / 1000000000000)
      | 4 => orderedInterval (-6700547220 / 1000000000000) (-6700546249 / 1000000000000)
      | 5 => orderedInterval (-6811712142 / 1000000000000) (-6811698256 / 1000000000000)
      | 6 => orderedInterval (-2063567542 / 1000000000000) (-2063567484 / 1000000000000)
      | 7 => orderedInterval (2224236917 / 1000000000000) (2224238096 / 1000000000000)
      | _ => orderedInterval (11326316612 / 1000000000000) (11326320762 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-22979610825 / 1000000000000) (-22979605912 / 1000000000000)
      | 1 => orderedInterval (12265236613 / 1000000000000) (12265250211 / 1000000000000)
      | 2 => orderedInterval (-8561711274 / 1000000000000) (-8561700626 / 1000000000000)
      | 3 => orderedInterval (-230589505248 / 1000000000000) (-230589082718 / 1000000000000)
      | 4 => orderedInterval (5681805182 / 1000000000000) (5681806937 / 1000000000000)
      | 5 => orderedInterval (-12559277948 / 1000000000000) (-12559252263 / 1000000000000)
      | 6 => orderedInterval (7214998529 / 1000000000000) (7214998586 / 1000000000000)
      | 7 => orderedInterval (-4100483605 / 1000000000000) (-4100482659 / 1000000000000)
      | _ => orderedInterval (-34176824101 / 1000000000000) (-34176816430 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-25267579036 / 1000000000000) (-25267551320 / 1000000000000)
    | 1 => orderedInterval (-5803409386 / 1000000000000) (-5803356383 / 1000000000000)
    | 2 => orderedInterval (67625419856 / 1000000000000) (67625527803 / 1000000000000)
    | 3 => orderedInterval (-2090687291 / 1000000000000) (-2090460243 / 1000000000000)
    | _ => orderedInterval (-287805372677 / 1000000000000) (-287804884874 / 1000000000000)

theorem compactCertificate396_stateChecks0 :
    compactCertificate396.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (535 / 2)) (orderedInterval (-46288461462 / 1000000000000) (-46288461461 / 1000000000000), orderedInterval (-15316791363 / 1000000000000) (-15316791361 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (157631431425407 / 800000000000)) (orderedInterval (5464448594 / 1000000000000) (5464448608 / 1000000000000), orderedInterval (-56591937062 / 1000000000000) (-56591937048 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (50974766180831 / 160000000000)) (orderedInterval (-39107786207 / 1000000000000) (-39107745144 / 1000000000000), orderedInterval (21713340427 / 1000000000000) (21713381489 / 1000000000000))) = true
  rfl'

theorem compactCertificate396_stateChecks1 :
    compactCertificate396.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (45996458551549 / 800000000000)) (orderedInterval (103891115903 / 1000000000000) (103891116137 / 1000000000000), orderedInterval (-17598889023 / 1000000000000) (-17598888789 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (123552957606553 / 800000000000)) (orderedInterval (-61648517185 / 1000000000000) (-61648517183 / 1000000000000), orderedInterval (-17731598630 / 1000000000000) (-17731598628 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (335470314374901 / 800000000000)) (orderedInterval (-29283384854 / 1000000000000) (-29283353601 / 1000000000000), orderedInterval (25737794355 / 1000000000000) (25737825608 / 1000000000000))) = true
  rfl'

theorem compactCertificate396_stateChecks2 :
    compactCertificate396.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (247105915213213 / 800000000000)) (orderedInterval (44299382581 / 1000000000000) (44299384854 / 1000000000000), orderedInterval (-10001702842 / 1000000000000) (-10001700569 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (423420197503249 / 800000000000)) (orderedInterval (26480157481 / 1000000000000) (26480179592 / 1000000000000), orderedInterval (-22421783894 / 1000000000000) (-22421761783 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (311889401059891 / 800000000000)) (orderedInterval (35815894483 / 1000000000000) (35815894484 / 1000000000000), orderedInterval (18666579861 / 1000000000000) (18666579862 / 1000000000000))) = true
  rfl'

theorem compactCertificate396_stateChecks3 :
    compactCertificate396.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (478518547184893 / 800000000000)) (orderedInterval (29233055425 / 1000000000000) (29233149711 / 1000000000000), orderedInterval (-14506997472 / 1000000000000) (-14506903185 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (276272812029397 / 800000000000)) (orderedInterval (22473244426 / 1000000000000) (22473244427 / 1000000000000), orderedInterval (36551703472 / 1000000000000) (36551703473 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (490250953070873 / 800000000000)) (orderedInterval (-26916293340 / 1000000000000) (-26916293339 / 1000000000000), orderedInterval (-17708244413 / 1000000000000) (-17708244412 / 1000000000000))) = true
  rfl'

theorem compactCertificate396_stateChecks4 :
    compactCertificate396.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (458056034039837 / 800000000000)) (orderedInterval (33341075589 / 1000000000000) (33341076575 / 1000000000000), orderedInterval (-514700333 / 1000000000000) (-514699347 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (326890399573421 / 800000000000)) (orderedInterval (33021865050 / 1000000000000) (33021865051 / 1000000000000), orderedInterval (21582675890 / 1000000000000) (21582675891 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (370658872819659 / 800000000000)) (orderedInterval (-27774701125 / 1000000000000) (-27774676469 / 1000000000000), orderedInterval (24577770044 / 1000000000000) (24577794700 / 1000000000000))) = true
  rfl'

theorem compactCertificate396_stateChecks5 :
    compactCertificate396.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (309016725026971 / 800000000000)) (orderedInterval (-24247089726 / 1000000000000) (-24247089725 / 1000000000000), orderedInterval (-32529270551 / 1000000000000) (-32529270550 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (273025648098391 / 800000000000)) (orderedInterval (15477427077 / 1000000000000) (15477427318 / 1000000000000), orderedInterval (-40344232142 / 1000000000000) (-40344231900 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (79133474504709 / 160000000000)) (orderedInterval (-30233836417 / 1000000000000) (-30233751490 / 1000000000000), orderedInterval (19346294709 / 1000000000000) (19346379636 / 1000000000000))) = true
  rfl'

theorem compactCertificate396_stateChecks6 :
    compactCertificate396.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (218887355046623 / 800000000000)) (orderedInterval (-42441381143 / 1000000000000) (-42441381142 / 1000000000000), orderedInterval (-22845694334 / 1000000000000) (-22845694333 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (185553234984103 / 800000000000)) (orderedInterval (12887759461 / 1000000000000) (12887759462 / 1000000000000), orderedInterval (50752662723 / 1000000000000) (50752662724 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (116110598940109 / 800000000000)) (orderedInterval (65369538322 / 1000000000000) (65369538326 / 1000000000000), orderedInterval (10409554578 / 1000000000000) (10409554582 / 1000000000000))) = true
  rfl'

theorem compactCertificate396_stateChecks7 :
    compactCertificate396.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (62444666276403 / 800000000000)) (orderedInterval (-26672150132 / 1000000000000) (-26672150131 / 1000000000000), orderedInterval (-86111761652 / 1000000000000) (-86111761651 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (169549416158209 / 800000000000)) (orderedInterval (-43159906704 / 1000000000000) (-43159805389 / 1000000000000), orderedInterval (33881112176 / 1000000000000) (33881213491 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (231505232538593 / 800000000000)) (orderedInterval (42617662463 / 1000000000000) (42617662464 / 1000000000000), orderedInterval (19513730739 / 1000000000000) (19513730740 / 1000000000000))) = true
  rfl'

theorem compactCertificate396_stateChecks8 :
    compactCertificate396.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (97889401059891 / 800000000000)) (orderedInterval (-42145346621 / 1000000000000) (-42145346620 / 1000000000000), orderedInterval (-58364538180 / 1000000000000) (-58364538179 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (397914980651411 / 800000000000)) (orderedInterval (34780503527 / 1000000000000) (34780510988 / 1000000000000), orderedInterval (-8415114053 / 1000000000000) (-8415106592 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (265788766077949 / 800000000000)) (orderedInterval (532202161 / 1000000000000) (532202163 / 1000000000000), orderedInterval (43770039979 / 1000000000000) (43770039981 / 1000000000000))) = true
  rfl'

theorem compactCertificate396_states : ∀ j,
    BesselStateValid (compactCertificate396.point j) (compactCertificate396.state j) :=
  compactCertificate396.statesValid_of_checks3 compactCertificate396_stateChecks0
    compactCertificate396_stateChecks1 compactCertificate396_stateChecks2
    compactCertificate396_stateChecks3 compactCertificate396_stateChecks4
    compactCertificate396_stateChecks5 compactCertificate396_stateChecks6
    compactCertificate396_stateChecks7 compactCertificate396_stateChecks8

theorem compactCertificate396_chunkChecks0_0 :
    compactCertificate396.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (535 / 2) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-46288461462 / 1000000000000) (-46288461461 / 1000000000000), orderedInterval (-15316791363 / 1000000000000) (-15316791361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (157631431425407 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (5464448594 / 1000000000000) (5464448608 / 1000000000000), orderedInterval (-56591937062 / 1000000000000) (-56591937048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (50974766180831 / 160000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39107786207 / 1000000000000) (-39107745144 / 1000000000000), orderedInterval (21713340427 / 1000000000000) (21713381489 / 1000000000000)))) (orderedInterval (-20591097131 / 1000000000000) (-20591094701 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (45996458551549 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (103891115903 / 1000000000000) (103891116137 / 1000000000000), orderedInterval (-17598889023 / 1000000000000) (-17598888789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (123552957606553 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61648517185 / 1000000000000) (-61648517183 / 1000000000000), orderedInterval (-17731598630 / 1000000000000) (-17731598628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (335470314374901 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29283384854 / 1000000000000) (-29283353601 / 1000000000000), orderedInterval (25737794355 / 1000000000000) (25737825608 / 1000000000000)))) (orderedInterval (-1296296874 / 1000000000000) (-1296294617 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (247105915213213 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (44299382581 / 1000000000000) (44299384854 / 1000000000000), orderedInterval (-10001702842 / 1000000000000) (-10001700569 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (423420197503249 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26480157481 / 1000000000000) (26480179592 / 1000000000000), orderedInterval (-22421783894 / 1000000000000) (-22421761783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (311889401059891 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (35815894483 / 1000000000000) (35815894484 / 1000000000000), orderedInterval (18666579861 / 1000000000000) (18666579862 / 1000000000000)))) (orderedInterval (48844811 / 1000000000000) (48845509 / 1000000000000))) = true
  rfl'

theorem compactCertificate396_chunkChecks0_1 :
    compactCertificate396.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (478518547184893 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29233055425 / 1000000000000) (29233149711 / 1000000000000), orderedInterval (-14506997472 / 1000000000000) (-14506903185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (276272812029397 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22473244426 / 1000000000000) (22473244427 / 1000000000000), orderedInterval (36551703472 / 1000000000000) (36551703473 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (490250953070873 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26916293340 / 1000000000000) (-26916293339 / 1000000000000), orderedInterval (-17708244413 / 1000000000000) (-17708244412 / 1000000000000)))) (orderedInterval (-7355605005 / 1000000000000) (-7355588145 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (458056034039837 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33341075589 / 1000000000000) (33341076575 / 1000000000000), orderedInterval (-514700333 / 1000000000000) (-514699347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (326890399573421 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33021865050 / 1000000000000) (33021865051 / 1000000000000), orderedInterval (21582675890 / 1000000000000) (21582675891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (370658872819659 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27774701125 / 1000000000000) (-27774676469 / 1000000000000), orderedInterval (24577770044 / 1000000000000) (24577794700 / 1000000000000)))) (orderedInterval (2661288722 / 1000000000000) (2661288897 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (309016725026971 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24247089726 / 1000000000000) (-24247089725 / 1000000000000), orderedInterval (-32529270551 / 1000000000000) (-32529270550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (273025648098391 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (15477427077 / 1000000000000) (15477427318 / 1000000000000), orderedInterval (-40344232142 / 1000000000000) (-40344231900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (79133474504709 / 160000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30233836417 / 1000000000000) (-30233751490 / 1000000000000), orderedInterval (19346294709 / 1000000000000) (19346379636 / 1000000000000)))) (orderedInterval (-1939824774 / 1000000000000) (-1939822559 / 1000000000000))) = true
  rfl'

theorem compactCertificate396_chunkChecks0_2 :
    compactCertificate396.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (218887355046623 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-42441381143 / 1000000000000) (-42441381142 / 1000000000000), orderedInterval (-22845694334 / 1000000000000) (-22845694333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (185553234984103 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12887759461 / 1000000000000) (12887759462 / 1000000000000), orderedInterval (50752662723 / 1000000000000) (50752662724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (116110598940109 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (65369538322 / 1000000000000) (65369538326 / 1000000000000), orderedInterval (10409554578 / 1000000000000) (10409554582 / 1000000000000)))) (orderedInterval (8184732456 / 1000000000000) (8184732524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (62444666276403 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-26672150132 / 1000000000000) (-26672150131 / 1000000000000), orderedInterval (-86111761652 / 1000000000000) (-86111761651 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (169549416158209 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43159906704 / 1000000000000) (-43159805389 / 1000000000000), orderedInterval (33881112176 / 1000000000000) (33881213491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (231505232538593 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42617662463 / 1000000000000) (42617662464 / 1000000000000), orderedInterval (19513730739 / 1000000000000) (19513730740 / 1000000000000)))) (orderedInterval (-1794504588 / 1000000000000) (-1794502257 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (97889401059891 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42145346621 / 1000000000000) (-42145346620 / 1000000000000), orderedInterval (-58364538180 / 1000000000000) (-58364538179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (397914980651411 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (34780503527 / 1000000000000) (34780510988 / 1000000000000), orderedInterval (-8415114053 / 1000000000000) (-8415106592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (265788766077949 / 800000000000) 0 (IntervalRat.scale (535 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (532202161 / 1000000000000) (532202163 / 1000000000000), orderedInterval (43770039979 / 1000000000000) (43770039981 / 1000000000000)))) (orderedInterval (-3185116653 / 1000000000000) (-3185115971 / 1000000000000))) = true
  rfl'

theorem compactCertificate396_chunkChecks0 :
    compactCertificate396.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate396.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate396_chunkChecks0_0
    compactCertificate396_chunkChecks0_1 compactCertificate396_chunkChecks0_2

theorem compactCertificate396_chunkChecks1_0 :
    compactCertificate396.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (535 / 2) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-46288461462 / 1000000000000) (-46288461461 / 1000000000000), orderedInterval (-15316791363 / 1000000000000) (-15316791361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (157631431425407 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (5464448594 / 1000000000000) (5464448608 / 1000000000000), orderedInterval (-56591937062 / 1000000000000) (-56591937048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (50974766180831 / 160000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39107786207 / 1000000000000) (-39107745144 / 1000000000000), orderedInterval (21713340427 / 1000000000000) (21713381489 / 1000000000000)))) (orderedInterval (-4941938837 / 1000000000000) (-4941935945 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (45996458551549 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (103891115903 / 1000000000000) (103891116137 / 1000000000000), orderedInterval (-17598889023 / 1000000000000) (-17598888789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (123552957606553 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61648517185 / 1000000000000) (-61648517183 / 1000000000000), orderedInterval (-17731598630 / 1000000000000) (-17731598628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (335470314374901 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29283384854 / 1000000000000) (-29283353601 / 1000000000000), orderedInterval (25737794355 / 1000000000000) (25737825608 / 1000000000000)))) (orderedInterval (-3201004125 / 1000000000000) (-3201000605 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (247105915213213 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (44299382581 / 1000000000000) (44299384854 / 1000000000000), orderedInterval (-10001702842 / 1000000000000) (-10001700569 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (423420197503249 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26480157481 / 1000000000000) (26480179592 / 1000000000000), orderedInterval (-22421783894 / 1000000000000) (-22421761783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (311889401059891 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (35815894483 / 1000000000000) (35815894484 / 1000000000000), orderedInterval (18666579861 / 1000000000000) (18666579862 / 1000000000000)))) (orderedInterval (2025848786 / 1000000000000) (2025850162 / 1000000000000))) = true
  rfl'

theorem compactCertificate396_chunkChecks1_1 :
    compactCertificate396.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (478518547184893 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29233055425 / 1000000000000) (29233149711 / 1000000000000), orderedInterval (-14506997472 / 1000000000000) (-14506903185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (276272812029397 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22473244426 / 1000000000000) (22473244427 / 1000000000000), orderedInterval (36551703472 / 1000000000000) (36551703473 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (490250953070873 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26916293340 / 1000000000000) (-26916293339 / 1000000000000), orderedInterval (-17708244413 / 1000000000000) (-17708244412 / 1000000000000)))) (orderedInterval (3493226820 / 1000000000000) (3493264503 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (458056034039837 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33341075589 / 1000000000000) (33341076575 / 1000000000000), orderedInterval (-514700333 / 1000000000000) (-514699347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (326890399573421 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33021865050 / 1000000000000) (33021865051 / 1000000000000), orderedInterval (21582675890 / 1000000000000) (21582675891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (370658872819659 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27774701125 / 1000000000000) (-27774676469 / 1000000000000), orderedInterval (24577770044 / 1000000000000) (24577794700 / 1000000000000)))) (orderedInterval (2922016488 / 1000000000000) (2922016795 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (309016725026971 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24247089726 / 1000000000000) (-24247089725 / 1000000000000), orderedInterval (-32529270551 / 1000000000000) (-32529270550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (273025648098391 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (15477427077 / 1000000000000) (15477427318 / 1000000000000), orderedInterval (-40344232142 / 1000000000000) (-40344231900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (79133474504709 / 160000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30233836417 / 1000000000000) (-30233751490 / 1000000000000), orderedInterval (19346294709 / 1000000000000) (19346379636 / 1000000000000)))) (orderedInterval (3318993976 / 1000000000000) (3318998052 / 1000000000000))) = true
  rfl'

theorem compactCertificate396_chunkChecks1_2 :
    compactCertificate396.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (218887355046623 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-42441381143 / 1000000000000) (-42441381142 / 1000000000000), orderedInterval (-22845694334 / 1000000000000) (-22845694333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (185553234984103 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12887759461 / 1000000000000) (12887759462 / 1000000000000), orderedInterval (50752662723 / 1000000000000) (50752662724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (116110598940109 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (65369538322 / 1000000000000) (65369538326 / 1000000000000), orderedInterval (10409554578 / 1000000000000) (10409554582 / 1000000000000)))) (orderedInterval (1429400997 / 1000000000000) (1429401060 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (62444666276403 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-26672150132 / 1000000000000) (-26672150131 / 1000000000000), orderedInterval (-86111761652 / 1000000000000) (-86111761651 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (169549416158209 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43159906704 / 1000000000000) (-43159805389 / 1000000000000), orderedInterval (33881112176 / 1000000000000) (33881213491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (231505232538593 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42617662463 / 1000000000000) (42617662464 / 1000000000000), orderedInterval (19513730739 / 1000000000000) (19513730740 / 1000000000000)))) (orderedInterval (-1762864681 / 1000000000000) (-1762862830 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (97889401059891 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42145346621 / 1000000000000) (-42145346620 / 1000000000000), orderedInterval (-58364538180 / 1000000000000) (-58364538179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (397914980651411 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (34780503527 / 1000000000000) (34780510988 / 1000000000000), orderedInterval (-8415114053 / 1000000000000) (-8415106592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (265788766077949 / 800000000000) 1 (IntervalRat.scale (535 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (532202161 / 1000000000000) (532202163 / 1000000000000), orderedInterval (43770039979 / 1000000000000) (43770039981 / 1000000000000)))) (orderedInterval (-9087088810 / 1000000000000) (-9087087575 / 1000000000000))) = true
  rfl'

theorem compactCertificate396_chunkChecks1 :
    compactCertificate396.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate396.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate396_chunkChecks1_0
    compactCertificate396_chunkChecks1_1 compactCertificate396_chunkChecks1_2

theorem compactCertificate396_chunkChecks2_0 :
    compactCertificate396.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (535 / 2) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-46288461462 / 1000000000000) (-46288461461 / 1000000000000), orderedInterval (-15316791363 / 1000000000000) (-15316791361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (157631431425407 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (5464448594 / 1000000000000) (5464448608 / 1000000000000), orderedInterval (-56591937062 / 1000000000000) (-56591937048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (50974766180831 / 160000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39107786207 / 1000000000000) (-39107745144 / 1000000000000), orderedInterval (21713340427 / 1000000000000) (21713381489 / 1000000000000)))) (orderedInterval (21593222842 / 1000000000000) (21593226296 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (45996458551549 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (103891115903 / 1000000000000) (103891116137 / 1000000000000), orderedInterval (-17598889023 / 1000000000000) (-17598888789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (123552957606553 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61648517185 / 1000000000000) (-61648517183 / 1000000000000), orderedInterval (-17731598630 / 1000000000000) (-17731598628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (335470314374901 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29283384854 / 1000000000000) (-29283353601 / 1000000000000), orderedInterval (25737794355 / 1000000000000) (25737825608 / 1000000000000)))) (orderedInterval (-4301401096 / 1000000000000) (-4301395572 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (247105915213213 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (44299382581 / 1000000000000) (44299384854 / 1000000000000), orderedInterval (-10001702842 / 1000000000000) (-10001700569 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (423420197503249 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26480157481 / 1000000000000) (26480179592 / 1000000000000), orderedInterval (-22421783894 / 1000000000000) (-22421761783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (311889401059891 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (35815894483 / 1000000000000) (35815894484 / 1000000000000), orderedInterval (18666579861 / 1000000000000) (18666579862 / 1000000000000)))) (orderedInterval (1351285040 / 1000000000000) (1351287762 / 1000000000000))) = true
  rfl'

theorem compactCertificate396_chunkChecks2_1 :
    compactCertificate396.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (478518547184893 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29233055425 / 1000000000000) (29233149711 / 1000000000000), orderedInterval (-14506997472 / 1000000000000) (-14506903185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (276272812029397 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22473244426 / 1000000000000) (22473244427 / 1000000000000), orderedInterval (36551703472 / 1000000000000) (36551703473 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (490250953070873 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26916293340 / 1000000000000) (-26916293339 / 1000000000000), orderedInterval (-17708244413 / 1000000000000) (-17708244412 / 1000000000000)))) (orderedInterval (43264799179 / 1000000000000) (43264883559 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (458056034039837 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33341075589 / 1000000000000) (33341076575 / 1000000000000), orderedInterval (-514700333 / 1000000000000) (-514699347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (326890399573421 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33021865050 / 1000000000000) (33021865051 / 1000000000000), orderedInterval (21582675890 / 1000000000000) (21582675891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (370658872819659 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27774701125 / 1000000000000) (-27774676469 / 1000000000000), orderedInterval (24577770044 / 1000000000000) (24577794700 / 1000000000000)))) (orderedInterval (-4961096511 / 1000000000000) (-4961095968 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (309016725026971 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24247089726 / 1000000000000) (-24247089725 / 1000000000000), orderedInterval (-32529270551 / 1000000000000) (-32529270550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (273025648098391 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (15477427077 / 1000000000000) (15477427318 / 1000000000000), orderedInterval (-40344232142 / 1000000000000) (-40344231900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (79133474504709 / 160000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30233836417 / 1000000000000) (-30233751490 / 1000000000000), orderedInterval (19346294709 / 1000000000000) (19346379636 / 1000000000000)))) (orderedInterval (4659390186 / 1000000000000) (4659397713 / 1000000000000))) = true
  rfl'

theorem compactCertificate396_chunkChecks2_2 :
    compactCertificate396.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (218887355046623 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-42441381143 / 1000000000000) (-42441381142 / 1000000000000), orderedInterval (-22845694334 / 1000000000000) (-22845694333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (185553234984103 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12887759461 / 1000000000000) (12887759462 / 1000000000000), orderedInterval (50752662723 / 1000000000000) (50752662724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (116110598940109 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (65369538322 / 1000000000000) (65369538326 / 1000000000000), orderedInterval (10409554578 / 1000000000000) (10409554582 / 1000000000000)))) (orderedInterval (-7182981663 / 1000000000000) (-7182981603 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (62444666276403 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-26672150132 / 1000000000000) (-26672150131 / 1000000000000), orderedInterval (-86111761652 / 1000000000000) (-86111761651 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (169549416158209 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43159906704 / 1000000000000) (-43159805389 / 1000000000000), orderedInterval (33881112176 / 1000000000000) (33881213491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (231505232538593 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42617662463 / 1000000000000) (42617662464 / 1000000000000), orderedInterval (19513730739 / 1000000000000) (19513730740 / 1000000000000)))) (orderedInterval (3172387270 / 1000000000000) (3172388749 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (97889401059891 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42145346621 / 1000000000000) (-42145346620 / 1000000000000), orderedInterval (-58364538180 / 1000000000000) (-58364538179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (397914980651411 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (34780503527 / 1000000000000) (34780510988 / 1000000000000), orderedInterval (-8415114053 / 1000000000000) (-8415106592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (265788766077949 / 800000000000) 2 (IntervalRat.scale (535 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (532202161 / 1000000000000) (532202163 / 1000000000000), orderedInterval (43770039979 / 1000000000000) (43770039981 / 1000000000000)))) (orderedInterval (10029814609 / 1000000000000) (10029816867 / 1000000000000))) = true
  rfl'

theorem compactCertificate396_chunkChecks2 :
    compactCertificate396.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate396.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate396_chunkChecks2_0
    compactCertificate396_chunkChecks2_1 compactCertificate396_chunkChecks2_2

theorem compactCertificate396_chunkChecks3_0 :
    compactCertificate396.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (535 / 2) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-46288461462 / 1000000000000) (-46288461461 / 1000000000000), orderedInterval (-15316791363 / 1000000000000) (-15316791361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (157631431425407 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (5464448594 / 1000000000000) (5464448608 / 1000000000000), orderedInterval (-56591937062 / 1000000000000) (-56591937048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (50974766180831 / 160000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39107786207 / 1000000000000) (-39107745144 / 1000000000000), orderedInterval (21713340427 / 1000000000000) (21713381489 / 1000000000000)))) (orderedInterval (4048412723 / 1000000000000) (4048416836 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (45996458551549 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (103891115903 / 1000000000000) (103891116137 / 1000000000000), orderedInterval (-17598889023 / 1000000000000) (-17598888789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (123552957606553 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61648517185 / 1000000000000) (-61648517183 / 1000000000000), orderedInterval (-17731598630 / 1000000000000) (-17731598628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (335470314374901 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29283384854 / 1000000000000) (-29283353601 / 1000000000000), orderedInterval (25737794355 / 1000000000000) (25737825608 / 1000000000000)))) (orderedInterval (7187264730 / 1000000000000) (7187273386 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (247105915213213 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (44299382581 / 1000000000000) (44299384854 / 1000000000000), orderedInterval (-10001702842 / 1000000000000) (-10001700569 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (423420197503249 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26480157481 / 1000000000000) (26480179592 / 1000000000000), orderedInterval (-22421783894 / 1000000000000) (-22421761783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (311889401059891 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (35815894483 / 1000000000000) (35815894484 / 1000000000000), orderedInterval (18666579861 / 1000000000000) (18666579862 / 1000000000000)))) (orderedInterval (-6758514315 / 1000000000000) (-6758508938 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate396_chunkChecks3_1 :
    compactCertificate396.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (478518547184893 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29233055425 / 1000000000000) (29233149711 / 1000000000000), orderedInterval (-14506997472 / 1000000000000) (-14506903185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (276272812029397 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22473244426 / 1000000000000) (22473244427 / 1000000000000), orderedInterval (36551703472 / 1000000000000) (36551703473 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (490250953070873 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26916293340 / 1000000000000) (-26916293339 / 1000000000000), orderedInterval (-17708244413 / 1000000000000) (-17708244412 / 1000000000000)))) (orderedInterval (-4542577054 / 1000000000000) (-4542388396 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (458056034039837 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33341075589 / 1000000000000) (33341076575 / 1000000000000), orderedInterval (-514700333 / 1000000000000) (-514699347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (326890399573421 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33021865050 / 1000000000000) (33021865051 / 1000000000000), orderedInterval (21582675890 / 1000000000000) (21582675891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (370658872819659 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27774701125 / 1000000000000) (-27774676469 / 1000000000000), orderedInterval (24577770044 / 1000000000000) (24577794700 / 1000000000000)))) (orderedInterval (-6700547220 / 1000000000000) (-6700546249 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (309016725026971 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24247089726 / 1000000000000) (-24247089725 / 1000000000000), orderedInterval (-32529270551 / 1000000000000) (-32529270550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (273025648098391 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (15477427077 / 1000000000000) (15477427318 / 1000000000000), orderedInterval (-40344232142 / 1000000000000) (-40344231900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (79133474504709 / 160000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30233836417 / 1000000000000) (-30233751490 / 1000000000000), orderedInterval (19346294709 / 1000000000000) (19346379636 / 1000000000000)))) (orderedInterval (-6811712142 / 1000000000000) (-6811698256 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate396_chunkChecks3_2 :
    compactCertificate396.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (218887355046623 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-42441381143 / 1000000000000) (-42441381142 / 1000000000000), orderedInterval (-22845694334 / 1000000000000) (-22845694333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (185553234984103 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12887759461 / 1000000000000) (12887759462 / 1000000000000), orderedInterval (50752662723 / 1000000000000) (50752662724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (116110598940109 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (65369538322 / 1000000000000) (65369538326 / 1000000000000), orderedInterval (10409554578 / 1000000000000) (10409554582 / 1000000000000)))) (orderedInterval (-2063567542 / 1000000000000) (-2063567484 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (62444666276403 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-26672150132 / 1000000000000) (-26672150131 / 1000000000000), orderedInterval (-86111761652 / 1000000000000) (-86111761651 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (169549416158209 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43159906704 / 1000000000000) (-43159805389 / 1000000000000), orderedInterval (33881112176 / 1000000000000) (33881213491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (231505232538593 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42617662463 / 1000000000000) (42617662464 / 1000000000000), orderedInterval (19513730739 / 1000000000000) (19513730740 / 1000000000000)))) (orderedInterval (2224236917 / 1000000000000) (2224238096 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (97889401059891 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42145346621 / 1000000000000) (-42145346620 / 1000000000000), orderedInterval (-58364538180 / 1000000000000) (-58364538179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (397914980651411 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (34780503527 / 1000000000000) (34780510988 / 1000000000000), orderedInterval (-8415114053 / 1000000000000) (-8415106592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (265788766077949 / 800000000000) 3 (IntervalRat.scale (535 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (532202161 / 1000000000000) (532202163 / 1000000000000), orderedInterval (43770039979 / 1000000000000) (43770039981 / 1000000000000)))) (orderedInterval (11326316612 / 1000000000000) (11326320762 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate396_chunkChecks3 :
    compactCertificate396.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate396.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate396_chunkChecks3_0
    compactCertificate396_chunkChecks3_1 compactCertificate396_chunkChecks3_2

theorem compactCertificate396_chunkChecks4_0 :
    compactCertificate396.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (535 / 2) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-46288461462 / 1000000000000) (-46288461461 / 1000000000000), orderedInterval (-15316791363 / 1000000000000) (-15316791361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (157631431425407 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (5464448594 / 1000000000000) (5464448608 / 1000000000000), orderedInterval (-56591937062 / 1000000000000) (-56591937048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (50974766180831 / 160000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39107786207 / 1000000000000) (-39107745144 / 1000000000000), orderedInterval (21713340427 / 1000000000000) (21713381489 / 1000000000000)))) (orderedInterval (-22979610825 / 1000000000000) (-22979605912 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (45996458551549 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (103891115903 / 1000000000000) (103891116137 / 1000000000000), orderedInterval (-17598889023 / 1000000000000) (-17598888789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (123552957606553 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61648517185 / 1000000000000) (-61648517183 / 1000000000000), orderedInterval (-17731598630 / 1000000000000) (-17731598628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (335470314374901 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29283384854 / 1000000000000) (-29283353601 / 1000000000000), orderedInterval (25737794355 / 1000000000000) (25737825608 / 1000000000000)))) (orderedInterval (12265236613 / 1000000000000) (12265250211 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (247105915213213 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (44299382581 / 1000000000000) (44299384854 / 1000000000000), orderedInterval (-10001702842 / 1000000000000) (-10001700569 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (423420197503249 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26480157481 / 1000000000000) (26480179592 / 1000000000000), orderedInterval (-22421783894 / 1000000000000) (-22421761783 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (311889401059891 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (35815894483 / 1000000000000) (35815894484 / 1000000000000), orderedInterval (18666579861 / 1000000000000) (18666579862 / 1000000000000)))) (orderedInterval (-8561711274 / 1000000000000) (-8561700626 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate396_chunkChecks4_1 :
    compactCertificate396.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (478518547184893 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (29233055425 / 1000000000000) (29233149711 / 1000000000000), orderedInterval (-14506997472 / 1000000000000) (-14506903185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (276272812029397 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22473244426 / 1000000000000) (22473244427 / 1000000000000), orderedInterval (36551703472 / 1000000000000) (36551703473 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (490250953070873 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-26916293340 / 1000000000000) (-26916293339 / 1000000000000), orderedInterval (-17708244413 / 1000000000000) (-17708244412 / 1000000000000)))) (orderedInterval (-230589505248 / 1000000000000) (-230589082718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (458056034039837 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33341075589 / 1000000000000) (33341076575 / 1000000000000), orderedInterval (-514700333 / 1000000000000) (-514699347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (326890399573421 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33021865050 / 1000000000000) (33021865051 / 1000000000000), orderedInterval (21582675890 / 1000000000000) (21582675891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (370658872819659 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27774701125 / 1000000000000) (-27774676469 / 1000000000000), orderedInterval (24577770044 / 1000000000000) (24577794700 / 1000000000000)))) (orderedInterval (5681805182 / 1000000000000) (5681806937 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (309016725026971 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24247089726 / 1000000000000) (-24247089725 / 1000000000000), orderedInterval (-32529270551 / 1000000000000) (-32529270550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (273025648098391 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (15477427077 / 1000000000000) (15477427318 / 1000000000000), orderedInterval (-40344232142 / 1000000000000) (-40344231900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (79133474504709 / 160000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30233836417 / 1000000000000) (-30233751490 / 1000000000000), orderedInterval (19346294709 / 1000000000000) (19346379636 / 1000000000000)))) (orderedInterval (-12559277948 / 1000000000000) (-12559252263 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate396_chunkChecks4_2 :
    compactCertificate396.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (218887355046623 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-42441381143 / 1000000000000) (-42441381142 / 1000000000000), orderedInterval (-22845694334 / 1000000000000) (-22845694333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (185553234984103 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12887759461 / 1000000000000) (12887759462 / 1000000000000), orderedInterval (50752662723 / 1000000000000) (50752662724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (116110598940109 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (65369538322 / 1000000000000) (65369538326 / 1000000000000), orderedInterval (10409554578 / 1000000000000) (10409554582 / 1000000000000)))) (orderedInterval (7214998529 / 1000000000000) (7214998586 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (62444666276403 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-26672150132 / 1000000000000) (-26672150131 / 1000000000000), orderedInterval (-86111761652 / 1000000000000) (-86111761651 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (169549416158209 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43159906704 / 1000000000000) (-43159805389 / 1000000000000), orderedInterval (33881112176 / 1000000000000) (33881213491 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (231505232538593 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42617662463 / 1000000000000) (42617662464 / 1000000000000), orderedInterval (19513730739 / 1000000000000) (19513730740 / 1000000000000)))) (orderedInterval (-4100483605 / 1000000000000) (-4100482659 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (97889401059891 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42145346621 / 1000000000000) (-42145346620 / 1000000000000), orderedInterval (-58364538180 / 1000000000000) (-58364538179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (397914980651411 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (34780503527 / 1000000000000) (34780510988 / 1000000000000), orderedInterval (-8415114053 / 1000000000000) (-8415106592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (265788766077949 / 800000000000) 4 (IntervalRat.scale (535 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (532202161 / 1000000000000) (532202163 / 1000000000000), orderedInterval (43770039979 / 1000000000000) (43770039981 / 1000000000000)))) (orderedInterval (-34176824101 / 1000000000000) (-34176816430 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate396_chunkChecks4 :
    compactCertificate396.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate396.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate396_chunkChecks4_0
    compactCertificate396_chunkChecks4_1 compactCertificate396_chunkChecks4_2

theorem compactCertificate396_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate396.chunkCheck r b = true :=
  compactCertificate396.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate396_chunkChecks0
    · exact compactCertificate396_chunkChecks1
    · exact compactCertificate396_chunkChecks2
    · exact compactCertificate396_chunkChecks3
    · exact compactCertificate396_chunkChecks4)

theorem compactCertificate396_coefficient0 :
    compactCertificate396.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate396_coefficient1 :
    compactCertificate396.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate396_coefficient2 :
    compactCertificate396.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate396_coefficient3 :
    compactCertificate396.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate396_coefficient4 :
    compactCertificate396.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate396_coefficients : ∀ r : Fin 5,
    compactCertificate396.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate396_coefficient0
  · exact compactCertificate396_coefficient1
  · exact compactCertificate396_coefficient2
  · exact compactCertificate396_coefficient3
  · exact compactCertificate396_coefficient4

theorem compactCertificate396_lower : (1 : ℚ) ≤ compactCertificate396.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate396, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate396_proves {t : ℝ} (ht : t ∈ compactCertificate396.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate396.proves compactCertificate396_states compactCertificate396_chunks
    compactCertificate396_coefficients compactCertificate396_lower ht

end Erdos232
