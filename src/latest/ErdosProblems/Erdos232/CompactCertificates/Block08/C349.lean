/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate349 : CompactCertificate where
  left := 220
  right := 221
  center := 441 / 2
  grid := fun i =>
    match i.val with
    | 0 => 70
    | 1 => 52
    | 2 => 84
    | 3 => 15
    | 4 => 41
    | 5 => 110
    | 6 => 81
    | 7 => 139
    | 8 => 102
    | 9 => 157
    | 10 => 91
    | 11 => 161
    | 12 => 150
    | 13 => 107
    | 14 => 122
    | 15 => 101
    | 16 => 90
    | 17 => 130
    | 18 => 72
    | 19 => 61
    | 20 => 38
    | 21 => 20
    | 22 => 56
    | 23 => 76
    | 24 => 32
    | 25 => 131
    | _ => 87
  point := fun i =>
    match i.val with
    | 0 => 441 / 2
    | 1 => 649677208024341 / 4000000000000
    | 2 => 210092260614453 / 800000000000
    | 3 => 189574188983487 / 4000000000000
    | 4 => 509222937425139 / 4000000000000
    | 5 => 1382639333077863 / 4000000000000
    | 6 => 1018445874850719 / 4000000000000
    | 7 => 1745124365410587 / 4000000000000
    | 8 => 1285450709041233 / 4000000000000
    | 9 => 1972211956154559 / 4000000000000
    | 10 => 1138657103784711 / 4000000000000
    | 11 => 2020567012189299 / 4000000000000
    | 12 => 1887875803846431 / 4000000000000
    | 13 => 1347277254316623 / 4000000000000
    | 14 => 1527668812275417 / 4000000000000
    | 15 => 1273610988195273 / 4000000000000
    | 16 => 1125273932816733 / 4000000000000
    | 17 => 326148245388567 / 800000000000
    | 18 => 902143210986549 / 4000000000000
    | 19 => 764756790915789 / 4000000000000
    | 20 => 478549290958767 / 4000000000000
    | 21 => 257365400260689 / 4000000000000
    | 22 => 698797126409067 / 4000000000000
    | 23 => 954147734107659 / 4000000000000
    | 24 => 403450709041233 / 4000000000000
    | 25 => 1640004733338993 / 4000000000000
    | _ => 1095447157386687 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (52688245589 / 1000000000000) (52688245593 / 1000000000000), orderedInterval (10421229421 / 1000000000000) (10421229425 / 1000000000000))
    | 1 => (orderedInterval (-9905601753 / 1000000000000) (-9905601706 / 1000000000000), orderedInterval (61848802563 / 1000000000000) (61848802609 / 1000000000000))
    | 2 => (orderedInterval (-23324991109 / 1000000000000) (-23324989247 / 1000000000000), orderedInterval (43404532636 / 1000000000000) (43404534498 / 1000000000000))
    | 3 => (orderedInterval (-100670051419 / 1000000000000) (-100670051418 / 1000000000000), orderedInterval (-56364406422 / 1000000000000) (-56364406421 / 1000000000000))
    | 4 => (orderedInterval (46370181675 / 1000000000000) (46370216584 / 1000000000000), orderedInterval (-53572448554 / 1000000000000) (-53572413644 / 1000000000000))
    | 5 => (orderedInterval (32792734217 / 1000000000000) (32792734218 / 1000000000000), orderedInterval (27636287770 / 1000000000000) (27636287771 / 1000000000000))
    | 6 => (orderedInterval (-40005097111 / 1000000000000) (-40005097110 / 1000000000000), orderedInterval (-29920583507 / 1000000000000) (-29920583506 / 1000000000000))
    | 7 => (orderedInterval (-14339914021 / 1000000000000) (-14339914020 / 1000000000000), orderedInterval (-35389270042 / 1000000000000) (-35389270041 / 1000000000000))
    | 8 => (orderedInterval (44106793183 / 1000000000000) (44106794086 / 1000000000000), orderedInterval (-6034310373 / 1000000000000) (-6034309470 / 1000000000000))
    | 9 => (orderedInterval (-20528452922 / 1000000000000) (-20528452921 / 1000000000000), orderedInterval (-29470911139 / 1000000000000) (-29470911138 / 1000000000000))
    | 10 => (orderedInterval (19958542214 / 1000000000000) (19958543045 / 1000000000000), orderedInterval (-42907504630 / 1000000000000) (-42907503800 / 1000000000000))
    | 11 => (orderedInterval (-4619190366 / 1000000000000) (-4619190365 / 1000000000000), orderedInterval (-35194051813 / 1000000000000) (-35194051812 / 1000000000000))
    | 12 => (orderedInterval (36670037453 / 1000000000000) (36670037667 / 1000000000000), orderedInterval (2002481841 / 1000000000000) (2002482056 / 1000000000000))
    | 13 => (orderedInterval (-43178608729 / 1000000000000) (-43178608695 / 1000000000000), orderedInterval (-5005277479 / 1000000000000) (-5005277445 / 1000000000000))
    | 14 => (orderedInterval (-22101678962 / 1000000000000) (-22101676679 / 1000000000000), orderedInterval (34357080258 / 1000000000000) (34357082541 / 1000000000000))
    | 15 => (orderedInterval (-42499442080 / 1000000000000) (-42499435413 / 1000000000000), orderedInterval (13966821808 / 1000000000000) (13966828475 / 1000000000000))
    | 16 => (orderedInterval (-28405329761 / 1000000000000) (-28405321685 / 1000000000000), orderedInterval (38209680230 / 1000000000000) (38209688307 / 1000000000000))
    | 17 => (orderedInterval (2501820927 / 1000000000000) (2501820928 / 1000000000000), orderedInterval (39434085083 / 1000000000000) (39434085084 / 1000000000000))
    | 18 => (orderedInterval (6675272261 / 1000000000000) (6675272262 / 1000000000000), orderedInterval (52693330212 / 1000000000000) (52693330213 / 1000000000000))
    | 19 => (orderedInterval (-19068902268 / 1000000000000) (-19068902267 / 1000000000000), orderedInterval (-54412735837 / 1000000000000) (-54412735836 / 1000000000000))
    | 20 => (orderedInterval (62952041660 / 1000000000000) (62952041661 / 1000000000000), orderedInterval (36591555333 / 1000000000000) (36591555334 / 1000000000000))
    | 21 => (orderedInterval (74639829740 / 1000000000000) (74639918757 / 1000000000000), orderedInterval (-66331555571 / 1000000000000) (-66331466554 / 1000000000000))
    | 22 => (orderedInterval (-25997316747 / 1000000000000) (-25997314967 / 1000000000000), orderedInterval (54555944316 / 1000000000000) (54555946095 / 1000000000000))
    | 23 => (orderedInterval (27475063930 / 1000000000000) (27475063931 / 1000000000000), orderedInterval (43691414123 / 1000000000000) (43691414124 / 1000000000000))
    | 24 => (orderedInterval (71365880152 / 1000000000000) (71365880153 / 1000000000000), orderedInterval (34554844262 / 1000000000000) (34554844263 / 1000000000000))
    | 25 => (orderedInterval (27214051831 / 1000000000000) (27214066092 / 1000000000000), orderedInterval (-28530943856 / 1000000000000) (-28530929595 / 1000000000000))
    | _ => (orderedInterval (-46801918745 / 1000000000000) (-46801918742 / 1000000000000), orderedInterval (-11498134286 / 1000000000000) (-11498134283 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (19422738026 / 1000000000000) (19422738153 / 1000000000000)
      | 1 => orderedInterval (454031262 / 1000000000000) (454032563 / 1000000000000)
      | 2 => orderedInterval (1508274484 / 1000000000000) (1508274519 / 1000000000000)
      | 3 => orderedInterval (4469776792 / 1000000000000) (4469776942 / 1000000000000)
      | 4 => orderedInterval (-4633253134 / 1000000000000) (-4633253088 / 1000000000000)
      | 5 => orderedInterval (1198829124 / 1000000000000) (1198829685 / 1000000000000)
      | 6 => orderedInterval (2061394195 / 1000000000000) (2061394251 / 1000000000000)
      | 7 => orderedInterval (-2894095202 / 1000000000000) (-2894093491 / 1000000000000)
      | _ => orderedInterval (6996225034 / 1000000000000) (6996226257 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (7588626171 / 1000000000000) (7588626321 / 1000000000000)
      | 1 => orderedInterval (-4077701201 / 1000000000000) (-4077700434 / 1000000000000)
      | 2 => orderedInterval (1947185873 / 1000000000000) (1947185927 / 1000000000000)
      | 3 => orderedInterval (-3856171891 / 1000000000000) (-3856171630 / 1000000000000)
      | 4 => orderedInterval (-1101523312 / 1000000000000) (-1101523235 / 1000000000000)
      | 5 => orderedInterval (-690043075 / 1000000000000) (-690042343 / 1000000000000)
      | 6 => orderedInterval (-5300973681 / 1000000000000) (-5300973629 / 1000000000000)
      | 7 => orderedInterval (-4245582444 / 1000000000000) (-4245581908 / 1000000000000)
      | _ => orderedInterval (7093162663 / 1000000000000) (7093164908 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-18926586834 / 1000000000000) (-18926586656 / 1000000000000)
      | 1 => orderedInterval (5132495579 / 1000000000000) (5132496050 / 1000000000000)
      | 2 => orderedInterval (-4004601218 / 1000000000000) (-4004601132 / 1000000000000)
      | 3 => orderedInterval (-17239212563 / 1000000000000) (-17239212069 / 1000000000000)
      | 4 => orderedInterval (12229671280 / 1000000000000) (12229671411 / 1000000000000)
      | 5 => orderedInterval (-1838446620 / 1000000000000) (-1838445658 / 1000000000000)
      | 6 => orderedInterval (-274075545 / 1000000000000) (-274075495 / 1000000000000)
      | 7 => orderedInterval (2230611776 / 1000000000000) (2230611968 / 1000000000000)
      | _ => orderedInterval (-6008811689 / 1000000000000) (-6008807537 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-8577913609 / 1000000000000) (-8577913398 / 1000000000000)
      | 1 => orderedInterval (7915454902 / 1000000000000) (7915455212 / 1000000000000)
      | 2 => orderedInterval (-7985368842 / 1000000000000) (-7985368704 / 1000000000000)
      | 3 => orderedInterval (8522907640 / 1000000000000) (8522908627 / 1000000000000)
      | 4 => orderedInterval (2889461939 / 1000000000000) (2889462169 / 1000000000000)
      | 5 => orderedInterval (-2317985987 / 1000000000000) (-2317984720 / 1000000000000)
      | 6 => orderedInterval (6819044219 / 1000000000000) (6819044268 / 1000000000000)
      | 7 => orderedInterval (4814139965 / 1000000000000) (4814140051 / 1000000000000)
      | _ => orderedInterval (-19056456024 / 1000000000000) (-19056448346 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (18180005645 / 1000000000000) (18180005896 / 1000000000000)
      | 1 => orderedInterval (-13959379936 / 1000000000000) (-13959379695 / 1000000000000)
      | 2 => orderedInterval (11660513647 / 1000000000000) (11660513876 / 1000000000000)
      | 3 => orderedInterval (77135185174 / 1000000000000) (77135187244 / 1000000000000)
      | 4 => orderedInterval (-35145259746 / 1000000000000) (-35145259334 / 1000000000000)
      | 5 => orderedInterval (2942589370 / 1000000000000) (2942591052 / 1000000000000)
      | 6 => orderedInterval (-442423677 / 1000000000000) (-442423629 / 1000000000000)
      | 7 => orderedInterval (-2705084843 / 1000000000000) (-2705084788 / 1000000000000)
      | _ => orderedInterval (-5394048117 / 1000000000000) (-5394033857 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (28583920581 / 1000000000000) (28583925791 / 1000000000000)
    | 1 => orderedInterval (-2643020897 / 1000000000000) (-2643016023 / 1000000000000)
    | 2 => orderedInterval (-28698955834 / 1000000000000) (-28698949118 / 1000000000000)
    | 3 => orderedInterval (-6976715797 / 1000000000000) (-6976704841 / 1000000000000)
    | _ => orderedInterval (52272097517 / 1000000000000) (52272116765 / 1000000000000)

theorem compactCertificate349_stateChecks0 :
    compactCertificate349.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (441 / 2)) (orderedInterval (52688245589 / 1000000000000) (52688245593 / 1000000000000), orderedInterval (10421229421 / 1000000000000) (10421229425 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (649677208024341 / 4000000000000)) (orderedInterval (-9905601753 / 1000000000000) (-9905601706 / 1000000000000), orderedInterval (61848802563 / 1000000000000) (61848802609 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (210092260614453 / 800000000000)) (orderedInterval (-23324991109 / 1000000000000) (-23324989247 / 1000000000000), orderedInterval (43404532636 / 1000000000000) (43404534498 / 1000000000000))) = true
  rfl'

theorem compactCertificate349_stateChecks1 :
    compactCertificate349.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (189574188983487 / 4000000000000)) (orderedInterval (-100670051419 / 1000000000000) (-100670051418 / 1000000000000), orderedInterval (-56364406422 / 1000000000000) (-56364406421 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (509222937425139 / 4000000000000)) (orderedInterval (46370181675 / 1000000000000) (46370216584 / 1000000000000), orderedInterval (-53572448554 / 1000000000000) (-53572413644 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1382639333077863 / 4000000000000)) (orderedInterval (32792734217 / 1000000000000) (32792734218 / 1000000000000), orderedInterval (27636287770 / 1000000000000) (27636287771 / 1000000000000))) = true
  rfl'

theorem compactCertificate349_stateChecks2 :
    compactCertificate349.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1018445874850719 / 4000000000000)) (orderedInterval (-40005097111 / 1000000000000) (-40005097110 / 1000000000000), orderedInterval (-29920583507 / 1000000000000) (-29920583506 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1745124365410587 / 4000000000000)) (orderedInterval (-14339914021 / 1000000000000) (-14339914020 / 1000000000000), orderedInterval (-35389270042 / 1000000000000) (-35389270041 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1285450709041233 / 4000000000000)) (orderedInterval (44106793183 / 1000000000000) (44106794086 / 1000000000000), orderedInterval (-6034310373 / 1000000000000) (-6034309470 / 1000000000000))) = true
  rfl'

theorem compactCertificate349_stateChecks3 :
    compactCertificate349.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1972211956154559 / 4000000000000)) (orderedInterval (-20528452922 / 1000000000000) (-20528452921 / 1000000000000), orderedInterval (-29470911139 / 1000000000000) (-29470911138 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1138657103784711 / 4000000000000)) (orderedInterval (19958542214 / 1000000000000) (19958543045 / 1000000000000), orderedInterval (-42907504630 / 1000000000000) (-42907503800 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2020567012189299 / 4000000000000)) (orderedInterval (-4619190366 / 1000000000000) (-4619190365 / 1000000000000), orderedInterval (-35194051813 / 1000000000000) (-35194051812 / 1000000000000))) = true
  rfl'

theorem compactCertificate349_stateChecks4 :
    compactCertificate349.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1887875803846431 / 4000000000000)) (orderedInterval (36670037453 / 1000000000000) (36670037667 / 1000000000000), orderedInterval (2002481841 / 1000000000000) (2002482056 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1347277254316623 / 4000000000000)) (orderedInterval (-43178608729 / 1000000000000) (-43178608695 / 1000000000000), orderedInterval (-5005277479 / 1000000000000) (-5005277445 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1527668812275417 / 4000000000000)) (orderedInterval (-22101678962 / 1000000000000) (-22101676679 / 1000000000000), orderedInterval (34357080258 / 1000000000000) (34357082541 / 1000000000000))) = true
  rfl'

theorem compactCertificate349_stateChecks5 :
    compactCertificate349.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1273610988195273 / 4000000000000)) (orderedInterval (-42499442080 / 1000000000000) (-42499435413 / 1000000000000), orderedInterval (13966821808 / 1000000000000) (13966828475 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1125273932816733 / 4000000000000)) (orderedInterval (-28405329761 / 1000000000000) (-28405321685 / 1000000000000), orderedInterval (38209680230 / 1000000000000) (38209688307 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (326148245388567 / 800000000000)) (orderedInterval (2501820927 / 1000000000000) (2501820928 / 1000000000000), orderedInterval (39434085083 / 1000000000000) (39434085084 / 1000000000000))) = true
  rfl'

theorem compactCertificate349_stateChecks6 :
    compactCertificate349.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (902143210986549 / 4000000000000)) (orderedInterval (6675272261 / 1000000000000) (6675272262 / 1000000000000), orderedInterval (52693330212 / 1000000000000) (52693330213 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (764756790915789 / 4000000000000)) (orderedInterval (-19068902268 / 1000000000000) (-19068902267 / 1000000000000), orderedInterval (-54412735837 / 1000000000000) (-54412735836 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (478549290958767 / 4000000000000)) (orderedInterval (62952041660 / 1000000000000) (62952041661 / 1000000000000), orderedInterval (36591555333 / 1000000000000) (36591555334 / 1000000000000))) = true
  rfl'

theorem compactCertificate349_stateChecks7 :
    compactCertificate349.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (257365400260689 / 4000000000000)) (orderedInterval (74639829740 / 1000000000000) (74639918757 / 1000000000000), orderedInterval (-66331555571 / 1000000000000) (-66331466554 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (698797126409067 / 4000000000000)) (orderedInterval (-25997316747 / 1000000000000) (-25997314967 / 1000000000000), orderedInterval (54555944316 / 1000000000000) (54555946095 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (954147734107659 / 4000000000000)) (orderedInterval (27475063930 / 1000000000000) (27475063931 / 1000000000000), orderedInterval (43691414123 / 1000000000000) (43691414124 / 1000000000000))) = true
  rfl'

theorem compactCertificate349_stateChecks8 :
    compactCertificate349.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (403450709041233 / 4000000000000)) (orderedInterval (71365880152 / 1000000000000) (71365880153 / 1000000000000), orderedInterval (34554844262 / 1000000000000) (34554844263 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1640004733338993 / 4000000000000)) (orderedInterval (27214051831 / 1000000000000) (27214066092 / 1000000000000), orderedInterval (-28530943856 / 1000000000000) (-28530929595 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1095447157386687 / 4000000000000)) (orderedInterval (-46801918745 / 1000000000000) (-46801918742 / 1000000000000), orderedInterval (-11498134286 / 1000000000000) (-11498134283 / 1000000000000))) = true
  rfl'

theorem compactCertificate349_states : ∀ j,
    BesselStateValid (compactCertificate349.point j) (compactCertificate349.state j) :=
  compactCertificate349.statesValid_of_checks3 compactCertificate349_stateChecks0
    compactCertificate349_stateChecks1 compactCertificate349_stateChecks2
    compactCertificate349_stateChecks3 compactCertificate349_stateChecks4
    compactCertificate349_stateChecks5 compactCertificate349_stateChecks6
    compactCertificate349_stateChecks7 compactCertificate349_stateChecks8

theorem compactCertificate349_chunkChecks0_0 :
    compactCertificate349.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (441 / 2) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (52688245589 / 1000000000000) (52688245593 / 1000000000000), orderedInterval (10421229421 / 1000000000000) (10421229425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (649677208024341 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-9905601753 / 1000000000000) (-9905601706 / 1000000000000), orderedInterval (61848802563 / 1000000000000) (61848802609 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (210092260614453 / 800000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23324991109 / 1000000000000) (-23324989247 / 1000000000000), orderedInterval (43404532636 / 1000000000000) (43404534498 / 1000000000000)))) (orderedInterval (19422738026 / 1000000000000) (19422738153 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (189574188983487 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-100670051419 / 1000000000000) (-100670051418 / 1000000000000), orderedInterval (-56364406422 / 1000000000000) (-56364406421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (509222937425139 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46370181675 / 1000000000000) (46370216584 / 1000000000000), orderedInterval (-53572448554 / 1000000000000) (-53572413644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1382639333077863 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (32792734217 / 1000000000000) (32792734218 / 1000000000000), orderedInterval (27636287770 / 1000000000000) (27636287771 / 1000000000000)))) (orderedInterval (454031262 / 1000000000000) (454032563 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1018445874850719 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-40005097111 / 1000000000000) (-40005097110 / 1000000000000), orderedInterval (-29920583507 / 1000000000000) (-29920583506 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1745124365410587 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-14339914021 / 1000000000000) (-14339914020 / 1000000000000), orderedInterval (-35389270042 / 1000000000000) (-35389270041 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1285450709041233 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (44106793183 / 1000000000000) (44106794086 / 1000000000000), orderedInterval (-6034310373 / 1000000000000) (-6034309470 / 1000000000000)))) (orderedInterval (1508274484 / 1000000000000) (1508274519 / 1000000000000))) = true
  rfl'

theorem compactCertificate349_chunkChecks0_1 :
    compactCertificate349.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1972211956154559 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20528452922 / 1000000000000) (-20528452921 / 1000000000000), orderedInterval (-29470911139 / 1000000000000) (-29470911138 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1138657103784711 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19958542214 / 1000000000000) (19958543045 / 1000000000000), orderedInterval (-42907504630 / 1000000000000) (-42907503800 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2020567012189299 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4619190366 / 1000000000000) (-4619190365 / 1000000000000), orderedInterval (-35194051813 / 1000000000000) (-35194051812 / 1000000000000)))) (orderedInterval (4469776792 / 1000000000000) (4469776942 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1887875803846431 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36670037453 / 1000000000000) (36670037667 / 1000000000000), orderedInterval (2002481841 / 1000000000000) (2002482056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1347277254316623 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43178608729 / 1000000000000) (-43178608695 / 1000000000000), orderedInterval (-5005277479 / 1000000000000) (-5005277445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1527668812275417 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22101678962 / 1000000000000) (-22101676679 / 1000000000000), orderedInterval (34357080258 / 1000000000000) (34357082541 / 1000000000000)))) (orderedInterval (-4633253134 / 1000000000000) (-4633253088 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1273610988195273 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42499442080 / 1000000000000) (-42499435413 / 1000000000000), orderedInterval (13966821808 / 1000000000000) (13966828475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1125273932816733 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28405329761 / 1000000000000) (-28405321685 / 1000000000000), orderedInterval (38209680230 / 1000000000000) (38209688307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (326148245388567 / 800000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (2501820927 / 1000000000000) (2501820928 / 1000000000000), orderedInterval (39434085083 / 1000000000000) (39434085084 / 1000000000000)))) (orderedInterval (1198829124 / 1000000000000) (1198829685 / 1000000000000))) = true
  rfl'

theorem compactCertificate349_chunkChecks0_2 :
    compactCertificate349.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (902143210986549 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (6675272261 / 1000000000000) (6675272262 / 1000000000000), orderedInterval (52693330212 / 1000000000000) (52693330213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (764756790915789 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-19068902268 / 1000000000000) (-19068902267 / 1000000000000), orderedInterval (-54412735837 / 1000000000000) (-54412735836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (478549290958767 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62952041660 / 1000000000000) (62952041661 / 1000000000000), orderedInterval (36591555333 / 1000000000000) (36591555334 / 1000000000000)))) (orderedInterval (2061394195 / 1000000000000) (2061394251 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (257365400260689 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74639829740 / 1000000000000) (74639918757 / 1000000000000), orderedInterval (-66331555571 / 1000000000000) (-66331466554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (698797126409067 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-25997316747 / 1000000000000) (-25997314967 / 1000000000000), orderedInterval (54555944316 / 1000000000000) (54555946095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (954147734107659 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (27475063930 / 1000000000000) (27475063931 / 1000000000000), orderedInterval (43691414123 / 1000000000000) (43691414124 / 1000000000000)))) (orderedInterval (-2894095202 / 1000000000000) (-2894093491 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (403450709041233 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (71365880152 / 1000000000000) (71365880153 / 1000000000000), orderedInterval (34554844262 / 1000000000000) (34554844263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1640004733338993 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27214051831 / 1000000000000) (27214066092 / 1000000000000), orderedInterval (-28530943856 / 1000000000000) (-28530929595 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1095447157386687 / 4000000000000) 0 (IntervalRat.scale (441 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-46801918745 / 1000000000000) (-46801918742 / 1000000000000), orderedInterval (-11498134286 / 1000000000000) (-11498134283 / 1000000000000)))) (orderedInterval (6996225034 / 1000000000000) (6996226257 / 1000000000000))) = true
  rfl'

theorem compactCertificate349_chunkChecks0 :
    compactCertificate349.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate349.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate349_chunkChecks0_0
    compactCertificate349_chunkChecks0_1 compactCertificate349_chunkChecks0_2

theorem compactCertificate349_chunkChecks1_0 :
    compactCertificate349.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (441 / 2) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (52688245589 / 1000000000000) (52688245593 / 1000000000000), orderedInterval (10421229421 / 1000000000000) (10421229425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (649677208024341 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-9905601753 / 1000000000000) (-9905601706 / 1000000000000), orderedInterval (61848802563 / 1000000000000) (61848802609 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (210092260614453 / 800000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23324991109 / 1000000000000) (-23324989247 / 1000000000000), orderedInterval (43404532636 / 1000000000000) (43404534498 / 1000000000000)))) (orderedInterval (7588626171 / 1000000000000) (7588626321 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (189574188983487 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-100670051419 / 1000000000000) (-100670051418 / 1000000000000), orderedInterval (-56364406422 / 1000000000000) (-56364406421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (509222937425139 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46370181675 / 1000000000000) (46370216584 / 1000000000000), orderedInterval (-53572448554 / 1000000000000) (-53572413644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1382639333077863 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (32792734217 / 1000000000000) (32792734218 / 1000000000000), orderedInterval (27636287770 / 1000000000000) (27636287771 / 1000000000000)))) (orderedInterval (-4077701201 / 1000000000000) (-4077700434 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1018445874850719 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-40005097111 / 1000000000000) (-40005097110 / 1000000000000), orderedInterval (-29920583507 / 1000000000000) (-29920583506 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1745124365410587 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-14339914021 / 1000000000000) (-14339914020 / 1000000000000), orderedInterval (-35389270042 / 1000000000000) (-35389270041 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1285450709041233 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (44106793183 / 1000000000000) (44106794086 / 1000000000000), orderedInterval (-6034310373 / 1000000000000) (-6034309470 / 1000000000000)))) (orderedInterval (1947185873 / 1000000000000) (1947185927 / 1000000000000))) = true
  rfl'

theorem compactCertificate349_chunkChecks1_1 :
    compactCertificate349.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1972211956154559 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20528452922 / 1000000000000) (-20528452921 / 1000000000000), orderedInterval (-29470911139 / 1000000000000) (-29470911138 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1138657103784711 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19958542214 / 1000000000000) (19958543045 / 1000000000000), orderedInterval (-42907504630 / 1000000000000) (-42907503800 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2020567012189299 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4619190366 / 1000000000000) (-4619190365 / 1000000000000), orderedInterval (-35194051813 / 1000000000000) (-35194051812 / 1000000000000)))) (orderedInterval (-3856171891 / 1000000000000) (-3856171630 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1887875803846431 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36670037453 / 1000000000000) (36670037667 / 1000000000000), orderedInterval (2002481841 / 1000000000000) (2002482056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1347277254316623 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43178608729 / 1000000000000) (-43178608695 / 1000000000000), orderedInterval (-5005277479 / 1000000000000) (-5005277445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1527668812275417 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22101678962 / 1000000000000) (-22101676679 / 1000000000000), orderedInterval (34357080258 / 1000000000000) (34357082541 / 1000000000000)))) (orderedInterval (-1101523312 / 1000000000000) (-1101523235 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1273610988195273 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42499442080 / 1000000000000) (-42499435413 / 1000000000000), orderedInterval (13966821808 / 1000000000000) (13966828475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1125273932816733 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28405329761 / 1000000000000) (-28405321685 / 1000000000000), orderedInterval (38209680230 / 1000000000000) (38209688307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (326148245388567 / 800000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (2501820927 / 1000000000000) (2501820928 / 1000000000000), orderedInterval (39434085083 / 1000000000000) (39434085084 / 1000000000000)))) (orderedInterval (-690043075 / 1000000000000) (-690042343 / 1000000000000))) = true
  rfl'

theorem compactCertificate349_chunkChecks1_2 :
    compactCertificate349.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (902143210986549 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (6675272261 / 1000000000000) (6675272262 / 1000000000000), orderedInterval (52693330212 / 1000000000000) (52693330213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (764756790915789 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-19068902268 / 1000000000000) (-19068902267 / 1000000000000), orderedInterval (-54412735837 / 1000000000000) (-54412735836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (478549290958767 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62952041660 / 1000000000000) (62952041661 / 1000000000000), orderedInterval (36591555333 / 1000000000000) (36591555334 / 1000000000000)))) (orderedInterval (-5300973681 / 1000000000000) (-5300973629 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (257365400260689 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74639829740 / 1000000000000) (74639918757 / 1000000000000), orderedInterval (-66331555571 / 1000000000000) (-66331466554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (698797126409067 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-25997316747 / 1000000000000) (-25997314967 / 1000000000000), orderedInterval (54555944316 / 1000000000000) (54555946095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (954147734107659 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (27475063930 / 1000000000000) (27475063931 / 1000000000000), orderedInterval (43691414123 / 1000000000000) (43691414124 / 1000000000000)))) (orderedInterval (-4245582444 / 1000000000000) (-4245581908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (403450709041233 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (71365880152 / 1000000000000) (71365880153 / 1000000000000), orderedInterval (34554844262 / 1000000000000) (34554844263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1640004733338993 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27214051831 / 1000000000000) (27214066092 / 1000000000000), orderedInterval (-28530943856 / 1000000000000) (-28530929595 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1095447157386687 / 4000000000000) 1 (IntervalRat.scale (441 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-46801918745 / 1000000000000) (-46801918742 / 1000000000000), orderedInterval (-11498134286 / 1000000000000) (-11498134283 / 1000000000000)))) (orderedInterval (7093162663 / 1000000000000) (7093164908 / 1000000000000))) = true
  rfl'

theorem compactCertificate349_chunkChecks1 :
    compactCertificate349.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate349.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate349_chunkChecks1_0
    compactCertificate349_chunkChecks1_1 compactCertificate349_chunkChecks1_2

theorem compactCertificate349_chunkChecks2_0 :
    compactCertificate349.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (441 / 2) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (52688245589 / 1000000000000) (52688245593 / 1000000000000), orderedInterval (10421229421 / 1000000000000) (10421229425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (649677208024341 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-9905601753 / 1000000000000) (-9905601706 / 1000000000000), orderedInterval (61848802563 / 1000000000000) (61848802609 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (210092260614453 / 800000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23324991109 / 1000000000000) (-23324989247 / 1000000000000), orderedInterval (43404532636 / 1000000000000) (43404534498 / 1000000000000)))) (orderedInterval (-18926586834 / 1000000000000) (-18926586656 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (189574188983487 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-100670051419 / 1000000000000) (-100670051418 / 1000000000000), orderedInterval (-56364406422 / 1000000000000) (-56364406421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (509222937425139 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46370181675 / 1000000000000) (46370216584 / 1000000000000), orderedInterval (-53572448554 / 1000000000000) (-53572413644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1382639333077863 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (32792734217 / 1000000000000) (32792734218 / 1000000000000), orderedInterval (27636287770 / 1000000000000) (27636287771 / 1000000000000)))) (orderedInterval (5132495579 / 1000000000000) (5132496050 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1018445874850719 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-40005097111 / 1000000000000) (-40005097110 / 1000000000000), orderedInterval (-29920583507 / 1000000000000) (-29920583506 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1745124365410587 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-14339914021 / 1000000000000) (-14339914020 / 1000000000000), orderedInterval (-35389270042 / 1000000000000) (-35389270041 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1285450709041233 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (44106793183 / 1000000000000) (44106794086 / 1000000000000), orderedInterval (-6034310373 / 1000000000000) (-6034309470 / 1000000000000)))) (orderedInterval (-4004601218 / 1000000000000) (-4004601132 / 1000000000000))) = true
  rfl'

theorem compactCertificate349_chunkChecks2_1 :
    compactCertificate349.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1972211956154559 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20528452922 / 1000000000000) (-20528452921 / 1000000000000), orderedInterval (-29470911139 / 1000000000000) (-29470911138 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1138657103784711 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19958542214 / 1000000000000) (19958543045 / 1000000000000), orderedInterval (-42907504630 / 1000000000000) (-42907503800 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2020567012189299 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4619190366 / 1000000000000) (-4619190365 / 1000000000000), orderedInterval (-35194051813 / 1000000000000) (-35194051812 / 1000000000000)))) (orderedInterval (-17239212563 / 1000000000000) (-17239212069 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1887875803846431 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36670037453 / 1000000000000) (36670037667 / 1000000000000), orderedInterval (2002481841 / 1000000000000) (2002482056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1347277254316623 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43178608729 / 1000000000000) (-43178608695 / 1000000000000), orderedInterval (-5005277479 / 1000000000000) (-5005277445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1527668812275417 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22101678962 / 1000000000000) (-22101676679 / 1000000000000), orderedInterval (34357080258 / 1000000000000) (34357082541 / 1000000000000)))) (orderedInterval (12229671280 / 1000000000000) (12229671411 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1273610988195273 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42499442080 / 1000000000000) (-42499435413 / 1000000000000), orderedInterval (13966821808 / 1000000000000) (13966828475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1125273932816733 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28405329761 / 1000000000000) (-28405321685 / 1000000000000), orderedInterval (38209680230 / 1000000000000) (38209688307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (326148245388567 / 800000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (2501820927 / 1000000000000) (2501820928 / 1000000000000), orderedInterval (39434085083 / 1000000000000) (39434085084 / 1000000000000)))) (orderedInterval (-1838446620 / 1000000000000) (-1838445658 / 1000000000000))) = true
  rfl'

theorem compactCertificate349_chunkChecks2_2 :
    compactCertificate349.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (902143210986549 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (6675272261 / 1000000000000) (6675272262 / 1000000000000), orderedInterval (52693330212 / 1000000000000) (52693330213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (764756790915789 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-19068902268 / 1000000000000) (-19068902267 / 1000000000000), orderedInterval (-54412735837 / 1000000000000) (-54412735836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (478549290958767 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62952041660 / 1000000000000) (62952041661 / 1000000000000), orderedInterval (36591555333 / 1000000000000) (36591555334 / 1000000000000)))) (orderedInterval (-274075545 / 1000000000000) (-274075495 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (257365400260689 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74639829740 / 1000000000000) (74639918757 / 1000000000000), orderedInterval (-66331555571 / 1000000000000) (-66331466554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (698797126409067 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-25997316747 / 1000000000000) (-25997314967 / 1000000000000), orderedInterval (54555944316 / 1000000000000) (54555946095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (954147734107659 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (27475063930 / 1000000000000) (27475063931 / 1000000000000), orderedInterval (43691414123 / 1000000000000) (43691414124 / 1000000000000)))) (orderedInterval (2230611776 / 1000000000000) (2230611968 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (403450709041233 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (71365880152 / 1000000000000) (71365880153 / 1000000000000), orderedInterval (34554844262 / 1000000000000) (34554844263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1640004733338993 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27214051831 / 1000000000000) (27214066092 / 1000000000000), orderedInterval (-28530943856 / 1000000000000) (-28530929595 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1095447157386687 / 4000000000000) 2 (IntervalRat.scale (441 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-46801918745 / 1000000000000) (-46801918742 / 1000000000000), orderedInterval (-11498134286 / 1000000000000) (-11498134283 / 1000000000000)))) (orderedInterval (-6008811689 / 1000000000000) (-6008807537 / 1000000000000))) = true
  rfl'

theorem compactCertificate349_chunkChecks2 :
    compactCertificate349.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate349.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate349_chunkChecks2_0
    compactCertificate349_chunkChecks2_1 compactCertificate349_chunkChecks2_2

theorem compactCertificate349_chunkChecks3_0 :
    compactCertificate349.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (441 / 2) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (52688245589 / 1000000000000) (52688245593 / 1000000000000), orderedInterval (10421229421 / 1000000000000) (10421229425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (649677208024341 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-9905601753 / 1000000000000) (-9905601706 / 1000000000000), orderedInterval (61848802563 / 1000000000000) (61848802609 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (210092260614453 / 800000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23324991109 / 1000000000000) (-23324989247 / 1000000000000), orderedInterval (43404532636 / 1000000000000) (43404534498 / 1000000000000)))) (orderedInterval (-8577913609 / 1000000000000) (-8577913398 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (189574188983487 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-100670051419 / 1000000000000) (-100670051418 / 1000000000000), orderedInterval (-56364406422 / 1000000000000) (-56364406421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (509222937425139 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46370181675 / 1000000000000) (46370216584 / 1000000000000), orderedInterval (-53572448554 / 1000000000000) (-53572413644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1382639333077863 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (32792734217 / 1000000000000) (32792734218 / 1000000000000), orderedInterval (27636287770 / 1000000000000) (27636287771 / 1000000000000)))) (orderedInterval (7915454902 / 1000000000000) (7915455212 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1018445874850719 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-40005097111 / 1000000000000) (-40005097110 / 1000000000000), orderedInterval (-29920583507 / 1000000000000) (-29920583506 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1745124365410587 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-14339914021 / 1000000000000) (-14339914020 / 1000000000000), orderedInterval (-35389270042 / 1000000000000) (-35389270041 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1285450709041233 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (44106793183 / 1000000000000) (44106794086 / 1000000000000), orderedInterval (-6034310373 / 1000000000000) (-6034309470 / 1000000000000)))) (orderedInterval (-7985368842 / 1000000000000) (-7985368704 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate349_chunkChecks3_1 :
    compactCertificate349.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1972211956154559 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20528452922 / 1000000000000) (-20528452921 / 1000000000000), orderedInterval (-29470911139 / 1000000000000) (-29470911138 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1138657103784711 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19958542214 / 1000000000000) (19958543045 / 1000000000000), orderedInterval (-42907504630 / 1000000000000) (-42907503800 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2020567012189299 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4619190366 / 1000000000000) (-4619190365 / 1000000000000), orderedInterval (-35194051813 / 1000000000000) (-35194051812 / 1000000000000)))) (orderedInterval (8522907640 / 1000000000000) (8522908627 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1887875803846431 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36670037453 / 1000000000000) (36670037667 / 1000000000000), orderedInterval (2002481841 / 1000000000000) (2002482056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1347277254316623 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43178608729 / 1000000000000) (-43178608695 / 1000000000000), orderedInterval (-5005277479 / 1000000000000) (-5005277445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1527668812275417 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22101678962 / 1000000000000) (-22101676679 / 1000000000000), orderedInterval (34357080258 / 1000000000000) (34357082541 / 1000000000000)))) (orderedInterval (2889461939 / 1000000000000) (2889462169 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1273610988195273 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42499442080 / 1000000000000) (-42499435413 / 1000000000000), orderedInterval (13966821808 / 1000000000000) (13966828475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1125273932816733 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28405329761 / 1000000000000) (-28405321685 / 1000000000000), orderedInterval (38209680230 / 1000000000000) (38209688307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (326148245388567 / 800000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (2501820927 / 1000000000000) (2501820928 / 1000000000000), orderedInterval (39434085083 / 1000000000000) (39434085084 / 1000000000000)))) (orderedInterval (-2317985987 / 1000000000000) (-2317984720 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate349_chunkChecks3_2 :
    compactCertificate349.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (902143210986549 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (6675272261 / 1000000000000) (6675272262 / 1000000000000), orderedInterval (52693330212 / 1000000000000) (52693330213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (764756790915789 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-19068902268 / 1000000000000) (-19068902267 / 1000000000000), orderedInterval (-54412735837 / 1000000000000) (-54412735836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (478549290958767 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62952041660 / 1000000000000) (62952041661 / 1000000000000), orderedInterval (36591555333 / 1000000000000) (36591555334 / 1000000000000)))) (orderedInterval (6819044219 / 1000000000000) (6819044268 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (257365400260689 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74639829740 / 1000000000000) (74639918757 / 1000000000000), orderedInterval (-66331555571 / 1000000000000) (-66331466554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (698797126409067 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-25997316747 / 1000000000000) (-25997314967 / 1000000000000), orderedInterval (54555944316 / 1000000000000) (54555946095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (954147734107659 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (27475063930 / 1000000000000) (27475063931 / 1000000000000), orderedInterval (43691414123 / 1000000000000) (43691414124 / 1000000000000)))) (orderedInterval (4814139965 / 1000000000000) (4814140051 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (403450709041233 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (71365880152 / 1000000000000) (71365880153 / 1000000000000), orderedInterval (34554844262 / 1000000000000) (34554844263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1640004733338993 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27214051831 / 1000000000000) (27214066092 / 1000000000000), orderedInterval (-28530943856 / 1000000000000) (-28530929595 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1095447157386687 / 4000000000000) 3 (IntervalRat.scale (441 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-46801918745 / 1000000000000) (-46801918742 / 1000000000000), orderedInterval (-11498134286 / 1000000000000) (-11498134283 / 1000000000000)))) (orderedInterval (-19056456024 / 1000000000000) (-19056448346 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate349_chunkChecks3 :
    compactCertificate349.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate349.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate349_chunkChecks3_0
    compactCertificate349_chunkChecks3_1 compactCertificate349_chunkChecks3_2

theorem compactCertificate349_chunkChecks4_0 :
    compactCertificate349.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (441 / 2) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (52688245589 / 1000000000000) (52688245593 / 1000000000000), orderedInterval (10421229421 / 1000000000000) (10421229425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (649677208024341 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-9905601753 / 1000000000000) (-9905601706 / 1000000000000), orderedInterval (61848802563 / 1000000000000) (61848802609 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (210092260614453 / 800000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23324991109 / 1000000000000) (-23324989247 / 1000000000000), orderedInterval (43404532636 / 1000000000000) (43404534498 / 1000000000000)))) (orderedInterval (18180005645 / 1000000000000) (18180005896 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (189574188983487 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-100670051419 / 1000000000000) (-100670051418 / 1000000000000), orderedInterval (-56364406422 / 1000000000000) (-56364406421 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (509222937425139 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46370181675 / 1000000000000) (46370216584 / 1000000000000), orderedInterval (-53572448554 / 1000000000000) (-53572413644 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1382639333077863 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (32792734217 / 1000000000000) (32792734218 / 1000000000000), orderedInterval (27636287770 / 1000000000000) (27636287771 / 1000000000000)))) (orderedInterval (-13959379936 / 1000000000000) (-13959379695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1018445874850719 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-40005097111 / 1000000000000) (-40005097110 / 1000000000000), orderedInterval (-29920583507 / 1000000000000) (-29920583506 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1745124365410587 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-14339914021 / 1000000000000) (-14339914020 / 1000000000000), orderedInterval (-35389270042 / 1000000000000) (-35389270041 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1285450709041233 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (44106793183 / 1000000000000) (44106794086 / 1000000000000), orderedInterval (-6034310373 / 1000000000000) (-6034309470 / 1000000000000)))) (orderedInterval (11660513647 / 1000000000000) (11660513876 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate349_chunkChecks4_1 :
    compactCertificate349.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1972211956154559 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20528452922 / 1000000000000) (-20528452921 / 1000000000000), orderedInterval (-29470911139 / 1000000000000) (-29470911138 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1138657103784711 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19958542214 / 1000000000000) (19958543045 / 1000000000000), orderedInterval (-42907504630 / 1000000000000) (-42907503800 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2020567012189299 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4619190366 / 1000000000000) (-4619190365 / 1000000000000), orderedInterval (-35194051813 / 1000000000000) (-35194051812 / 1000000000000)))) (orderedInterval (77135185174 / 1000000000000) (77135187244 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1887875803846431 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36670037453 / 1000000000000) (36670037667 / 1000000000000), orderedInterval (2002481841 / 1000000000000) (2002482056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1347277254316623 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43178608729 / 1000000000000) (-43178608695 / 1000000000000), orderedInterval (-5005277479 / 1000000000000) (-5005277445 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1527668812275417 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22101678962 / 1000000000000) (-22101676679 / 1000000000000), orderedInterval (34357080258 / 1000000000000) (34357082541 / 1000000000000)))) (orderedInterval (-35145259746 / 1000000000000) (-35145259334 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1273610988195273 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42499442080 / 1000000000000) (-42499435413 / 1000000000000), orderedInterval (13966821808 / 1000000000000) (13966828475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1125273932816733 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28405329761 / 1000000000000) (-28405321685 / 1000000000000), orderedInterval (38209680230 / 1000000000000) (38209688307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (326148245388567 / 800000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (2501820927 / 1000000000000) (2501820928 / 1000000000000), orderedInterval (39434085083 / 1000000000000) (39434085084 / 1000000000000)))) (orderedInterval (2942589370 / 1000000000000) (2942591052 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate349_chunkChecks4_2 :
    compactCertificate349.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (902143210986549 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (6675272261 / 1000000000000) (6675272262 / 1000000000000), orderedInterval (52693330212 / 1000000000000) (52693330213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (764756790915789 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-19068902268 / 1000000000000) (-19068902267 / 1000000000000), orderedInterval (-54412735837 / 1000000000000) (-54412735836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (478549290958767 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62952041660 / 1000000000000) (62952041661 / 1000000000000), orderedInterval (36591555333 / 1000000000000) (36591555334 / 1000000000000)))) (orderedInterval (-442423677 / 1000000000000) (-442423629 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (257365400260689 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74639829740 / 1000000000000) (74639918757 / 1000000000000), orderedInterval (-66331555571 / 1000000000000) (-66331466554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (698797126409067 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-25997316747 / 1000000000000) (-25997314967 / 1000000000000), orderedInterval (54555944316 / 1000000000000) (54555946095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (954147734107659 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (27475063930 / 1000000000000) (27475063931 / 1000000000000), orderedInterval (43691414123 / 1000000000000) (43691414124 / 1000000000000)))) (orderedInterval (-2705084843 / 1000000000000) (-2705084788 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (403450709041233 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (71365880152 / 1000000000000) (71365880153 / 1000000000000), orderedInterval (34554844262 / 1000000000000) (34554844263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1640004733338993 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27214051831 / 1000000000000) (27214066092 / 1000000000000), orderedInterval (-28530943856 / 1000000000000) (-28530929595 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1095447157386687 / 4000000000000) 4 (IntervalRat.scale (441 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-46801918745 / 1000000000000) (-46801918742 / 1000000000000), orderedInterval (-11498134286 / 1000000000000) (-11498134283 / 1000000000000)))) (orderedInterval (-5394048117 / 1000000000000) (-5394033857 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate349_chunkChecks4 :
    compactCertificate349.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate349.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate349_chunkChecks4_0
    compactCertificate349_chunkChecks4_1 compactCertificate349_chunkChecks4_2

theorem compactCertificate349_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate349.chunkCheck r b = true :=
  compactCertificate349.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate349_chunkChecks0
    · exact compactCertificate349_chunkChecks1
    · exact compactCertificate349_chunkChecks2
    · exact compactCertificate349_chunkChecks3
    · exact compactCertificate349_chunkChecks4)

theorem compactCertificate349_coefficient0 :
    compactCertificate349.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate349_coefficient1 :
    compactCertificate349.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate349_coefficient2 :
    compactCertificate349.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate349_coefficient3 :
    compactCertificate349.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate349_coefficient4 :
    compactCertificate349.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate349_coefficients : ∀ r : Fin 5,
    compactCertificate349.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate349_coefficient0
  · exact compactCertificate349_coefficient1
  · exact compactCertificate349_coefficient2
  · exact compactCertificate349_coefficient3
  · exact compactCertificate349_coefficient4

theorem compactCertificate349_lower : (1 : ℚ) ≤ compactCertificate349.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate349, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate349_proves {t : ℝ} (ht : t ∈ compactCertificate349.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate349.proves compactCertificate349_states compactCertificate349_chunks
    compactCertificate349_coefficients compactCertificate349_lower ht

end Erdos232
