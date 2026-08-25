/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate508 : CompactCertificate where
  left := 379
  right := 380
  center := 759 / 2
  grid := fun i =>
    match i.val with
    | 0 => 121
    | 1 => 89
    | 2 => 144
    | 3 => 26
    | 4 => 70
    | 5 => 189
    | 6 => 140
    | 7 => 239
    | 8 => 176
    | 9 => 270
    | 10 => 156
    | 11 => 277
    | 12 => 259
    | 13 => 185
    | 14 => 209
    | 15 => 175
    | 16 => 154
    | 17 => 223
    | 18 => 124
    | 19 => 105
    | 20 => 66
    | 21 => 35
    | 22 => 96
    | 23 => 131
    | 24 => 55
    | 25 => 225
    | _ => 150
  point := fun i =>
    match i.val with
    | 0 => 759 / 2
    | 1 => 1118151929456859 / 4000000000000
    | 2 => 361587360105147 / 800000000000
    | 3 => 326273944304913 / 4000000000000
    | 4 => 876417708629661 / 4000000000000
    | 5 => 2379644566453737 / 4000000000000
    | 6 => 1752835417260081 / 4000000000000
    | 7 => 3003513363597813 / 4000000000000
    | 8 => 2212374349574367 / 4000000000000
    | 9 => 3394351189844241 / 4000000000000
    | 10 => 1959729573180489 / 4000000000000
    | 11 => 3477574517577501 / 4000000000000
    | 12 => 3249201213422769 / 4000000000000
    | 13 => 2318783301646977 / 4000000000000
    | 14 => 2629253125888983 / 4000000000000
    | 15 => 2191997142948327 / 4000000000000
    | 16 => 1936695952398867 / 4000000000000
    | 17 => 561329973355833 / 800000000000
    | 18 => 1552668247480251 / 4000000000000
    | 19 => 1316214068719011 / 4000000000000
    | 20 => 823625650425633 / 4000000000000
    | 21 => 442948614054111 / 4000000000000
    | 22 => 1202691652935333 / 4000000000000
    | 23 => 1642172630811141 / 4000000000000
    | 24 => 694374349574367 / 4000000000000
    | 25 => 2822593180508607 / 4000000000000
    | _ => 1885361434141713 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-6216084132 / 1000000000000) (-6216084131 / 1000000000000), orderedInterval (-40474944246 / 1000000000000) (-40474944245 / 1000000000000))
    | 1 => (orderedInterval (-31509775135 / 1000000000000) (-31509775134 / 1000000000000), orderedInterval (-35784041999 / 1000000000000) (-35784041998 / 1000000000000))
    | 2 => (orderedInterval (13919926507 / 1000000000000) (13919926508 / 1000000000000), orderedInterval (34837669049 / 1000000000000) (34837669050 / 1000000000000))
    | 3 => (orderedInterval (54925366444 / 1000000000000) (54925366445 / 1000000000000), orderedInterval (68858448955 / 1000000000000) (68858448956 / 1000000000000))
    | 4 => (orderedInterval (-1198217751 / 1000000000000) (-1198217747 / 1000000000000), orderedInterval (53892677351 / 1000000000000) (53892677355 / 1000000000000))
    | 5 => (orderedInterval (-30563137466 / 1000000000000) (-30563096823 / 1000000000000), orderedInterval (11687765898 / 1000000000000) (11687806541 / 1000000000000))
    | 6 => (orderedInterval (-28100860105 / 1000000000000) (-28100836629 / 1000000000000), orderedInterval (25783153813 / 1000000000000) (25783177288 / 1000000000000))
    | 7 => (orderedInterval (-21347274489 / 1000000000000) (-21347274488 / 1000000000000), orderedInterval (-19787989693 / 1000000000000) (-19787989692 / 1000000000000))
    | 8 => (orderedInterval (27762261883 / 1000000000000) (27762261884 / 1000000000000), orderedInterval (19475493115 / 1000000000000) (19475493116 / 1000000000000))
    | 9 => (orderedInterval (24922012137 / 1000000000000) (24922012152 / 1000000000000), orderedInterval (11347712995 / 1000000000000) (11347713010 / 1000000000000))
    | 10 => (orderedInterval (21210298163 / 1000000000000) (21210298164 / 1000000000000), orderedInterval (29124996349 / 1000000000000) (29124996350 / 1000000000000))
    | 11 => (orderedInterval (1143800715 / 1000000000000) (1143800716 / 1000000000000), orderedInterval (-27036727655 / 1000000000000) (-27036727654 / 1000000000000))
    | 12 => (orderedInterval (15504340753 / 1000000000000) (15504340942 / 1000000000000), orderedInterval (-23319200879 / 1000000000000) (-23319200690 / 1000000000000))
    | 13 => (orderedInterval (21692300900 / 1000000000000) (21692304496 / 1000000000000), orderedInterval (-25071462058 / 1000000000000) (-25071458462 / 1000000000000))
    | 14 => (orderedInterval (-31054951257 / 1000000000000) (-31054950625 / 1000000000000), orderedInterval (-2003145005 / 1000000000000) (-2003144374 / 1000000000000))
    | 15 => (orderedInterval (28574422150 / 1000000000000) (28574485047 / 1000000000000), orderedInterval (-18606112758 / 1000000000000) (-18606049861 / 1000000000000))
    | 16 => (orderedInterval (33154610646 / 1000000000000) (33154610648 / 1000000000000), orderedInterval (14650065085 / 1000000000000) (14650065087 / 1000000000000))
    | 17 => (orderedInterval (-28760708803 / 1000000000000) (-28760671207 / 1000000000000), orderedInterval (8971705185 / 1000000000000) (8971742781 / 1000000000000))
    | 18 => (orderedInterval (-23045258568 / 1000000000000) (-23045255385 / 1000000000000), orderedInterval (33331080168 / 1000000000000) (33331083351 / 1000000000000))
    | 19 => (orderedInterval (1261901099 / 1000000000000) (1261901101 / 1000000000000), orderedInterval (-43969060095 / 1000000000000) (-43969060093 / 1000000000000))
    | 20 => (orderedInterval (-33823554097 / 1000000000000) (-33823540543 / 1000000000000), orderedInterval (44215580993 / 1000000000000) (44215594547 / 1000000000000))
    | 21 => (orderedInterval (-75820297879 / 1000000000000) (-75820297847 / 1000000000000), orderedInterval (-45588418 / 1000000000000) (-45588385 / 1000000000000))
    | 22 => (orderedInterval (-6193033956 / 1000000000000) (-6193033944 / 1000000000000), orderedInterval (45605976291 / 1000000000000) (45605976302 / 1000000000000))
    | 23 => (orderedInterval (8608423266 / 1000000000000) (8608423283 / 1000000000000), orderedInterval (-38436685440 / 1000000000000) (-38436685422 / 1000000000000))
    | 24 => (orderedInterval (-60546153154 / 1000000000000) (-60546153079 / 1000000000000), orderedInterval (1377799633 / 1000000000000) (1377799708 / 1000000000000))
    | 25 => (orderedInterval (12379947072 / 1000000000000) (12379947113 / 1000000000000), orderedInterval (-27375069136 / 1000000000000) (-27375069095 / 1000000000000))
    | _ => (orderedInterval (28479426981 / 1000000000000) (28479426982 / 1000000000000), orderedInterval (23198658823 / 1000000000000) (23198658824 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-1940610976 / 1000000000000) (-1940610949 / 1000000000000)
      | 1 => orderedInterval (1533069252 / 1000000000000) (1533072187 / 1000000000000)
      | 2 => orderedInterval (1329394439 / 1000000000000) (1329394461 / 1000000000000)
      | 3 => orderedInterval (-2694234161 / 1000000000000) (-2694234008 / 1000000000000)
      | 4 => orderedInterval (1928540858 / 1000000000000) (1928541250 / 1000000000000)
      | 5 => orderedInterval (-2303747966 / 1000000000000) (-2303746240 / 1000000000000)
      | 6 => orderedInterval (2512203596 / 1000000000000) (2512204641 / 1000000000000)
      | 7 => orderedInterval (880791321 / 1000000000000) (880791369 / 1000000000000)
      | _ => orderedInterval (-6716237793 / 1000000000000) (-6716237683 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-13853683300 / 1000000000000) (-13853683270 / 1000000000000)
      | 1 => orderedInterval (-327016364 / 1000000000000) (-327011782 / 1000000000000)
      | 2 => orderedInterval (1893607634 / 1000000000000) (1893607672 / 1000000000000)
      | 3 => orderedInterval (-10527717852 / 1000000000000) (-10527717534 / 1000000000000)
      | 4 => orderedInterval (-2702850027 / 1000000000000) (-2702849421 / 1000000000000)
      | 5 => orderedInterval (-955154479 / 1000000000000) (-955151597 / 1000000000000)
      | 6 => orderedInterval (-2512260826 / 1000000000000) (-2512259978 / 1000000000000)
      | 7 => orderedInterval (2367207190 / 1000000000000) (2367207234 / 1000000000000)
      | _ => orderedInterval (-1258765990 / 1000000000000) (-1258765836 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (1500981585 / 1000000000000) (1500981620 / 1000000000000)
      | 1 => orderedInterval (-5296333109 / 1000000000000) (-5296325924 / 1000000000000)
      | 2 => orderedInterval (-4007848241 / 1000000000000) (-4007848174 / 1000000000000)
      | 3 => orderedInterval (18696918148 / 1000000000000) (18696918831 / 1000000000000)
      | 4 => orderedInterval (-3968307700 / 1000000000000) (-3968306758 / 1000000000000)
      | 5 => orderedInterval (4920123330 / 1000000000000) (4920128221 / 1000000000000)
      | 6 => orderedInterval (-3470515721 / 1000000000000) (-3470514972 / 1000000000000)
      | 7 => orderedInterval (558448740 / 1000000000000) (558448783 / 1000000000000)
      | _ => orderedInterval (11806640717 / 1000000000000) (11806640947 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (12718380658 / 1000000000000) (12718380699 / 1000000000000)
      | 1 => orderedInterval (2843486600 / 1000000000000) (2843497857 / 1000000000000)
      | 2 => orderedInterval (-6174183821 / 1000000000000) (-6174183701 / 1000000000000)
      | 3 => orderedInterval (64060730236 / 1000000000000) (64060731732 / 1000000000000)
      | 4 => orderedInterval (4279553640 / 1000000000000) (4279555110 / 1000000000000)
      | 5 => orderedInterval (923097601 / 1000000000000) (923106006 / 1000000000000)
      | 6 => orderedInterval (3859853800 / 1000000000000) (3859854498 / 1000000000000)
      | 7 => orderedInterval (-3216282567 / 1000000000000) (-3216282523 / 1000000000000)
      | _ => orderedInterval (-6018483116 / 1000000000000) (-6018482758 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-973744842 / 1000000000000) (-973744795 / 1000000000000)
      | 1 => orderedInterval (13099785403 / 1000000000000) (13099803075 / 1000000000000)
      | 2 => orderedInterval (13150961845 / 1000000000000) (13150962067 / 1000000000000)
      | 3 => orderedInterval (-102202178458 / 1000000000000) (-102202175136 / 1000000000000)
      | 4 => orderedInterval (6684715984 / 1000000000000) (6684718300 / 1000000000000)
      | 5 => orderedInterval (-12202522413 / 1000000000000) (-12202507771 / 1000000000000)
      | 6 => orderedInterval (3876918682 / 1000000000000) (3876919362 / 1000000000000)
      | 7 => orderedInterval (-821102650 / 1000000000000) (-821102604 / 1000000000000)
      | _ => orderedInterval (-24745635618 / 1000000000000) (-24745635038 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-5470831430 / 1000000000000) (-5470824972 / 1000000000000)
    | 1 => orderedInterval (-27876634014 / 1000000000000) (-27876624512 / 1000000000000)
    | 2 => orderedInterval (20740107749 / 1000000000000) (20740122574 / 1000000000000)
    | 3 => orderedInterval (73276153031 / 1000000000000) (73276176920 / 1000000000000)
    | _ => orderedInterval (-104132802067 / 1000000000000) (-104132762540 / 1000000000000)

theorem compactCertificate508_stateChecks0 :
    compactCertificate508.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (759 / 2)) (orderedInterval (-6216084132 / 1000000000000) (-6216084131 / 1000000000000), orderedInterval (-40474944246 / 1000000000000) (-40474944245 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1118151929456859 / 4000000000000)) (orderedInterval (-31509775135 / 1000000000000) (-31509775134 / 1000000000000), orderedInterval (-35784041999 / 1000000000000) (-35784041998 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (361587360105147 / 800000000000)) (orderedInterval (13919926507 / 1000000000000) (13919926508 / 1000000000000), orderedInterval (34837669049 / 1000000000000) (34837669050 / 1000000000000))) = true
  rfl'

theorem compactCertificate508_stateChecks1 :
    compactCertificate508.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (326273944304913 / 4000000000000)) (orderedInterval (54925366444 / 1000000000000) (54925366445 / 1000000000000), orderedInterval (68858448955 / 1000000000000) (68858448956 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (876417708629661 / 4000000000000)) (orderedInterval (-1198217751 / 1000000000000) (-1198217747 / 1000000000000), orderedInterval (53892677351 / 1000000000000) (53892677355 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2379644566453737 / 4000000000000)) (orderedInterval (-30563137466 / 1000000000000) (-30563096823 / 1000000000000), orderedInterval (11687765898 / 1000000000000) (11687806541 / 1000000000000))) = true
  rfl'

theorem compactCertificate508_stateChecks2 :
    compactCertificate508.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1752835417260081 / 4000000000000)) (orderedInterval (-28100860105 / 1000000000000) (-28100836629 / 1000000000000), orderedInterval (25783153813 / 1000000000000) (25783177288 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 239 12 (3003513363597813 / 4000000000000)) (orderedInterval (-21347274489 / 1000000000000) (-21347274488 / 1000000000000), orderedInterval (-19787989693 / 1000000000000) (-19787989692 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (2212374349574367 / 4000000000000)) (orderedInterval (27762261883 / 1000000000000) (27762261884 / 1000000000000), orderedInterval (19475493115 / 1000000000000) (19475493116 / 1000000000000))) = true
  rfl'

theorem compactCertificate508_stateChecks3 :
    compactCertificate508.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 270 12 (3394351189844241 / 4000000000000)) (orderedInterval (24922012137 / 1000000000000) (24922012152 / 1000000000000), orderedInterval (11347712995 / 1000000000000) (11347713010 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1959729573180489 / 4000000000000)) (orderedInterval (21210298163 / 1000000000000) (21210298164 / 1000000000000), orderedInterval (29124996349 / 1000000000000) (29124996350 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 277 12 (3477574517577501 / 4000000000000)) (orderedInterval (1143800715 / 1000000000000) (1143800716 / 1000000000000), orderedInterval (-27036727655 / 1000000000000) (-27036727654 / 1000000000000))) = true
  rfl'

theorem compactCertificate508_stateChecks4 :
    compactCertificate508.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 259 12 (3249201213422769 / 4000000000000)) (orderedInterval (15504340753 / 1000000000000) (15504340942 / 1000000000000), orderedInterval (-23319200879 / 1000000000000) (-23319200690 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2318783301646977 / 4000000000000)) (orderedInterval (21692300900 / 1000000000000) (21692304496 / 1000000000000), orderedInterval (-25071462058 / 1000000000000) (-25071458462 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 209 12 (2629253125888983 / 4000000000000)) (orderedInterval (-31054951257 / 1000000000000) (-31054950625 / 1000000000000), orderedInterval (-2003145005 / 1000000000000) (-2003144374 / 1000000000000))) = true
  rfl'

theorem compactCertificate508_stateChecks5 :
    compactCertificate508.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2191997142948327 / 4000000000000)) (orderedInterval (28574422150 / 1000000000000) (28574485047 / 1000000000000), orderedInterval (-18606112758 / 1000000000000) (-18606049861 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1936695952398867 / 4000000000000)) (orderedInterval (33154610646 / 1000000000000) (33154610648 / 1000000000000), orderedInterval (14650065085 / 1000000000000) (14650065087 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (561329973355833 / 800000000000)) (orderedInterval (-28760708803 / 1000000000000) (-28760671207 / 1000000000000), orderedInterval (8971705185 / 1000000000000) (8971742781 / 1000000000000))) = true
  rfl'

theorem compactCertificate508_stateChecks6 :
    compactCertificate508.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1552668247480251 / 4000000000000)) (orderedInterval (-23045258568 / 1000000000000) (-23045255385 / 1000000000000), orderedInterval (33331080168 / 1000000000000) (33331083351 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1316214068719011 / 4000000000000)) (orderedInterval (1261901099 / 1000000000000) (1261901101 / 1000000000000), orderedInterval (-43969060095 / 1000000000000) (-43969060093 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (823625650425633 / 4000000000000)) (orderedInterval (-33823554097 / 1000000000000) (-33823540543 / 1000000000000), orderedInterval (44215580993 / 1000000000000) (44215594547 / 1000000000000))) = true
  rfl'

theorem compactCertificate508_stateChecks7 :
    compactCertificate508.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (442948614054111 / 4000000000000)) (orderedInterval (-75820297879 / 1000000000000) (-75820297847 / 1000000000000), orderedInterval (-45588418 / 1000000000000) (-45588385 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1202691652935333 / 4000000000000)) (orderedInterval (-6193033956 / 1000000000000) (-6193033944 / 1000000000000), orderedInterval (45605976291 / 1000000000000) (45605976302 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1642172630811141 / 4000000000000)) (orderedInterval (8608423266 / 1000000000000) (8608423283 / 1000000000000), orderedInterval (-38436685440 / 1000000000000) (-38436685422 / 1000000000000))) = true
  rfl'

theorem compactCertificate508_stateChecks8 :
    compactCertificate508.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (694374349574367 / 4000000000000)) (orderedInterval (-60546153154 / 1000000000000) (-60546153079 / 1000000000000), orderedInterval (1377799633 / 1000000000000) (1377799708 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (2822593180508607 / 4000000000000)) (orderedInterval (12379947072 / 1000000000000) (12379947113 / 1000000000000), orderedInterval (-27375069136 / 1000000000000) (-27375069095 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1885361434141713 / 4000000000000)) (orderedInterval (28479426981 / 1000000000000) (28479426982 / 1000000000000), orderedInterval (23198658823 / 1000000000000) (23198658824 / 1000000000000))) = true
  rfl'

theorem compactCertificate508_states : ∀ j,
    BesselStateValid (compactCertificate508.point j) (compactCertificate508.state j) :=
  compactCertificate508.statesValid_of_checks3 compactCertificate508_stateChecks0
    compactCertificate508_stateChecks1 compactCertificate508_stateChecks2
    compactCertificate508_stateChecks3 compactCertificate508_stateChecks4
    compactCertificate508_stateChecks5 compactCertificate508_stateChecks6
    compactCertificate508_stateChecks7 compactCertificate508_stateChecks8

theorem compactCertificate508_chunkChecks0_0 :
    compactCertificate508.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (759 / 2) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6216084132 / 1000000000000) (-6216084131 / 1000000000000), orderedInterval (-40474944246 / 1000000000000) (-40474944245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1118151929456859 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31509775135 / 1000000000000) (-31509775134 / 1000000000000), orderedInterval (-35784041999 / 1000000000000) (-35784041998 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (361587360105147 / 800000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13919926507 / 1000000000000) (13919926508 / 1000000000000), orderedInterval (34837669049 / 1000000000000) (34837669050 / 1000000000000)))) (orderedInterval (-1940610976 / 1000000000000) (-1940610949 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (326273944304913 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (54925366444 / 1000000000000) (54925366445 / 1000000000000), orderedInterval (68858448955 / 1000000000000) (68858448956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (876417708629661 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1198217751 / 1000000000000) (-1198217747 / 1000000000000), orderedInterval (53892677351 / 1000000000000) (53892677355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2379644566453737 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30563137466 / 1000000000000) (-30563096823 / 1000000000000), orderedInterval (11687765898 / 1000000000000) (11687806541 / 1000000000000)))) (orderedInterval (1533069252 / 1000000000000) (1533072187 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1752835417260081 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28100860105 / 1000000000000) (-28100836629 / 1000000000000), orderedInterval (25783153813 / 1000000000000) (25783177288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3003513363597813 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21347274489 / 1000000000000) (-21347274488 / 1000000000000), orderedInterval (-19787989693 / 1000000000000) (-19787989692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2212374349574367 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27762261883 / 1000000000000) (27762261884 / 1000000000000), orderedInterval (19475493115 / 1000000000000) (19475493116 / 1000000000000)))) (orderedInterval (1329394439 / 1000000000000) (1329394461 / 1000000000000))) = true
  rfl'

theorem compactCertificate508_chunkChecks0_1 :
    compactCertificate508.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3394351189844241 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24922012137 / 1000000000000) (24922012152 / 1000000000000), orderedInterval (11347712995 / 1000000000000) (11347713010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1959729573180489 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (21210298163 / 1000000000000) (21210298164 / 1000000000000), orderedInterval (29124996349 / 1000000000000) (29124996350 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3477574517577501 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (1143800715 / 1000000000000) (1143800716 / 1000000000000), orderedInterval (-27036727655 / 1000000000000) (-27036727654 / 1000000000000)))) (orderedInterval (-2694234161 / 1000000000000) (-2694234008 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3249201213422769 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15504340753 / 1000000000000) (15504340942 / 1000000000000), orderedInterval (-23319200879 / 1000000000000) (-23319200690 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2318783301646977 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21692300900 / 1000000000000) (21692304496 / 1000000000000), orderedInterval (-25071462058 / 1000000000000) (-25071458462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2629253125888983 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31054951257 / 1000000000000) (-31054950625 / 1000000000000), orderedInterval (-2003145005 / 1000000000000) (-2003144374 / 1000000000000)))) (orderedInterval (1928540858 / 1000000000000) (1928541250 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2191997142948327 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28574422150 / 1000000000000) (28574485047 / 1000000000000), orderedInterval (-18606112758 / 1000000000000) (-18606049861 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1936695952398867 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33154610646 / 1000000000000) (33154610648 / 1000000000000), orderedInterval (14650065085 / 1000000000000) (14650065087 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (561329973355833 / 800000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28760708803 / 1000000000000) (-28760671207 / 1000000000000), orderedInterval (8971705185 / 1000000000000) (8971742781 / 1000000000000)))) (orderedInterval (-2303747966 / 1000000000000) (-2303746240 / 1000000000000))) = true
  rfl'

theorem compactCertificate508_chunkChecks0_2 :
    compactCertificate508.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1552668247480251 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23045258568 / 1000000000000) (-23045255385 / 1000000000000), orderedInterval (33331080168 / 1000000000000) (33331083351 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1316214068719011 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1261901099 / 1000000000000) (1261901101 / 1000000000000), orderedInterval (-43969060095 / 1000000000000) (-43969060093 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (823625650425633 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33823554097 / 1000000000000) (-33823540543 / 1000000000000), orderedInterval (44215580993 / 1000000000000) (44215594547 / 1000000000000)))) (orderedInterval (2512203596 / 1000000000000) (2512204641 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (442948614054111 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-75820297879 / 1000000000000) (-75820297847 / 1000000000000), orderedInterval (-45588418 / 1000000000000) (-45588385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1202691652935333 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6193033956 / 1000000000000) (-6193033944 / 1000000000000), orderedInterval (45605976291 / 1000000000000) (45605976302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1642172630811141 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (8608423266 / 1000000000000) (8608423283 / 1000000000000), orderedInterval (-38436685440 / 1000000000000) (-38436685422 / 1000000000000)))) (orderedInterval (880791321 / 1000000000000) (880791369 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (694374349574367 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60546153154 / 1000000000000) (-60546153079 / 1000000000000), orderedInterval (1377799633 / 1000000000000) (1377799708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2822593180508607 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12379947072 / 1000000000000) (12379947113 / 1000000000000), orderedInterval (-27375069136 / 1000000000000) (-27375069095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1885361434141713 / 4000000000000) 0 (IntervalRat.scale (759 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28479426981 / 1000000000000) (28479426982 / 1000000000000), orderedInterval (23198658823 / 1000000000000) (23198658824 / 1000000000000)))) (orderedInterval (-6716237793 / 1000000000000) (-6716237683 / 1000000000000))) = true
  rfl'

theorem compactCertificate508_chunkChecks0 :
    compactCertificate508.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate508.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate508_chunkChecks0_0
    compactCertificate508_chunkChecks0_1 compactCertificate508_chunkChecks0_2

theorem compactCertificate508_chunkChecks1_0 :
    compactCertificate508.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (759 / 2) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6216084132 / 1000000000000) (-6216084131 / 1000000000000), orderedInterval (-40474944246 / 1000000000000) (-40474944245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1118151929456859 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31509775135 / 1000000000000) (-31509775134 / 1000000000000), orderedInterval (-35784041999 / 1000000000000) (-35784041998 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (361587360105147 / 800000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13919926507 / 1000000000000) (13919926508 / 1000000000000), orderedInterval (34837669049 / 1000000000000) (34837669050 / 1000000000000)))) (orderedInterval (-13853683300 / 1000000000000) (-13853683270 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (326273944304913 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (54925366444 / 1000000000000) (54925366445 / 1000000000000), orderedInterval (68858448955 / 1000000000000) (68858448956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (876417708629661 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1198217751 / 1000000000000) (-1198217747 / 1000000000000), orderedInterval (53892677351 / 1000000000000) (53892677355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2379644566453737 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30563137466 / 1000000000000) (-30563096823 / 1000000000000), orderedInterval (11687765898 / 1000000000000) (11687806541 / 1000000000000)))) (orderedInterval (-327016364 / 1000000000000) (-327011782 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1752835417260081 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28100860105 / 1000000000000) (-28100836629 / 1000000000000), orderedInterval (25783153813 / 1000000000000) (25783177288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3003513363597813 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21347274489 / 1000000000000) (-21347274488 / 1000000000000), orderedInterval (-19787989693 / 1000000000000) (-19787989692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2212374349574367 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27762261883 / 1000000000000) (27762261884 / 1000000000000), orderedInterval (19475493115 / 1000000000000) (19475493116 / 1000000000000)))) (orderedInterval (1893607634 / 1000000000000) (1893607672 / 1000000000000))) = true
  rfl'

theorem compactCertificate508_chunkChecks1_1 :
    compactCertificate508.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3394351189844241 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24922012137 / 1000000000000) (24922012152 / 1000000000000), orderedInterval (11347712995 / 1000000000000) (11347713010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1959729573180489 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (21210298163 / 1000000000000) (21210298164 / 1000000000000), orderedInterval (29124996349 / 1000000000000) (29124996350 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3477574517577501 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (1143800715 / 1000000000000) (1143800716 / 1000000000000), orderedInterval (-27036727655 / 1000000000000) (-27036727654 / 1000000000000)))) (orderedInterval (-10527717852 / 1000000000000) (-10527717534 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3249201213422769 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15504340753 / 1000000000000) (15504340942 / 1000000000000), orderedInterval (-23319200879 / 1000000000000) (-23319200690 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2318783301646977 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21692300900 / 1000000000000) (21692304496 / 1000000000000), orderedInterval (-25071462058 / 1000000000000) (-25071458462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2629253125888983 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31054951257 / 1000000000000) (-31054950625 / 1000000000000), orderedInterval (-2003145005 / 1000000000000) (-2003144374 / 1000000000000)))) (orderedInterval (-2702850027 / 1000000000000) (-2702849421 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2191997142948327 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28574422150 / 1000000000000) (28574485047 / 1000000000000), orderedInterval (-18606112758 / 1000000000000) (-18606049861 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1936695952398867 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33154610646 / 1000000000000) (33154610648 / 1000000000000), orderedInterval (14650065085 / 1000000000000) (14650065087 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (561329973355833 / 800000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28760708803 / 1000000000000) (-28760671207 / 1000000000000), orderedInterval (8971705185 / 1000000000000) (8971742781 / 1000000000000)))) (orderedInterval (-955154479 / 1000000000000) (-955151597 / 1000000000000))) = true
  rfl'

theorem compactCertificate508_chunkChecks1_2 :
    compactCertificate508.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1552668247480251 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23045258568 / 1000000000000) (-23045255385 / 1000000000000), orderedInterval (33331080168 / 1000000000000) (33331083351 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1316214068719011 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1261901099 / 1000000000000) (1261901101 / 1000000000000), orderedInterval (-43969060095 / 1000000000000) (-43969060093 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (823625650425633 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33823554097 / 1000000000000) (-33823540543 / 1000000000000), orderedInterval (44215580993 / 1000000000000) (44215594547 / 1000000000000)))) (orderedInterval (-2512260826 / 1000000000000) (-2512259978 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (442948614054111 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-75820297879 / 1000000000000) (-75820297847 / 1000000000000), orderedInterval (-45588418 / 1000000000000) (-45588385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1202691652935333 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6193033956 / 1000000000000) (-6193033944 / 1000000000000), orderedInterval (45605976291 / 1000000000000) (45605976302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1642172630811141 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (8608423266 / 1000000000000) (8608423283 / 1000000000000), orderedInterval (-38436685440 / 1000000000000) (-38436685422 / 1000000000000)))) (orderedInterval (2367207190 / 1000000000000) (2367207234 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (694374349574367 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60546153154 / 1000000000000) (-60546153079 / 1000000000000), orderedInterval (1377799633 / 1000000000000) (1377799708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2822593180508607 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12379947072 / 1000000000000) (12379947113 / 1000000000000), orderedInterval (-27375069136 / 1000000000000) (-27375069095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1885361434141713 / 4000000000000) 1 (IntervalRat.scale (759 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28479426981 / 1000000000000) (28479426982 / 1000000000000), orderedInterval (23198658823 / 1000000000000) (23198658824 / 1000000000000)))) (orderedInterval (-1258765990 / 1000000000000) (-1258765836 / 1000000000000))) = true
  rfl'

theorem compactCertificate508_chunkChecks1 :
    compactCertificate508.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate508.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate508_chunkChecks1_0
    compactCertificate508_chunkChecks1_1 compactCertificate508_chunkChecks1_2

theorem compactCertificate508_chunkChecks2_0 :
    compactCertificate508.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (759 / 2) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6216084132 / 1000000000000) (-6216084131 / 1000000000000), orderedInterval (-40474944246 / 1000000000000) (-40474944245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1118151929456859 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31509775135 / 1000000000000) (-31509775134 / 1000000000000), orderedInterval (-35784041999 / 1000000000000) (-35784041998 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (361587360105147 / 800000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13919926507 / 1000000000000) (13919926508 / 1000000000000), orderedInterval (34837669049 / 1000000000000) (34837669050 / 1000000000000)))) (orderedInterval (1500981585 / 1000000000000) (1500981620 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (326273944304913 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (54925366444 / 1000000000000) (54925366445 / 1000000000000), orderedInterval (68858448955 / 1000000000000) (68858448956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (876417708629661 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1198217751 / 1000000000000) (-1198217747 / 1000000000000), orderedInterval (53892677351 / 1000000000000) (53892677355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2379644566453737 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30563137466 / 1000000000000) (-30563096823 / 1000000000000), orderedInterval (11687765898 / 1000000000000) (11687806541 / 1000000000000)))) (orderedInterval (-5296333109 / 1000000000000) (-5296325924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1752835417260081 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28100860105 / 1000000000000) (-28100836629 / 1000000000000), orderedInterval (25783153813 / 1000000000000) (25783177288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3003513363597813 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21347274489 / 1000000000000) (-21347274488 / 1000000000000), orderedInterval (-19787989693 / 1000000000000) (-19787989692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2212374349574367 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27762261883 / 1000000000000) (27762261884 / 1000000000000), orderedInterval (19475493115 / 1000000000000) (19475493116 / 1000000000000)))) (orderedInterval (-4007848241 / 1000000000000) (-4007848174 / 1000000000000))) = true
  rfl'

theorem compactCertificate508_chunkChecks2_1 :
    compactCertificate508.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3394351189844241 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24922012137 / 1000000000000) (24922012152 / 1000000000000), orderedInterval (11347712995 / 1000000000000) (11347713010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1959729573180489 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (21210298163 / 1000000000000) (21210298164 / 1000000000000), orderedInterval (29124996349 / 1000000000000) (29124996350 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3477574517577501 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (1143800715 / 1000000000000) (1143800716 / 1000000000000), orderedInterval (-27036727655 / 1000000000000) (-27036727654 / 1000000000000)))) (orderedInterval (18696918148 / 1000000000000) (18696918831 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3249201213422769 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15504340753 / 1000000000000) (15504340942 / 1000000000000), orderedInterval (-23319200879 / 1000000000000) (-23319200690 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2318783301646977 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21692300900 / 1000000000000) (21692304496 / 1000000000000), orderedInterval (-25071462058 / 1000000000000) (-25071458462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2629253125888983 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31054951257 / 1000000000000) (-31054950625 / 1000000000000), orderedInterval (-2003145005 / 1000000000000) (-2003144374 / 1000000000000)))) (orderedInterval (-3968307700 / 1000000000000) (-3968306758 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2191997142948327 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28574422150 / 1000000000000) (28574485047 / 1000000000000), orderedInterval (-18606112758 / 1000000000000) (-18606049861 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1936695952398867 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33154610646 / 1000000000000) (33154610648 / 1000000000000), orderedInterval (14650065085 / 1000000000000) (14650065087 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (561329973355833 / 800000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28760708803 / 1000000000000) (-28760671207 / 1000000000000), orderedInterval (8971705185 / 1000000000000) (8971742781 / 1000000000000)))) (orderedInterval (4920123330 / 1000000000000) (4920128221 / 1000000000000))) = true
  rfl'

theorem compactCertificate508_chunkChecks2_2 :
    compactCertificate508.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1552668247480251 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23045258568 / 1000000000000) (-23045255385 / 1000000000000), orderedInterval (33331080168 / 1000000000000) (33331083351 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1316214068719011 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1261901099 / 1000000000000) (1261901101 / 1000000000000), orderedInterval (-43969060095 / 1000000000000) (-43969060093 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (823625650425633 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33823554097 / 1000000000000) (-33823540543 / 1000000000000), orderedInterval (44215580993 / 1000000000000) (44215594547 / 1000000000000)))) (orderedInterval (-3470515721 / 1000000000000) (-3470514972 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (442948614054111 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-75820297879 / 1000000000000) (-75820297847 / 1000000000000), orderedInterval (-45588418 / 1000000000000) (-45588385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1202691652935333 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6193033956 / 1000000000000) (-6193033944 / 1000000000000), orderedInterval (45605976291 / 1000000000000) (45605976302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1642172630811141 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (8608423266 / 1000000000000) (8608423283 / 1000000000000), orderedInterval (-38436685440 / 1000000000000) (-38436685422 / 1000000000000)))) (orderedInterval (558448740 / 1000000000000) (558448783 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (694374349574367 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60546153154 / 1000000000000) (-60546153079 / 1000000000000), orderedInterval (1377799633 / 1000000000000) (1377799708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2822593180508607 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12379947072 / 1000000000000) (12379947113 / 1000000000000), orderedInterval (-27375069136 / 1000000000000) (-27375069095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1885361434141713 / 4000000000000) 2 (IntervalRat.scale (759 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28479426981 / 1000000000000) (28479426982 / 1000000000000), orderedInterval (23198658823 / 1000000000000) (23198658824 / 1000000000000)))) (orderedInterval (11806640717 / 1000000000000) (11806640947 / 1000000000000))) = true
  rfl'

theorem compactCertificate508_chunkChecks2 :
    compactCertificate508.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate508.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate508_chunkChecks2_0
    compactCertificate508_chunkChecks2_1 compactCertificate508_chunkChecks2_2

theorem compactCertificate508_chunkChecks3_0 :
    compactCertificate508.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (759 / 2) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6216084132 / 1000000000000) (-6216084131 / 1000000000000), orderedInterval (-40474944246 / 1000000000000) (-40474944245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1118151929456859 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31509775135 / 1000000000000) (-31509775134 / 1000000000000), orderedInterval (-35784041999 / 1000000000000) (-35784041998 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (361587360105147 / 800000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13919926507 / 1000000000000) (13919926508 / 1000000000000), orderedInterval (34837669049 / 1000000000000) (34837669050 / 1000000000000)))) (orderedInterval (12718380658 / 1000000000000) (12718380699 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (326273944304913 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (54925366444 / 1000000000000) (54925366445 / 1000000000000), orderedInterval (68858448955 / 1000000000000) (68858448956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (876417708629661 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1198217751 / 1000000000000) (-1198217747 / 1000000000000), orderedInterval (53892677351 / 1000000000000) (53892677355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2379644566453737 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30563137466 / 1000000000000) (-30563096823 / 1000000000000), orderedInterval (11687765898 / 1000000000000) (11687806541 / 1000000000000)))) (orderedInterval (2843486600 / 1000000000000) (2843497857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1752835417260081 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28100860105 / 1000000000000) (-28100836629 / 1000000000000), orderedInterval (25783153813 / 1000000000000) (25783177288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3003513363597813 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21347274489 / 1000000000000) (-21347274488 / 1000000000000), orderedInterval (-19787989693 / 1000000000000) (-19787989692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2212374349574367 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27762261883 / 1000000000000) (27762261884 / 1000000000000), orderedInterval (19475493115 / 1000000000000) (19475493116 / 1000000000000)))) (orderedInterval (-6174183821 / 1000000000000) (-6174183701 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate508_chunkChecks3_1 :
    compactCertificate508.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3394351189844241 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24922012137 / 1000000000000) (24922012152 / 1000000000000), orderedInterval (11347712995 / 1000000000000) (11347713010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1959729573180489 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (21210298163 / 1000000000000) (21210298164 / 1000000000000), orderedInterval (29124996349 / 1000000000000) (29124996350 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3477574517577501 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (1143800715 / 1000000000000) (1143800716 / 1000000000000), orderedInterval (-27036727655 / 1000000000000) (-27036727654 / 1000000000000)))) (orderedInterval (64060730236 / 1000000000000) (64060731732 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3249201213422769 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15504340753 / 1000000000000) (15504340942 / 1000000000000), orderedInterval (-23319200879 / 1000000000000) (-23319200690 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2318783301646977 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21692300900 / 1000000000000) (21692304496 / 1000000000000), orderedInterval (-25071462058 / 1000000000000) (-25071458462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2629253125888983 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31054951257 / 1000000000000) (-31054950625 / 1000000000000), orderedInterval (-2003145005 / 1000000000000) (-2003144374 / 1000000000000)))) (orderedInterval (4279553640 / 1000000000000) (4279555110 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2191997142948327 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28574422150 / 1000000000000) (28574485047 / 1000000000000), orderedInterval (-18606112758 / 1000000000000) (-18606049861 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1936695952398867 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33154610646 / 1000000000000) (33154610648 / 1000000000000), orderedInterval (14650065085 / 1000000000000) (14650065087 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (561329973355833 / 800000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28760708803 / 1000000000000) (-28760671207 / 1000000000000), orderedInterval (8971705185 / 1000000000000) (8971742781 / 1000000000000)))) (orderedInterval (923097601 / 1000000000000) (923106006 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate508_chunkChecks3_2 :
    compactCertificate508.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1552668247480251 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23045258568 / 1000000000000) (-23045255385 / 1000000000000), orderedInterval (33331080168 / 1000000000000) (33331083351 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1316214068719011 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1261901099 / 1000000000000) (1261901101 / 1000000000000), orderedInterval (-43969060095 / 1000000000000) (-43969060093 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (823625650425633 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33823554097 / 1000000000000) (-33823540543 / 1000000000000), orderedInterval (44215580993 / 1000000000000) (44215594547 / 1000000000000)))) (orderedInterval (3859853800 / 1000000000000) (3859854498 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (442948614054111 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-75820297879 / 1000000000000) (-75820297847 / 1000000000000), orderedInterval (-45588418 / 1000000000000) (-45588385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1202691652935333 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6193033956 / 1000000000000) (-6193033944 / 1000000000000), orderedInterval (45605976291 / 1000000000000) (45605976302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1642172630811141 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (8608423266 / 1000000000000) (8608423283 / 1000000000000), orderedInterval (-38436685440 / 1000000000000) (-38436685422 / 1000000000000)))) (orderedInterval (-3216282567 / 1000000000000) (-3216282523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (694374349574367 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60546153154 / 1000000000000) (-60546153079 / 1000000000000), orderedInterval (1377799633 / 1000000000000) (1377799708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2822593180508607 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12379947072 / 1000000000000) (12379947113 / 1000000000000), orderedInterval (-27375069136 / 1000000000000) (-27375069095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1885361434141713 / 4000000000000) 3 (IntervalRat.scale (759 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28479426981 / 1000000000000) (28479426982 / 1000000000000), orderedInterval (23198658823 / 1000000000000) (23198658824 / 1000000000000)))) (orderedInterval (-6018483116 / 1000000000000) (-6018482758 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate508_chunkChecks3 :
    compactCertificate508.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate508.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate508_chunkChecks3_0
    compactCertificate508_chunkChecks3_1 compactCertificate508_chunkChecks3_2

theorem compactCertificate508_chunkChecks4_0 :
    compactCertificate508.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (759 / 2) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6216084132 / 1000000000000) (-6216084131 / 1000000000000), orderedInterval (-40474944246 / 1000000000000) (-40474944245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1118151929456859 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-31509775135 / 1000000000000) (-31509775134 / 1000000000000), orderedInterval (-35784041999 / 1000000000000) (-35784041998 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (361587360105147 / 800000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13919926507 / 1000000000000) (13919926508 / 1000000000000), orderedInterval (34837669049 / 1000000000000) (34837669050 / 1000000000000)))) (orderedInterval (-973744842 / 1000000000000) (-973744795 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (326273944304913 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (54925366444 / 1000000000000) (54925366445 / 1000000000000), orderedInterval (68858448955 / 1000000000000) (68858448956 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (876417708629661 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1198217751 / 1000000000000) (-1198217747 / 1000000000000), orderedInterval (53892677351 / 1000000000000) (53892677355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2379644566453737 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30563137466 / 1000000000000) (-30563096823 / 1000000000000), orderedInterval (11687765898 / 1000000000000) (11687806541 / 1000000000000)))) (orderedInterval (13099785403 / 1000000000000) (13099803075 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1752835417260081 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28100860105 / 1000000000000) (-28100836629 / 1000000000000), orderedInterval (25783153813 / 1000000000000) (25783177288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3003513363597813 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21347274489 / 1000000000000) (-21347274488 / 1000000000000), orderedInterval (-19787989693 / 1000000000000) (-19787989692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2212374349574367 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27762261883 / 1000000000000) (27762261884 / 1000000000000), orderedInterval (19475493115 / 1000000000000) (19475493116 / 1000000000000)))) (orderedInterval (13150961845 / 1000000000000) (13150962067 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate508_chunkChecks4_1 :
    compactCertificate508.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3394351189844241 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24922012137 / 1000000000000) (24922012152 / 1000000000000), orderedInterval (11347712995 / 1000000000000) (11347713010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1959729573180489 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (21210298163 / 1000000000000) (21210298164 / 1000000000000), orderedInterval (29124996349 / 1000000000000) (29124996350 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3477574517577501 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (1143800715 / 1000000000000) (1143800716 / 1000000000000), orderedInterval (-27036727655 / 1000000000000) (-27036727654 / 1000000000000)))) (orderedInterval (-102202178458 / 1000000000000) (-102202175136 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3249201213422769 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (15504340753 / 1000000000000) (15504340942 / 1000000000000), orderedInterval (-23319200879 / 1000000000000) (-23319200690 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2318783301646977 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21692300900 / 1000000000000) (21692304496 / 1000000000000), orderedInterval (-25071462058 / 1000000000000) (-25071458462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2629253125888983 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-31054951257 / 1000000000000) (-31054950625 / 1000000000000), orderedInterval (-2003145005 / 1000000000000) (-2003144374 / 1000000000000)))) (orderedInterval (6684715984 / 1000000000000) (6684718300 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2191997142948327 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28574422150 / 1000000000000) (28574485047 / 1000000000000), orderedInterval (-18606112758 / 1000000000000) (-18606049861 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1936695952398867 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33154610646 / 1000000000000) (33154610648 / 1000000000000), orderedInterval (14650065085 / 1000000000000) (14650065087 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (561329973355833 / 800000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28760708803 / 1000000000000) (-28760671207 / 1000000000000), orderedInterval (8971705185 / 1000000000000) (8971742781 / 1000000000000)))) (orderedInterval (-12202522413 / 1000000000000) (-12202507771 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate508_chunkChecks4_2 :
    compactCertificate508.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1552668247480251 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-23045258568 / 1000000000000) (-23045255385 / 1000000000000), orderedInterval (33331080168 / 1000000000000) (33331083351 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1316214068719011 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1261901099 / 1000000000000) (1261901101 / 1000000000000), orderedInterval (-43969060095 / 1000000000000) (-43969060093 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (823625650425633 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-33823554097 / 1000000000000) (-33823540543 / 1000000000000), orderedInterval (44215580993 / 1000000000000) (44215594547 / 1000000000000)))) (orderedInterval (3876918682 / 1000000000000) (3876919362 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (442948614054111 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-75820297879 / 1000000000000) (-75820297847 / 1000000000000), orderedInterval (-45588418 / 1000000000000) (-45588385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1202691652935333 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6193033956 / 1000000000000) (-6193033944 / 1000000000000), orderedInterval (45605976291 / 1000000000000) (45605976302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1642172630811141 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (8608423266 / 1000000000000) (8608423283 / 1000000000000), orderedInterval (-38436685440 / 1000000000000) (-38436685422 / 1000000000000)))) (orderedInterval (-821102650 / 1000000000000) (-821102604 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (694374349574367 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60546153154 / 1000000000000) (-60546153079 / 1000000000000), orderedInterval (1377799633 / 1000000000000) (1377799708 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2822593180508607 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (12379947072 / 1000000000000) (12379947113 / 1000000000000), orderedInterval (-27375069136 / 1000000000000) (-27375069095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1885361434141713 / 4000000000000) 4 (IntervalRat.scale (759 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28479426981 / 1000000000000) (28479426982 / 1000000000000), orderedInterval (23198658823 / 1000000000000) (23198658824 / 1000000000000)))) (orderedInterval (-24745635618 / 1000000000000) (-24745635038 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate508_chunkChecks4 :
    compactCertificate508.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate508.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate508_chunkChecks4_0
    compactCertificate508_chunkChecks4_1 compactCertificate508_chunkChecks4_2

theorem compactCertificate508_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate508.chunkCheck r b = true :=
  compactCertificate508.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate508_chunkChecks0
    · exact compactCertificate508_chunkChecks1
    · exact compactCertificate508_chunkChecks2
    · exact compactCertificate508_chunkChecks3
    · exact compactCertificate508_chunkChecks4)

theorem compactCertificate508_coefficient0 :
    compactCertificate508.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate508_coefficient1 :
    compactCertificate508.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate508_coefficient2 :
    compactCertificate508.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate508_coefficient3 :
    compactCertificate508.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate508_coefficient4 :
    compactCertificate508.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate508_coefficients : ∀ r : Fin 5,
    compactCertificate508.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate508_coefficient0
  · exact compactCertificate508_coefficient1
  · exact compactCertificate508_coefficient2
  · exact compactCertificate508_coefficient3
  · exact compactCertificate508_coefficient4

theorem compactCertificate508_lower : (1 : ℚ) ≤ compactCertificate508.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate508, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate508_proves {t : ℝ} (ht : t ∈ compactCertificate508.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate508.proves compactCertificate508_states compactCertificate508_chunks
    compactCertificate508_coefficients compactCertificate508_lower ht

end Erdos232
