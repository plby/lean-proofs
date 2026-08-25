/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate473 : CompactCertificate where
  left := 344
  right := 345
  center := 689 / 2
  grid := fun i =>
    match i.val with
    | 0 => 110
    | 1 => 81
    | 2 => 131
    | 3 => 24
    | 4 => 63
    | 5 => 172
    | 6 => 127
    | 7 => 217
    | 8 => 160
    | 9 => 245
    | 10 => 142
    | 11 => 251
    | 12 => 235
    | 13 => 168
    | 14 => 190
    | 15 => 158
    | 16 => 140
    | 17 => 203
    | 18 => 112
    | 19 => 95
    | 20 => 60
    | 21 => 32
    | 22 => 87
    | 23 => 119
    | 24 => 50
    | 25 => 204
    | _ => 136
  point := fun i =>
    match i.val with
    | 0 => 689 / 2
    | 1 => 1015028563103789 / 4000000000000
    | 2 => 328239382229837 / 800000000000
    | 3 => 296182803196423 / 4000000000000
    | 4 => 795588670943131 / 4000000000000
    | 5 => 2160178005647727 / 4000000000000
    | 6 => 1591177341886951 / 4000000000000
    | 7 => 2726509496072323 / 4000000000000
    | 8 => 2008334554488457 / 4000000000000
    | 9 => 3081301672994311 / 4000000000000
    | 10 => 1778990350357519 / 4000000000000
    | 11 => 3156849595007771 / 4000000000000
    | 12 => 2949538387415399 / 4000000000000
    | 13 => 2104929769215767 / 4000000000000
    | 14 => 2386766012829393 / 4000000000000
    | 15 => 1989836668631617 / 4000000000000
    | 16 => 1758081042427957 / 4000000000000
    | 17 => 509560410595743 / 800000000000
    | 18 => 1409470912403021 / 4000000000000
    | 19 => 1194824101906981 / 4000000000000
    | 20 => 747665445511543 / 4000000000000
    | 21 => 402096963219081 / 4000000000000
    | 22 => 1091771474140243 / 4000000000000
    | 23 => 1490720609524211 / 4000000000000
    | 24 => 630334554488457 / 4000000000000
    | 25 => 2562274968867497 / 4000000000000
    | _ => 1711480932969223 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-12298906696 / 1000000000000) (-12298906614 / 1000000000000), orderedInterval (41208764556 / 1000000000000) (41208764639 / 1000000000000))
    | 1 => (orderedInterval (-3655218925 / 1000000000000) (-3655218924 / 1000000000000), orderedInterval (-49946976702 / 1000000000000) (-49946976701 / 1000000000000))
    | 2 => (orderedInterval (17639444127 / 1000000000000) (17639444668 / 1000000000000), orderedInterval (-35241510960 / 1000000000000) (-35241510419 / 1000000000000))
    | 3 => (orderedInterval (-49943325420 / 1000000000000) (-49943314204 / 1000000000000), orderedInterval (78461531294 / 1000000000000) (78461542509 / 1000000000000))
    | 4 => (orderedInterval (-55548347869 / 1000000000000) (-55548347024 / 1000000000000), orderedInterval (10869039009 / 1000000000000) (10869039855 / 1000000000000))
    | 5 => (orderedInterval (15724623545 / 1000000000000) (15724623546 / 1000000000000), orderedInterval (30506988924 / 1000000000000) (30506988925 / 1000000000000))
    | 6 => (orderedInterval (15683410109 / 1000000000000) (15683410376 / 1000000000000), orderedInterval (-36821963956 / 1000000000000) (-36821963688 / 1000000000000))
    | 7 => (orderedInterval (-19381965077 / 1000000000000) (-19381965076 / 1000000000000), orderedInterval (-23614363827 / 1000000000000) (-23614363826 / 1000000000000))
    | 8 => (orderedInterval (7560880000 / 1000000000000) (7560880001 / 1000000000000), orderedInterval (34788868131 / 1000000000000) (34788868132 / 1000000000000))
    | 9 => (orderedInterval (-28423409035 / 1000000000000) (-28423408589 / 1000000000000), orderedInterval (-4287282738 / 1000000000000) (-4287282292 / 1000000000000))
    | 10 => (orderedInterval (-20526317104 / 1000000000000) (-20526315486 / 1000000000000), orderedInterval (31804970797 / 1000000000000) (31804972415 / 1000000000000))
    | 11 => (orderedInterval (-28220756035 / 1000000000000) (-28220755237 / 1000000000000), orderedInterval (-3182247722 / 1000000000000) (-3182246924 / 1000000000000))
    | 12 => (orderedInterval (3063398989 / 1000000000000) (3063398990 / 1000000000000), orderedInterval (-29224741820 / 1000000000000) (-29224741819 / 1000000000000))
    | 13 => (orderedInterval (-24211863566 / 1000000000000) (-24211854981 / 1000000000000), orderedInterval (24994084349 / 1000000000000) (24994092934 / 1000000000000))
    | 14 => (orderedInterval (17738628849 / 1000000000000) (17738628850 / 1000000000000), orderedInterval (27412445269 / 1000000000000) (27412445270 / 1000000000000))
    | 15 => (orderedInterval (34155787924 / 1000000000000) (34155802233 / 1000000000000), orderedInterval (-10670308546 / 1000000000000) (-10670294236 / 1000000000000))
    | 16 => (orderedInterval (17655638580 / 1000000000000) (17655638581 / 1000000000000), orderedInterval (33695213212 / 1000000000000) (33695213213 / 1000000000000))
    | 17 => (orderedInterval (240063426 / 1000000000000) (240063427 / 1000000000000), orderedInterval (-31613847215 / 1000000000000) (-31613847214 / 1000000000000))
    | 18 => (orderedInterval (40891826364 / 1000000000000) (40891826368 / 1000000000000), orderedInterval (11541478716 / 1000000000000) (11541478719 / 1000000000000))
    | 19 => (orderedInterval (-39806401956 / 1000000000000) (-39806401955 / 1000000000000), orderedInterval (-23315145128 / 1000000000000) (-23315145127 / 1000000000000))
    | 20 => (orderedInterval (-41639407492 / 1000000000000) (-41639353289 / 1000000000000), orderedInterval (41002294457 / 1000000000000) (41002348660 / 1000000000000))
    | 21 => (orderedInterval (55821179218 / 1000000000000) (55821179219 / 1000000000000), orderedInterval (56440914032 / 1000000000000) (56440914033 / 1000000000000))
    | 22 => (orderedInterval (-19217591418 / 1000000000000) (-19217591417 / 1000000000000), orderedInterval (-44271855250 / 1000000000000) (-44271855249 / 1000000000000))
    | 23 => (orderedInterval (15495675455 / 1000000000000) (15495675703 / 1000000000000), orderedInterval (-38336652688 / 1000000000000) (-38336652441 / 1000000000000))
    | 24 => (orderedInterval (61046082544 / 1000000000000) (61046082545 / 1000000000000), orderedInterval (17504996653 / 1000000000000) (17504996654 / 1000000000000))
    | 25 => (orderedInterval (14250427644 / 1000000000000) (14250427645 / 1000000000000), orderedInterval (28109344450 / 1000000000000) (28109344451 / 1000000000000))
    | _ => (orderedInterval (38003490936 / 1000000000000) (38003490966 / 1000000000000), orderedInterval (6559695470 / 1000000000000) (6559695499 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-3873812938 / 1000000000000) (-3873812849 / 1000000000000)
      | 1 => orderedInterval (-2604175482 / 1000000000000) (-2604175288 / 1000000000000)
      | 2 => orderedInterval (780548892 / 1000000000000) (780548912 / 1000000000000)
      | 3 => orderedInterval (-482081480 / 1000000000000) (-482081030 / 1000000000000)
      | 4 => orderedInterval (-2434614716 / 1000000000000) (-2434613862 / 1000000000000)
      | 5 => orderedInterval (-609807204 / 1000000000000) (-609807005 / 1000000000000)
      | 6 => orderedInterval (-5640835615 / 1000000000000) (-5640833763 / 1000000000000)
      | 7 => orderedInterval (-1782328857 / 1000000000000) (-1782328797 / 1000000000000)
      | _ => orderedInterval (-7922467396 / 1000000000000) (-7922467295 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (13527892849 / 1000000000000) (13527892947 / 1000000000000)
      | 1 => orderedInterval (-3353587511 / 1000000000000) (-3353587419 / 1000000000000)
      | 2 => orderedInterval (2666508374 / 1000000000000) (2666508408 / 1000000000000)
      | 3 => orderedInterval (3709300766 / 1000000000000) (3709301640 / 1000000000000)
      | 4 => orderedInterval (4499343556 / 1000000000000) (4499344863 / 1000000000000)
      | 5 => orderedInterval (-4134629680 / 1000000000000) (-4134629393 / 1000000000000)
      | 6 => orderedInterval (-19073632 / 1000000000000) (-19072593 / 1000000000000)
      | 7 => orderedInterval (3670069737 / 1000000000000) (3670069795 / 1000000000000)
      | _ => orderedInterval (-5734977358 / 1000000000000) (-5734977216 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (3385796016 / 1000000000000) (3385796125 / 1000000000000)
      | 1 => orderedInterval (3407812237 / 1000000000000) (3407812318 / 1000000000000)
      | 2 => orderedInterval (-2736246983 / 1000000000000) (-2736246923 / 1000000000000)
      | 3 => orderedInterval (-1674133337 / 1000000000000) (-1674131537 / 1000000000000)
      | 4 => orderedInterval (5851883610 / 1000000000000) (5851885619 / 1000000000000)
      | 5 => orderedInterval (813170662 / 1000000000000) (813171079 / 1000000000000)
      | 6 => orderedInterval (5545603097 / 1000000000000) (5545603697 / 1000000000000)
      | 7 => orderedInterval (1193237527 / 1000000000000) (1193237586 / 1000000000000)
      | _ => orderedInterval (14949555218 / 1000000000000) (14949555425 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-12663707061 / 1000000000000) (-12663706938 / 1000000000000)
      | 1 => orderedInterval (8276777549 / 1000000000000) (8276777654 / 1000000000000)
      | 2 => orderedInterval (-8236676880 / 1000000000000) (-8236676771 / 1000000000000)
      | 3 => orderedInterval (-8143705637 / 1000000000000) (-8143701796 / 1000000000000)
      | 4 => orderedInterval (-12894101217 / 1000000000000) (-12894098131 / 1000000000000)
      | 5 => orderedInterval (9489027784 / 1000000000000) (9489028393 / 1000000000000)
      | 6 => orderedInterval (885196882 / 1000000000000) (885197240 / 1000000000000)
      | 7 => orderedInterval (-4196725518 / 1000000000000) (-4196725455 / 1000000000000)
      | _ => orderedInterval (17014521063 / 1000000000000) (17014521379 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-2728622644 / 1000000000000) (-2728622504 / 1000000000000)
      | 1 => orderedInterval (-7022903083 / 1000000000000) (-7022902928 / 1000000000000)
      | 2 => orderedInterval (10034437107 / 1000000000000) (10034437309 / 1000000000000)
      | 3 => orderedInterval (11587708297 / 1000000000000) (11587716702 / 1000000000000)
      | 4 => orderedInterval (-14359139330 / 1000000000000) (-14359134568 / 1000000000000)
      | 5 => orderedInterval (-945334155 / 1000000000000) (-945333259 / 1000000000000)
      | 6 => orderedInterval (-6005460525 / 1000000000000) (-6005460296 / 1000000000000)
      | 7 => orderedInterval (-1437782774 / 1000000000000) (-1437782707 / 1000000000000)
      | _ => orderedInterval (-30916230880 / 1000000000000) (-30916230376 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-24569574796 / 1000000000000) (-24569570977 / 1000000000000)
    | 1 => orderedInterval (14830847101 / 1000000000000) (14830851032 / 1000000000000)
    | 2 => orderedInterval (30736678047 / 1000000000000) (30736683389 / 1000000000000)
    | 3 => orderedInterval (-10469393035 / 1000000000000) (-10469384425 / 1000000000000)
    | _ => orderedInterval (-41793327987 / 1000000000000) (-41793312627 / 1000000000000)

theorem compactCertificate473_stateChecks0 :
    compactCertificate473.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (689 / 2)) (orderedInterval (-12298906696 / 1000000000000) (-12298906614 / 1000000000000), orderedInterval (41208764556 / 1000000000000) (41208764639 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1015028563103789 / 4000000000000)) (orderedInterval (-3655218925 / 1000000000000) (-3655218924 / 1000000000000), orderedInterval (-49946976702 / 1000000000000) (-49946976701 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (328239382229837 / 800000000000)) (orderedInterval (17639444127 / 1000000000000) (17639444668 / 1000000000000), orderedInterval (-35241510960 / 1000000000000) (-35241510419 / 1000000000000))) = true
  rfl'

theorem compactCertificate473_stateChecks1 :
    compactCertificate473.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (296182803196423 / 4000000000000)) (orderedInterval (-49943325420 / 1000000000000) (-49943314204 / 1000000000000), orderedInterval (78461531294 / 1000000000000) (78461542509 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (795588670943131 / 4000000000000)) (orderedInterval (-55548347869 / 1000000000000) (-55548347024 / 1000000000000), orderedInterval (10869039009 / 1000000000000) (10869039855 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2160178005647727 / 4000000000000)) (orderedInterval (15724623545 / 1000000000000) (15724623546 / 1000000000000), orderedInterval (30506988924 / 1000000000000) (30506988925 / 1000000000000))) = true
  rfl'

theorem compactCertificate473_stateChecks2 :
    compactCertificate473.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1591177341886951 / 4000000000000)) (orderedInterval (15683410109 / 1000000000000) (15683410376 / 1000000000000), orderedInterval (-36821963956 / 1000000000000) (-36821963688 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 217 12 (2726509496072323 / 4000000000000)) (orderedInterval (-19381965077 / 1000000000000) (-19381965076 / 1000000000000), orderedInterval (-23614363827 / 1000000000000) (-23614363826 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2008334554488457 / 4000000000000)) (orderedInterval (7560880000 / 1000000000000) (7560880001 / 1000000000000), orderedInterval (34788868131 / 1000000000000) (34788868132 / 1000000000000))) = true
  rfl'

theorem compactCertificate473_stateChecks3 :
    compactCertificate473.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 245 12 (3081301672994311 / 4000000000000)) (orderedInterval (-28423409035 / 1000000000000) (-28423408589 / 1000000000000), orderedInterval (-4287282738 / 1000000000000) (-4287282292 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1778990350357519 / 4000000000000)) (orderedInterval (-20526317104 / 1000000000000) (-20526315486 / 1000000000000), orderedInterval (31804970797 / 1000000000000) (31804972415 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 251 12 (3156849595007771 / 4000000000000)) (orderedInterval (-28220756035 / 1000000000000) (-28220755237 / 1000000000000), orderedInterval (-3182247722 / 1000000000000) (-3182246924 / 1000000000000))) = true
  rfl'

theorem compactCertificate473_stateChecks4 :
    compactCertificate473.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 235 12 (2949538387415399 / 4000000000000)) (orderedInterval (3063398989 / 1000000000000) (3063398990 / 1000000000000), orderedInterval (-29224741820 / 1000000000000) (-29224741819 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2104929769215767 / 4000000000000)) (orderedInterval (-24211863566 / 1000000000000) (-24211854981 / 1000000000000), orderedInterval (24994084349 / 1000000000000) (24994092934 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2386766012829393 / 4000000000000)) (orderedInterval (17738628849 / 1000000000000) (17738628850 / 1000000000000), orderedInterval (27412445269 / 1000000000000) (27412445270 / 1000000000000))) = true
  rfl'

theorem compactCertificate473_stateChecks5 :
    compactCertificate473.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1989836668631617 / 4000000000000)) (orderedInterval (34155787924 / 1000000000000) (34155802233 / 1000000000000), orderedInterval (-10670308546 / 1000000000000) (-10670294236 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1758081042427957 / 4000000000000)) (orderedInterval (17655638580 / 1000000000000) (17655638581 / 1000000000000), orderedInterval (33695213212 / 1000000000000) (33695213213 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (509560410595743 / 800000000000)) (orderedInterval (240063426 / 1000000000000) (240063427 / 1000000000000), orderedInterval (-31613847215 / 1000000000000) (-31613847214 / 1000000000000))) = true
  rfl'

theorem compactCertificate473_stateChecks6 :
    compactCertificate473.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1409470912403021 / 4000000000000)) (orderedInterval (40891826364 / 1000000000000) (40891826368 / 1000000000000), orderedInterval (11541478716 / 1000000000000) (11541478719 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1194824101906981 / 4000000000000)) (orderedInterval (-39806401956 / 1000000000000) (-39806401955 / 1000000000000), orderedInterval (-23315145128 / 1000000000000) (-23315145127 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (747665445511543 / 4000000000000)) (orderedInterval (-41639407492 / 1000000000000) (-41639353289 / 1000000000000), orderedInterval (41002294457 / 1000000000000) (41002348660 / 1000000000000))) = true
  rfl'

theorem compactCertificate473_stateChecks7 :
    compactCertificate473.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (402096963219081 / 4000000000000)) (orderedInterval (55821179218 / 1000000000000) (55821179219 / 1000000000000), orderedInterval (56440914032 / 1000000000000) (56440914033 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1091771474140243 / 4000000000000)) (orderedInterval (-19217591418 / 1000000000000) (-19217591417 / 1000000000000), orderedInterval (-44271855250 / 1000000000000) (-44271855249 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1490720609524211 / 4000000000000)) (orderedInterval (15495675455 / 1000000000000) (15495675703 / 1000000000000), orderedInterval (-38336652688 / 1000000000000) (-38336652441 / 1000000000000))) = true
  rfl'

theorem compactCertificate473_stateChecks8 :
    compactCertificate473.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (630334554488457 / 4000000000000)) (orderedInterval (61046082544 / 1000000000000) (61046082545 / 1000000000000), orderedInterval (17504996653 / 1000000000000) (17504996654 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (2562274968867497 / 4000000000000)) (orderedInterval (14250427644 / 1000000000000) (14250427645 / 1000000000000), orderedInterval (28109344450 / 1000000000000) (28109344451 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1711480932969223 / 4000000000000)) (orderedInterval (38003490936 / 1000000000000) (38003490966 / 1000000000000), orderedInterval (6559695470 / 1000000000000) (6559695499 / 1000000000000))) = true
  rfl'

theorem compactCertificate473_states : ∀ j,
    BesselStateValid (compactCertificate473.point j) (compactCertificate473.state j) :=
  compactCertificate473.statesValid_of_checks3 compactCertificate473_stateChecks0
    compactCertificate473_stateChecks1 compactCertificate473_stateChecks2
    compactCertificate473_stateChecks3 compactCertificate473_stateChecks4
    compactCertificate473_stateChecks5 compactCertificate473_stateChecks6
    compactCertificate473_stateChecks7 compactCertificate473_stateChecks8

theorem compactCertificate473_chunkChecks0_0 :
    compactCertificate473.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (689 / 2) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12298906696 / 1000000000000) (-12298906614 / 1000000000000), orderedInterval (41208764556 / 1000000000000) (41208764639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1015028563103789 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-3655218925 / 1000000000000) (-3655218924 / 1000000000000), orderedInterval (-49946976702 / 1000000000000) (-49946976701 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (328239382229837 / 800000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17639444127 / 1000000000000) (17639444668 / 1000000000000), orderedInterval (-35241510960 / 1000000000000) (-35241510419 / 1000000000000)))) (orderedInterval (-3873812938 / 1000000000000) (-3873812849 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (296182803196423 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-49943325420 / 1000000000000) (-49943314204 / 1000000000000), orderedInterval (78461531294 / 1000000000000) (78461542509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (795588670943131 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-55548347869 / 1000000000000) (-55548347024 / 1000000000000), orderedInterval (10869039009 / 1000000000000) (10869039855 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2160178005647727 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (15724623545 / 1000000000000) (15724623546 / 1000000000000), orderedInterval (30506988924 / 1000000000000) (30506988925 / 1000000000000)))) (orderedInterval (-2604175482 / 1000000000000) (-2604175288 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1591177341886951 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (15683410109 / 1000000000000) (15683410376 / 1000000000000), orderedInterval (-36821963956 / 1000000000000) (-36821963688 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2726509496072323 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19381965077 / 1000000000000) (-19381965076 / 1000000000000), orderedInterval (-23614363827 / 1000000000000) (-23614363826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2008334554488457 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7560880000 / 1000000000000) (7560880001 / 1000000000000), orderedInterval (34788868131 / 1000000000000) (34788868132 / 1000000000000)))) (orderedInterval (780548892 / 1000000000000) (780548912 / 1000000000000))) = true
  rfl'

theorem compactCertificate473_chunkChecks0_1 :
    compactCertificate473.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3081301672994311 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28423409035 / 1000000000000) (-28423408589 / 1000000000000), orderedInterval (-4287282738 / 1000000000000) (-4287282292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1778990350357519 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20526317104 / 1000000000000) (-20526315486 / 1000000000000), orderedInterval (31804970797 / 1000000000000) (31804972415 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3156849595007771 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28220756035 / 1000000000000) (-28220755237 / 1000000000000), orderedInterval (-3182247722 / 1000000000000) (-3182246924 / 1000000000000)))) (orderedInterval (-482081480 / 1000000000000) (-482081030 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2949538387415399 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3063398989 / 1000000000000) (3063398990 / 1000000000000), orderedInterval (-29224741820 / 1000000000000) (-29224741819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2104929769215767 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24211863566 / 1000000000000) (-24211854981 / 1000000000000), orderedInterval (24994084349 / 1000000000000) (24994092934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2386766012829393 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (17738628849 / 1000000000000) (17738628850 / 1000000000000), orderedInterval (27412445269 / 1000000000000) (27412445270 / 1000000000000)))) (orderedInterval (-2434614716 / 1000000000000) (-2434613862 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1989836668631617 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34155787924 / 1000000000000) (34155802233 / 1000000000000), orderedInterval (-10670308546 / 1000000000000) (-10670294236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1758081042427957 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17655638580 / 1000000000000) (17655638581 / 1000000000000), orderedInterval (33695213212 / 1000000000000) (33695213213 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (509560410595743 / 800000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (240063426 / 1000000000000) (240063427 / 1000000000000), orderedInterval (-31613847215 / 1000000000000) (-31613847214 / 1000000000000)))) (orderedInterval (-609807204 / 1000000000000) (-609807005 / 1000000000000))) = true
  rfl'

theorem compactCertificate473_chunkChecks0_2 :
    compactCertificate473.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1409470912403021 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40891826364 / 1000000000000) (40891826368 / 1000000000000), orderedInterval (11541478716 / 1000000000000) (11541478719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1194824101906981 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39806401956 / 1000000000000) (-39806401955 / 1000000000000), orderedInterval (-23315145128 / 1000000000000) (-23315145127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (747665445511543 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-41639407492 / 1000000000000) (-41639353289 / 1000000000000), orderedInterval (41002294457 / 1000000000000) (41002348660 / 1000000000000)))) (orderedInterval (-5640835615 / 1000000000000) (-5640833763 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (402096963219081 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (55821179218 / 1000000000000) (55821179219 / 1000000000000), orderedInterval (56440914032 / 1000000000000) (56440914033 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1091771474140243 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19217591418 / 1000000000000) (-19217591417 / 1000000000000), orderedInterval (-44271855250 / 1000000000000) (-44271855249 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1490720609524211 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (15495675455 / 1000000000000) (15495675703 / 1000000000000), orderedInterval (-38336652688 / 1000000000000) (-38336652441 / 1000000000000)))) (orderedInterval (-1782328857 / 1000000000000) (-1782328797 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (630334554488457 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61046082544 / 1000000000000) (61046082545 / 1000000000000), orderedInterval (17504996653 / 1000000000000) (17504996654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2562274968867497 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14250427644 / 1000000000000) (14250427645 / 1000000000000), orderedInterval (28109344450 / 1000000000000) (28109344451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1711480932969223 / 4000000000000) 0 (IntervalRat.scale (689 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38003490936 / 1000000000000) (38003490966 / 1000000000000), orderedInterval (6559695470 / 1000000000000) (6559695499 / 1000000000000)))) (orderedInterval (-7922467396 / 1000000000000) (-7922467295 / 1000000000000))) = true
  rfl'

theorem compactCertificate473_chunkChecks0 :
    compactCertificate473.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate473.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate473_chunkChecks0_0
    compactCertificate473_chunkChecks0_1 compactCertificate473_chunkChecks0_2

theorem compactCertificate473_chunkChecks1_0 :
    compactCertificate473.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (689 / 2) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12298906696 / 1000000000000) (-12298906614 / 1000000000000), orderedInterval (41208764556 / 1000000000000) (41208764639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1015028563103789 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-3655218925 / 1000000000000) (-3655218924 / 1000000000000), orderedInterval (-49946976702 / 1000000000000) (-49946976701 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (328239382229837 / 800000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17639444127 / 1000000000000) (17639444668 / 1000000000000), orderedInterval (-35241510960 / 1000000000000) (-35241510419 / 1000000000000)))) (orderedInterval (13527892849 / 1000000000000) (13527892947 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (296182803196423 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-49943325420 / 1000000000000) (-49943314204 / 1000000000000), orderedInterval (78461531294 / 1000000000000) (78461542509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (795588670943131 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-55548347869 / 1000000000000) (-55548347024 / 1000000000000), orderedInterval (10869039009 / 1000000000000) (10869039855 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2160178005647727 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (15724623545 / 1000000000000) (15724623546 / 1000000000000), orderedInterval (30506988924 / 1000000000000) (30506988925 / 1000000000000)))) (orderedInterval (-3353587511 / 1000000000000) (-3353587419 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1591177341886951 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (15683410109 / 1000000000000) (15683410376 / 1000000000000), orderedInterval (-36821963956 / 1000000000000) (-36821963688 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2726509496072323 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19381965077 / 1000000000000) (-19381965076 / 1000000000000), orderedInterval (-23614363827 / 1000000000000) (-23614363826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2008334554488457 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7560880000 / 1000000000000) (7560880001 / 1000000000000), orderedInterval (34788868131 / 1000000000000) (34788868132 / 1000000000000)))) (orderedInterval (2666508374 / 1000000000000) (2666508408 / 1000000000000))) = true
  rfl'

theorem compactCertificate473_chunkChecks1_1 :
    compactCertificate473.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3081301672994311 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28423409035 / 1000000000000) (-28423408589 / 1000000000000), orderedInterval (-4287282738 / 1000000000000) (-4287282292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1778990350357519 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20526317104 / 1000000000000) (-20526315486 / 1000000000000), orderedInterval (31804970797 / 1000000000000) (31804972415 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3156849595007771 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28220756035 / 1000000000000) (-28220755237 / 1000000000000), orderedInterval (-3182247722 / 1000000000000) (-3182246924 / 1000000000000)))) (orderedInterval (3709300766 / 1000000000000) (3709301640 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2949538387415399 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3063398989 / 1000000000000) (3063398990 / 1000000000000), orderedInterval (-29224741820 / 1000000000000) (-29224741819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2104929769215767 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24211863566 / 1000000000000) (-24211854981 / 1000000000000), orderedInterval (24994084349 / 1000000000000) (24994092934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2386766012829393 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (17738628849 / 1000000000000) (17738628850 / 1000000000000), orderedInterval (27412445269 / 1000000000000) (27412445270 / 1000000000000)))) (orderedInterval (4499343556 / 1000000000000) (4499344863 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1989836668631617 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34155787924 / 1000000000000) (34155802233 / 1000000000000), orderedInterval (-10670308546 / 1000000000000) (-10670294236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1758081042427957 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17655638580 / 1000000000000) (17655638581 / 1000000000000), orderedInterval (33695213212 / 1000000000000) (33695213213 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (509560410595743 / 800000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (240063426 / 1000000000000) (240063427 / 1000000000000), orderedInterval (-31613847215 / 1000000000000) (-31613847214 / 1000000000000)))) (orderedInterval (-4134629680 / 1000000000000) (-4134629393 / 1000000000000))) = true
  rfl'

theorem compactCertificate473_chunkChecks1_2 :
    compactCertificate473.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1409470912403021 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40891826364 / 1000000000000) (40891826368 / 1000000000000), orderedInterval (11541478716 / 1000000000000) (11541478719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1194824101906981 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39806401956 / 1000000000000) (-39806401955 / 1000000000000), orderedInterval (-23315145128 / 1000000000000) (-23315145127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (747665445511543 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-41639407492 / 1000000000000) (-41639353289 / 1000000000000), orderedInterval (41002294457 / 1000000000000) (41002348660 / 1000000000000)))) (orderedInterval (-19073632 / 1000000000000) (-19072593 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (402096963219081 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (55821179218 / 1000000000000) (55821179219 / 1000000000000), orderedInterval (56440914032 / 1000000000000) (56440914033 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1091771474140243 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19217591418 / 1000000000000) (-19217591417 / 1000000000000), orderedInterval (-44271855250 / 1000000000000) (-44271855249 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1490720609524211 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (15495675455 / 1000000000000) (15495675703 / 1000000000000), orderedInterval (-38336652688 / 1000000000000) (-38336652441 / 1000000000000)))) (orderedInterval (3670069737 / 1000000000000) (3670069795 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (630334554488457 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61046082544 / 1000000000000) (61046082545 / 1000000000000), orderedInterval (17504996653 / 1000000000000) (17504996654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2562274968867497 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14250427644 / 1000000000000) (14250427645 / 1000000000000), orderedInterval (28109344450 / 1000000000000) (28109344451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1711480932969223 / 4000000000000) 1 (IntervalRat.scale (689 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38003490936 / 1000000000000) (38003490966 / 1000000000000), orderedInterval (6559695470 / 1000000000000) (6559695499 / 1000000000000)))) (orderedInterval (-5734977358 / 1000000000000) (-5734977216 / 1000000000000))) = true
  rfl'

theorem compactCertificate473_chunkChecks1 :
    compactCertificate473.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate473.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate473_chunkChecks1_0
    compactCertificate473_chunkChecks1_1 compactCertificate473_chunkChecks1_2

theorem compactCertificate473_chunkChecks2_0 :
    compactCertificate473.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (689 / 2) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12298906696 / 1000000000000) (-12298906614 / 1000000000000), orderedInterval (41208764556 / 1000000000000) (41208764639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1015028563103789 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-3655218925 / 1000000000000) (-3655218924 / 1000000000000), orderedInterval (-49946976702 / 1000000000000) (-49946976701 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (328239382229837 / 800000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17639444127 / 1000000000000) (17639444668 / 1000000000000), orderedInterval (-35241510960 / 1000000000000) (-35241510419 / 1000000000000)))) (orderedInterval (3385796016 / 1000000000000) (3385796125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (296182803196423 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-49943325420 / 1000000000000) (-49943314204 / 1000000000000), orderedInterval (78461531294 / 1000000000000) (78461542509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (795588670943131 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-55548347869 / 1000000000000) (-55548347024 / 1000000000000), orderedInterval (10869039009 / 1000000000000) (10869039855 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2160178005647727 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (15724623545 / 1000000000000) (15724623546 / 1000000000000), orderedInterval (30506988924 / 1000000000000) (30506988925 / 1000000000000)))) (orderedInterval (3407812237 / 1000000000000) (3407812318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1591177341886951 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (15683410109 / 1000000000000) (15683410376 / 1000000000000), orderedInterval (-36821963956 / 1000000000000) (-36821963688 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2726509496072323 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19381965077 / 1000000000000) (-19381965076 / 1000000000000), orderedInterval (-23614363827 / 1000000000000) (-23614363826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2008334554488457 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7560880000 / 1000000000000) (7560880001 / 1000000000000), orderedInterval (34788868131 / 1000000000000) (34788868132 / 1000000000000)))) (orderedInterval (-2736246983 / 1000000000000) (-2736246923 / 1000000000000))) = true
  rfl'

theorem compactCertificate473_chunkChecks2_1 :
    compactCertificate473.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3081301672994311 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28423409035 / 1000000000000) (-28423408589 / 1000000000000), orderedInterval (-4287282738 / 1000000000000) (-4287282292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1778990350357519 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20526317104 / 1000000000000) (-20526315486 / 1000000000000), orderedInterval (31804970797 / 1000000000000) (31804972415 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3156849595007771 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28220756035 / 1000000000000) (-28220755237 / 1000000000000), orderedInterval (-3182247722 / 1000000000000) (-3182246924 / 1000000000000)))) (orderedInterval (-1674133337 / 1000000000000) (-1674131537 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2949538387415399 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3063398989 / 1000000000000) (3063398990 / 1000000000000), orderedInterval (-29224741820 / 1000000000000) (-29224741819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2104929769215767 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24211863566 / 1000000000000) (-24211854981 / 1000000000000), orderedInterval (24994084349 / 1000000000000) (24994092934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2386766012829393 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (17738628849 / 1000000000000) (17738628850 / 1000000000000), orderedInterval (27412445269 / 1000000000000) (27412445270 / 1000000000000)))) (orderedInterval (5851883610 / 1000000000000) (5851885619 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1989836668631617 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34155787924 / 1000000000000) (34155802233 / 1000000000000), orderedInterval (-10670308546 / 1000000000000) (-10670294236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1758081042427957 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17655638580 / 1000000000000) (17655638581 / 1000000000000), orderedInterval (33695213212 / 1000000000000) (33695213213 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (509560410595743 / 800000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (240063426 / 1000000000000) (240063427 / 1000000000000), orderedInterval (-31613847215 / 1000000000000) (-31613847214 / 1000000000000)))) (orderedInterval (813170662 / 1000000000000) (813171079 / 1000000000000))) = true
  rfl'

theorem compactCertificate473_chunkChecks2_2 :
    compactCertificate473.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1409470912403021 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40891826364 / 1000000000000) (40891826368 / 1000000000000), orderedInterval (11541478716 / 1000000000000) (11541478719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1194824101906981 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39806401956 / 1000000000000) (-39806401955 / 1000000000000), orderedInterval (-23315145128 / 1000000000000) (-23315145127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (747665445511543 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-41639407492 / 1000000000000) (-41639353289 / 1000000000000), orderedInterval (41002294457 / 1000000000000) (41002348660 / 1000000000000)))) (orderedInterval (5545603097 / 1000000000000) (5545603697 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (402096963219081 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (55821179218 / 1000000000000) (55821179219 / 1000000000000), orderedInterval (56440914032 / 1000000000000) (56440914033 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1091771474140243 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19217591418 / 1000000000000) (-19217591417 / 1000000000000), orderedInterval (-44271855250 / 1000000000000) (-44271855249 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1490720609524211 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (15495675455 / 1000000000000) (15495675703 / 1000000000000), orderedInterval (-38336652688 / 1000000000000) (-38336652441 / 1000000000000)))) (orderedInterval (1193237527 / 1000000000000) (1193237586 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (630334554488457 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61046082544 / 1000000000000) (61046082545 / 1000000000000), orderedInterval (17504996653 / 1000000000000) (17504996654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2562274968867497 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14250427644 / 1000000000000) (14250427645 / 1000000000000), orderedInterval (28109344450 / 1000000000000) (28109344451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1711480932969223 / 4000000000000) 2 (IntervalRat.scale (689 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38003490936 / 1000000000000) (38003490966 / 1000000000000), orderedInterval (6559695470 / 1000000000000) (6559695499 / 1000000000000)))) (orderedInterval (14949555218 / 1000000000000) (14949555425 / 1000000000000))) = true
  rfl'

theorem compactCertificate473_chunkChecks2 :
    compactCertificate473.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate473.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate473_chunkChecks2_0
    compactCertificate473_chunkChecks2_1 compactCertificate473_chunkChecks2_2

theorem compactCertificate473_chunkChecks3_0 :
    compactCertificate473.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (689 / 2) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12298906696 / 1000000000000) (-12298906614 / 1000000000000), orderedInterval (41208764556 / 1000000000000) (41208764639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1015028563103789 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-3655218925 / 1000000000000) (-3655218924 / 1000000000000), orderedInterval (-49946976702 / 1000000000000) (-49946976701 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (328239382229837 / 800000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17639444127 / 1000000000000) (17639444668 / 1000000000000), orderedInterval (-35241510960 / 1000000000000) (-35241510419 / 1000000000000)))) (orderedInterval (-12663707061 / 1000000000000) (-12663706938 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (296182803196423 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-49943325420 / 1000000000000) (-49943314204 / 1000000000000), orderedInterval (78461531294 / 1000000000000) (78461542509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (795588670943131 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-55548347869 / 1000000000000) (-55548347024 / 1000000000000), orderedInterval (10869039009 / 1000000000000) (10869039855 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2160178005647727 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (15724623545 / 1000000000000) (15724623546 / 1000000000000), orderedInterval (30506988924 / 1000000000000) (30506988925 / 1000000000000)))) (orderedInterval (8276777549 / 1000000000000) (8276777654 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1591177341886951 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (15683410109 / 1000000000000) (15683410376 / 1000000000000), orderedInterval (-36821963956 / 1000000000000) (-36821963688 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2726509496072323 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19381965077 / 1000000000000) (-19381965076 / 1000000000000), orderedInterval (-23614363827 / 1000000000000) (-23614363826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2008334554488457 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7560880000 / 1000000000000) (7560880001 / 1000000000000), orderedInterval (34788868131 / 1000000000000) (34788868132 / 1000000000000)))) (orderedInterval (-8236676880 / 1000000000000) (-8236676771 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate473_chunkChecks3_1 :
    compactCertificate473.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3081301672994311 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28423409035 / 1000000000000) (-28423408589 / 1000000000000), orderedInterval (-4287282738 / 1000000000000) (-4287282292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1778990350357519 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20526317104 / 1000000000000) (-20526315486 / 1000000000000), orderedInterval (31804970797 / 1000000000000) (31804972415 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3156849595007771 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28220756035 / 1000000000000) (-28220755237 / 1000000000000), orderedInterval (-3182247722 / 1000000000000) (-3182246924 / 1000000000000)))) (orderedInterval (-8143705637 / 1000000000000) (-8143701796 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2949538387415399 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3063398989 / 1000000000000) (3063398990 / 1000000000000), orderedInterval (-29224741820 / 1000000000000) (-29224741819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2104929769215767 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24211863566 / 1000000000000) (-24211854981 / 1000000000000), orderedInterval (24994084349 / 1000000000000) (24994092934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2386766012829393 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (17738628849 / 1000000000000) (17738628850 / 1000000000000), orderedInterval (27412445269 / 1000000000000) (27412445270 / 1000000000000)))) (orderedInterval (-12894101217 / 1000000000000) (-12894098131 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1989836668631617 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34155787924 / 1000000000000) (34155802233 / 1000000000000), orderedInterval (-10670308546 / 1000000000000) (-10670294236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1758081042427957 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17655638580 / 1000000000000) (17655638581 / 1000000000000), orderedInterval (33695213212 / 1000000000000) (33695213213 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (509560410595743 / 800000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (240063426 / 1000000000000) (240063427 / 1000000000000), orderedInterval (-31613847215 / 1000000000000) (-31613847214 / 1000000000000)))) (orderedInterval (9489027784 / 1000000000000) (9489028393 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate473_chunkChecks3_2 :
    compactCertificate473.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1409470912403021 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40891826364 / 1000000000000) (40891826368 / 1000000000000), orderedInterval (11541478716 / 1000000000000) (11541478719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1194824101906981 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39806401956 / 1000000000000) (-39806401955 / 1000000000000), orderedInterval (-23315145128 / 1000000000000) (-23315145127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (747665445511543 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-41639407492 / 1000000000000) (-41639353289 / 1000000000000), orderedInterval (41002294457 / 1000000000000) (41002348660 / 1000000000000)))) (orderedInterval (885196882 / 1000000000000) (885197240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (402096963219081 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (55821179218 / 1000000000000) (55821179219 / 1000000000000), orderedInterval (56440914032 / 1000000000000) (56440914033 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1091771474140243 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19217591418 / 1000000000000) (-19217591417 / 1000000000000), orderedInterval (-44271855250 / 1000000000000) (-44271855249 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1490720609524211 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (15495675455 / 1000000000000) (15495675703 / 1000000000000), orderedInterval (-38336652688 / 1000000000000) (-38336652441 / 1000000000000)))) (orderedInterval (-4196725518 / 1000000000000) (-4196725455 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (630334554488457 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61046082544 / 1000000000000) (61046082545 / 1000000000000), orderedInterval (17504996653 / 1000000000000) (17504996654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2562274968867497 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14250427644 / 1000000000000) (14250427645 / 1000000000000), orderedInterval (28109344450 / 1000000000000) (28109344451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1711480932969223 / 4000000000000) 3 (IntervalRat.scale (689 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38003490936 / 1000000000000) (38003490966 / 1000000000000), orderedInterval (6559695470 / 1000000000000) (6559695499 / 1000000000000)))) (orderedInterval (17014521063 / 1000000000000) (17014521379 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate473_chunkChecks3 :
    compactCertificate473.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate473.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate473_chunkChecks3_0
    compactCertificate473_chunkChecks3_1 compactCertificate473_chunkChecks3_2

theorem compactCertificate473_chunkChecks4_0 :
    compactCertificate473.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (689 / 2) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12298906696 / 1000000000000) (-12298906614 / 1000000000000), orderedInterval (41208764556 / 1000000000000) (41208764639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1015028563103789 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-3655218925 / 1000000000000) (-3655218924 / 1000000000000), orderedInterval (-49946976702 / 1000000000000) (-49946976701 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (328239382229837 / 800000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (17639444127 / 1000000000000) (17639444668 / 1000000000000), orderedInterval (-35241510960 / 1000000000000) (-35241510419 / 1000000000000)))) (orderedInterval (-2728622644 / 1000000000000) (-2728622504 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (296182803196423 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-49943325420 / 1000000000000) (-49943314204 / 1000000000000), orderedInterval (78461531294 / 1000000000000) (78461542509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (795588670943131 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-55548347869 / 1000000000000) (-55548347024 / 1000000000000), orderedInterval (10869039009 / 1000000000000) (10869039855 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2160178005647727 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (15724623545 / 1000000000000) (15724623546 / 1000000000000), orderedInterval (30506988924 / 1000000000000) (30506988925 / 1000000000000)))) (orderedInterval (-7022903083 / 1000000000000) (-7022902928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1591177341886951 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (15683410109 / 1000000000000) (15683410376 / 1000000000000), orderedInterval (-36821963956 / 1000000000000) (-36821963688 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2726509496072323 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19381965077 / 1000000000000) (-19381965076 / 1000000000000), orderedInterval (-23614363827 / 1000000000000) (-23614363826 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2008334554488457 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7560880000 / 1000000000000) (7560880001 / 1000000000000), orderedInterval (34788868131 / 1000000000000) (34788868132 / 1000000000000)))) (orderedInterval (10034437107 / 1000000000000) (10034437309 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate473_chunkChecks4_1 :
    compactCertificate473.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3081301672994311 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28423409035 / 1000000000000) (-28423408589 / 1000000000000), orderedInterval (-4287282738 / 1000000000000) (-4287282292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1778990350357519 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20526317104 / 1000000000000) (-20526315486 / 1000000000000), orderedInterval (31804970797 / 1000000000000) (31804972415 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3156849595007771 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28220756035 / 1000000000000) (-28220755237 / 1000000000000), orderedInterval (-3182247722 / 1000000000000) (-3182246924 / 1000000000000)))) (orderedInterval (11587708297 / 1000000000000) (11587716702 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2949538387415399 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3063398989 / 1000000000000) (3063398990 / 1000000000000), orderedInterval (-29224741820 / 1000000000000) (-29224741819 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2104929769215767 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24211863566 / 1000000000000) (-24211854981 / 1000000000000), orderedInterval (24994084349 / 1000000000000) (24994092934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2386766012829393 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (17738628849 / 1000000000000) (17738628850 / 1000000000000), orderedInterval (27412445269 / 1000000000000) (27412445270 / 1000000000000)))) (orderedInterval (-14359139330 / 1000000000000) (-14359134568 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1989836668631617 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34155787924 / 1000000000000) (34155802233 / 1000000000000), orderedInterval (-10670308546 / 1000000000000) (-10670294236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1758081042427957 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (17655638580 / 1000000000000) (17655638581 / 1000000000000), orderedInterval (33695213212 / 1000000000000) (33695213213 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (509560410595743 / 800000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (240063426 / 1000000000000) (240063427 / 1000000000000), orderedInterval (-31613847215 / 1000000000000) (-31613847214 / 1000000000000)))) (orderedInterval (-945334155 / 1000000000000) (-945333259 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate473_chunkChecks4_2 :
    compactCertificate473.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1409470912403021 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40891826364 / 1000000000000) (40891826368 / 1000000000000), orderedInterval (11541478716 / 1000000000000) (11541478719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1194824101906981 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39806401956 / 1000000000000) (-39806401955 / 1000000000000), orderedInterval (-23315145128 / 1000000000000) (-23315145127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (747665445511543 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-41639407492 / 1000000000000) (-41639353289 / 1000000000000), orderedInterval (41002294457 / 1000000000000) (41002348660 / 1000000000000)))) (orderedInterval (-6005460525 / 1000000000000) (-6005460296 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (402096963219081 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (55821179218 / 1000000000000) (55821179219 / 1000000000000), orderedInterval (56440914032 / 1000000000000) (56440914033 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1091771474140243 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19217591418 / 1000000000000) (-19217591417 / 1000000000000), orderedInterval (-44271855250 / 1000000000000) (-44271855249 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1490720609524211 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (15495675455 / 1000000000000) (15495675703 / 1000000000000), orderedInterval (-38336652688 / 1000000000000) (-38336652441 / 1000000000000)))) (orderedInterval (-1437782774 / 1000000000000) (-1437782707 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (630334554488457 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61046082544 / 1000000000000) (61046082545 / 1000000000000), orderedInterval (17504996653 / 1000000000000) (17504996654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2562274968867497 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14250427644 / 1000000000000) (14250427645 / 1000000000000), orderedInterval (28109344450 / 1000000000000) (28109344451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1711480932969223 / 4000000000000) 4 (IntervalRat.scale (689 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38003490936 / 1000000000000) (38003490966 / 1000000000000), orderedInterval (6559695470 / 1000000000000) (6559695499 / 1000000000000)))) (orderedInterval (-30916230880 / 1000000000000) (-30916230376 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate473_chunkChecks4 :
    compactCertificate473.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate473.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate473_chunkChecks4_0
    compactCertificate473_chunkChecks4_1 compactCertificate473_chunkChecks4_2

theorem compactCertificate473_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate473.chunkCheck r b = true :=
  compactCertificate473.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate473_chunkChecks0
    · exact compactCertificate473_chunkChecks1
    · exact compactCertificate473_chunkChecks2
    · exact compactCertificate473_chunkChecks3
    · exact compactCertificate473_chunkChecks4)

theorem compactCertificate473_coefficient0 :
    compactCertificate473.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate473_coefficient1 :
    compactCertificate473.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate473_coefficient2 :
    compactCertificate473.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate473_coefficient3 :
    compactCertificate473.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate473_coefficient4 :
    compactCertificate473.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate473_coefficients : ∀ r : Fin 5,
    compactCertificate473.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate473_coefficient0
  · exact compactCertificate473_coefficient1
  · exact compactCertificate473_coefficient2
  · exact compactCertificate473_coefficient3
  · exact compactCertificate473_coefficient4

theorem compactCertificate473_lower : (1 : ℚ) ≤ compactCertificate473.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate473, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate473_proves {t : ℝ} (ht : t ∈ compactCertificate473.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate473.proves compactCertificate473_states compactCertificate473_chunks
    compactCertificate473_coefficients compactCertificate473_lower ht

end Erdos232
