/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate495 : CompactCertificate where
  left := 366
  right := 367
  center := 733 / 2
  grid := fun i =>
    match i.val with
    | 0 => 117
    | 1 => 86
    | 2 => 139
    | 3 => 25
    | 4 => 67
    | 5 => 183
    | 6 => 135
    | 7 => 231
    | 8 => 170
    | 9 => 261
    | 10 => 151
    | 11 => 267
    | 12 => 250
    | 13 => 178
    | 14 => 202
    | 15 => 169
    | 16 => 149
    | 17 => 216
    | 18 => 119
    | 19 => 101
    | 20 => 63
    | 21 => 34
    | 22 => 92
    | 23 => 126
    | 24 => 53
    | 25 => 217
    | _ => 145
  point := fun i =>
    match i.val with
    | 0 => 733 / 2
    | 1 => 1079848964811433 / 4000000000000
    | 2 => 349200968322889 / 800000000000
    | 3 => 315097234750331 / 4000000000000
    | 4 => 846395494631807 / 4000000000000
    | 5 => 2298128415297219 / 4000000000000
    | 6 => 1692790989264347 / 4000000000000
    | 7 => 2900626212802631 / 4000000000000
    | 8 => 2136588139971029 / 4000000000000
    | 9 => 3278075655014267 / 4000000000000
    | 10 => 1892597861846243 / 4000000000000
    | 11 => 3358448117765887 / 4000000000000
    | 12 => 3137897878048603 / 4000000000000
    | 13 => 2239351989601099 / 4000000000000
    | 14 => 2539186483895421 / 4000000000000
    | 15 => 2116908966773549 / 4000000000000
    | 16 => 1870353271552529 / 4000000000000
    | 17 => 542101278616371 / 800000000000
    | 18 => 1499480665880137 / 4000000000000
    | 19 => 1271126366760257 / 4000000000000
    | 20 => 795411860028971 / 4000000000000
    | 21 => 427775143743957 / 4000000000000
    | 22 => 1161492729382871 / 4000000000000
    | 23 => 1585919022904567 / 4000000000000
    | 24 => 670588139971029 / 4000000000000
    | 25 => 2725903559041909 / 4000000000000
    | _ => 1820777247991931 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (11569239814 / 1000000000000) (11569239876 / 1000000000000), orderedInterval (-40055505644 / 1000000000000) (-40055505582 / 1000000000000))
    | 1 => (orderedInterval (26213614080 / 1000000000000) (26213614081 / 1000000000000), orderedInterval (40829670236 / 1000000000000) (40829670237 / 1000000000000))
    | 2 => (orderedInterval (-21719120928 / 1000000000000) (-21719120927 / 1000000000000), orderedInterval (-31387549199 / 1000000000000) (-31387549198 / 1000000000000))
    | 3 => (orderedInterval (-76521722622 / 1000000000000) (-76521722621 / 1000000000000), orderedInterval (-46693961610 / 1000000000000) (-46693961609 / 1000000000000))
    | 4 => (orderedInterval (-51958730292 / 1000000000000) (-51958726082 / 1000000000000), orderedInterval (17698323542 / 1000000000000) (17698327753 / 1000000000000))
    | 5 => (orderedInterval (-13141302093 / 1000000000000) (-13141302092 / 1000000000000), orderedInterval (-30572431116 / 1000000000000) (-30572431115 / 1000000000000))
    | 6 => (orderedInterval (5110897267 / 1000000000000) (5110897271 / 1000000000000), orderedInterval (-38453246111 / 1000000000000) (-38453246107 / 1000000000000))
    | 7 => (orderedInterval (-6866625766 / 1000000000000) (-6866625765 / 1000000000000), orderedInterval (-28818108852 / 1000000000000) (-28818108851 / 1000000000000))
    | 8 => (orderedInterval (26195648843 / 1000000000000) (26195648844 / 1000000000000), orderedInterval (22461732391 / 1000000000000) (22461732392 / 1000000000000))
    | 9 => (orderedInterval (-9517189329 / 1000000000000) (-9517189328 / 1000000000000), orderedInterval (-26190463165 / 1000000000000) (-26190463164 / 1000000000000))
    | 10 => (orderedInterval (15819112600 / 1000000000000) (15819112884 / 1000000000000), orderedInterval (-33111280779 / 1000000000000) (-33111280494 / 1000000000000))
    | 11 => (orderedInterval (-27529779159 / 1000000000000) (-27529774318 / 1000000000000), orderedInterval (601319577 / 1000000000000) (601324418 / 1000000000000))
    | 12 => (orderedInterval (-3931615250 / 1000000000000) (-3931615249 / 1000000000000), orderedInterval (28217155438 / 1000000000000) (28217155439 / 1000000000000))
    | 13 => (orderedInterval (33337343506 / 1000000000000) (33337343613 / 1000000000000), orderedInterval (5046748299 / 1000000000000) (5046748405 / 1000000000000))
    | 14 => (orderedInterval (26302188344 / 1000000000000) (26302188345 / 1000000000000), orderedInterval (17616368766 / 1000000000000) (17616368767 / 1000000000000))
    | 15 => (orderedInterval (27525641124 / 1000000000000) (27525675559 / 1000000000000), orderedInterval (-21127236870 / 1000000000000) (-21127202434 / 1000000000000))
    | 16 => (orderedInterval (-10060256464 / 1000000000000) (-10060256463 / 1000000000000), orderedInterval (-35489780703 / 1000000000000) (-35489780702 / 1000000000000))
    | 17 => (orderedInterval (-5252093824 / 1000000000000) (-5252093823 / 1000000000000), orderedInterval (30201563660 / 1000000000000) (30201563662 / 1000000000000))
    | 18 => (orderedInterval (-40077896111 / 1000000000000) (-40077892275 / 1000000000000), orderedInterval (9645207449 / 1000000000000) (9645211284 / 1000000000000))
    | 19 => (orderedInterval (-42691971692 / 1000000000000) (-42691971690 / 1000000000000), orderedInterval (-13375983102 / 1000000000000) (-13375983100 / 1000000000000))
    | 20 => (orderedInterval (-55974423216 / 1000000000000) (-55974422726 / 1000000000000), orderedInterval (8405975180 / 1000000000000) (8405975671 / 1000000000000))
    | 21 => (orderedInterval (61096145591 / 1000000000000) (61096145592 / 1000000000000), orderedInterval (46832184597 / 1000000000000) (46832184598 / 1000000000000))
    | 22 => (orderedInterval (39650554577 / 1000000000000) (39650613492 / 1000000000000), orderedInterval (-24973102392 / 1000000000000) (-24973043477 / 1000000000000))
    | 23 => (orderedInterval (39640915698 / 1000000000000) (39640915732 / 1000000000000), orderedInterval (5804663347 / 1000000000000) (5804663381 / 1000000000000))
    | 24 => (orderedInterval (-57748591510 / 1000000000000) (-57748586918 / 1000000000000), orderedInterval (21677328039 / 1000000000000) (21677332631 / 1000000000000))
    | 25 => (orderedInterval (-15596055149 / 1000000000000) (-15596055148 / 1000000000000), orderedInterval (-26274316943 / 1000000000000) (-26274316942 / 1000000000000))
    | _ => (orderedInterval (-16216080638 / 1000000000000) (-16216080637 / 1000000000000), orderedInterval (-33680946179 / 1000000000000) (-33680946178 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (3555398898 / 1000000000000) (3555398948 / 1000000000000)
      | 1 => orderedInterval (-132687101 / 1000000000000) (-132686902 / 1000000000000)
      | 2 => orderedInterval (844891350 / 1000000000000) (844891371 / 1000000000000)
      | 3 => orderedInterval (-1050364684 / 1000000000000) (-1050363830 / 1000000000000)
      | 4 => orderedInterval (3090348290 / 1000000000000) (3090348344 / 1000000000000)
      | 5 => orderedInterval (759097702 / 1000000000000) (759098135 / 1000000000000)
      | 6 => orderedInterval (7002253222 / 1000000000000) (7002253944 / 1000000000000)
      | 7 => orderedInterval (-5065730483 / 1000000000000) (-5065729099 / 1000000000000)
      | _ => orderedInterval (3963985993 / 1000000000000) (3963986122 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-17790010470 / 1000000000000) (-17790010416 / 1000000000000)
      | 1 => orderedInterval (3889003159 / 1000000000000) (3889003298 / 1000000000000)
      | 2 => orderedInterval (2549881662 / 1000000000000) (2549881699 / 1000000000000)
      | 3 => orderedInterval (7434720081 / 1000000000000) (7434721986 / 1000000000000)
      | 4 => orderedInterval (-515781118 / 1000000000000) (-515781032 / 1000000000000)
      | 5 => orderedInterval (3668575924 / 1000000000000) (3668576550 / 1000000000000)
      | 6 => orderedInterval (-772495124 / 1000000000000) (-772494402 / 1000000000000)
      | 7 => orderedInterval (-284709927 / 1000000000000) (-284708825 / 1000000000000)
      | _ => orderedInterval (11885415462 / 1000000000000) (11885415618 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-2861774722 / 1000000000000) (-2861774664 / 1000000000000)
      | 1 => orderedInterval (-1712351080 / 1000000000000) (-1712350959 / 1000000000000)
      | 2 => orderedInterval (-2180858593 / 1000000000000) (-2180858528 / 1000000000000)
      | 3 => orderedInterval (10109707261 / 1000000000000) (10109711558 / 1000000000000)
      | 4 => orderedInterval (-7280240726 / 1000000000000) (-7280240584 / 1000000000000)
      | 5 => orderedInterval (-1150193237 / 1000000000000) (-1150192330 / 1000000000000)
      | 6 => orderedInterval (-7982292439 / 1000000000000) (-7982291709 / 1000000000000)
      | 7 => orderedInterval (4216882782 / 1000000000000) (4216883667 / 1000000000000)
      | _ => orderedInterval (-9042333638 / 1000000000000) (-9042333421 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (18843872716 / 1000000000000) (18843872780 / 1000000000000)
      | 1 => orderedInterval (-8497230488 / 1000000000000) (-8497230354 / 1000000000000)
      | 2 => orderedInterval (-8559644860 / 1000000000000) (-8559644743 / 1000000000000)
      | 3 => orderedInterval (-47806949341 / 1000000000000) (-47806939596 / 1000000000000)
      | 4 => orderedInterval (3777621367 / 1000000000000) (3777621602 / 1000000000000)
      | 5 => orderedInterval (-8367393439 / 1000000000000) (-8367392122 / 1000000000000)
      | 6 => orderedInterval (1134831978 / 1000000000000) (1134832718 / 1000000000000)
      | 7 => orderedInterval (291413452 / 1000000000000) (291414163 / 1000000000000)
      | _ => orderedInterval (-25844792498 / 1000000000000) (-25844792170 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (1990290383 / 1000000000000) (1990290453 / 1000000000000)
      | 1 => orderedInterval (5478987534 / 1000000000000) (5478987712 / 1000000000000)
      | 2 => orderedInterval (6149061076 / 1000000000000) (6149061291 / 1000000000000)
      | 3 => orderedInterval (-61998002144 / 1000000000000) (-61997979941 / 1000000000000)
      | 4 => orderedInterval (17434714125 / 1000000000000) (17434714526 / 1000000000000)
      | 5 => orderedInterval (1381513060 / 1000000000000) (1381514980 / 1000000000000)
      | 6 => orderedInterval (8215520897 / 1000000000000) (8215521651 / 1000000000000)
      | 7 => orderedInterval (-4525026402 / 1000000000000) (-4525025826 / 1000000000000)
      | _ => orderedInterval (22541518059 / 1000000000000) (22541518583 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (12967193187 / 1000000000000) (12967197033 / 1000000000000)
    | 1 => orderedInterval (10064599649 / 1000000000000) (10064604476 / 1000000000000)
    | 2 => orderedInterval (-17883454392 / 1000000000000) (-17883446970 / 1000000000000)
    | 3 => orderedInterval (-75028271113 / 1000000000000) (-75028257722 / 1000000000000)
    | _ => orderedInterval (-3331423412 / 1000000000000) (-3331396571 / 1000000000000)

theorem compactCertificate495_stateChecks0 :
    compactCertificate495.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (733 / 2)) (orderedInterval (11569239814 / 1000000000000) (11569239876 / 1000000000000), orderedInterval (-40055505644 / 1000000000000) (-40055505582 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1079848964811433 / 4000000000000)) (orderedInterval (26213614080 / 1000000000000) (26213614081 / 1000000000000), orderedInterval (40829670236 / 1000000000000) (40829670237 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (349200968322889 / 800000000000)) (orderedInterval (-21719120928 / 1000000000000) (-21719120927 / 1000000000000), orderedInterval (-31387549199 / 1000000000000) (-31387549198 / 1000000000000))) = true
  rfl'

theorem compactCertificate495_stateChecks1 :
    compactCertificate495.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (315097234750331 / 4000000000000)) (orderedInterval (-76521722622 / 1000000000000) (-76521722621 / 1000000000000), orderedInterval (-46693961610 / 1000000000000) (-46693961609 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (846395494631807 / 4000000000000)) (orderedInterval (-51958730292 / 1000000000000) (-51958726082 / 1000000000000), orderedInterval (17698323542 / 1000000000000) (17698327753 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2298128415297219 / 4000000000000)) (orderedInterval (-13141302093 / 1000000000000) (-13141302092 / 1000000000000), orderedInterval (-30572431116 / 1000000000000) (-30572431115 / 1000000000000))) = true
  rfl'

theorem compactCertificate495_stateChecks2 :
    compactCertificate495.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1692790989264347 / 4000000000000)) (orderedInterval (5110897267 / 1000000000000) (5110897271 / 1000000000000), orderedInterval (-38453246111 / 1000000000000) (-38453246107 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 231 12 (2900626212802631 / 4000000000000)) (orderedInterval (-6866625766 / 1000000000000) (-6866625765 / 1000000000000), orderedInterval (-28818108852 / 1000000000000) (-28818108851 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2136588139971029 / 4000000000000)) (orderedInterval (26195648843 / 1000000000000) (26195648844 / 1000000000000), orderedInterval (22461732391 / 1000000000000) (22461732392 / 1000000000000))) = true
  rfl'

theorem compactCertificate495_stateChecks3 :
    compactCertificate495.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 261 12 (3278075655014267 / 4000000000000)) (orderedInterval (-9517189329 / 1000000000000) (-9517189328 / 1000000000000), orderedInterval (-26190463165 / 1000000000000) (-26190463164 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1892597861846243 / 4000000000000)) (orderedInterval (15819112600 / 1000000000000) (15819112884 / 1000000000000), orderedInterval (-33111280779 / 1000000000000) (-33111280494 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 267 12 (3358448117765887 / 4000000000000)) (orderedInterval (-27529779159 / 1000000000000) (-27529774318 / 1000000000000), orderedInterval (601319577 / 1000000000000) (601324418 / 1000000000000))) = true
  rfl'

theorem compactCertificate495_stateChecks4 :
    compactCertificate495.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 250 12 (3137897878048603 / 4000000000000)) (orderedInterval (-3931615250 / 1000000000000) (-3931615249 / 1000000000000), orderedInterval (28217155438 / 1000000000000) (28217155439 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2239351989601099 / 4000000000000)) (orderedInterval (33337343506 / 1000000000000) (33337343613 / 1000000000000), orderedInterval (5046748299 / 1000000000000) (5046748405 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (2539186483895421 / 4000000000000)) (orderedInterval (26302188344 / 1000000000000) (26302188345 / 1000000000000), orderedInterval (17616368766 / 1000000000000) (17616368767 / 1000000000000))) = true
  rfl'

theorem compactCertificate495_stateChecks5 :
    compactCertificate495.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2116908966773549 / 4000000000000)) (orderedInterval (27525641124 / 1000000000000) (27525675559 / 1000000000000), orderedInterval (-21127236870 / 1000000000000) (-21127202434 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1870353271552529 / 4000000000000)) (orderedInterval (-10060256464 / 1000000000000) (-10060256463 / 1000000000000), orderedInterval (-35489780703 / 1000000000000) (-35489780702 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (542101278616371 / 800000000000)) (orderedInterval (-5252093824 / 1000000000000) (-5252093823 / 1000000000000), orderedInterval (30201563660 / 1000000000000) (30201563662 / 1000000000000))) = true
  rfl'

theorem compactCertificate495_stateChecks6 :
    compactCertificate495.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1499480665880137 / 4000000000000)) (orderedInterval (-40077896111 / 1000000000000) (-40077892275 / 1000000000000), orderedInterval (9645207449 / 1000000000000) (9645211284 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1271126366760257 / 4000000000000)) (orderedInterval (-42691971692 / 1000000000000) (-42691971690 / 1000000000000), orderedInterval (-13375983102 / 1000000000000) (-13375983100 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (795411860028971 / 4000000000000)) (orderedInterval (-55974423216 / 1000000000000) (-55974422726 / 1000000000000), orderedInterval (8405975180 / 1000000000000) (8405975671 / 1000000000000))) = true
  rfl'

theorem compactCertificate495_stateChecks7 :
    compactCertificate495.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (427775143743957 / 4000000000000)) (orderedInterval (61096145591 / 1000000000000) (61096145592 / 1000000000000), orderedInterval (46832184597 / 1000000000000) (46832184598 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1161492729382871 / 4000000000000)) (orderedInterval (39650554577 / 1000000000000) (39650613492 / 1000000000000), orderedInterval (-24973102392 / 1000000000000) (-24973043477 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1585919022904567 / 4000000000000)) (orderedInterval (39640915698 / 1000000000000) (39640915732 / 1000000000000), orderedInterval (5804663347 / 1000000000000) (5804663381 / 1000000000000))) = true
  rfl'

theorem compactCertificate495_stateChecks8 :
    compactCertificate495.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (670588139971029 / 4000000000000)) (orderedInterval (-57748591510 / 1000000000000) (-57748586918 / 1000000000000), orderedInterval (21677328039 / 1000000000000) (21677332631 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 217 12 (2725903559041909 / 4000000000000)) (orderedInterval (-15596055149 / 1000000000000) (-15596055148 / 1000000000000), orderedInterval (-26274316943 / 1000000000000) (-26274316942 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1820777247991931 / 4000000000000)) (orderedInterval (-16216080638 / 1000000000000) (-16216080637 / 1000000000000), orderedInterval (-33680946179 / 1000000000000) (-33680946178 / 1000000000000))) = true
  rfl'

theorem compactCertificate495_states : ∀ j,
    BesselStateValid (compactCertificate495.point j) (compactCertificate495.state j) :=
  compactCertificate495.statesValid_of_checks3 compactCertificate495_stateChecks0
    compactCertificate495_stateChecks1 compactCertificate495_stateChecks2
    compactCertificate495_stateChecks3 compactCertificate495_stateChecks4
    compactCertificate495_stateChecks5 compactCertificate495_stateChecks6
    compactCertificate495_stateChecks7 compactCertificate495_stateChecks8

theorem compactCertificate495_chunkChecks0_0 :
    compactCertificate495.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (733 / 2) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11569239814 / 1000000000000) (11569239876 / 1000000000000), orderedInterval (-40055505644 / 1000000000000) (-40055505582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1079848964811433 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26213614080 / 1000000000000) (26213614081 / 1000000000000), orderedInterval (40829670236 / 1000000000000) (40829670237 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (349200968322889 / 800000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-21719120928 / 1000000000000) (-21719120927 / 1000000000000), orderedInterval (-31387549199 / 1000000000000) (-31387549198 / 1000000000000)))) (orderedInterval (3555398898 / 1000000000000) (3555398948 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (315097234750331 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-76521722622 / 1000000000000) (-76521722621 / 1000000000000), orderedInterval (-46693961610 / 1000000000000) (-46693961609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (846395494631807 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51958730292 / 1000000000000) (-51958726082 / 1000000000000), orderedInterval (17698323542 / 1000000000000) (17698327753 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2298128415297219 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-13141302093 / 1000000000000) (-13141302092 / 1000000000000), orderedInterval (-30572431116 / 1000000000000) (-30572431115 / 1000000000000)))) (orderedInterval (-132687101 / 1000000000000) (-132686902 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1692790989264347 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (5110897267 / 1000000000000) (5110897271 / 1000000000000), orderedInterval (-38453246111 / 1000000000000) (-38453246107 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2900626212802631 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6866625766 / 1000000000000) (-6866625765 / 1000000000000), orderedInterval (-28818108852 / 1000000000000) (-28818108851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2136588139971029 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26195648843 / 1000000000000) (26195648844 / 1000000000000), orderedInterval (22461732391 / 1000000000000) (22461732392 / 1000000000000)))) (orderedInterval (844891350 / 1000000000000) (844891371 / 1000000000000))) = true
  rfl'

theorem compactCertificate495_chunkChecks0_1 :
    compactCertificate495.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3278075655014267 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9517189329 / 1000000000000) (-9517189328 / 1000000000000), orderedInterval (-26190463165 / 1000000000000) (-26190463164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1892597861846243 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (15819112600 / 1000000000000) (15819112884 / 1000000000000), orderedInterval (-33111280779 / 1000000000000) (-33111280494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3358448117765887 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27529779159 / 1000000000000) (-27529774318 / 1000000000000), orderedInterval (601319577 / 1000000000000) (601324418 / 1000000000000)))) (orderedInterval (-1050364684 / 1000000000000) (-1050363830 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3137897878048603 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3931615250 / 1000000000000) (-3931615249 / 1000000000000), orderedInterval (28217155438 / 1000000000000) (28217155439 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2239351989601099 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33337343506 / 1000000000000) (33337343613 / 1000000000000), orderedInterval (5046748299 / 1000000000000) (5046748405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2539186483895421 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26302188344 / 1000000000000) (26302188345 / 1000000000000), orderedInterval (17616368766 / 1000000000000) (17616368767 / 1000000000000)))) (orderedInterval (3090348290 / 1000000000000) (3090348344 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2116908966773549 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27525641124 / 1000000000000) (27525675559 / 1000000000000), orderedInterval (-21127236870 / 1000000000000) (-21127202434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1870353271552529 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-10060256464 / 1000000000000) (-10060256463 / 1000000000000), orderedInterval (-35489780703 / 1000000000000) (-35489780702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (542101278616371 / 800000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-5252093824 / 1000000000000) (-5252093823 / 1000000000000), orderedInterval (30201563660 / 1000000000000) (30201563662 / 1000000000000)))) (orderedInterval (759097702 / 1000000000000) (759098135 / 1000000000000))) = true
  rfl'

theorem compactCertificate495_chunkChecks0_2 :
    compactCertificate495.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1499480665880137 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40077896111 / 1000000000000) (-40077892275 / 1000000000000), orderedInterval (9645207449 / 1000000000000) (9645211284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1271126366760257 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-42691971692 / 1000000000000) (-42691971690 / 1000000000000), orderedInterval (-13375983102 / 1000000000000) (-13375983100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (795411860028971 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-55974423216 / 1000000000000) (-55974422726 / 1000000000000), orderedInterval (8405975180 / 1000000000000) (8405975671 / 1000000000000)))) (orderedInterval (7002253222 / 1000000000000) (7002253944 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (427775143743957 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61096145591 / 1000000000000) (61096145592 / 1000000000000), orderedInterval (46832184597 / 1000000000000) (46832184598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1161492729382871 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39650554577 / 1000000000000) (39650613492 / 1000000000000), orderedInterval (-24973102392 / 1000000000000) (-24973043477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1585919022904567 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39640915698 / 1000000000000) (39640915732 / 1000000000000), orderedInterval (5804663347 / 1000000000000) (5804663381 / 1000000000000)))) (orderedInterval (-5065730483 / 1000000000000) (-5065729099 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (670588139971029 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57748591510 / 1000000000000) (-57748586918 / 1000000000000), orderedInterval (21677328039 / 1000000000000) (21677332631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2725903559041909 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15596055149 / 1000000000000) (-15596055148 / 1000000000000), orderedInterval (-26274316943 / 1000000000000) (-26274316942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1820777247991931 / 4000000000000) 0 (IntervalRat.scale (733 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-16216080638 / 1000000000000) (-16216080637 / 1000000000000), orderedInterval (-33680946179 / 1000000000000) (-33680946178 / 1000000000000)))) (orderedInterval (3963985993 / 1000000000000) (3963986122 / 1000000000000))) = true
  rfl'

theorem compactCertificate495_chunkChecks0 :
    compactCertificate495.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate495.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate495_chunkChecks0_0
    compactCertificate495_chunkChecks0_1 compactCertificate495_chunkChecks0_2

theorem compactCertificate495_chunkChecks1_0 :
    compactCertificate495.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (733 / 2) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11569239814 / 1000000000000) (11569239876 / 1000000000000), orderedInterval (-40055505644 / 1000000000000) (-40055505582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1079848964811433 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26213614080 / 1000000000000) (26213614081 / 1000000000000), orderedInterval (40829670236 / 1000000000000) (40829670237 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (349200968322889 / 800000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-21719120928 / 1000000000000) (-21719120927 / 1000000000000), orderedInterval (-31387549199 / 1000000000000) (-31387549198 / 1000000000000)))) (orderedInterval (-17790010470 / 1000000000000) (-17790010416 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (315097234750331 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-76521722622 / 1000000000000) (-76521722621 / 1000000000000), orderedInterval (-46693961610 / 1000000000000) (-46693961609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (846395494631807 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51958730292 / 1000000000000) (-51958726082 / 1000000000000), orderedInterval (17698323542 / 1000000000000) (17698327753 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2298128415297219 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-13141302093 / 1000000000000) (-13141302092 / 1000000000000), orderedInterval (-30572431116 / 1000000000000) (-30572431115 / 1000000000000)))) (orderedInterval (3889003159 / 1000000000000) (3889003298 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1692790989264347 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (5110897267 / 1000000000000) (5110897271 / 1000000000000), orderedInterval (-38453246111 / 1000000000000) (-38453246107 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2900626212802631 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6866625766 / 1000000000000) (-6866625765 / 1000000000000), orderedInterval (-28818108852 / 1000000000000) (-28818108851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2136588139971029 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26195648843 / 1000000000000) (26195648844 / 1000000000000), orderedInterval (22461732391 / 1000000000000) (22461732392 / 1000000000000)))) (orderedInterval (2549881662 / 1000000000000) (2549881699 / 1000000000000))) = true
  rfl'

theorem compactCertificate495_chunkChecks1_1 :
    compactCertificate495.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3278075655014267 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9517189329 / 1000000000000) (-9517189328 / 1000000000000), orderedInterval (-26190463165 / 1000000000000) (-26190463164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1892597861846243 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (15819112600 / 1000000000000) (15819112884 / 1000000000000), orderedInterval (-33111280779 / 1000000000000) (-33111280494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3358448117765887 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27529779159 / 1000000000000) (-27529774318 / 1000000000000), orderedInterval (601319577 / 1000000000000) (601324418 / 1000000000000)))) (orderedInterval (7434720081 / 1000000000000) (7434721986 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3137897878048603 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3931615250 / 1000000000000) (-3931615249 / 1000000000000), orderedInterval (28217155438 / 1000000000000) (28217155439 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2239351989601099 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33337343506 / 1000000000000) (33337343613 / 1000000000000), orderedInterval (5046748299 / 1000000000000) (5046748405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2539186483895421 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26302188344 / 1000000000000) (26302188345 / 1000000000000), orderedInterval (17616368766 / 1000000000000) (17616368767 / 1000000000000)))) (orderedInterval (-515781118 / 1000000000000) (-515781032 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2116908966773549 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27525641124 / 1000000000000) (27525675559 / 1000000000000), orderedInterval (-21127236870 / 1000000000000) (-21127202434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1870353271552529 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-10060256464 / 1000000000000) (-10060256463 / 1000000000000), orderedInterval (-35489780703 / 1000000000000) (-35489780702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (542101278616371 / 800000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-5252093824 / 1000000000000) (-5252093823 / 1000000000000), orderedInterval (30201563660 / 1000000000000) (30201563662 / 1000000000000)))) (orderedInterval (3668575924 / 1000000000000) (3668576550 / 1000000000000))) = true
  rfl'

theorem compactCertificate495_chunkChecks1_2 :
    compactCertificate495.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1499480665880137 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40077896111 / 1000000000000) (-40077892275 / 1000000000000), orderedInterval (9645207449 / 1000000000000) (9645211284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1271126366760257 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-42691971692 / 1000000000000) (-42691971690 / 1000000000000), orderedInterval (-13375983102 / 1000000000000) (-13375983100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (795411860028971 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-55974423216 / 1000000000000) (-55974422726 / 1000000000000), orderedInterval (8405975180 / 1000000000000) (8405975671 / 1000000000000)))) (orderedInterval (-772495124 / 1000000000000) (-772494402 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (427775143743957 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61096145591 / 1000000000000) (61096145592 / 1000000000000), orderedInterval (46832184597 / 1000000000000) (46832184598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1161492729382871 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39650554577 / 1000000000000) (39650613492 / 1000000000000), orderedInterval (-24973102392 / 1000000000000) (-24973043477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1585919022904567 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39640915698 / 1000000000000) (39640915732 / 1000000000000), orderedInterval (5804663347 / 1000000000000) (5804663381 / 1000000000000)))) (orderedInterval (-284709927 / 1000000000000) (-284708825 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (670588139971029 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57748591510 / 1000000000000) (-57748586918 / 1000000000000), orderedInterval (21677328039 / 1000000000000) (21677332631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2725903559041909 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15596055149 / 1000000000000) (-15596055148 / 1000000000000), orderedInterval (-26274316943 / 1000000000000) (-26274316942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1820777247991931 / 4000000000000) 1 (IntervalRat.scale (733 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-16216080638 / 1000000000000) (-16216080637 / 1000000000000), orderedInterval (-33680946179 / 1000000000000) (-33680946178 / 1000000000000)))) (orderedInterval (11885415462 / 1000000000000) (11885415618 / 1000000000000))) = true
  rfl'

theorem compactCertificate495_chunkChecks1 :
    compactCertificate495.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate495.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate495_chunkChecks1_0
    compactCertificate495_chunkChecks1_1 compactCertificate495_chunkChecks1_2

theorem compactCertificate495_chunkChecks2_0 :
    compactCertificate495.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (733 / 2) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11569239814 / 1000000000000) (11569239876 / 1000000000000), orderedInterval (-40055505644 / 1000000000000) (-40055505582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1079848964811433 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26213614080 / 1000000000000) (26213614081 / 1000000000000), orderedInterval (40829670236 / 1000000000000) (40829670237 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (349200968322889 / 800000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-21719120928 / 1000000000000) (-21719120927 / 1000000000000), orderedInterval (-31387549199 / 1000000000000) (-31387549198 / 1000000000000)))) (orderedInterval (-2861774722 / 1000000000000) (-2861774664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (315097234750331 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-76521722622 / 1000000000000) (-76521722621 / 1000000000000), orderedInterval (-46693961610 / 1000000000000) (-46693961609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (846395494631807 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51958730292 / 1000000000000) (-51958726082 / 1000000000000), orderedInterval (17698323542 / 1000000000000) (17698327753 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2298128415297219 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-13141302093 / 1000000000000) (-13141302092 / 1000000000000), orderedInterval (-30572431116 / 1000000000000) (-30572431115 / 1000000000000)))) (orderedInterval (-1712351080 / 1000000000000) (-1712350959 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1692790989264347 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (5110897267 / 1000000000000) (5110897271 / 1000000000000), orderedInterval (-38453246111 / 1000000000000) (-38453246107 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2900626212802631 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6866625766 / 1000000000000) (-6866625765 / 1000000000000), orderedInterval (-28818108852 / 1000000000000) (-28818108851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2136588139971029 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26195648843 / 1000000000000) (26195648844 / 1000000000000), orderedInterval (22461732391 / 1000000000000) (22461732392 / 1000000000000)))) (orderedInterval (-2180858593 / 1000000000000) (-2180858528 / 1000000000000))) = true
  rfl'

theorem compactCertificate495_chunkChecks2_1 :
    compactCertificate495.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3278075655014267 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9517189329 / 1000000000000) (-9517189328 / 1000000000000), orderedInterval (-26190463165 / 1000000000000) (-26190463164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1892597861846243 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (15819112600 / 1000000000000) (15819112884 / 1000000000000), orderedInterval (-33111280779 / 1000000000000) (-33111280494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3358448117765887 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27529779159 / 1000000000000) (-27529774318 / 1000000000000), orderedInterval (601319577 / 1000000000000) (601324418 / 1000000000000)))) (orderedInterval (10109707261 / 1000000000000) (10109711558 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3137897878048603 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3931615250 / 1000000000000) (-3931615249 / 1000000000000), orderedInterval (28217155438 / 1000000000000) (28217155439 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2239351989601099 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33337343506 / 1000000000000) (33337343613 / 1000000000000), orderedInterval (5046748299 / 1000000000000) (5046748405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2539186483895421 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26302188344 / 1000000000000) (26302188345 / 1000000000000), orderedInterval (17616368766 / 1000000000000) (17616368767 / 1000000000000)))) (orderedInterval (-7280240726 / 1000000000000) (-7280240584 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2116908966773549 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27525641124 / 1000000000000) (27525675559 / 1000000000000), orderedInterval (-21127236870 / 1000000000000) (-21127202434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1870353271552529 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-10060256464 / 1000000000000) (-10060256463 / 1000000000000), orderedInterval (-35489780703 / 1000000000000) (-35489780702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (542101278616371 / 800000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-5252093824 / 1000000000000) (-5252093823 / 1000000000000), orderedInterval (30201563660 / 1000000000000) (30201563662 / 1000000000000)))) (orderedInterval (-1150193237 / 1000000000000) (-1150192330 / 1000000000000))) = true
  rfl'

theorem compactCertificate495_chunkChecks2_2 :
    compactCertificate495.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1499480665880137 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40077896111 / 1000000000000) (-40077892275 / 1000000000000), orderedInterval (9645207449 / 1000000000000) (9645211284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1271126366760257 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-42691971692 / 1000000000000) (-42691971690 / 1000000000000), orderedInterval (-13375983102 / 1000000000000) (-13375983100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (795411860028971 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-55974423216 / 1000000000000) (-55974422726 / 1000000000000), orderedInterval (8405975180 / 1000000000000) (8405975671 / 1000000000000)))) (orderedInterval (-7982292439 / 1000000000000) (-7982291709 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (427775143743957 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61096145591 / 1000000000000) (61096145592 / 1000000000000), orderedInterval (46832184597 / 1000000000000) (46832184598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1161492729382871 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39650554577 / 1000000000000) (39650613492 / 1000000000000), orderedInterval (-24973102392 / 1000000000000) (-24973043477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1585919022904567 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39640915698 / 1000000000000) (39640915732 / 1000000000000), orderedInterval (5804663347 / 1000000000000) (5804663381 / 1000000000000)))) (orderedInterval (4216882782 / 1000000000000) (4216883667 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (670588139971029 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57748591510 / 1000000000000) (-57748586918 / 1000000000000), orderedInterval (21677328039 / 1000000000000) (21677332631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2725903559041909 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15596055149 / 1000000000000) (-15596055148 / 1000000000000), orderedInterval (-26274316943 / 1000000000000) (-26274316942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1820777247991931 / 4000000000000) 2 (IntervalRat.scale (733 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-16216080638 / 1000000000000) (-16216080637 / 1000000000000), orderedInterval (-33680946179 / 1000000000000) (-33680946178 / 1000000000000)))) (orderedInterval (-9042333638 / 1000000000000) (-9042333421 / 1000000000000))) = true
  rfl'

theorem compactCertificate495_chunkChecks2 :
    compactCertificate495.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate495.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate495_chunkChecks2_0
    compactCertificate495_chunkChecks2_1 compactCertificate495_chunkChecks2_2

theorem compactCertificate495_chunkChecks3_0 :
    compactCertificate495.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (733 / 2) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11569239814 / 1000000000000) (11569239876 / 1000000000000), orderedInterval (-40055505644 / 1000000000000) (-40055505582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1079848964811433 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26213614080 / 1000000000000) (26213614081 / 1000000000000), orderedInterval (40829670236 / 1000000000000) (40829670237 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (349200968322889 / 800000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-21719120928 / 1000000000000) (-21719120927 / 1000000000000), orderedInterval (-31387549199 / 1000000000000) (-31387549198 / 1000000000000)))) (orderedInterval (18843872716 / 1000000000000) (18843872780 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (315097234750331 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-76521722622 / 1000000000000) (-76521722621 / 1000000000000), orderedInterval (-46693961610 / 1000000000000) (-46693961609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (846395494631807 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51958730292 / 1000000000000) (-51958726082 / 1000000000000), orderedInterval (17698323542 / 1000000000000) (17698327753 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2298128415297219 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-13141302093 / 1000000000000) (-13141302092 / 1000000000000), orderedInterval (-30572431116 / 1000000000000) (-30572431115 / 1000000000000)))) (orderedInterval (-8497230488 / 1000000000000) (-8497230354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1692790989264347 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (5110897267 / 1000000000000) (5110897271 / 1000000000000), orderedInterval (-38453246111 / 1000000000000) (-38453246107 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2900626212802631 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6866625766 / 1000000000000) (-6866625765 / 1000000000000), orderedInterval (-28818108852 / 1000000000000) (-28818108851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2136588139971029 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26195648843 / 1000000000000) (26195648844 / 1000000000000), orderedInterval (22461732391 / 1000000000000) (22461732392 / 1000000000000)))) (orderedInterval (-8559644860 / 1000000000000) (-8559644743 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate495_chunkChecks3_1 :
    compactCertificate495.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3278075655014267 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9517189329 / 1000000000000) (-9517189328 / 1000000000000), orderedInterval (-26190463165 / 1000000000000) (-26190463164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1892597861846243 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (15819112600 / 1000000000000) (15819112884 / 1000000000000), orderedInterval (-33111280779 / 1000000000000) (-33111280494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3358448117765887 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27529779159 / 1000000000000) (-27529774318 / 1000000000000), orderedInterval (601319577 / 1000000000000) (601324418 / 1000000000000)))) (orderedInterval (-47806949341 / 1000000000000) (-47806939596 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3137897878048603 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3931615250 / 1000000000000) (-3931615249 / 1000000000000), orderedInterval (28217155438 / 1000000000000) (28217155439 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2239351989601099 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33337343506 / 1000000000000) (33337343613 / 1000000000000), orderedInterval (5046748299 / 1000000000000) (5046748405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2539186483895421 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26302188344 / 1000000000000) (26302188345 / 1000000000000), orderedInterval (17616368766 / 1000000000000) (17616368767 / 1000000000000)))) (orderedInterval (3777621367 / 1000000000000) (3777621602 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2116908966773549 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27525641124 / 1000000000000) (27525675559 / 1000000000000), orderedInterval (-21127236870 / 1000000000000) (-21127202434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1870353271552529 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-10060256464 / 1000000000000) (-10060256463 / 1000000000000), orderedInterval (-35489780703 / 1000000000000) (-35489780702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (542101278616371 / 800000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-5252093824 / 1000000000000) (-5252093823 / 1000000000000), orderedInterval (30201563660 / 1000000000000) (30201563662 / 1000000000000)))) (orderedInterval (-8367393439 / 1000000000000) (-8367392122 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate495_chunkChecks3_2 :
    compactCertificate495.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1499480665880137 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40077896111 / 1000000000000) (-40077892275 / 1000000000000), orderedInterval (9645207449 / 1000000000000) (9645211284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1271126366760257 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-42691971692 / 1000000000000) (-42691971690 / 1000000000000), orderedInterval (-13375983102 / 1000000000000) (-13375983100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (795411860028971 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-55974423216 / 1000000000000) (-55974422726 / 1000000000000), orderedInterval (8405975180 / 1000000000000) (8405975671 / 1000000000000)))) (orderedInterval (1134831978 / 1000000000000) (1134832718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (427775143743957 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61096145591 / 1000000000000) (61096145592 / 1000000000000), orderedInterval (46832184597 / 1000000000000) (46832184598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1161492729382871 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39650554577 / 1000000000000) (39650613492 / 1000000000000), orderedInterval (-24973102392 / 1000000000000) (-24973043477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1585919022904567 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39640915698 / 1000000000000) (39640915732 / 1000000000000), orderedInterval (5804663347 / 1000000000000) (5804663381 / 1000000000000)))) (orderedInterval (291413452 / 1000000000000) (291414163 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (670588139971029 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57748591510 / 1000000000000) (-57748586918 / 1000000000000), orderedInterval (21677328039 / 1000000000000) (21677332631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2725903559041909 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15596055149 / 1000000000000) (-15596055148 / 1000000000000), orderedInterval (-26274316943 / 1000000000000) (-26274316942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1820777247991931 / 4000000000000) 3 (IntervalRat.scale (733 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-16216080638 / 1000000000000) (-16216080637 / 1000000000000), orderedInterval (-33680946179 / 1000000000000) (-33680946178 / 1000000000000)))) (orderedInterval (-25844792498 / 1000000000000) (-25844792170 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate495_chunkChecks3 :
    compactCertificate495.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate495.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate495_chunkChecks3_0
    compactCertificate495_chunkChecks3_1 compactCertificate495_chunkChecks3_2

theorem compactCertificate495_chunkChecks4_0 :
    compactCertificate495.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (733 / 2) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11569239814 / 1000000000000) (11569239876 / 1000000000000), orderedInterval (-40055505644 / 1000000000000) (-40055505582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1079848964811433 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26213614080 / 1000000000000) (26213614081 / 1000000000000), orderedInterval (40829670236 / 1000000000000) (40829670237 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (349200968322889 / 800000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-21719120928 / 1000000000000) (-21719120927 / 1000000000000), orderedInterval (-31387549199 / 1000000000000) (-31387549198 / 1000000000000)))) (orderedInterval (1990290383 / 1000000000000) (1990290453 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (315097234750331 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-76521722622 / 1000000000000) (-76521722621 / 1000000000000), orderedInterval (-46693961610 / 1000000000000) (-46693961609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (846395494631807 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51958730292 / 1000000000000) (-51958726082 / 1000000000000), orderedInterval (17698323542 / 1000000000000) (17698327753 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2298128415297219 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-13141302093 / 1000000000000) (-13141302092 / 1000000000000), orderedInterval (-30572431116 / 1000000000000) (-30572431115 / 1000000000000)))) (orderedInterval (5478987534 / 1000000000000) (5478987712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1692790989264347 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (5110897267 / 1000000000000) (5110897271 / 1000000000000), orderedInterval (-38453246111 / 1000000000000) (-38453246107 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2900626212802631 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6866625766 / 1000000000000) (-6866625765 / 1000000000000), orderedInterval (-28818108852 / 1000000000000) (-28818108851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2136588139971029 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26195648843 / 1000000000000) (26195648844 / 1000000000000), orderedInterval (22461732391 / 1000000000000) (22461732392 / 1000000000000)))) (orderedInterval (6149061076 / 1000000000000) (6149061291 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate495_chunkChecks4_1 :
    compactCertificate495.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3278075655014267 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-9517189329 / 1000000000000) (-9517189328 / 1000000000000), orderedInterval (-26190463165 / 1000000000000) (-26190463164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1892597861846243 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (15819112600 / 1000000000000) (15819112884 / 1000000000000), orderedInterval (-33111280779 / 1000000000000) (-33111280494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3358448117765887 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27529779159 / 1000000000000) (-27529774318 / 1000000000000), orderedInterval (601319577 / 1000000000000) (601324418 / 1000000000000)))) (orderedInterval (-61998002144 / 1000000000000) (-61997979941 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3137897878048603 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3931615250 / 1000000000000) (-3931615249 / 1000000000000), orderedInterval (28217155438 / 1000000000000) (28217155439 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2239351989601099 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33337343506 / 1000000000000) (33337343613 / 1000000000000), orderedInterval (5046748299 / 1000000000000) (5046748405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2539186483895421 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26302188344 / 1000000000000) (26302188345 / 1000000000000), orderedInterval (17616368766 / 1000000000000) (17616368767 / 1000000000000)))) (orderedInterval (17434714125 / 1000000000000) (17434714526 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2116908966773549 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27525641124 / 1000000000000) (27525675559 / 1000000000000), orderedInterval (-21127236870 / 1000000000000) (-21127202434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1870353271552529 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-10060256464 / 1000000000000) (-10060256463 / 1000000000000), orderedInterval (-35489780703 / 1000000000000) (-35489780702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (542101278616371 / 800000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-5252093824 / 1000000000000) (-5252093823 / 1000000000000), orderedInterval (30201563660 / 1000000000000) (30201563662 / 1000000000000)))) (orderedInterval (1381513060 / 1000000000000) (1381514980 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate495_chunkChecks4_2 :
    compactCertificate495.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1499480665880137 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40077896111 / 1000000000000) (-40077892275 / 1000000000000), orderedInterval (9645207449 / 1000000000000) (9645211284 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1271126366760257 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-42691971692 / 1000000000000) (-42691971690 / 1000000000000), orderedInterval (-13375983102 / 1000000000000) (-13375983100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (795411860028971 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-55974423216 / 1000000000000) (-55974422726 / 1000000000000), orderedInterval (8405975180 / 1000000000000) (8405975671 / 1000000000000)))) (orderedInterval (8215520897 / 1000000000000) (8215521651 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (427775143743957 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61096145591 / 1000000000000) (61096145592 / 1000000000000), orderedInterval (46832184597 / 1000000000000) (46832184598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1161492729382871 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39650554577 / 1000000000000) (39650613492 / 1000000000000), orderedInterval (-24973102392 / 1000000000000) (-24973043477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1585919022904567 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39640915698 / 1000000000000) (39640915732 / 1000000000000), orderedInterval (5804663347 / 1000000000000) (5804663381 / 1000000000000)))) (orderedInterval (-4525026402 / 1000000000000) (-4525025826 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (670588139971029 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57748591510 / 1000000000000) (-57748586918 / 1000000000000), orderedInterval (21677328039 / 1000000000000) (21677332631 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2725903559041909 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15596055149 / 1000000000000) (-15596055148 / 1000000000000), orderedInterval (-26274316943 / 1000000000000) (-26274316942 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1820777247991931 / 4000000000000) 4 (IntervalRat.scale (733 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-16216080638 / 1000000000000) (-16216080637 / 1000000000000), orderedInterval (-33680946179 / 1000000000000) (-33680946178 / 1000000000000)))) (orderedInterval (22541518059 / 1000000000000) (22541518583 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate495_chunkChecks4 :
    compactCertificate495.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate495.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate495_chunkChecks4_0
    compactCertificate495_chunkChecks4_1 compactCertificate495_chunkChecks4_2

theorem compactCertificate495_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate495.chunkCheck r b = true :=
  compactCertificate495.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate495_chunkChecks0
    · exact compactCertificate495_chunkChecks1
    · exact compactCertificate495_chunkChecks2
    · exact compactCertificate495_chunkChecks3
    · exact compactCertificate495_chunkChecks4)

theorem compactCertificate495_coefficient0 :
    compactCertificate495.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate495_coefficient1 :
    compactCertificate495.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate495_coefficient2 :
    compactCertificate495.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate495_coefficient3 :
    compactCertificate495.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate495_coefficient4 :
    compactCertificate495.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate495_coefficients : ∀ r : Fin 5,
    compactCertificate495.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate495_coefficient0
  · exact compactCertificate495_coefficient1
  · exact compactCertificate495_coefficient2
  · exact compactCertificate495_coefficient3
  · exact compactCertificate495_coefficient4

theorem compactCertificate495_lower : (1 : ℚ) ≤ compactCertificate495.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate495, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate495_proves {t : ℝ} (ht : t ∈ compactCertificate495.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate495.proves compactCertificate495_states compactCertificate495_chunks
    compactCertificate495_coefficients compactCertificate495_lower ht

end Erdos232
