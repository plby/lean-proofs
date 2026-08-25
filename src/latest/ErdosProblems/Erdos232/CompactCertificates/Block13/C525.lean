/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate525 : CompactCertificate where
  left := 396
  right := 397
  center := 793 / 2
  grid := fun i =>
    match i.val with
    | 0 => 126
    | 1 => 93
    | 2 => 150
    | 3 => 27
    | 4 => 73
    | 5 => 198
    | 6 => 146
    | 7 => 250
    | 8 => 184
    | 9 => 282
    | 10 => 163
    | 11 => 289
    | 12 => 270
    | 13 => 193
    | 14 => 219
    | 15 => 182
    | 16 => 161
    | 17 => 233
    | 18 => 129
    | 19 => 109
    | 20 => 69
    | 21 => 37
    | 22 => 100
    | 23 => 137
    | 24 => 58
    | 25 => 235
    | _ => 157
  point := fun i =>
    match i.val with
    | 0 => 793 / 2
    | 1 => 1168240421685493 / 4000000000000
    | 2 => 377784949358869 / 800000000000
    | 3 => 340889641414751 / 4000000000000
    | 4 => 915677526934547 / 4000000000000
    | 5 => 2486242610273799 / 4000000000000
    | 6 => 1831355053869887 / 4000000000000
    | 7 => 3138058099253051 / 4000000000000
    | 8 => 2311479392901809 / 4000000000000
    | 9 => 3546403812314207 / 4000000000000
    | 10 => 2047517195694503 / 4000000000000
    | 11 => 3633355194254227 / 4000000000000
    | 12 => 3394751728912063 / 4000000000000
    | 13 => 2422655017399279 / 4000000000000
    | 14 => 2747032580803641 / 4000000000000
    | 15 => 2290189373330729 / 4000000000000
    | 16 => 2023451765813309 / 4000000000000
    | 17 => 586475189553591 / 800000000000
    | 18 => 1622221238803477 / 4000000000000
    | 19 => 1375174909741997 / 4000000000000
    | 20 => 860520607098191 / 4000000000000
    | 21 => 462790844459697 / 4000000000000
    | 22 => 1256567168350091 / 4000000000000
    | 23 => 1715735041150507 / 4000000000000
    | 24 => 725479392901809 / 4000000000000
    | 25 => 2949033454734289 / 4000000000000
    | _ => 1969817677568351 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (39750293246 / 1000000000000) (39750293292 / 1000000000000), orderedInterval (5000751332 / 1000000000000) (5000751378 / 1000000000000))
    | 1 => (orderedInterval (-29246436988 / 1000000000000) (-29246436987 / 1000000000000), orderedInterval (-36342273934 / 1000000000000) (-36342273933 / 1000000000000))
    | 2 => (orderedInterval (35935601224 / 1000000000000) (35935606022 / 1000000000000), orderedInterval (-7570785722 / 1000000000000) (-7570780924 / 1000000000000))
    | 3 => (orderedInterval (-80022284259 / 1000000000000) (-80022284258 / 1000000000000), orderedInterval (-32186923812 / 1000000000000) (-32186923811 / 1000000000000))
    | 4 => (orderedInterval (-18969920150 / 1000000000000) (-18969920149 / 1000000000000), orderedInterval (-49163496010 / 1000000000000) (-49163496009 / 1000000000000))
    | 5 => (orderedInterval (9778327344 / 1000000000000) (9778327345 / 1000000000000), orderedInterval (30465277982 / 1000000000000) (30465277983 / 1000000000000))
    | 6 => (orderedInterval (-1812989888 / 1000000000000) (-1812989886 / 1000000000000), orderedInterval (37247152922 / 1000000000000) (37247152923 / 1000000000000))
    | 7 => (orderedInterval (-2798546128 / 1000000000000) (-2798546127 / 1000000000000), orderedInterval (28350518260 / 1000000000000) (28350518261 / 1000000000000))
    | 8 => (orderedInterval (18795501008 / 1000000000000) (18795501009 / 1000000000000), orderedInterval (27340558170 / 1000000000000) (27340558171 / 1000000000000))
    | 9 => (orderedInterval (26623302279 / 1000000000000) (26623303697 / 1000000000000), orderedInterval (3025555202 / 1000000000000) (3025556620 / 1000000000000))
    | 10 => (orderedInterval (-19469462081 / 1000000000000) (-19469462080 / 1000000000000), orderedInterval (-29385598760 / 1000000000000) (-29385598759 / 1000000000000))
    | 11 => (orderedInterval (-24710711984 / 1000000000000) (-24710711923 / 1000000000000), orderedInterval (-9485988587 / 1000000000000) (-9485988526 / 1000000000000))
    | 12 => (orderedInterval (25931510914 / 1000000000000) (25931510983 / 1000000000000), orderedInterval (8798289966 / 1000000000000) (8798290035 / 1000000000000))
    | 13 => (orderedInterval (-3931506022 / 1000000000000) (-3931506021 / 1000000000000), orderedInterval (-32178340820 / 1000000000000) (-32178340819 / 1000000000000))
    | 14 => (orderedInterval (13664622240 / 1000000000000) (13664622324 / 1000000000000), orderedInterval (-27217868902 / 1000000000000) (-27217868817 / 1000000000000))
    | 15 => (orderedInterval (33344168908 / 1000000000000) (33344169659 / 1000000000000), orderedInterval (242178311 / 1000000000000) (242179062 / 1000000000000))
    | 16 => (orderedInterval (-26690927038 / 1000000000000) (-26690927037 / 1000000000000), orderedInterval (-23341910132 / 1000000000000) (-23341910131 / 1000000000000))
    | 17 => (orderedInterval (-27997357740 / 1000000000000) (-27997307946 / 1000000000000), orderedInterval (9214202303 / 1000000000000) (9214252097 / 1000000000000))
    | 18 => (orderedInterval (-34848399456 / 1000000000000) (-34848399455 / 1000000000000), orderedInterval (-18807413922 / 1000000000000) (-18807413921 / 1000000000000))
    | 19 => (orderedInterval (-36126926976 / 1000000000000) (-36126843516 / 1000000000000), orderedInterval (23431901824 / 1000000000000) (23431985284 / 1000000000000))
    | 20 => (orderedInterval (41044958105 / 1000000000000) (41045038862 / 1000000000000), orderedInterval (-35796101733 / 1000000000000) (-35796020976 / 1000000000000))
    | 21 => (orderedInterval (-17855656058 / 1000000000000) (-17855656057 / 1000000000000), orderedInterval (-71920485433 / 1000000000000) (-71920485432 / 1000000000000))
    | 22 => (orderedInterval (31257928153 / 1000000000000) (31257928154 / 1000000000000), orderedInterval (32345902948 / 1000000000000) (32345902949 / 1000000000000))
    | 23 => (orderedInterval (24204187719 / 1000000000000) (24204193337 / 1000000000000), orderedInterval (-30000682927 / 1000000000000) (-30000677308 / 1000000000000))
    | 24 => (orderedInterval (-3423482139 / 1000000000000) (-3423482131 / 1000000000000), orderedInterval (59156348125 / 1000000000000) (59156348133 / 1000000000000))
    | 25 => (orderedInterval (6718679625 / 1000000000000) (6718679627 / 1000000000000), orderedInterval (-28611473360 / 1000000000000) (-28611473358 / 1000000000000))
    | _ => (orderedInterval (-342180729 / 1000000000000) (-342180728 / 1000000000000), orderedInterval (-35952847166 / 1000000000000) (-35952847165 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (17591846682 / 1000000000000) (17591847010 / 1000000000000)
      | 1 => orderedInterval (-519577662 / 1000000000000) (-519577614 / 1000000000000)
      | 2 => orderedInterval (540568524 / 1000000000000) (540568547 / 1000000000000)
      | 3 => orderedInterval (-9685939926 / 1000000000000) (-9685939508 / 1000000000000)
      | 4 => orderedInterval (-909069159 / 1000000000000) (-909069109 / 1000000000000)
      | 5 => orderedInterval (1195637552 / 1000000000000) (1195638875 / 1000000000000)
      | 6 => orderedInterval (8953003126 / 1000000000000) (8953010579 / 1000000000000)
      | 7 => orderedInterval (-2234419575 / 1000000000000) (-2234419096 / 1000000000000)
      | _ => orderedInterval (-503348207 / 1000000000000) (-503348097 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (1203566344 / 1000000000000) (1203566729 / 1000000000000)
      | 1 => orderedInterval (-4356406630 / 1000000000000) (-4356406576 / 1000000000000)
      | 2 => orderedInterval (-767152685 / 1000000000000) (-767152646 / 1000000000000)
      | 3 => orderedInterval (-7102157885 / 1000000000000) (-7102156976 / 1000000000000)
      | 4 => orderedInterval (-4749481661 / 1000000000000) (-4749481581 / 1000000000000)
      | 5 => orderedInterval (2144449591 / 1000000000000) (2144452016 / 1000000000000)
      | 6 => orderedInterval (1293600329 / 1000000000000) (1293605944 / 1000000000000)
      | 7 => orderedInterval (2293405730 / 1000000000000) (2293406239 / 1000000000000)
      | _ => orderedInterval (12871943528 / 1000000000000) (12871943683 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-18602005180 / 1000000000000) (-18602004726 / 1000000000000)
      | 1 => orderedInterval (1910004276 / 1000000000000) (1910004351 / 1000000000000)
      | 2 => orderedInterval (-1300858988 / 1000000000000) (-1300858918 / 1000000000000)
      | 3 => orderedInterval (44511013215 / 1000000000000) (44511015220 / 1000000000000)
      | 4 => orderedInterval (3231715390 / 1000000000000) (3231715525 / 1000000000000)
      | 5 => orderedInterval (-844011630 / 1000000000000) (-844007165 / 1000000000000)
      | 6 => orderedInterval (-7763332357 / 1000000000000) (-7763327929 / 1000000000000)
      | 7 => orderedInterval (2582155155 / 1000000000000) (2582155703 / 1000000000000)
      | _ => orderedInterval (1763727649 / 1000000000000) (1763727877 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-1049320422 / 1000000000000) (-1049319886 / 1000000000000)
      | 1 => orderedInterval (8680339940 / 1000000000000) (8680340052 / 1000000000000)
      | 2 => orderedInterval (4731105318 / 1000000000000) (4731105444 / 1000000000000)
      | 3 => orderedInterval (26795881021 / 1000000000000) (26795885475 / 1000000000000)
      | 4 => orderedInterval (11679237495 / 1000000000000) (11679237725 / 1000000000000)
      | 5 => orderedInterval (-4271395426 / 1000000000000) (-4271387205 / 1000000000000)
      | 6 => orderedInterval (-2147668931 / 1000000000000) (-2147665335 / 1000000000000)
      | 7 => orderedInterval (-2585396451 / 1000000000000) (-2585395860 / 1000000000000)
      | _ => orderedInterval (-27935294430 / 1000000000000) (-27935294077 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (19923537378 / 1000000000000) (19923538014 / 1000000000000)
      | 1 => orderedInterval (-4316778998 / 1000000000000) (-4316778825 / 1000000000000)
      | 2 => orderedInterval (3348523968 / 1000000000000) (3348524200 / 1000000000000)
      | 3 => orderedInterval (-219161865285 / 1000000000000) (-219161855335 / 1000000000000)
      | 4 => orderedInterval (-12531848932 / 1000000000000) (-12531848527 / 1000000000000)
      | 5 => orderedInterval (-2634479177 / 1000000000000) (-2634464000 / 1000000000000)
      | 6 => orderedInterval (7381053751 / 1000000000000) (7381056751 / 1000000000000)
      | 7 => orderedInterval (-2804527544 / 1000000000000) (-2804526905 / 1000000000000)
      | _ => orderedInterval (-6244895681 / 1000000000000) (-6244895115 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (14428701355 / 1000000000000) (14428711587 / 1000000000000)
    | 1 => orderedInterval (2831766661 / 1000000000000) (2831776832 / 1000000000000)
    | 2 => orderedInterval (25488407530 / 1000000000000) (25488419938 / 1000000000000)
    | 3 => orderedInterval (13897488114 / 1000000000000) (13897506333 / 1000000000000)
    | _ => orderedInterval (-217041280520 / 1000000000000) (-217041249742 / 1000000000000)

theorem compactCertificate525_stateChecks0 :
    compactCertificate525.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (793 / 2)) (orderedInterval (39750293246 / 1000000000000) (39750293292 / 1000000000000), orderedInterval (5000751332 / 1000000000000) (5000751378 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1168240421685493 / 4000000000000)) (orderedInterval (-29246436988 / 1000000000000) (-29246436987 / 1000000000000), orderedInterval (-36342273934 / 1000000000000) (-36342273933 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (377784949358869 / 800000000000)) (orderedInterval (35935601224 / 1000000000000) (35935606022 / 1000000000000), orderedInterval (-7570785722 / 1000000000000) (-7570780924 / 1000000000000))) = true
  rfl'

theorem compactCertificate525_stateChecks1 :
    compactCertificate525.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (340889641414751 / 4000000000000)) (orderedInterval (-80022284259 / 1000000000000) (-80022284258 / 1000000000000), orderedInterval (-32186923812 / 1000000000000) (-32186923811 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (915677526934547 / 4000000000000)) (orderedInterval (-18969920150 / 1000000000000) (-18969920149 / 1000000000000), orderedInterval (-49163496010 / 1000000000000) (-49163496009 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (2486242610273799 / 4000000000000)) (orderedInterval (9778327344 / 1000000000000) (9778327345 / 1000000000000), orderedInterval (30465277982 / 1000000000000) (30465277983 / 1000000000000))) = true
  rfl'

theorem compactCertificate525_stateChecks2 :
    compactCertificate525.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1831355053869887 / 4000000000000)) (orderedInterval (-1812989888 / 1000000000000) (-1812989886 / 1000000000000), orderedInterval (37247152922 / 1000000000000) (37247152923 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 250 12 (3138058099253051 / 4000000000000)) (orderedInterval (-2798546128 / 1000000000000) (-2798546127 / 1000000000000), orderedInterval (28350518260 / 1000000000000) (28350518261 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2311479392901809 / 4000000000000)) (orderedInterval (18795501008 / 1000000000000) (18795501009 / 1000000000000), orderedInterval (27340558170 / 1000000000000) (27340558171 / 1000000000000))) = true
  rfl'

theorem compactCertificate525_stateChecks3 :
    compactCertificate525.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 282 12 (3546403812314207 / 4000000000000)) (orderedInterval (26623302279 / 1000000000000) (26623303697 / 1000000000000), orderedInterval (3025555202 / 1000000000000) (3025556620 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2047517195694503 / 4000000000000)) (orderedInterval (-19469462081 / 1000000000000) (-19469462080 / 1000000000000), orderedInterval (-29385598760 / 1000000000000) (-29385598759 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 289 12 (3633355194254227 / 4000000000000)) (orderedInterval (-24710711984 / 1000000000000) (-24710711923 / 1000000000000), orderedInterval (-9485988587 / 1000000000000) (-9485988526 / 1000000000000))) = true
  rfl'

theorem compactCertificate525_stateChecks4 :
    compactCertificate525.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 270 12 (3394751728912063 / 4000000000000)) (orderedInterval (25931510914 / 1000000000000) (25931510983 / 1000000000000), orderedInterval (8798289966 / 1000000000000) (8798290035 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2422655017399279 / 4000000000000)) (orderedInterval (-3931506022 / 1000000000000) (-3931506021 / 1000000000000), orderedInterval (-32178340820 / 1000000000000) (-32178340819 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 219 12 (2747032580803641 / 4000000000000)) (orderedInterval (13664622240 / 1000000000000) (13664622324 / 1000000000000), orderedInterval (-27217868902 / 1000000000000) (-27217868817 / 1000000000000))) = true
  rfl'

theorem compactCertificate525_stateChecks5 :
    compactCertificate525.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2290189373330729 / 4000000000000)) (orderedInterval (33344168908 / 1000000000000) (33344169659 / 1000000000000), orderedInterval (242178311 / 1000000000000) (242179062 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2023451765813309 / 4000000000000)) (orderedInterval (-26690927038 / 1000000000000) (-26690927037 / 1000000000000), orderedInterval (-23341910132 / 1000000000000) (-23341910131 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 233 12 (586475189553591 / 800000000000)) (orderedInterval (-27997357740 / 1000000000000) (-27997307946 / 1000000000000), orderedInterval (9214202303 / 1000000000000) (9214252097 / 1000000000000))) = true
  rfl'

theorem compactCertificate525_stateChecks6 :
    compactCertificate525.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1622221238803477 / 4000000000000)) (orderedInterval (-34848399456 / 1000000000000) (-34848399455 / 1000000000000), orderedInterval (-18807413922 / 1000000000000) (-18807413921 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1375174909741997 / 4000000000000)) (orderedInterval (-36126926976 / 1000000000000) (-36126843516 / 1000000000000), orderedInterval (23431901824 / 1000000000000) (23431985284 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (860520607098191 / 4000000000000)) (orderedInterval (41044958105 / 1000000000000) (41045038862 / 1000000000000), orderedInterval (-35796101733 / 1000000000000) (-35796020976 / 1000000000000))) = true
  rfl'

theorem compactCertificate525_stateChecks7 :
    compactCertificate525.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (462790844459697 / 4000000000000)) (orderedInterval (-17855656058 / 1000000000000) (-17855656057 / 1000000000000), orderedInterval (-71920485433 / 1000000000000) (-71920485432 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1256567168350091 / 4000000000000)) (orderedInterval (31257928153 / 1000000000000) (31257928154 / 1000000000000), orderedInterval (32345902948 / 1000000000000) (32345902949 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1715735041150507 / 4000000000000)) (orderedInterval (24204187719 / 1000000000000) (24204193337 / 1000000000000), orderedInterval (-30000682927 / 1000000000000) (-30000677308 / 1000000000000))) = true
  rfl'

theorem compactCertificate525_stateChecks8 :
    compactCertificate525.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (725479392901809 / 4000000000000)) (orderedInterval (-3423482139 / 1000000000000) (-3423482131 / 1000000000000), orderedInterval (59156348125 / 1000000000000) (59156348133 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 235 12 (2949033454734289 / 4000000000000)) (orderedInterval (6718679625 / 1000000000000) (6718679627 / 1000000000000), orderedInterval (-28611473360 / 1000000000000) (-28611473358 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1969817677568351 / 4000000000000)) (orderedInterval (-342180729 / 1000000000000) (-342180728 / 1000000000000), orderedInterval (-35952847166 / 1000000000000) (-35952847165 / 1000000000000))) = true
  rfl'

theorem compactCertificate525_states : ∀ j,
    BesselStateValid (compactCertificate525.point j) (compactCertificate525.state j) :=
  compactCertificate525.statesValid_of_checks3 compactCertificate525_stateChecks0
    compactCertificate525_stateChecks1 compactCertificate525_stateChecks2
    compactCertificate525_stateChecks3 compactCertificate525_stateChecks4
    compactCertificate525_stateChecks5 compactCertificate525_stateChecks6
    compactCertificate525_stateChecks7 compactCertificate525_stateChecks8

theorem compactCertificate525_chunkChecks0_0 :
    compactCertificate525.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (793 / 2) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39750293246 / 1000000000000) (39750293292 / 1000000000000), orderedInterval (5000751332 / 1000000000000) (5000751378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1168240421685493 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-29246436988 / 1000000000000) (-29246436987 / 1000000000000), orderedInterval (-36342273934 / 1000000000000) (-36342273933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (377784949358869 / 800000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35935601224 / 1000000000000) (35935606022 / 1000000000000), orderedInterval (-7570785722 / 1000000000000) (-7570780924 / 1000000000000)))) (orderedInterval (17591846682 / 1000000000000) (17591847010 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (340889641414751 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-80022284259 / 1000000000000) (-80022284258 / 1000000000000), orderedInterval (-32186923812 / 1000000000000) (-32186923811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (915677526934547 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-18969920150 / 1000000000000) (-18969920149 / 1000000000000), orderedInterval (-49163496010 / 1000000000000) (-49163496009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2486242610273799 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (9778327344 / 1000000000000) (9778327345 / 1000000000000), orderedInterval (30465277982 / 1000000000000) (30465277983 / 1000000000000)))) (orderedInterval (-519577662 / 1000000000000) (-519577614 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1831355053869887 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-1812989888 / 1000000000000) (-1812989886 / 1000000000000), orderedInterval (37247152922 / 1000000000000) (37247152923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3138058099253051 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-2798546128 / 1000000000000) (-2798546127 / 1000000000000), orderedInterval (28350518260 / 1000000000000) (28350518261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2311479392901809 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18795501008 / 1000000000000) (18795501009 / 1000000000000), orderedInterval (27340558170 / 1000000000000) (27340558171 / 1000000000000)))) (orderedInterval (540568524 / 1000000000000) (540568547 / 1000000000000))) = true
  rfl'

theorem compactCertificate525_chunkChecks0_1 :
    compactCertificate525.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3546403812314207 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26623302279 / 1000000000000) (26623303697 / 1000000000000), orderedInterval (3025555202 / 1000000000000) (3025556620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2047517195694503 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-19469462081 / 1000000000000) (-19469462080 / 1000000000000), orderedInterval (-29385598760 / 1000000000000) (-29385598759 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3633355194254227 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24710711984 / 1000000000000) (-24710711923 / 1000000000000), orderedInterval (-9485988587 / 1000000000000) (-9485988526 / 1000000000000)))) (orderedInterval (-9685939926 / 1000000000000) (-9685939508 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3394751728912063 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25931510914 / 1000000000000) (25931510983 / 1000000000000), orderedInterval (8798289966 / 1000000000000) (8798290035 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2422655017399279 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-3931506022 / 1000000000000) (-3931506021 / 1000000000000), orderedInterval (-32178340820 / 1000000000000) (-32178340819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2747032580803641 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13664622240 / 1000000000000) (13664622324 / 1000000000000), orderedInterval (-27217868902 / 1000000000000) (-27217868817 / 1000000000000)))) (orderedInterval (-909069159 / 1000000000000) (-909069109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2290189373330729 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33344168908 / 1000000000000) (33344169659 / 1000000000000), orderedInterval (242178311 / 1000000000000) (242179062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2023451765813309 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26690927038 / 1000000000000) (-26690927037 / 1000000000000), orderedInterval (-23341910132 / 1000000000000) (-23341910131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (586475189553591 / 800000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27997357740 / 1000000000000) (-27997307946 / 1000000000000), orderedInterval (9214202303 / 1000000000000) (9214252097 / 1000000000000)))) (orderedInterval (1195637552 / 1000000000000) (1195638875 / 1000000000000))) = true
  rfl'

theorem compactCertificate525_chunkChecks0_2 :
    compactCertificate525.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1622221238803477 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34848399456 / 1000000000000) (-34848399455 / 1000000000000), orderedInterval (-18807413922 / 1000000000000) (-18807413921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1375174909741997 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36126926976 / 1000000000000) (-36126843516 / 1000000000000), orderedInterval (23431901824 / 1000000000000) (23431985284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (860520607098191 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (41044958105 / 1000000000000) (41045038862 / 1000000000000), orderedInterval (-35796101733 / 1000000000000) (-35796020976 / 1000000000000)))) (orderedInterval (8953003126 / 1000000000000) (8953010579 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (462790844459697 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-17855656058 / 1000000000000) (-17855656057 / 1000000000000), orderedInterval (-71920485433 / 1000000000000) (-71920485432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1256567168350091 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31257928153 / 1000000000000) (31257928154 / 1000000000000), orderedInterval (32345902948 / 1000000000000) (32345902949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1715735041150507 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24204187719 / 1000000000000) (24204193337 / 1000000000000), orderedInterval (-30000682927 / 1000000000000) (-30000677308 / 1000000000000)))) (orderedInterval (-2234419575 / 1000000000000) (-2234419096 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (725479392901809 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-3423482139 / 1000000000000) (-3423482131 / 1000000000000), orderedInterval (59156348125 / 1000000000000) (59156348133 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2949033454734289 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6718679625 / 1000000000000) (6718679627 / 1000000000000), orderedInterval (-28611473360 / 1000000000000) (-28611473358 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1969817677568351 / 4000000000000) 0 (IntervalRat.scale (793 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-342180729 / 1000000000000) (-342180728 / 1000000000000), orderedInterval (-35952847166 / 1000000000000) (-35952847165 / 1000000000000)))) (orderedInterval (-503348207 / 1000000000000) (-503348097 / 1000000000000))) = true
  rfl'

theorem compactCertificate525_chunkChecks0 :
    compactCertificate525.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate525.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate525_chunkChecks0_0
    compactCertificate525_chunkChecks0_1 compactCertificate525_chunkChecks0_2

theorem compactCertificate525_chunkChecks1_0 :
    compactCertificate525.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (793 / 2) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39750293246 / 1000000000000) (39750293292 / 1000000000000), orderedInterval (5000751332 / 1000000000000) (5000751378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1168240421685493 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-29246436988 / 1000000000000) (-29246436987 / 1000000000000), orderedInterval (-36342273934 / 1000000000000) (-36342273933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (377784949358869 / 800000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35935601224 / 1000000000000) (35935606022 / 1000000000000), orderedInterval (-7570785722 / 1000000000000) (-7570780924 / 1000000000000)))) (orderedInterval (1203566344 / 1000000000000) (1203566729 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (340889641414751 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-80022284259 / 1000000000000) (-80022284258 / 1000000000000), orderedInterval (-32186923812 / 1000000000000) (-32186923811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (915677526934547 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-18969920150 / 1000000000000) (-18969920149 / 1000000000000), orderedInterval (-49163496010 / 1000000000000) (-49163496009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2486242610273799 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (9778327344 / 1000000000000) (9778327345 / 1000000000000), orderedInterval (30465277982 / 1000000000000) (30465277983 / 1000000000000)))) (orderedInterval (-4356406630 / 1000000000000) (-4356406576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1831355053869887 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-1812989888 / 1000000000000) (-1812989886 / 1000000000000), orderedInterval (37247152922 / 1000000000000) (37247152923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3138058099253051 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-2798546128 / 1000000000000) (-2798546127 / 1000000000000), orderedInterval (28350518260 / 1000000000000) (28350518261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2311479392901809 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18795501008 / 1000000000000) (18795501009 / 1000000000000), orderedInterval (27340558170 / 1000000000000) (27340558171 / 1000000000000)))) (orderedInterval (-767152685 / 1000000000000) (-767152646 / 1000000000000))) = true
  rfl'

theorem compactCertificate525_chunkChecks1_1 :
    compactCertificate525.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3546403812314207 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26623302279 / 1000000000000) (26623303697 / 1000000000000), orderedInterval (3025555202 / 1000000000000) (3025556620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2047517195694503 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-19469462081 / 1000000000000) (-19469462080 / 1000000000000), orderedInterval (-29385598760 / 1000000000000) (-29385598759 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3633355194254227 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24710711984 / 1000000000000) (-24710711923 / 1000000000000), orderedInterval (-9485988587 / 1000000000000) (-9485988526 / 1000000000000)))) (orderedInterval (-7102157885 / 1000000000000) (-7102156976 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3394751728912063 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25931510914 / 1000000000000) (25931510983 / 1000000000000), orderedInterval (8798289966 / 1000000000000) (8798290035 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2422655017399279 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-3931506022 / 1000000000000) (-3931506021 / 1000000000000), orderedInterval (-32178340820 / 1000000000000) (-32178340819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2747032580803641 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13664622240 / 1000000000000) (13664622324 / 1000000000000), orderedInterval (-27217868902 / 1000000000000) (-27217868817 / 1000000000000)))) (orderedInterval (-4749481661 / 1000000000000) (-4749481581 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2290189373330729 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33344168908 / 1000000000000) (33344169659 / 1000000000000), orderedInterval (242178311 / 1000000000000) (242179062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2023451765813309 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26690927038 / 1000000000000) (-26690927037 / 1000000000000), orderedInterval (-23341910132 / 1000000000000) (-23341910131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (586475189553591 / 800000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27997357740 / 1000000000000) (-27997307946 / 1000000000000), orderedInterval (9214202303 / 1000000000000) (9214252097 / 1000000000000)))) (orderedInterval (2144449591 / 1000000000000) (2144452016 / 1000000000000))) = true
  rfl'

theorem compactCertificate525_chunkChecks1_2 :
    compactCertificate525.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1622221238803477 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34848399456 / 1000000000000) (-34848399455 / 1000000000000), orderedInterval (-18807413922 / 1000000000000) (-18807413921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1375174909741997 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36126926976 / 1000000000000) (-36126843516 / 1000000000000), orderedInterval (23431901824 / 1000000000000) (23431985284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (860520607098191 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (41044958105 / 1000000000000) (41045038862 / 1000000000000), orderedInterval (-35796101733 / 1000000000000) (-35796020976 / 1000000000000)))) (orderedInterval (1293600329 / 1000000000000) (1293605944 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (462790844459697 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-17855656058 / 1000000000000) (-17855656057 / 1000000000000), orderedInterval (-71920485433 / 1000000000000) (-71920485432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1256567168350091 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31257928153 / 1000000000000) (31257928154 / 1000000000000), orderedInterval (32345902948 / 1000000000000) (32345902949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1715735041150507 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24204187719 / 1000000000000) (24204193337 / 1000000000000), orderedInterval (-30000682927 / 1000000000000) (-30000677308 / 1000000000000)))) (orderedInterval (2293405730 / 1000000000000) (2293406239 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (725479392901809 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-3423482139 / 1000000000000) (-3423482131 / 1000000000000), orderedInterval (59156348125 / 1000000000000) (59156348133 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2949033454734289 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6718679625 / 1000000000000) (6718679627 / 1000000000000), orderedInterval (-28611473360 / 1000000000000) (-28611473358 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1969817677568351 / 4000000000000) 1 (IntervalRat.scale (793 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-342180729 / 1000000000000) (-342180728 / 1000000000000), orderedInterval (-35952847166 / 1000000000000) (-35952847165 / 1000000000000)))) (orderedInterval (12871943528 / 1000000000000) (12871943683 / 1000000000000))) = true
  rfl'

theorem compactCertificate525_chunkChecks1 :
    compactCertificate525.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate525.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate525_chunkChecks1_0
    compactCertificate525_chunkChecks1_1 compactCertificate525_chunkChecks1_2

theorem compactCertificate525_chunkChecks2_0 :
    compactCertificate525.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (793 / 2) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39750293246 / 1000000000000) (39750293292 / 1000000000000), orderedInterval (5000751332 / 1000000000000) (5000751378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1168240421685493 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-29246436988 / 1000000000000) (-29246436987 / 1000000000000), orderedInterval (-36342273934 / 1000000000000) (-36342273933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (377784949358869 / 800000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35935601224 / 1000000000000) (35935606022 / 1000000000000), orderedInterval (-7570785722 / 1000000000000) (-7570780924 / 1000000000000)))) (orderedInterval (-18602005180 / 1000000000000) (-18602004726 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (340889641414751 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-80022284259 / 1000000000000) (-80022284258 / 1000000000000), orderedInterval (-32186923812 / 1000000000000) (-32186923811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (915677526934547 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-18969920150 / 1000000000000) (-18969920149 / 1000000000000), orderedInterval (-49163496010 / 1000000000000) (-49163496009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2486242610273799 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (9778327344 / 1000000000000) (9778327345 / 1000000000000), orderedInterval (30465277982 / 1000000000000) (30465277983 / 1000000000000)))) (orderedInterval (1910004276 / 1000000000000) (1910004351 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1831355053869887 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-1812989888 / 1000000000000) (-1812989886 / 1000000000000), orderedInterval (37247152922 / 1000000000000) (37247152923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3138058099253051 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-2798546128 / 1000000000000) (-2798546127 / 1000000000000), orderedInterval (28350518260 / 1000000000000) (28350518261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2311479392901809 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18795501008 / 1000000000000) (18795501009 / 1000000000000), orderedInterval (27340558170 / 1000000000000) (27340558171 / 1000000000000)))) (orderedInterval (-1300858988 / 1000000000000) (-1300858918 / 1000000000000))) = true
  rfl'

theorem compactCertificate525_chunkChecks2_1 :
    compactCertificate525.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3546403812314207 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26623302279 / 1000000000000) (26623303697 / 1000000000000), orderedInterval (3025555202 / 1000000000000) (3025556620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2047517195694503 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-19469462081 / 1000000000000) (-19469462080 / 1000000000000), orderedInterval (-29385598760 / 1000000000000) (-29385598759 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3633355194254227 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24710711984 / 1000000000000) (-24710711923 / 1000000000000), orderedInterval (-9485988587 / 1000000000000) (-9485988526 / 1000000000000)))) (orderedInterval (44511013215 / 1000000000000) (44511015220 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3394751728912063 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25931510914 / 1000000000000) (25931510983 / 1000000000000), orderedInterval (8798289966 / 1000000000000) (8798290035 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2422655017399279 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-3931506022 / 1000000000000) (-3931506021 / 1000000000000), orderedInterval (-32178340820 / 1000000000000) (-32178340819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2747032580803641 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13664622240 / 1000000000000) (13664622324 / 1000000000000), orderedInterval (-27217868902 / 1000000000000) (-27217868817 / 1000000000000)))) (orderedInterval (3231715390 / 1000000000000) (3231715525 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2290189373330729 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33344168908 / 1000000000000) (33344169659 / 1000000000000), orderedInterval (242178311 / 1000000000000) (242179062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2023451765813309 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26690927038 / 1000000000000) (-26690927037 / 1000000000000), orderedInterval (-23341910132 / 1000000000000) (-23341910131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (586475189553591 / 800000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27997357740 / 1000000000000) (-27997307946 / 1000000000000), orderedInterval (9214202303 / 1000000000000) (9214252097 / 1000000000000)))) (orderedInterval (-844011630 / 1000000000000) (-844007165 / 1000000000000))) = true
  rfl'

theorem compactCertificate525_chunkChecks2_2 :
    compactCertificate525.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1622221238803477 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34848399456 / 1000000000000) (-34848399455 / 1000000000000), orderedInterval (-18807413922 / 1000000000000) (-18807413921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1375174909741997 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36126926976 / 1000000000000) (-36126843516 / 1000000000000), orderedInterval (23431901824 / 1000000000000) (23431985284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (860520607098191 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (41044958105 / 1000000000000) (41045038862 / 1000000000000), orderedInterval (-35796101733 / 1000000000000) (-35796020976 / 1000000000000)))) (orderedInterval (-7763332357 / 1000000000000) (-7763327929 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (462790844459697 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-17855656058 / 1000000000000) (-17855656057 / 1000000000000), orderedInterval (-71920485433 / 1000000000000) (-71920485432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1256567168350091 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31257928153 / 1000000000000) (31257928154 / 1000000000000), orderedInterval (32345902948 / 1000000000000) (32345902949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1715735041150507 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24204187719 / 1000000000000) (24204193337 / 1000000000000), orderedInterval (-30000682927 / 1000000000000) (-30000677308 / 1000000000000)))) (orderedInterval (2582155155 / 1000000000000) (2582155703 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (725479392901809 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-3423482139 / 1000000000000) (-3423482131 / 1000000000000), orderedInterval (59156348125 / 1000000000000) (59156348133 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2949033454734289 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6718679625 / 1000000000000) (6718679627 / 1000000000000), orderedInterval (-28611473360 / 1000000000000) (-28611473358 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1969817677568351 / 4000000000000) 2 (IntervalRat.scale (793 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-342180729 / 1000000000000) (-342180728 / 1000000000000), orderedInterval (-35952847166 / 1000000000000) (-35952847165 / 1000000000000)))) (orderedInterval (1763727649 / 1000000000000) (1763727877 / 1000000000000))) = true
  rfl'

theorem compactCertificate525_chunkChecks2 :
    compactCertificate525.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate525.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate525_chunkChecks2_0
    compactCertificate525_chunkChecks2_1 compactCertificate525_chunkChecks2_2

theorem compactCertificate525_chunkChecks3_0 :
    compactCertificate525.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (793 / 2) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39750293246 / 1000000000000) (39750293292 / 1000000000000), orderedInterval (5000751332 / 1000000000000) (5000751378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1168240421685493 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-29246436988 / 1000000000000) (-29246436987 / 1000000000000), orderedInterval (-36342273934 / 1000000000000) (-36342273933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (377784949358869 / 800000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35935601224 / 1000000000000) (35935606022 / 1000000000000), orderedInterval (-7570785722 / 1000000000000) (-7570780924 / 1000000000000)))) (orderedInterval (-1049320422 / 1000000000000) (-1049319886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (340889641414751 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-80022284259 / 1000000000000) (-80022284258 / 1000000000000), orderedInterval (-32186923812 / 1000000000000) (-32186923811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (915677526934547 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-18969920150 / 1000000000000) (-18969920149 / 1000000000000), orderedInterval (-49163496010 / 1000000000000) (-49163496009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2486242610273799 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (9778327344 / 1000000000000) (9778327345 / 1000000000000), orderedInterval (30465277982 / 1000000000000) (30465277983 / 1000000000000)))) (orderedInterval (8680339940 / 1000000000000) (8680340052 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1831355053869887 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-1812989888 / 1000000000000) (-1812989886 / 1000000000000), orderedInterval (37247152922 / 1000000000000) (37247152923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3138058099253051 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-2798546128 / 1000000000000) (-2798546127 / 1000000000000), orderedInterval (28350518260 / 1000000000000) (28350518261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2311479392901809 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18795501008 / 1000000000000) (18795501009 / 1000000000000), orderedInterval (27340558170 / 1000000000000) (27340558171 / 1000000000000)))) (orderedInterval (4731105318 / 1000000000000) (4731105444 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate525_chunkChecks3_1 :
    compactCertificate525.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3546403812314207 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26623302279 / 1000000000000) (26623303697 / 1000000000000), orderedInterval (3025555202 / 1000000000000) (3025556620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2047517195694503 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-19469462081 / 1000000000000) (-19469462080 / 1000000000000), orderedInterval (-29385598760 / 1000000000000) (-29385598759 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3633355194254227 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24710711984 / 1000000000000) (-24710711923 / 1000000000000), orderedInterval (-9485988587 / 1000000000000) (-9485988526 / 1000000000000)))) (orderedInterval (26795881021 / 1000000000000) (26795885475 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3394751728912063 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25931510914 / 1000000000000) (25931510983 / 1000000000000), orderedInterval (8798289966 / 1000000000000) (8798290035 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2422655017399279 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-3931506022 / 1000000000000) (-3931506021 / 1000000000000), orderedInterval (-32178340820 / 1000000000000) (-32178340819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2747032580803641 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13664622240 / 1000000000000) (13664622324 / 1000000000000), orderedInterval (-27217868902 / 1000000000000) (-27217868817 / 1000000000000)))) (orderedInterval (11679237495 / 1000000000000) (11679237725 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2290189373330729 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33344168908 / 1000000000000) (33344169659 / 1000000000000), orderedInterval (242178311 / 1000000000000) (242179062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2023451765813309 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26690927038 / 1000000000000) (-26690927037 / 1000000000000), orderedInterval (-23341910132 / 1000000000000) (-23341910131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (586475189553591 / 800000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27997357740 / 1000000000000) (-27997307946 / 1000000000000), orderedInterval (9214202303 / 1000000000000) (9214252097 / 1000000000000)))) (orderedInterval (-4271395426 / 1000000000000) (-4271387205 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate525_chunkChecks3_2 :
    compactCertificate525.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1622221238803477 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34848399456 / 1000000000000) (-34848399455 / 1000000000000), orderedInterval (-18807413922 / 1000000000000) (-18807413921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1375174909741997 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36126926976 / 1000000000000) (-36126843516 / 1000000000000), orderedInterval (23431901824 / 1000000000000) (23431985284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (860520607098191 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (41044958105 / 1000000000000) (41045038862 / 1000000000000), orderedInterval (-35796101733 / 1000000000000) (-35796020976 / 1000000000000)))) (orderedInterval (-2147668931 / 1000000000000) (-2147665335 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (462790844459697 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-17855656058 / 1000000000000) (-17855656057 / 1000000000000), orderedInterval (-71920485433 / 1000000000000) (-71920485432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1256567168350091 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31257928153 / 1000000000000) (31257928154 / 1000000000000), orderedInterval (32345902948 / 1000000000000) (32345902949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1715735041150507 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24204187719 / 1000000000000) (24204193337 / 1000000000000), orderedInterval (-30000682927 / 1000000000000) (-30000677308 / 1000000000000)))) (orderedInterval (-2585396451 / 1000000000000) (-2585395860 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (725479392901809 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-3423482139 / 1000000000000) (-3423482131 / 1000000000000), orderedInterval (59156348125 / 1000000000000) (59156348133 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2949033454734289 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6718679625 / 1000000000000) (6718679627 / 1000000000000), orderedInterval (-28611473360 / 1000000000000) (-28611473358 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1969817677568351 / 4000000000000) 3 (IntervalRat.scale (793 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-342180729 / 1000000000000) (-342180728 / 1000000000000), orderedInterval (-35952847166 / 1000000000000) (-35952847165 / 1000000000000)))) (orderedInterval (-27935294430 / 1000000000000) (-27935294077 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate525_chunkChecks3 :
    compactCertificate525.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate525.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate525_chunkChecks3_0
    compactCertificate525_chunkChecks3_1 compactCertificate525_chunkChecks3_2

theorem compactCertificate525_chunkChecks4_0 :
    compactCertificate525.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (793 / 2) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39750293246 / 1000000000000) (39750293292 / 1000000000000), orderedInterval (5000751332 / 1000000000000) (5000751378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1168240421685493 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-29246436988 / 1000000000000) (-29246436987 / 1000000000000), orderedInterval (-36342273934 / 1000000000000) (-36342273933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (377784949358869 / 800000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35935601224 / 1000000000000) (35935606022 / 1000000000000), orderedInterval (-7570785722 / 1000000000000) (-7570780924 / 1000000000000)))) (orderedInterval (19923537378 / 1000000000000) (19923538014 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (340889641414751 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-80022284259 / 1000000000000) (-80022284258 / 1000000000000), orderedInterval (-32186923812 / 1000000000000) (-32186923811 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (915677526934547 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-18969920150 / 1000000000000) (-18969920149 / 1000000000000), orderedInterval (-49163496010 / 1000000000000) (-49163496009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2486242610273799 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (9778327344 / 1000000000000) (9778327345 / 1000000000000), orderedInterval (30465277982 / 1000000000000) (30465277983 / 1000000000000)))) (orderedInterval (-4316778998 / 1000000000000) (-4316778825 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1831355053869887 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-1812989888 / 1000000000000) (-1812989886 / 1000000000000), orderedInterval (37247152922 / 1000000000000) (37247152923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3138058099253051 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-2798546128 / 1000000000000) (-2798546127 / 1000000000000), orderedInterval (28350518260 / 1000000000000) (28350518261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2311479392901809 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18795501008 / 1000000000000) (18795501009 / 1000000000000), orderedInterval (27340558170 / 1000000000000) (27340558171 / 1000000000000)))) (orderedInterval (3348523968 / 1000000000000) (3348524200 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate525_chunkChecks4_1 :
    compactCertificate525.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3546403812314207 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26623302279 / 1000000000000) (26623303697 / 1000000000000), orderedInterval (3025555202 / 1000000000000) (3025556620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2047517195694503 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-19469462081 / 1000000000000) (-19469462080 / 1000000000000), orderedInterval (-29385598760 / 1000000000000) (-29385598759 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3633355194254227 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24710711984 / 1000000000000) (-24710711923 / 1000000000000), orderedInterval (-9485988587 / 1000000000000) (-9485988526 / 1000000000000)))) (orderedInterval (-219161865285 / 1000000000000) (-219161855335 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3394751728912063 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25931510914 / 1000000000000) (25931510983 / 1000000000000), orderedInterval (8798289966 / 1000000000000) (8798290035 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2422655017399279 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-3931506022 / 1000000000000) (-3931506021 / 1000000000000), orderedInterval (-32178340820 / 1000000000000) (-32178340819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2747032580803641 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13664622240 / 1000000000000) (13664622324 / 1000000000000), orderedInterval (-27217868902 / 1000000000000) (-27217868817 / 1000000000000)))) (orderedInterval (-12531848932 / 1000000000000) (-12531848527 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2290189373330729 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (33344168908 / 1000000000000) (33344169659 / 1000000000000), orderedInterval (242178311 / 1000000000000) (242179062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2023451765813309 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26690927038 / 1000000000000) (-26690927037 / 1000000000000), orderedInterval (-23341910132 / 1000000000000) (-23341910131 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (586475189553591 / 800000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27997357740 / 1000000000000) (-27997307946 / 1000000000000), orderedInterval (9214202303 / 1000000000000) (9214252097 / 1000000000000)))) (orderedInterval (-2634479177 / 1000000000000) (-2634464000 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate525_chunkChecks4_2 :
    compactCertificate525.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1622221238803477 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34848399456 / 1000000000000) (-34848399455 / 1000000000000), orderedInterval (-18807413922 / 1000000000000) (-18807413921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1375174909741997 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36126926976 / 1000000000000) (-36126843516 / 1000000000000), orderedInterval (23431901824 / 1000000000000) (23431985284 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (860520607098191 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (41044958105 / 1000000000000) (41045038862 / 1000000000000), orderedInterval (-35796101733 / 1000000000000) (-35796020976 / 1000000000000)))) (orderedInterval (7381053751 / 1000000000000) (7381056751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (462790844459697 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-17855656058 / 1000000000000) (-17855656057 / 1000000000000), orderedInterval (-71920485433 / 1000000000000) (-71920485432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1256567168350091 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (31257928153 / 1000000000000) (31257928154 / 1000000000000), orderedInterval (32345902948 / 1000000000000) (32345902949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1715735041150507 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24204187719 / 1000000000000) (24204193337 / 1000000000000), orderedInterval (-30000682927 / 1000000000000) (-30000677308 / 1000000000000)))) (orderedInterval (-2804527544 / 1000000000000) (-2804526905 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (725479392901809 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-3423482139 / 1000000000000) (-3423482131 / 1000000000000), orderedInterval (59156348125 / 1000000000000) (59156348133 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2949033454734289 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6718679625 / 1000000000000) (6718679627 / 1000000000000), orderedInterval (-28611473360 / 1000000000000) (-28611473358 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1969817677568351 / 4000000000000) 4 (IntervalRat.scale (793 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-342180729 / 1000000000000) (-342180728 / 1000000000000), orderedInterval (-35952847166 / 1000000000000) (-35952847165 / 1000000000000)))) (orderedInterval (-6244895681 / 1000000000000) (-6244895115 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate525_chunkChecks4 :
    compactCertificate525.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate525.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate525_chunkChecks4_0
    compactCertificate525_chunkChecks4_1 compactCertificate525_chunkChecks4_2

theorem compactCertificate525_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate525.chunkCheck r b = true :=
  compactCertificate525.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate525_chunkChecks0
    · exact compactCertificate525_chunkChecks1
    · exact compactCertificate525_chunkChecks2
    · exact compactCertificate525_chunkChecks3
    · exact compactCertificate525_chunkChecks4)

theorem compactCertificate525_coefficient0 :
    compactCertificate525.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate525_coefficient1 :
    compactCertificate525.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate525_coefficient2 :
    compactCertificate525.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate525_coefficient3 :
    compactCertificate525.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate525_coefficient4 :
    compactCertificate525.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate525_coefficients : ∀ r : Fin 5,
    compactCertificate525.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate525_coefficient0
  · exact compactCertificate525_coefficient1
  · exact compactCertificate525_coefficient2
  · exact compactCertificate525_coefficient3
  · exact compactCertificate525_coefficient4

theorem compactCertificate525_lower : (1 : ℚ) ≤ compactCertificate525.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate525, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate525_proves {t : ℝ} (ht : t ∈ compactCertificate525.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate525.proves compactCertificate525_states compactCertificate525_chunks
    compactCertificate525_coefficients compactCertificate525_lower ht

end Erdos232
