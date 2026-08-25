/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate416 : CompactCertificate where
  left := 287
  right := 288
  center := 575 / 2
  grid := fun i =>
    match i.val with
    | 0 => 92
    | 1 => 67
    | 2 => 109
    | 3 => 20
    | 4 => 53
    | 5 => 144
    | 6 => 106
    | 7 => 181
    | 8 => 133
    | 9 => 205
    | 10 => 118
    | 11 => 210
    | 12 => 196
    | 13 => 140
    | 14 => 159
    | 15 => 132
    | 16 => 117
    | 17 => 169
    | 18 => 94
    | 19 => 79
    | 20 => 50
    | 21 => 27
    | 22 => 73
    | 23 => 99
    | 24 => 42
    | 25 => 170
    | _ => 114
  point := fun i =>
    match i.val with
    | 0 => 575 / 2
    | 1 => 33883391801723 / 160000000000
    | 2 => 10957192730459 / 32000000000
    | 3 => 9887089221361 / 160000000000
    | 4 => 26558112382717 / 160000000000
    | 5 => 72110441407689 / 160000000000
    | 6 => 53116224765457 / 160000000000
    | 7 => 91015556472661 / 160000000000
    | 8 => 67041646956799 / 160000000000
    | 9 => 102859126964977 / 160000000000
    | 10 => 59385744641833 / 160000000000
    | 11 => 105381045987197 / 160000000000
    | 12 => 98460642830993 / 160000000000
    | 13 => 70266160655969 / 160000000000
    | 14 => 79674337148151 / 160000000000
    | 15 => 66424155846919 / 160000000000
    | 16 => 58687756133299 / 160000000000
    | 17 => 17009999192601 / 32000000000
    | 18 => 47050552953947 / 160000000000
    | 19 => 39885274809667 / 160000000000
    | 20 => 24958353043201 / 160000000000
    | 21 => 13422685274367 / 160000000000
    | 22 => 36445201604101 / 160000000000
    | 23 => 49762806994277 / 160000000000
    | 24 => 21041646956799 / 160000000000
    | 25 => 85533126682079 / 160000000000
    | _ => 57132164670961 / 160000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-31783923008 / 1000000000000) (-31783901864 / 1000000000000), orderedInterval (34755594183 / 1000000000000) (34755615327 / 1000000000000))
    | 1 => (orderedInterval (-48155815515 / 1000000000000) (-48155792028 / 1000000000000), orderedInterval (26327838246 / 1000000000000) (26327861733 / 1000000000000))
    | 2 => (orderedInterval (-29821008093 / 1000000000000) (-29821008092 / 1000000000000), orderedInterval (-31100115929 / 1000000000000) (-31100115928 / 1000000000000))
    | 3 => (orderedInterval (-25520933505 / 1000000000000) (-25520933158 / 1000000000000), orderedInterval (98447088950 / 1000000000000) (98447089297 / 1000000000000))
    | 4 => (orderedInterval (-16425336626 / 1000000000000) (-16425336625 / 1000000000000), orderedInterval (-59662789059 / 1000000000000) (-59662789058 / 1000000000000))
    | 5 => (orderedInterval (-29763753929 / 1000000000000) (-29763705968 / 1000000000000), orderedInterval (22982157011 / 1000000000000) (22982204972 / 1000000000000))
    | 6 => (orderedInterval (-10723528353 / 1000000000000) (-10723528304 / 1000000000000), orderedInterval (42474054572 / 1000000000000) (42474054620 / 1000000000000))
    | 7 => (orderedInterval (-28224706708 / 1000000000000) (-28224706707 / 1000000000000), orderedInterval (-17933640561 / 1000000000000) (-17933640560 / 1000000000000))
    | 8 => (orderedInterval (-36010533226 / 1000000000000) (-36010509937 / 1000000000000), orderedInterval (14962179820 / 1000000000000) (14962203109 / 1000000000000))
    | 9 => (orderedInterval (11430791629 / 1000000000000) (11430791659 / 1000000000000), orderedInterval (-29328091400 / 1000000000000) (-29328091370 / 1000000000000))
    | 10 => (orderedInterval (39143197699 / 1000000000000) (39143197701 / 1000000000000), orderedInterval (13475802719 / 1000000000000) (13475802721 / 1000000000000))
    | 11 => (orderedInterval (-9712265608 / 1000000000000) (-9712265596 / 1000000000000), orderedInterval (29541280127 / 1000000000000) (29541280138 / 1000000000000))
    | 12 => (orderedInterval (12881350630 / 1000000000000) (12881350631 / 1000000000000), orderedInterval (29461343704 / 1000000000000) (29461343705 / 1000000000000))
    | 13 => (orderedInterval (4771254854 / 1000000000000) (4771254855 / 1000000000000), orderedInterval (37768302934 / 1000000000000) (37768302935 / 1000000000000))
    | 14 => (orderedInterval (24722583479 / 1000000000000) (24722592769 / 1000000000000), orderedInterval (-25855768411 / 1000000000000) (-25855759121 / 1000000000000))
    | 15 => (orderedInterval (37110062547 / 1000000000000) (37110062550 / 1000000000000), orderedInterval (12457627437 / 1000000000000) (12457627440 / 1000000000000))
    | 16 => (orderedInterval (-716225584 / 1000000000000) (-716225583 / 1000000000000), orderedInterval (-41653560750 / 1000000000000) (-41653560749 / 1000000000000))
    | 17 => (orderedInterval (-34206236078 / 1000000000000) (-34206235992 / 1000000000000), orderedInterval (-5218689133 / 1000000000000) (-5218689048 / 1000000000000))
    | 18 => (orderedInterval (-20605296787 / 1000000000000) (-20605295753 / 1000000000000), orderedInterval (41752073868 / 1000000000000) (41752074902 / 1000000000000))
    | 19 => (orderedInterval (-48107013653 / 1000000000000) (-48107009255 / 1000000000000), orderedInterval (15572760201 / 1000000000000) (15572764599 / 1000000000000))
    | 20 => (orderedInterval (-19203945497 / 1000000000000) (-19203945130 / 1000000000000), orderedInterval (60990947309 / 1000000000000) (60990947677 / 1000000000000))
    | 21 => (orderedInterval (12786100313 / 1000000000000) (12786100383 / 1000000000000), orderedInterval (-86245964497 / 1000000000000) (-86245964427 / 1000000000000))
    | 22 => (orderedInterval (36760504438 / 1000000000000) (36760540382 / 1000000000000), orderedInterval (-38074421391 / 1000000000000) (-38074385447 / 1000000000000))
    | 23 => (orderedInterval (-31974344658 / 1000000000000) (-31974344657 / 1000000000000), orderedInterval (-31956951467 / 1000000000000) (-31956951466 / 1000000000000))
    | 24 => (orderedInterval (23716819808 / 1000000000000) (23716819809 / 1000000000000), orderedInterval (65319121599 / 1000000000000) (65319121600 / 1000000000000))
    | 25 => (orderedInterval (33218527440 / 1000000000000) (33218527454 / 1000000000000), orderedInterval (9317878803 / 1000000000000) (9317878818 / 1000000000000))
    | _ => (orderedInterval (-11688532881 / 1000000000000) (-11688532816 / 1000000000000), orderedInterval (40590356761 / 1000000000000) (40590356827 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-14796683960 / 1000000000000) (-14796675340 / 1000000000000)
      | 1 => orderedInterval (1793057466 / 1000000000000) (1793060915 / 1000000000000)
      | 2 => orderedInterval (259334 / 1000000000000) (259914 / 1000000000000)
      | 3 => orderedInterval (-511580660 / 1000000000000) (-511580539 / 1000000000000)
      | 4 => orderedInterval (93524826 / 1000000000000) (93524908 / 1000000000000)
      | 5 => orderedInterval (-406292806 / 1000000000000) (-406292776 / 1000000000000)
      | 6 => orderedInterval (5392295977 / 1000000000000) (5392296476 / 1000000000000)
      | 7 => orderedInterval (1380399480 / 1000000000000) (1380400332 / 1000000000000)
      | _ => orderedInterval (-367995617 / 1000000000000) (-367995524 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (11783043705 / 1000000000000) (11783052270 / 1000000000000)
      | 1 => orderedInterval (-4048435022 / 1000000000000) (-4048429636 / 1000000000000)
      | 2 => orderedInterval (1621467529 / 1000000000000) (1621468378 / 1000000000000)
      | 3 => orderedInterval (22562219104 / 1000000000000) (22562219356 / 1000000000000)
      | 4 => orderedInterval (4543717892 / 1000000000000) (4543718030 / 1000000000000)
      | 5 => orderedInterval (3001846810 / 1000000000000) (3001846854 / 1000000000000)
      | 6 => orderedInterval (-6515236646 / 1000000000000) (-6515236188 / 1000000000000)
      | 7 => orderedInterval (3798553026 / 1000000000000) (3798553704 / 1000000000000)
      | _ => orderedInterval (-10689118282 / 1000000000000) (-10689118153 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (15282744251 / 1000000000000) (15282752807 / 1000000000000)
      | 1 => orderedInterval (-4998460760 / 1000000000000) (-4998452308 / 1000000000000)
      | 2 => orderedInterval (-1565161549 / 1000000000000) (-1565160300 / 1000000000000)
      | 3 => orderedInterval (12489383150 / 1000000000000) (12489383693 / 1000000000000)
      | 4 => orderedInterval (372189794 / 1000000000000) (372190028 / 1000000000000)
      | 5 => orderedInterval (2023240131 / 1000000000000) (2023240198 / 1000000000000)
      | 6 => orderedInterval (-5287203776 / 1000000000000) (-5287203347 / 1000000000000)
      | 7 => orderedInterval (-2337377922 / 1000000000000) (-2337377376 / 1000000000000)
      | _ => orderedInterval (5973325908 / 1000000000000) (5973326096 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-10843817472 / 1000000000000) (-10843808943 / 1000000000000)
      | 1 => orderedInterval (6741048824 / 1000000000000) (6741062069 / 1000000000000)
      | 2 => orderedInterval (-5398589712 / 1000000000000) (-5398587874 / 1000000000000)
      | 3 => orderedInterval (-110945332191 / 1000000000000) (-110945331003 / 1000000000000)
      | 4 => orderedInterval (-8194916322 / 1000000000000) (-8194915921 / 1000000000000)
      | 5 => orderedInterval (-4545776924 / 1000000000000) (-4545776818 / 1000000000000)
      | 6 => orderedInterval (7419495380 / 1000000000000) (7419495785 / 1000000000000)
      | 7 => orderedInterval (-3561652437 / 1000000000000) (-3561651997 / 1000000000000)
      | _ => orderedInterval (19408614295 / 1000000000000) (19408614581 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-16175517006 / 1000000000000) (-16175508466 / 1000000000000)
      | 1 => orderedInterval (12664757665 / 1000000000000) (12664778472 / 1000000000000)
      | 2 => orderedInterval (9453242555 / 1000000000000) (9453245275 / 1000000000000)
      | 3 => orderedInterval (-79977873517 / 1000000000000) (-79977870872 / 1000000000000)
      | 4 => orderedInterval (-3493801908 / 1000000000000) (-3493801211 / 1000000000000)
      | 5 => orderedInterval (-8231331900 / 1000000000000) (-8231331728 / 1000000000000)
      | 6 => orderedInterval (5039230929 / 1000000000000) (5039231315 / 1000000000000)
      | 7 => orderedInterval (3050553275 / 1000000000000) (3050553633 / 1000000000000)
      | _ => orderedInterval (-27233830058 / 1000000000000) (-27233829606 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-7423015960 / 1000000000000) (-7423001634 / 1000000000000)
    | 1 => orderedInterval (26058058116 / 1000000000000) (26058074615 / 1000000000000)
    | 2 => orderedInterval (21952679227 / 1000000000000) (21952699491 / 1000000000000)
    | 3 => orderedInterval (-109920926559 / 1000000000000) (-109920900121 / 1000000000000)
    | _ => orderedInterval (-104904569965 / 1000000000000) (-104904533188 / 1000000000000)

theorem compactCertificate416_stateChecks0 :
    compactCertificate416.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (575 / 2)) (orderedInterval (-31783923008 / 1000000000000) (-31783901864 / 1000000000000), orderedInterval (34755594183 / 1000000000000) (34755615327 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (33883391801723 / 160000000000)) (orderedInterval (-48155815515 / 1000000000000) (-48155792028 / 1000000000000), orderedInterval (26327838246 / 1000000000000) (26327861733 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (10957192730459 / 32000000000)) (orderedInterval (-29821008093 / 1000000000000) (-29821008092 / 1000000000000), orderedInterval (-31100115929 / 1000000000000) (-31100115928 / 1000000000000))) = true
  rfl'

theorem compactCertificate416_stateChecks1 :
    compactCertificate416.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (9887089221361 / 160000000000)) (orderedInterval (-25520933505 / 1000000000000) (-25520933158 / 1000000000000), orderedInterval (98447088950 / 1000000000000) (98447089297 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (26558112382717 / 160000000000)) (orderedInterval (-16425336626 / 1000000000000) (-16425336625 / 1000000000000), orderedInterval (-59662789059 / 1000000000000) (-59662789058 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (72110441407689 / 160000000000)) (orderedInterval (-29763753929 / 1000000000000) (-29763705968 / 1000000000000), orderedInterval (22982157011 / 1000000000000) (22982204972 / 1000000000000))) = true
  rfl'

theorem compactCertificate416_stateChecks2 :
    compactCertificate416.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (53116224765457 / 160000000000)) (orderedInterval (-10723528353 / 1000000000000) (-10723528304 / 1000000000000), orderedInterval (42474054572 / 1000000000000) (42474054620 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (91015556472661 / 160000000000)) (orderedInterval (-28224706708 / 1000000000000) (-28224706707 / 1000000000000), orderedInterval (-17933640561 / 1000000000000) (-17933640560 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (67041646956799 / 160000000000)) (orderedInterval (-36010533226 / 1000000000000) (-36010509937 / 1000000000000), orderedInterval (14962179820 / 1000000000000) (14962203109 / 1000000000000))) = true
  rfl'

theorem compactCertificate416_stateChecks3 :
    compactCertificate416.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (102859126964977 / 160000000000)) (orderedInterval (11430791629 / 1000000000000) (11430791659 / 1000000000000), orderedInterval (-29328091400 / 1000000000000) (-29328091370 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (59385744641833 / 160000000000)) (orderedInterval (39143197699 / 1000000000000) (39143197701 / 1000000000000), orderedInterval (13475802719 / 1000000000000) (13475802721 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (105381045987197 / 160000000000)) (orderedInterval (-9712265608 / 1000000000000) (-9712265596 / 1000000000000), orderedInterval (29541280127 / 1000000000000) (29541280138 / 1000000000000))) = true
  rfl'

theorem compactCertificate416_stateChecks4 :
    compactCertificate416.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (98460642830993 / 160000000000)) (orderedInterval (12881350630 / 1000000000000) (12881350631 / 1000000000000), orderedInterval (29461343704 / 1000000000000) (29461343705 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (70266160655969 / 160000000000)) (orderedInterval (4771254854 / 1000000000000) (4771254855 / 1000000000000), orderedInterval (37768302934 / 1000000000000) (37768302935 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (79674337148151 / 160000000000)) (orderedInterval (24722583479 / 1000000000000) (24722592769 / 1000000000000), orderedInterval (-25855768411 / 1000000000000) (-25855759121 / 1000000000000))) = true
  rfl'

theorem compactCertificate416_stateChecks5 :
    compactCertificate416.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (66424155846919 / 160000000000)) (orderedInterval (37110062547 / 1000000000000) (37110062550 / 1000000000000), orderedInterval (12457627437 / 1000000000000) (12457627440 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (58687756133299 / 160000000000)) (orderedInterval (-716225584 / 1000000000000) (-716225583 / 1000000000000), orderedInterval (-41653560750 / 1000000000000) (-41653560749 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (17009999192601 / 32000000000)) (orderedInterval (-34206236078 / 1000000000000) (-34206235992 / 1000000000000), orderedInterval (-5218689133 / 1000000000000) (-5218689048 / 1000000000000))) = true
  rfl'

theorem compactCertificate416_stateChecks6 :
    compactCertificate416.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (47050552953947 / 160000000000)) (orderedInterval (-20605296787 / 1000000000000) (-20605295753 / 1000000000000), orderedInterval (41752073868 / 1000000000000) (41752074902 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (39885274809667 / 160000000000)) (orderedInterval (-48107013653 / 1000000000000) (-48107009255 / 1000000000000), orderedInterval (15572760201 / 1000000000000) (15572764599 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (24958353043201 / 160000000000)) (orderedInterval (-19203945497 / 1000000000000) (-19203945130 / 1000000000000), orderedInterval (60990947309 / 1000000000000) (60990947677 / 1000000000000))) = true
  rfl'

theorem compactCertificate416_stateChecks7 :
    compactCertificate416.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (13422685274367 / 160000000000)) (orderedInterval (12786100313 / 1000000000000) (12786100383 / 1000000000000), orderedInterval (-86245964497 / 1000000000000) (-86245964427 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (36445201604101 / 160000000000)) (orderedInterval (36760504438 / 1000000000000) (36760540382 / 1000000000000), orderedInterval (-38074421391 / 1000000000000) (-38074385447 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (49762806994277 / 160000000000)) (orderedInterval (-31974344658 / 1000000000000) (-31974344657 / 1000000000000), orderedInterval (-31956951467 / 1000000000000) (-31956951466 / 1000000000000))) = true
  rfl'

theorem compactCertificate416_stateChecks8 :
    compactCertificate416.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (21041646956799 / 160000000000)) (orderedInterval (23716819808 / 1000000000000) (23716819809 / 1000000000000), orderedInterval (65319121599 / 1000000000000) (65319121600 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (85533126682079 / 160000000000)) (orderedInterval (33218527440 / 1000000000000) (33218527454 / 1000000000000), orderedInterval (9317878803 / 1000000000000) (9317878818 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (57132164670961 / 160000000000)) (orderedInterval (-11688532881 / 1000000000000) (-11688532816 / 1000000000000), orderedInterval (40590356761 / 1000000000000) (40590356827 / 1000000000000))) = true
  rfl'

theorem compactCertificate416_states : ∀ j,
    BesselStateValid (compactCertificate416.point j) (compactCertificate416.state j) :=
  compactCertificate416.statesValid_of_checks3 compactCertificate416_stateChecks0
    compactCertificate416_stateChecks1 compactCertificate416_stateChecks2
    compactCertificate416_stateChecks3 compactCertificate416_stateChecks4
    compactCertificate416_stateChecks5 compactCertificate416_stateChecks6
    compactCertificate416_stateChecks7 compactCertificate416_stateChecks8

theorem compactCertificate416_chunkChecks0_0 :
    compactCertificate416.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (575 / 2) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31783923008 / 1000000000000) (-31783901864 / 1000000000000), orderedInterval (34755594183 / 1000000000000) (34755615327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (33883391801723 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48155815515 / 1000000000000) (-48155792028 / 1000000000000), orderedInterval (26327838246 / 1000000000000) (26327861733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (10957192730459 / 32000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29821008093 / 1000000000000) (-29821008092 / 1000000000000), orderedInterval (-31100115929 / 1000000000000) (-31100115928 / 1000000000000)))) (orderedInterval (-14796683960 / 1000000000000) (-14796675340 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (9887089221361 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-25520933505 / 1000000000000) (-25520933158 / 1000000000000), orderedInterval (98447088950 / 1000000000000) (98447089297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (26558112382717 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16425336626 / 1000000000000) (-16425336625 / 1000000000000), orderedInterval (-59662789059 / 1000000000000) (-59662789058 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (72110441407689 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29763753929 / 1000000000000) (-29763705968 / 1000000000000), orderedInterval (22982157011 / 1000000000000) (22982204972 / 1000000000000)))) (orderedInterval (1793057466 / 1000000000000) (1793060915 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (53116224765457 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10723528353 / 1000000000000) (-10723528304 / 1000000000000), orderedInterval (42474054572 / 1000000000000) (42474054620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (91015556472661 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28224706708 / 1000000000000) (-28224706707 / 1000000000000), orderedInterval (-17933640561 / 1000000000000) (-17933640560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (67041646956799 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36010533226 / 1000000000000) (-36010509937 / 1000000000000), orderedInterval (14962179820 / 1000000000000) (14962203109 / 1000000000000)))) (orderedInterval (259334 / 1000000000000) (259914 / 1000000000000))) = true
  rfl'

theorem compactCertificate416_chunkChecks0_1 :
    compactCertificate416.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (102859126964977 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11430791629 / 1000000000000) (11430791659 / 1000000000000), orderedInterval (-29328091400 / 1000000000000) (-29328091370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (59385744641833 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39143197699 / 1000000000000) (39143197701 / 1000000000000), orderedInterval (13475802719 / 1000000000000) (13475802721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (105381045987197 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9712265608 / 1000000000000) (-9712265596 / 1000000000000), orderedInterval (29541280127 / 1000000000000) (29541280138 / 1000000000000)))) (orderedInterval (-511580660 / 1000000000000) (-511580539 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (98460642830993 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12881350630 / 1000000000000) (12881350631 / 1000000000000), orderedInterval (29461343704 / 1000000000000) (29461343705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (70266160655969 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4771254854 / 1000000000000) (4771254855 / 1000000000000), orderedInterval (37768302934 / 1000000000000) (37768302935 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (79674337148151 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24722583479 / 1000000000000) (24722592769 / 1000000000000), orderedInterval (-25855768411 / 1000000000000) (-25855759121 / 1000000000000)))) (orderedInterval (93524826 / 1000000000000) (93524908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (66424155846919 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37110062547 / 1000000000000) (37110062550 / 1000000000000), orderedInterval (12457627437 / 1000000000000) (12457627440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (58687756133299 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-716225584 / 1000000000000) (-716225583 / 1000000000000), orderedInterval (-41653560750 / 1000000000000) (-41653560749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (17009999192601 / 32000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34206236078 / 1000000000000) (-34206235992 / 1000000000000), orderedInterval (-5218689133 / 1000000000000) (-5218689048 / 1000000000000)))) (orderedInterval (-406292806 / 1000000000000) (-406292776 / 1000000000000))) = true
  rfl'

theorem compactCertificate416_chunkChecks0_2 :
    compactCertificate416.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (47050552953947 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20605296787 / 1000000000000) (-20605295753 / 1000000000000), orderedInterval (41752073868 / 1000000000000) (41752074902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (39885274809667 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-48107013653 / 1000000000000) (-48107009255 / 1000000000000), orderedInterval (15572760201 / 1000000000000) (15572764599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (24958353043201 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-19203945497 / 1000000000000) (-19203945130 / 1000000000000), orderedInterval (60990947309 / 1000000000000) (60990947677 / 1000000000000)))) (orderedInterval (5392295977 / 1000000000000) (5392296476 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (13422685274367 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (12786100313 / 1000000000000) (12786100383 / 1000000000000), orderedInterval (-86245964497 / 1000000000000) (-86245964427 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (36445201604101 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36760504438 / 1000000000000) (36760540382 / 1000000000000), orderedInterval (-38074421391 / 1000000000000) (-38074385447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (49762806994277 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31974344658 / 1000000000000) (-31974344657 / 1000000000000), orderedInterval (-31956951467 / 1000000000000) (-31956951466 / 1000000000000)))) (orderedInterval (1380399480 / 1000000000000) (1380400332 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (21041646956799 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (23716819808 / 1000000000000) (23716819809 / 1000000000000), orderedInterval (65319121599 / 1000000000000) (65319121600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (85533126682079 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33218527440 / 1000000000000) (33218527454 / 1000000000000), orderedInterval (9317878803 / 1000000000000) (9317878818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (57132164670961 / 160000000000) 0 (IntervalRat.scale (575 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-11688532881 / 1000000000000) (-11688532816 / 1000000000000), orderedInterval (40590356761 / 1000000000000) (40590356827 / 1000000000000)))) (orderedInterval (-367995617 / 1000000000000) (-367995524 / 1000000000000))) = true
  rfl'

theorem compactCertificate416_chunkChecks0 :
    compactCertificate416.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate416.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate416_chunkChecks0_0
    compactCertificate416_chunkChecks0_1 compactCertificate416_chunkChecks0_2

theorem compactCertificate416_chunkChecks1_0 :
    compactCertificate416.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (575 / 2) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31783923008 / 1000000000000) (-31783901864 / 1000000000000), orderedInterval (34755594183 / 1000000000000) (34755615327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (33883391801723 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48155815515 / 1000000000000) (-48155792028 / 1000000000000), orderedInterval (26327838246 / 1000000000000) (26327861733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (10957192730459 / 32000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29821008093 / 1000000000000) (-29821008092 / 1000000000000), orderedInterval (-31100115929 / 1000000000000) (-31100115928 / 1000000000000)))) (orderedInterval (11783043705 / 1000000000000) (11783052270 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (9887089221361 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-25520933505 / 1000000000000) (-25520933158 / 1000000000000), orderedInterval (98447088950 / 1000000000000) (98447089297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (26558112382717 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16425336626 / 1000000000000) (-16425336625 / 1000000000000), orderedInterval (-59662789059 / 1000000000000) (-59662789058 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (72110441407689 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29763753929 / 1000000000000) (-29763705968 / 1000000000000), orderedInterval (22982157011 / 1000000000000) (22982204972 / 1000000000000)))) (orderedInterval (-4048435022 / 1000000000000) (-4048429636 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (53116224765457 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10723528353 / 1000000000000) (-10723528304 / 1000000000000), orderedInterval (42474054572 / 1000000000000) (42474054620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (91015556472661 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28224706708 / 1000000000000) (-28224706707 / 1000000000000), orderedInterval (-17933640561 / 1000000000000) (-17933640560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (67041646956799 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36010533226 / 1000000000000) (-36010509937 / 1000000000000), orderedInterval (14962179820 / 1000000000000) (14962203109 / 1000000000000)))) (orderedInterval (1621467529 / 1000000000000) (1621468378 / 1000000000000))) = true
  rfl'

theorem compactCertificate416_chunkChecks1_1 :
    compactCertificate416.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (102859126964977 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11430791629 / 1000000000000) (11430791659 / 1000000000000), orderedInterval (-29328091400 / 1000000000000) (-29328091370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (59385744641833 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39143197699 / 1000000000000) (39143197701 / 1000000000000), orderedInterval (13475802719 / 1000000000000) (13475802721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (105381045987197 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9712265608 / 1000000000000) (-9712265596 / 1000000000000), orderedInterval (29541280127 / 1000000000000) (29541280138 / 1000000000000)))) (orderedInterval (22562219104 / 1000000000000) (22562219356 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (98460642830993 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12881350630 / 1000000000000) (12881350631 / 1000000000000), orderedInterval (29461343704 / 1000000000000) (29461343705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (70266160655969 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4771254854 / 1000000000000) (4771254855 / 1000000000000), orderedInterval (37768302934 / 1000000000000) (37768302935 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (79674337148151 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24722583479 / 1000000000000) (24722592769 / 1000000000000), orderedInterval (-25855768411 / 1000000000000) (-25855759121 / 1000000000000)))) (orderedInterval (4543717892 / 1000000000000) (4543718030 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (66424155846919 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37110062547 / 1000000000000) (37110062550 / 1000000000000), orderedInterval (12457627437 / 1000000000000) (12457627440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (58687756133299 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-716225584 / 1000000000000) (-716225583 / 1000000000000), orderedInterval (-41653560750 / 1000000000000) (-41653560749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (17009999192601 / 32000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34206236078 / 1000000000000) (-34206235992 / 1000000000000), orderedInterval (-5218689133 / 1000000000000) (-5218689048 / 1000000000000)))) (orderedInterval (3001846810 / 1000000000000) (3001846854 / 1000000000000))) = true
  rfl'

theorem compactCertificate416_chunkChecks1_2 :
    compactCertificate416.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (47050552953947 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20605296787 / 1000000000000) (-20605295753 / 1000000000000), orderedInterval (41752073868 / 1000000000000) (41752074902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (39885274809667 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-48107013653 / 1000000000000) (-48107009255 / 1000000000000), orderedInterval (15572760201 / 1000000000000) (15572764599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (24958353043201 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-19203945497 / 1000000000000) (-19203945130 / 1000000000000), orderedInterval (60990947309 / 1000000000000) (60990947677 / 1000000000000)))) (orderedInterval (-6515236646 / 1000000000000) (-6515236188 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (13422685274367 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (12786100313 / 1000000000000) (12786100383 / 1000000000000), orderedInterval (-86245964497 / 1000000000000) (-86245964427 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (36445201604101 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36760504438 / 1000000000000) (36760540382 / 1000000000000), orderedInterval (-38074421391 / 1000000000000) (-38074385447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (49762806994277 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31974344658 / 1000000000000) (-31974344657 / 1000000000000), orderedInterval (-31956951467 / 1000000000000) (-31956951466 / 1000000000000)))) (orderedInterval (3798553026 / 1000000000000) (3798553704 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (21041646956799 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (23716819808 / 1000000000000) (23716819809 / 1000000000000), orderedInterval (65319121599 / 1000000000000) (65319121600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (85533126682079 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33218527440 / 1000000000000) (33218527454 / 1000000000000), orderedInterval (9317878803 / 1000000000000) (9317878818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (57132164670961 / 160000000000) 1 (IntervalRat.scale (575 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-11688532881 / 1000000000000) (-11688532816 / 1000000000000), orderedInterval (40590356761 / 1000000000000) (40590356827 / 1000000000000)))) (orderedInterval (-10689118282 / 1000000000000) (-10689118153 / 1000000000000))) = true
  rfl'

theorem compactCertificate416_chunkChecks1 :
    compactCertificate416.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate416.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate416_chunkChecks1_0
    compactCertificate416_chunkChecks1_1 compactCertificate416_chunkChecks1_2

theorem compactCertificate416_chunkChecks2_0 :
    compactCertificate416.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (575 / 2) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31783923008 / 1000000000000) (-31783901864 / 1000000000000), orderedInterval (34755594183 / 1000000000000) (34755615327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (33883391801723 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48155815515 / 1000000000000) (-48155792028 / 1000000000000), orderedInterval (26327838246 / 1000000000000) (26327861733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (10957192730459 / 32000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29821008093 / 1000000000000) (-29821008092 / 1000000000000), orderedInterval (-31100115929 / 1000000000000) (-31100115928 / 1000000000000)))) (orderedInterval (15282744251 / 1000000000000) (15282752807 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (9887089221361 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-25520933505 / 1000000000000) (-25520933158 / 1000000000000), orderedInterval (98447088950 / 1000000000000) (98447089297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (26558112382717 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16425336626 / 1000000000000) (-16425336625 / 1000000000000), orderedInterval (-59662789059 / 1000000000000) (-59662789058 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (72110441407689 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29763753929 / 1000000000000) (-29763705968 / 1000000000000), orderedInterval (22982157011 / 1000000000000) (22982204972 / 1000000000000)))) (orderedInterval (-4998460760 / 1000000000000) (-4998452308 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (53116224765457 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10723528353 / 1000000000000) (-10723528304 / 1000000000000), orderedInterval (42474054572 / 1000000000000) (42474054620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (91015556472661 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28224706708 / 1000000000000) (-28224706707 / 1000000000000), orderedInterval (-17933640561 / 1000000000000) (-17933640560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (67041646956799 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36010533226 / 1000000000000) (-36010509937 / 1000000000000), orderedInterval (14962179820 / 1000000000000) (14962203109 / 1000000000000)))) (orderedInterval (-1565161549 / 1000000000000) (-1565160300 / 1000000000000))) = true
  rfl'

theorem compactCertificate416_chunkChecks2_1 :
    compactCertificate416.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (102859126964977 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11430791629 / 1000000000000) (11430791659 / 1000000000000), orderedInterval (-29328091400 / 1000000000000) (-29328091370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (59385744641833 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39143197699 / 1000000000000) (39143197701 / 1000000000000), orderedInterval (13475802719 / 1000000000000) (13475802721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (105381045987197 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9712265608 / 1000000000000) (-9712265596 / 1000000000000), orderedInterval (29541280127 / 1000000000000) (29541280138 / 1000000000000)))) (orderedInterval (12489383150 / 1000000000000) (12489383693 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (98460642830993 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12881350630 / 1000000000000) (12881350631 / 1000000000000), orderedInterval (29461343704 / 1000000000000) (29461343705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (70266160655969 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4771254854 / 1000000000000) (4771254855 / 1000000000000), orderedInterval (37768302934 / 1000000000000) (37768302935 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (79674337148151 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24722583479 / 1000000000000) (24722592769 / 1000000000000), orderedInterval (-25855768411 / 1000000000000) (-25855759121 / 1000000000000)))) (orderedInterval (372189794 / 1000000000000) (372190028 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (66424155846919 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37110062547 / 1000000000000) (37110062550 / 1000000000000), orderedInterval (12457627437 / 1000000000000) (12457627440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (58687756133299 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-716225584 / 1000000000000) (-716225583 / 1000000000000), orderedInterval (-41653560750 / 1000000000000) (-41653560749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (17009999192601 / 32000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34206236078 / 1000000000000) (-34206235992 / 1000000000000), orderedInterval (-5218689133 / 1000000000000) (-5218689048 / 1000000000000)))) (orderedInterval (2023240131 / 1000000000000) (2023240198 / 1000000000000))) = true
  rfl'

theorem compactCertificate416_chunkChecks2_2 :
    compactCertificate416.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (47050552953947 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20605296787 / 1000000000000) (-20605295753 / 1000000000000), orderedInterval (41752073868 / 1000000000000) (41752074902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (39885274809667 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-48107013653 / 1000000000000) (-48107009255 / 1000000000000), orderedInterval (15572760201 / 1000000000000) (15572764599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (24958353043201 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-19203945497 / 1000000000000) (-19203945130 / 1000000000000), orderedInterval (60990947309 / 1000000000000) (60990947677 / 1000000000000)))) (orderedInterval (-5287203776 / 1000000000000) (-5287203347 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (13422685274367 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (12786100313 / 1000000000000) (12786100383 / 1000000000000), orderedInterval (-86245964497 / 1000000000000) (-86245964427 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (36445201604101 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36760504438 / 1000000000000) (36760540382 / 1000000000000), orderedInterval (-38074421391 / 1000000000000) (-38074385447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (49762806994277 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31974344658 / 1000000000000) (-31974344657 / 1000000000000), orderedInterval (-31956951467 / 1000000000000) (-31956951466 / 1000000000000)))) (orderedInterval (-2337377922 / 1000000000000) (-2337377376 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (21041646956799 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (23716819808 / 1000000000000) (23716819809 / 1000000000000), orderedInterval (65319121599 / 1000000000000) (65319121600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (85533126682079 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33218527440 / 1000000000000) (33218527454 / 1000000000000), orderedInterval (9317878803 / 1000000000000) (9317878818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (57132164670961 / 160000000000) 2 (IntervalRat.scale (575 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-11688532881 / 1000000000000) (-11688532816 / 1000000000000), orderedInterval (40590356761 / 1000000000000) (40590356827 / 1000000000000)))) (orderedInterval (5973325908 / 1000000000000) (5973326096 / 1000000000000))) = true
  rfl'

theorem compactCertificate416_chunkChecks2 :
    compactCertificate416.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate416.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate416_chunkChecks2_0
    compactCertificate416_chunkChecks2_1 compactCertificate416_chunkChecks2_2

theorem compactCertificate416_chunkChecks3_0 :
    compactCertificate416.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (575 / 2) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31783923008 / 1000000000000) (-31783901864 / 1000000000000), orderedInterval (34755594183 / 1000000000000) (34755615327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (33883391801723 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48155815515 / 1000000000000) (-48155792028 / 1000000000000), orderedInterval (26327838246 / 1000000000000) (26327861733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (10957192730459 / 32000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29821008093 / 1000000000000) (-29821008092 / 1000000000000), orderedInterval (-31100115929 / 1000000000000) (-31100115928 / 1000000000000)))) (orderedInterval (-10843817472 / 1000000000000) (-10843808943 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (9887089221361 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-25520933505 / 1000000000000) (-25520933158 / 1000000000000), orderedInterval (98447088950 / 1000000000000) (98447089297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (26558112382717 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16425336626 / 1000000000000) (-16425336625 / 1000000000000), orderedInterval (-59662789059 / 1000000000000) (-59662789058 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (72110441407689 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29763753929 / 1000000000000) (-29763705968 / 1000000000000), orderedInterval (22982157011 / 1000000000000) (22982204972 / 1000000000000)))) (orderedInterval (6741048824 / 1000000000000) (6741062069 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (53116224765457 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10723528353 / 1000000000000) (-10723528304 / 1000000000000), orderedInterval (42474054572 / 1000000000000) (42474054620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (91015556472661 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28224706708 / 1000000000000) (-28224706707 / 1000000000000), orderedInterval (-17933640561 / 1000000000000) (-17933640560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (67041646956799 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36010533226 / 1000000000000) (-36010509937 / 1000000000000), orderedInterval (14962179820 / 1000000000000) (14962203109 / 1000000000000)))) (orderedInterval (-5398589712 / 1000000000000) (-5398587874 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate416_chunkChecks3_1 :
    compactCertificate416.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (102859126964977 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11430791629 / 1000000000000) (11430791659 / 1000000000000), orderedInterval (-29328091400 / 1000000000000) (-29328091370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (59385744641833 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39143197699 / 1000000000000) (39143197701 / 1000000000000), orderedInterval (13475802719 / 1000000000000) (13475802721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (105381045987197 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9712265608 / 1000000000000) (-9712265596 / 1000000000000), orderedInterval (29541280127 / 1000000000000) (29541280138 / 1000000000000)))) (orderedInterval (-110945332191 / 1000000000000) (-110945331003 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (98460642830993 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12881350630 / 1000000000000) (12881350631 / 1000000000000), orderedInterval (29461343704 / 1000000000000) (29461343705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (70266160655969 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4771254854 / 1000000000000) (4771254855 / 1000000000000), orderedInterval (37768302934 / 1000000000000) (37768302935 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (79674337148151 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24722583479 / 1000000000000) (24722592769 / 1000000000000), orderedInterval (-25855768411 / 1000000000000) (-25855759121 / 1000000000000)))) (orderedInterval (-8194916322 / 1000000000000) (-8194915921 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (66424155846919 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37110062547 / 1000000000000) (37110062550 / 1000000000000), orderedInterval (12457627437 / 1000000000000) (12457627440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (58687756133299 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-716225584 / 1000000000000) (-716225583 / 1000000000000), orderedInterval (-41653560750 / 1000000000000) (-41653560749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (17009999192601 / 32000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34206236078 / 1000000000000) (-34206235992 / 1000000000000), orderedInterval (-5218689133 / 1000000000000) (-5218689048 / 1000000000000)))) (orderedInterval (-4545776924 / 1000000000000) (-4545776818 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate416_chunkChecks3_2 :
    compactCertificate416.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (47050552953947 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20605296787 / 1000000000000) (-20605295753 / 1000000000000), orderedInterval (41752073868 / 1000000000000) (41752074902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (39885274809667 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-48107013653 / 1000000000000) (-48107009255 / 1000000000000), orderedInterval (15572760201 / 1000000000000) (15572764599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (24958353043201 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-19203945497 / 1000000000000) (-19203945130 / 1000000000000), orderedInterval (60990947309 / 1000000000000) (60990947677 / 1000000000000)))) (orderedInterval (7419495380 / 1000000000000) (7419495785 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (13422685274367 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (12786100313 / 1000000000000) (12786100383 / 1000000000000), orderedInterval (-86245964497 / 1000000000000) (-86245964427 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (36445201604101 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36760504438 / 1000000000000) (36760540382 / 1000000000000), orderedInterval (-38074421391 / 1000000000000) (-38074385447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (49762806994277 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31974344658 / 1000000000000) (-31974344657 / 1000000000000), orderedInterval (-31956951467 / 1000000000000) (-31956951466 / 1000000000000)))) (orderedInterval (-3561652437 / 1000000000000) (-3561651997 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (21041646956799 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (23716819808 / 1000000000000) (23716819809 / 1000000000000), orderedInterval (65319121599 / 1000000000000) (65319121600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (85533126682079 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33218527440 / 1000000000000) (33218527454 / 1000000000000), orderedInterval (9317878803 / 1000000000000) (9317878818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (57132164670961 / 160000000000) 3 (IntervalRat.scale (575 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-11688532881 / 1000000000000) (-11688532816 / 1000000000000), orderedInterval (40590356761 / 1000000000000) (40590356827 / 1000000000000)))) (orderedInterval (19408614295 / 1000000000000) (19408614581 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate416_chunkChecks3 :
    compactCertificate416.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate416.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate416_chunkChecks3_0
    compactCertificate416_chunkChecks3_1 compactCertificate416_chunkChecks3_2

theorem compactCertificate416_chunkChecks4_0 :
    compactCertificate416.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (575 / 2) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31783923008 / 1000000000000) (-31783901864 / 1000000000000), orderedInterval (34755594183 / 1000000000000) (34755615327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (33883391801723 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48155815515 / 1000000000000) (-48155792028 / 1000000000000), orderedInterval (26327838246 / 1000000000000) (26327861733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (10957192730459 / 32000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29821008093 / 1000000000000) (-29821008092 / 1000000000000), orderedInterval (-31100115929 / 1000000000000) (-31100115928 / 1000000000000)))) (orderedInterval (-16175517006 / 1000000000000) (-16175508466 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (9887089221361 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-25520933505 / 1000000000000) (-25520933158 / 1000000000000), orderedInterval (98447088950 / 1000000000000) (98447089297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (26558112382717 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-16425336626 / 1000000000000) (-16425336625 / 1000000000000), orderedInterval (-59662789059 / 1000000000000) (-59662789058 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (72110441407689 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29763753929 / 1000000000000) (-29763705968 / 1000000000000), orderedInterval (22982157011 / 1000000000000) (22982204972 / 1000000000000)))) (orderedInterval (12664757665 / 1000000000000) (12664778472 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (53116224765457 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10723528353 / 1000000000000) (-10723528304 / 1000000000000), orderedInterval (42474054572 / 1000000000000) (42474054620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (91015556472661 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28224706708 / 1000000000000) (-28224706707 / 1000000000000), orderedInterval (-17933640561 / 1000000000000) (-17933640560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (67041646956799 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36010533226 / 1000000000000) (-36010509937 / 1000000000000), orderedInterval (14962179820 / 1000000000000) (14962203109 / 1000000000000)))) (orderedInterval (9453242555 / 1000000000000) (9453245275 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate416_chunkChecks4_1 :
    compactCertificate416.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (102859126964977 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11430791629 / 1000000000000) (11430791659 / 1000000000000), orderedInterval (-29328091400 / 1000000000000) (-29328091370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (59385744641833 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39143197699 / 1000000000000) (39143197701 / 1000000000000), orderedInterval (13475802719 / 1000000000000) (13475802721 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (105381045987197 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9712265608 / 1000000000000) (-9712265596 / 1000000000000), orderedInterval (29541280127 / 1000000000000) (29541280138 / 1000000000000)))) (orderedInterval (-79977873517 / 1000000000000) (-79977870872 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (98460642830993 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12881350630 / 1000000000000) (12881350631 / 1000000000000), orderedInterval (29461343704 / 1000000000000) (29461343705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (70266160655969 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (4771254854 / 1000000000000) (4771254855 / 1000000000000), orderedInterval (37768302934 / 1000000000000) (37768302935 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (79674337148151 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24722583479 / 1000000000000) (24722592769 / 1000000000000), orderedInterval (-25855768411 / 1000000000000) (-25855759121 / 1000000000000)))) (orderedInterval (-3493801908 / 1000000000000) (-3493801211 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (66424155846919 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37110062547 / 1000000000000) (37110062550 / 1000000000000), orderedInterval (12457627437 / 1000000000000) (12457627440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (58687756133299 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-716225584 / 1000000000000) (-716225583 / 1000000000000), orderedInterval (-41653560750 / 1000000000000) (-41653560749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (17009999192601 / 32000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34206236078 / 1000000000000) (-34206235992 / 1000000000000), orderedInterval (-5218689133 / 1000000000000) (-5218689048 / 1000000000000)))) (orderedInterval (-8231331900 / 1000000000000) (-8231331728 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate416_chunkChecks4_2 :
    compactCertificate416.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (47050552953947 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20605296787 / 1000000000000) (-20605295753 / 1000000000000), orderedInterval (41752073868 / 1000000000000) (41752074902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (39885274809667 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-48107013653 / 1000000000000) (-48107009255 / 1000000000000), orderedInterval (15572760201 / 1000000000000) (15572764599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (24958353043201 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-19203945497 / 1000000000000) (-19203945130 / 1000000000000), orderedInterval (60990947309 / 1000000000000) (60990947677 / 1000000000000)))) (orderedInterval (5039230929 / 1000000000000) (5039231315 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (13422685274367 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (12786100313 / 1000000000000) (12786100383 / 1000000000000), orderedInterval (-86245964497 / 1000000000000) (-86245964427 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (36445201604101 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36760504438 / 1000000000000) (36760540382 / 1000000000000), orderedInterval (-38074421391 / 1000000000000) (-38074385447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (49762806994277 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31974344658 / 1000000000000) (-31974344657 / 1000000000000), orderedInterval (-31956951467 / 1000000000000) (-31956951466 / 1000000000000)))) (orderedInterval (3050553275 / 1000000000000) (3050553633 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (21041646956799 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (23716819808 / 1000000000000) (23716819809 / 1000000000000), orderedInterval (65319121599 / 1000000000000) (65319121600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (85533126682079 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33218527440 / 1000000000000) (33218527454 / 1000000000000), orderedInterval (9317878803 / 1000000000000) (9317878818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (57132164670961 / 160000000000) 4 (IntervalRat.scale (575 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-11688532881 / 1000000000000) (-11688532816 / 1000000000000), orderedInterval (40590356761 / 1000000000000) (40590356827 / 1000000000000)))) (orderedInterval (-27233830058 / 1000000000000) (-27233829606 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate416_chunkChecks4 :
    compactCertificate416.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate416.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate416_chunkChecks4_0
    compactCertificate416_chunkChecks4_1 compactCertificate416_chunkChecks4_2

theorem compactCertificate416_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate416.chunkCheck r b = true :=
  compactCertificate416.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate416_chunkChecks0
    · exact compactCertificate416_chunkChecks1
    · exact compactCertificate416_chunkChecks2
    · exact compactCertificate416_chunkChecks3
    · exact compactCertificate416_chunkChecks4)

theorem compactCertificate416_coefficient0 :
    compactCertificate416.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate416_coefficient1 :
    compactCertificate416.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate416_coefficient2 :
    compactCertificate416.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate416_coefficient3 :
    compactCertificate416.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate416_coefficient4 :
    compactCertificate416.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate416_coefficients : ∀ r : Fin 5,
    compactCertificate416.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate416_coefficient0
  · exact compactCertificate416_coefficient1
  · exact compactCertificate416_coefficient2
  · exact compactCertificate416_coefficient3
  · exact compactCertificate416_coefficient4

theorem compactCertificate416_lower : (1 : ℚ) ≤ compactCertificate416.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate416, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate416_proves {t : ℝ} (ht : t ∈ compactCertificate416.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate416.proves compactCertificate416_states compactCertificate416_chunks
    compactCertificate416_coefficients compactCertificate416_lower ht

end Erdos232
