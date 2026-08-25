/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate341 : CompactCertificate where
  left := 213
  right := 214
  center := 427 / 2
  grid := fun i =>
    match i.val with
    | 0 => 68
    | 1 => 50
    | 2 => 81
    | 3 => 15
    | 4 => 39
    | 5 => 107
    | 6 => 79
    | 7 => 135
    | 8 => 99
    | 9 => 152
    | 10 => 88
    | 11 => 156
    | 12 => 146
    | 13 => 104
    | 14 => 118
    | 15 => 98
    | 16 => 87
    | 17 => 126
    | 18 => 70
    | 19 => 59
    | 20 => 37
    | 21 => 20
    | 22 => 54
    | 23 => 74
    | 24 => 31
    | 25 => 126
    | _ => 84
  point := fun i =>
    match i.val with
    | 0 => 427 / 2
    | 1 => 629052534753727 / 4000000000000
    | 2 => 203422665039391 / 800000000000
    | 3 => 183555960761789 / 4000000000000
    | 4 => 493057129887833 / 4000000000000
    | 5 => 1338746020916661 / 4000000000000
    | 6 => 986114259776093 / 4000000000000
    | 7 => 1689723591905489 / 4000000000000
    | 8 => 1244642750024051 / 4000000000000
    | 9 => 1909602052784573 / 4000000000000
    | 10 => 1102509259220117 / 4000000000000
    | 11 => 1956422027675353 / 4000000000000
    | 12 => 1827943238644957 / 4000000000000
    | 13 => 1304506547830381 / 4000000000000
    | 14 => 1479171389663499 / 4000000000000
    | 15 => 1233178893331931 / 4000000000000
    | 16 => 1089550950822551 / 4000000000000
    | 17 => 315794332836549 / 800000000000
    | 18 => 873503743971103 / 4000000000000
    | 19 => 740478797553383 / 4000000000000
    | 20 => 463357249975949 / 4000000000000
    | 21 => 249195070093683 / 4000000000000
    | 22 => 676613090650049 / 4000000000000
    | 23 => 923857329850273 / 4000000000000
    | 24 => 390642750024051 / 4000000000000
    | 25 => 1587941091010771 / 4000000000000
    | _ => 1060671057152189 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (33329212055 / 1000000000000) (33329212056 / 1000000000000), orderedInterval (43176903470 / 1000000000000) (43176903471 / 1000000000000))
    | 1 => (orderedInterval (52414800947 / 1000000000000) (52414800948 / 1000000000000), orderedInterval (35899955067 / 1000000000000) (35899955068 / 1000000000000))
    | 2 => (orderedInterval (-28013976500 / 1000000000000) (-28013976499 / 1000000000000), orderedInterval (-41403961252 / 1000000000000) (-41403961251 / 1000000000000))
    | 3 => (orderedInterval (51466219494 / 1000000000000) (51466223365 / 1000000000000), orderedInterval (-106507748188 / 1000000000000) (-106507744318 / 1000000000000))
    | 4 => (orderedInterval (-71795041819 / 1000000000000) (-71795041799 / 1000000000000), orderedInterval (-2887325535 / 1000000000000) (-2887325515 / 1000000000000))
    | 5 => (orderedInterval (27385983020 / 1000000000000) (27385992135 / 1000000000000), orderedInterval (-33984188812 / 1000000000000) (-33984179697 / 1000000000000))
    | 6 => (orderedInterval (38917930269 / 1000000000000) (38918012122 / 1000000000000), orderedInterval (-32755066857 / 1000000000000) (-32754985004 / 1000000000000))
    | 7 => (orderedInterval (30385230744 / 1000000000000) (30385278435 / 1000000000000), orderedInterval (-24197421466 / 1000000000000) (-24197373775 / 1000000000000))
    | 8 => (orderedInterval (-36205158894 / 1000000000000) (-36205158893 / 1000000000000), orderedInterval (-27055242448 / 1000000000000) (-27055242447 / 1000000000000))
    | 9 => (orderedInterval (22492099783 / 1000000000000) (22492099784 / 1000000000000), orderedInterval (28744804025 / 1000000000000) (28744804026 / 1000000000000))
    | 10 => (orderedInterval (-2300880918 / 1000000000000) (-2300880914 / 1000000000000), orderedInterval (48008568811 / 1000000000000) (48008568815 / 1000000000000))
    | 11 => (orderedInterval (-7089880902 / 1000000000000) (-7089880895 / 1000000000000), orderedInterval (35381451777 / 1000000000000) (35381451783 / 1000000000000))
    | 12 => (orderedInterval (-29273865338 / 1000000000000) (-29273823571 / 1000000000000), orderedInterval (23186405693 / 1000000000000) (23186447460 / 1000000000000))
    | 13 => (orderedInterval (8171262965 / 1000000000000) (8171262966 / 1000000000000), orderedInterval (43407464153 / 1000000000000) (43407464154 / 1000000000000))
    | 14 => (orderedInterval (-5379785278 / 1000000000000) (-5379785272 / 1000000000000), orderedInterval (41148704034 / 1000000000000) (41148704040 / 1000000000000))
    | 15 => (orderedInterval (42413242148 / 1000000000000) (42413242149 / 1000000000000), orderedInterval (16243363069 / 1000000000000) (16243363070 / 1000000000000))
    | 16 => (orderedInterval (7027675877 / 1000000000000) (7027675894 / 1000000000000), orderedInterval (-47843828834 / 1000000000000) (-47843828817 / 1000000000000))
    | 17 => (orderedInterval (-12353174561 / 1000000000000) (-12353174482 / 1000000000000), orderedInterval (38227496026 / 1000000000000) (38227496105 / 1000000000000))
    | 18 => (orderedInterval (-36832299175 / 1000000000000) (-36832267358 / 1000000000000), orderedInterval (39563807546 / 1000000000000) (39563839362 / 1000000000000))
    | 19 => (orderedInterval (-30674501585 / 1000000000000) (-30674501584 / 1000000000000), orderedInterval (-49897581325 / 1000000000000) (-49897581324 / 1000000000000))
    | 20 => (orderedInterval (-27820850884 / 1000000000000) (-27820850883 / 1000000000000), orderedInterval (-68594919556 / 1000000000000) (-68594919555 / 1000000000000))
    | 21 => (orderedInterval (25039222089 / 1000000000000) (25039222090 / 1000000000000), orderedInterval (97738543951 / 1000000000000) (97738543952 / 1000000000000))
    | 22 => (orderedInterval (17655877123 / 1000000000000) (17655877124 / 1000000000000), orderedInterval (58700269254 / 1000000000000) (58700269255 / 1000000000000))
    | 23 => (orderedInterval (-34959112184 / 1000000000000) (-34959087698 / 1000000000000), orderedInterval (39244754708 / 1000000000000) (39244779195 / 1000000000000))
    | 24 => (orderedInterval (-70251155645 / 1000000000000) (-70251155644 / 1000000000000), orderedInterval (-39432568593 / 1000000000000) (-39432568592 / 1000000000000))
    | 25 => (orderedInterval (37494060449 / 1000000000000) (37494075630 / 1000000000000), orderedInterval (-14112422897 / 1000000000000) (-14112407715 / 1000000000000))
    | _ => (orderedInterval (43276090419 / 1000000000000) (43276117813 / 1000000000000), orderedInterval (-23059761555 / 1000000000000) (-23059734161 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (12055045078 / 1000000000000) (12055045094 / 1000000000000)
      | 1 => orderedInterval (-5126594727 / 1000000000000) (-5126594010 / 1000000000000)
      | 2 => orderedInterval (-1812210822 / 1000000000000) (-1812209339 / 1000000000000)
      | 3 => orderedInterval (-5174919290 / 1000000000000) (-5174919204 / 1000000000000)
      | 4 => orderedInterval (1328405698 / 1000000000000) (1328406479 / 1000000000000)
      | 5 => orderedInterval (-228686489 / 1000000000000) (-228686465 / 1000000000000)
      | 6 => orderedInterval (6719661245 / 1000000000000) (6719666387 / 1000000000000)
      | 7 => orderedInterval (1816316351 / 1000000000000) (1816318254 / 1000000000000)
      | _ => orderedInterval (-11595329109 / 1000000000000) (-11595322674 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (14466528059 / 1000000000000) (14466528076 / 1000000000000)
      | 1 => orderedInterval (3974746853 / 1000000000000) (3974747908 / 1000000000000)
      | 2 => orderedInterval (523744637 / 1000000000000) (523747569 / 1000000000000)
      | 3 => orderedInterval (4693626961 / 1000000000000) (4693627140 / 1000000000000)
      | 4 => orderedInterval (5013445608 / 1000000000000) (5013447264 / 1000000000000)
      | 5 => orderedInterval (5573650635 / 1000000000000) (5573650670 / 1000000000000)
      | 6 => orderedInterval (-5233282339 / 1000000000000) (-5233277085 / 1000000000000)
      | 7 => orderedInterval (-4835434793 / 1000000000000) (-4835432739 / 1000000000000)
      | _ => orderedInterval (7400989180 / 1000000000000) (7400997945 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-11211460156 / 1000000000000) (-11211460135 / 1000000000000)
      | 1 => orderedInterval (5665231696 / 1000000000000) (5665233337 / 1000000000000)
      | 2 => orderedInterval (5525153842 / 1000000000000) (5525159653 / 1000000000000)
      | 3 => orderedInterval (25534497743 / 1000000000000) (25534498126 / 1000000000000)
      | 4 => orderedInterval (-4329377453 / 1000000000000) (-4329373921 / 1000000000000)
      | 5 => orderedInterval (688494902 / 1000000000000) (688494955 / 1000000000000)
      | 6 => orderedInterval (-7175411780 / 1000000000000) (-7175406385 / 1000000000000)
      | 7 => orderedInterval (-2822024112 / 1000000000000) (-2822021883 / 1000000000000)
      | _ => orderedInterval (23131596925 / 1000000000000) (23131609290 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-13090037387 / 1000000000000) (-13090037364 / 1000000000000)
      | 1 => orderedInterval (-9324515284 / 1000000000000) (-9324512718 / 1000000000000)
      | 2 => orderedInterval (-3782804775 / 1000000000000) (-3782793286 / 1000000000000)
      | 3 => orderedInterval (-11140300691 / 1000000000000) (-11140299854 / 1000000000000)
      | 4 => orderedInterval (-9422913954 / 1000000000000) (-9422906427 / 1000000000000)
      | 5 => orderedInterval (-12440019439 / 1000000000000) (-12440019355 / 1000000000000)
      | 6 => orderedInterval (5318501165 / 1000000000000) (5318506680 / 1000000000000)
      | 7 => orderedInterval (4528042506 / 1000000000000) (4528044916 / 1000000000000)
      | _ => orderedInterval (-15759972454 / 1000000000000) (-15759954415 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (10169040484 / 1000000000000) (10169040511 / 1000000000000)
      | 1 => orderedInterval (-11961969676 / 1000000000000) (-11961965646 / 1000000000000)
      | 2 => orderedInterval (-18275938232 / 1000000000000) (-18275915456 / 1000000000000)
      | 3 => orderedInterval (-128043185931 / 1000000000000) (-128043184069 / 1000000000000)
      | 4 => orderedInterval (15633141493 / 1000000000000) (15633157592 / 1000000000000)
      | 5 => orderedInterval (-2515698842 / 1000000000000) (-2515698707 / 1000000000000)
      | 6 => orderedInterval (7298760076 / 1000000000000) (7298765741 / 1000000000000)
      | 7 => orderedInterval (3465757034 / 1000000000000) (3465759652 / 1000000000000)
      | _ => orderedInterval (-55675605817 / 1000000000000) (-55675578344 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-2018312065 / 1000000000000) (-2018295478 / 1000000000000)
    | 1 => orderedInterval (31578014801 / 1000000000000) (31578036748 / 1000000000000)
    | 2 => orderedInterval (35006701607 / 1000000000000) (35006733037 / 1000000000000)
    | 3 => orderedInterval (-65114020313 / 1000000000000) (-65113971823 / 1000000000000)
    | _ => orderedInterval (-179905699411 / 1000000000000) (-179905618726 / 1000000000000)

theorem compactCertificate341_stateChecks0 :
    compactCertificate341.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (427 / 2)) (orderedInterval (33329212055 / 1000000000000) (33329212056 / 1000000000000), orderedInterval (43176903470 / 1000000000000) (43176903471 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (629052534753727 / 4000000000000)) (orderedInterval (52414800947 / 1000000000000) (52414800948 / 1000000000000), orderedInterval (35899955067 / 1000000000000) (35899955068 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (203422665039391 / 800000000000)) (orderedInterval (-28013976500 / 1000000000000) (-28013976499 / 1000000000000), orderedInterval (-41403961252 / 1000000000000) (-41403961251 / 1000000000000))) = true
  rfl'

theorem compactCertificate341_stateChecks1 :
    compactCertificate341.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (183555960761789 / 4000000000000)) (orderedInterval (51466219494 / 1000000000000) (51466223365 / 1000000000000), orderedInterval (-106507748188 / 1000000000000) (-106507744318 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (493057129887833 / 4000000000000)) (orderedInterval (-71795041819 / 1000000000000) (-71795041799 / 1000000000000), orderedInterval (-2887325535 / 1000000000000) (-2887325515 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1338746020916661 / 4000000000000)) (orderedInterval (27385983020 / 1000000000000) (27385992135 / 1000000000000), orderedInterval (-33984188812 / 1000000000000) (-33984179697 / 1000000000000))) = true
  rfl'

theorem compactCertificate341_stateChecks2 :
    compactCertificate341.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (986114259776093 / 4000000000000)) (orderedInterval (38917930269 / 1000000000000) (38918012122 / 1000000000000), orderedInterval (-32755066857 / 1000000000000) (-32754985004 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1689723591905489 / 4000000000000)) (orderedInterval (30385230744 / 1000000000000) (30385278435 / 1000000000000), orderedInterval (-24197421466 / 1000000000000) (-24197373775 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1244642750024051 / 4000000000000)) (orderedInterval (-36205158894 / 1000000000000) (-36205158893 / 1000000000000), orderedInterval (-27055242448 / 1000000000000) (-27055242447 / 1000000000000))) = true
  rfl'

theorem compactCertificate341_stateChecks3 :
    compactCertificate341.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1909602052784573 / 4000000000000)) (orderedInterval (22492099783 / 1000000000000) (22492099784 / 1000000000000), orderedInterval (28744804025 / 1000000000000) (28744804026 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1102509259220117 / 4000000000000)) (orderedInterval (-2300880918 / 1000000000000) (-2300880914 / 1000000000000), orderedInterval (48008568811 / 1000000000000) (48008568815 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1956422027675353 / 4000000000000)) (orderedInterval (-7089880902 / 1000000000000) (-7089880895 / 1000000000000), orderedInterval (35381451777 / 1000000000000) (35381451783 / 1000000000000))) = true
  rfl'

theorem compactCertificate341_stateChecks4 :
    compactCertificate341.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1827943238644957 / 4000000000000)) (orderedInterval (-29273865338 / 1000000000000) (-29273823571 / 1000000000000), orderedInterval (23186405693 / 1000000000000) (23186447460 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1304506547830381 / 4000000000000)) (orderedInterval (8171262965 / 1000000000000) (8171262966 / 1000000000000), orderedInterval (43407464153 / 1000000000000) (43407464154 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1479171389663499 / 4000000000000)) (orderedInterval (-5379785278 / 1000000000000) (-5379785272 / 1000000000000), orderedInterval (41148704034 / 1000000000000) (41148704040 / 1000000000000))) = true
  rfl'

theorem compactCertificate341_stateChecks5 :
    compactCertificate341.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1233178893331931 / 4000000000000)) (orderedInterval (42413242148 / 1000000000000) (42413242149 / 1000000000000), orderedInterval (16243363069 / 1000000000000) (16243363070 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1089550950822551 / 4000000000000)) (orderedInterval (7027675877 / 1000000000000) (7027675894 / 1000000000000), orderedInterval (-47843828834 / 1000000000000) (-47843828817 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (315794332836549 / 800000000000)) (orderedInterval (-12353174561 / 1000000000000) (-12353174482 / 1000000000000), orderedInterval (38227496026 / 1000000000000) (38227496105 / 1000000000000))) = true
  rfl'

theorem compactCertificate341_stateChecks6 :
    compactCertificate341.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (873503743971103 / 4000000000000)) (orderedInterval (-36832299175 / 1000000000000) (-36832267358 / 1000000000000), orderedInterval (39563807546 / 1000000000000) (39563839362 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (740478797553383 / 4000000000000)) (orderedInterval (-30674501585 / 1000000000000) (-30674501584 / 1000000000000), orderedInterval (-49897581325 / 1000000000000) (-49897581324 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (463357249975949 / 4000000000000)) (orderedInterval (-27820850884 / 1000000000000) (-27820850883 / 1000000000000), orderedInterval (-68594919556 / 1000000000000) (-68594919555 / 1000000000000))) = true
  rfl'

theorem compactCertificate341_stateChecks7 :
    compactCertificate341.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (249195070093683 / 4000000000000)) (orderedInterval (25039222089 / 1000000000000) (25039222090 / 1000000000000), orderedInterval (97738543951 / 1000000000000) (97738543952 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (676613090650049 / 4000000000000)) (orderedInterval (17655877123 / 1000000000000) (17655877124 / 1000000000000), orderedInterval (58700269254 / 1000000000000) (58700269255 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (923857329850273 / 4000000000000)) (orderedInterval (-34959112184 / 1000000000000) (-34959087698 / 1000000000000), orderedInterval (39244754708 / 1000000000000) (39244779195 / 1000000000000))) = true
  rfl'

theorem compactCertificate341_stateChecks8 :
    compactCertificate341.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (390642750024051 / 4000000000000)) (orderedInterval (-70251155645 / 1000000000000) (-70251155644 / 1000000000000), orderedInterval (-39432568593 / 1000000000000) (-39432568592 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1587941091010771 / 4000000000000)) (orderedInterval (37494060449 / 1000000000000) (37494075630 / 1000000000000), orderedInterval (-14112422897 / 1000000000000) (-14112407715 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1060671057152189 / 4000000000000)) (orderedInterval (43276090419 / 1000000000000) (43276117813 / 1000000000000), orderedInterval (-23059761555 / 1000000000000) (-23059734161 / 1000000000000))) = true
  rfl'

theorem compactCertificate341_states : ∀ j,
    BesselStateValid (compactCertificate341.point j) (compactCertificate341.state j) :=
  compactCertificate341.statesValid_of_checks3 compactCertificate341_stateChecks0
    compactCertificate341_stateChecks1 compactCertificate341_stateChecks2
    compactCertificate341_stateChecks3 compactCertificate341_stateChecks4
    compactCertificate341_stateChecks5 compactCertificate341_stateChecks6
    compactCertificate341_stateChecks7 compactCertificate341_stateChecks8

theorem compactCertificate341_chunkChecks0_0 :
    compactCertificate341.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (427 / 2) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33329212055 / 1000000000000) (33329212056 / 1000000000000), orderedInterval (43176903470 / 1000000000000) (43176903471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (629052534753727 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (52414800947 / 1000000000000) (52414800948 / 1000000000000), orderedInterval (35899955067 / 1000000000000) (35899955068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (203422665039391 / 800000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28013976500 / 1000000000000) (-28013976499 / 1000000000000), orderedInterval (-41403961252 / 1000000000000) (-41403961251 / 1000000000000)))) (orderedInterval (12055045078 / 1000000000000) (12055045094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (183555960761789 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (51466219494 / 1000000000000) (51466223365 / 1000000000000), orderedInterval (-106507748188 / 1000000000000) (-106507744318 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (493057129887833 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71795041819 / 1000000000000) (-71795041799 / 1000000000000), orderedInterval (-2887325535 / 1000000000000) (-2887325515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1338746020916661 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27385983020 / 1000000000000) (27385992135 / 1000000000000), orderedInterval (-33984188812 / 1000000000000) (-33984179697 / 1000000000000)))) (orderedInterval (-5126594727 / 1000000000000) (-5126594010 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (986114259776093 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38917930269 / 1000000000000) (38918012122 / 1000000000000), orderedInterval (-32755066857 / 1000000000000) (-32754985004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1689723591905489 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (30385230744 / 1000000000000) (30385278435 / 1000000000000), orderedInterval (-24197421466 / 1000000000000) (-24197373775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1244642750024051 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36205158894 / 1000000000000) (-36205158893 / 1000000000000), orderedInterval (-27055242448 / 1000000000000) (-27055242447 / 1000000000000)))) (orderedInterval (-1812210822 / 1000000000000) (-1812209339 / 1000000000000))) = true
  rfl'

theorem compactCertificate341_chunkChecks0_1 :
    compactCertificate341.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1909602052784573 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22492099783 / 1000000000000) (22492099784 / 1000000000000), orderedInterval (28744804025 / 1000000000000) (28744804026 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1102509259220117 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2300880918 / 1000000000000) (-2300880914 / 1000000000000), orderedInterval (48008568811 / 1000000000000) (48008568815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1956422027675353 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7089880902 / 1000000000000) (-7089880895 / 1000000000000), orderedInterval (35381451777 / 1000000000000) (35381451783 / 1000000000000)))) (orderedInterval (-5174919290 / 1000000000000) (-5174919204 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1827943238644957 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29273865338 / 1000000000000) (-29273823571 / 1000000000000), orderedInterval (23186405693 / 1000000000000) (23186447460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1304506547830381 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (8171262965 / 1000000000000) (8171262966 / 1000000000000), orderedInterval (43407464153 / 1000000000000) (43407464154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1479171389663499 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-5379785278 / 1000000000000) (-5379785272 / 1000000000000), orderedInterval (41148704034 / 1000000000000) (41148704040 / 1000000000000)))) (orderedInterval (1328405698 / 1000000000000) (1328406479 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1233178893331931 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (42413242148 / 1000000000000) (42413242149 / 1000000000000), orderedInterval (16243363069 / 1000000000000) (16243363070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1089550950822551 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7027675877 / 1000000000000) (7027675894 / 1000000000000), orderedInterval (-47843828834 / 1000000000000) (-47843828817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (315794332836549 / 800000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12353174561 / 1000000000000) (-12353174482 / 1000000000000), orderedInterval (38227496026 / 1000000000000) (38227496105 / 1000000000000)))) (orderedInterval (-228686489 / 1000000000000) (-228686465 / 1000000000000))) = true
  rfl'

theorem compactCertificate341_chunkChecks0_2 :
    compactCertificate341.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (873503743971103 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36832299175 / 1000000000000) (-36832267358 / 1000000000000), orderedInterval (39563807546 / 1000000000000) (39563839362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (740478797553383 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30674501585 / 1000000000000) (-30674501584 / 1000000000000), orderedInterval (-49897581325 / 1000000000000) (-49897581324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (463357249975949 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-27820850884 / 1000000000000) (-27820850883 / 1000000000000), orderedInterval (-68594919556 / 1000000000000) (-68594919555 / 1000000000000)))) (orderedInterval (6719661245 / 1000000000000) (6719666387 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (249195070093683 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25039222089 / 1000000000000) (25039222090 / 1000000000000), orderedInterval (97738543951 / 1000000000000) (97738543952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (676613090650049 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (17655877123 / 1000000000000) (17655877124 / 1000000000000), orderedInterval (58700269254 / 1000000000000) (58700269255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (923857329850273 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34959112184 / 1000000000000) (-34959087698 / 1000000000000), orderedInterval (39244754708 / 1000000000000) (39244779195 / 1000000000000)))) (orderedInterval (1816316351 / 1000000000000) (1816318254 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (390642750024051 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-70251155645 / 1000000000000) (-70251155644 / 1000000000000), orderedInterval (-39432568593 / 1000000000000) (-39432568592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1587941091010771 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (37494060449 / 1000000000000) (37494075630 / 1000000000000), orderedInterval (-14112422897 / 1000000000000) (-14112407715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1060671057152189 / 4000000000000) 0 (IntervalRat.scale (427 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43276090419 / 1000000000000) (43276117813 / 1000000000000), orderedInterval (-23059761555 / 1000000000000) (-23059734161 / 1000000000000)))) (orderedInterval (-11595329109 / 1000000000000) (-11595322674 / 1000000000000))) = true
  rfl'

theorem compactCertificate341_chunkChecks0 :
    compactCertificate341.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate341.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate341_chunkChecks0_0
    compactCertificate341_chunkChecks0_1 compactCertificate341_chunkChecks0_2

theorem compactCertificate341_chunkChecks1_0 :
    compactCertificate341.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (427 / 2) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33329212055 / 1000000000000) (33329212056 / 1000000000000), orderedInterval (43176903470 / 1000000000000) (43176903471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (629052534753727 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (52414800947 / 1000000000000) (52414800948 / 1000000000000), orderedInterval (35899955067 / 1000000000000) (35899955068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (203422665039391 / 800000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28013976500 / 1000000000000) (-28013976499 / 1000000000000), orderedInterval (-41403961252 / 1000000000000) (-41403961251 / 1000000000000)))) (orderedInterval (14466528059 / 1000000000000) (14466528076 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (183555960761789 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (51466219494 / 1000000000000) (51466223365 / 1000000000000), orderedInterval (-106507748188 / 1000000000000) (-106507744318 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (493057129887833 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71795041819 / 1000000000000) (-71795041799 / 1000000000000), orderedInterval (-2887325535 / 1000000000000) (-2887325515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1338746020916661 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27385983020 / 1000000000000) (27385992135 / 1000000000000), orderedInterval (-33984188812 / 1000000000000) (-33984179697 / 1000000000000)))) (orderedInterval (3974746853 / 1000000000000) (3974747908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (986114259776093 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38917930269 / 1000000000000) (38918012122 / 1000000000000), orderedInterval (-32755066857 / 1000000000000) (-32754985004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1689723591905489 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (30385230744 / 1000000000000) (30385278435 / 1000000000000), orderedInterval (-24197421466 / 1000000000000) (-24197373775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1244642750024051 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36205158894 / 1000000000000) (-36205158893 / 1000000000000), orderedInterval (-27055242448 / 1000000000000) (-27055242447 / 1000000000000)))) (orderedInterval (523744637 / 1000000000000) (523747569 / 1000000000000))) = true
  rfl'

theorem compactCertificate341_chunkChecks1_1 :
    compactCertificate341.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1909602052784573 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22492099783 / 1000000000000) (22492099784 / 1000000000000), orderedInterval (28744804025 / 1000000000000) (28744804026 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1102509259220117 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2300880918 / 1000000000000) (-2300880914 / 1000000000000), orderedInterval (48008568811 / 1000000000000) (48008568815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1956422027675353 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7089880902 / 1000000000000) (-7089880895 / 1000000000000), orderedInterval (35381451777 / 1000000000000) (35381451783 / 1000000000000)))) (orderedInterval (4693626961 / 1000000000000) (4693627140 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1827943238644957 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29273865338 / 1000000000000) (-29273823571 / 1000000000000), orderedInterval (23186405693 / 1000000000000) (23186447460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1304506547830381 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (8171262965 / 1000000000000) (8171262966 / 1000000000000), orderedInterval (43407464153 / 1000000000000) (43407464154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1479171389663499 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-5379785278 / 1000000000000) (-5379785272 / 1000000000000), orderedInterval (41148704034 / 1000000000000) (41148704040 / 1000000000000)))) (orderedInterval (5013445608 / 1000000000000) (5013447264 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1233178893331931 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (42413242148 / 1000000000000) (42413242149 / 1000000000000), orderedInterval (16243363069 / 1000000000000) (16243363070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1089550950822551 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7027675877 / 1000000000000) (7027675894 / 1000000000000), orderedInterval (-47843828834 / 1000000000000) (-47843828817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (315794332836549 / 800000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12353174561 / 1000000000000) (-12353174482 / 1000000000000), orderedInterval (38227496026 / 1000000000000) (38227496105 / 1000000000000)))) (orderedInterval (5573650635 / 1000000000000) (5573650670 / 1000000000000))) = true
  rfl'

theorem compactCertificate341_chunkChecks1_2 :
    compactCertificate341.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (873503743971103 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36832299175 / 1000000000000) (-36832267358 / 1000000000000), orderedInterval (39563807546 / 1000000000000) (39563839362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (740478797553383 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30674501585 / 1000000000000) (-30674501584 / 1000000000000), orderedInterval (-49897581325 / 1000000000000) (-49897581324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (463357249975949 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-27820850884 / 1000000000000) (-27820850883 / 1000000000000), orderedInterval (-68594919556 / 1000000000000) (-68594919555 / 1000000000000)))) (orderedInterval (-5233282339 / 1000000000000) (-5233277085 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (249195070093683 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25039222089 / 1000000000000) (25039222090 / 1000000000000), orderedInterval (97738543951 / 1000000000000) (97738543952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (676613090650049 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (17655877123 / 1000000000000) (17655877124 / 1000000000000), orderedInterval (58700269254 / 1000000000000) (58700269255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (923857329850273 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34959112184 / 1000000000000) (-34959087698 / 1000000000000), orderedInterval (39244754708 / 1000000000000) (39244779195 / 1000000000000)))) (orderedInterval (-4835434793 / 1000000000000) (-4835432739 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (390642750024051 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-70251155645 / 1000000000000) (-70251155644 / 1000000000000), orderedInterval (-39432568593 / 1000000000000) (-39432568592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1587941091010771 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (37494060449 / 1000000000000) (37494075630 / 1000000000000), orderedInterval (-14112422897 / 1000000000000) (-14112407715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1060671057152189 / 4000000000000) 1 (IntervalRat.scale (427 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43276090419 / 1000000000000) (43276117813 / 1000000000000), orderedInterval (-23059761555 / 1000000000000) (-23059734161 / 1000000000000)))) (orderedInterval (7400989180 / 1000000000000) (7400997945 / 1000000000000))) = true
  rfl'

theorem compactCertificate341_chunkChecks1 :
    compactCertificate341.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate341.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate341_chunkChecks1_0
    compactCertificate341_chunkChecks1_1 compactCertificate341_chunkChecks1_2

theorem compactCertificate341_chunkChecks2_0 :
    compactCertificate341.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (427 / 2) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33329212055 / 1000000000000) (33329212056 / 1000000000000), orderedInterval (43176903470 / 1000000000000) (43176903471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (629052534753727 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (52414800947 / 1000000000000) (52414800948 / 1000000000000), orderedInterval (35899955067 / 1000000000000) (35899955068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (203422665039391 / 800000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28013976500 / 1000000000000) (-28013976499 / 1000000000000), orderedInterval (-41403961252 / 1000000000000) (-41403961251 / 1000000000000)))) (orderedInterval (-11211460156 / 1000000000000) (-11211460135 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (183555960761789 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (51466219494 / 1000000000000) (51466223365 / 1000000000000), orderedInterval (-106507748188 / 1000000000000) (-106507744318 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (493057129887833 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71795041819 / 1000000000000) (-71795041799 / 1000000000000), orderedInterval (-2887325535 / 1000000000000) (-2887325515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1338746020916661 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27385983020 / 1000000000000) (27385992135 / 1000000000000), orderedInterval (-33984188812 / 1000000000000) (-33984179697 / 1000000000000)))) (orderedInterval (5665231696 / 1000000000000) (5665233337 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (986114259776093 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38917930269 / 1000000000000) (38918012122 / 1000000000000), orderedInterval (-32755066857 / 1000000000000) (-32754985004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1689723591905489 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (30385230744 / 1000000000000) (30385278435 / 1000000000000), orderedInterval (-24197421466 / 1000000000000) (-24197373775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1244642750024051 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36205158894 / 1000000000000) (-36205158893 / 1000000000000), orderedInterval (-27055242448 / 1000000000000) (-27055242447 / 1000000000000)))) (orderedInterval (5525153842 / 1000000000000) (5525159653 / 1000000000000))) = true
  rfl'

theorem compactCertificate341_chunkChecks2_1 :
    compactCertificate341.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1909602052784573 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22492099783 / 1000000000000) (22492099784 / 1000000000000), orderedInterval (28744804025 / 1000000000000) (28744804026 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1102509259220117 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2300880918 / 1000000000000) (-2300880914 / 1000000000000), orderedInterval (48008568811 / 1000000000000) (48008568815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1956422027675353 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7089880902 / 1000000000000) (-7089880895 / 1000000000000), orderedInterval (35381451777 / 1000000000000) (35381451783 / 1000000000000)))) (orderedInterval (25534497743 / 1000000000000) (25534498126 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1827943238644957 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29273865338 / 1000000000000) (-29273823571 / 1000000000000), orderedInterval (23186405693 / 1000000000000) (23186447460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1304506547830381 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (8171262965 / 1000000000000) (8171262966 / 1000000000000), orderedInterval (43407464153 / 1000000000000) (43407464154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1479171389663499 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-5379785278 / 1000000000000) (-5379785272 / 1000000000000), orderedInterval (41148704034 / 1000000000000) (41148704040 / 1000000000000)))) (orderedInterval (-4329377453 / 1000000000000) (-4329373921 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1233178893331931 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (42413242148 / 1000000000000) (42413242149 / 1000000000000), orderedInterval (16243363069 / 1000000000000) (16243363070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1089550950822551 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7027675877 / 1000000000000) (7027675894 / 1000000000000), orderedInterval (-47843828834 / 1000000000000) (-47843828817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (315794332836549 / 800000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12353174561 / 1000000000000) (-12353174482 / 1000000000000), orderedInterval (38227496026 / 1000000000000) (38227496105 / 1000000000000)))) (orderedInterval (688494902 / 1000000000000) (688494955 / 1000000000000))) = true
  rfl'

theorem compactCertificate341_chunkChecks2_2 :
    compactCertificate341.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (873503743971103 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36832299175 / 1000000000000) (-36832267358 / 1000000000000), orderedInterval (39563807546 / 1000000000000) (39563839362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (740478797553383 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30674501585 / 1000000000000) (-30674501584 / 1000000000000), orderedInterval (-49897581325 / 1000000000000) (-49897581324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (463357249975949 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-27820850884 / 1000000000000) (-27820850883 / 1000000000000), orderedInterval (-68594919556 / 1000000000000) (-68594919555 / 1000000000000)))) (orderedInterval (-7175411780 / 1000000000000) (-7175406385 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (249195070093683 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25039222089 / 1000000000000) (25039222090 / 1000000000000), orderedInterval (97738543951 / 1000000000000) (97738543952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (676613090650049 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (17655877123 / 1000000000000) (17655877124 / 1000000000000), orderedInterval (58700269254 / 1000000000000) (58700269255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (923857329850273 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34959112184 / 1000000000000) (-34959087698 / 1000000000000), orderedInterval (39244754708 / 1000000000000) (39244779195 / 1000000000000)))) (orderedInterval (-2822024112 / 1000000000000) (-2822021883 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (390642750024051 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-70251155645 / 1000000000000) (-70251155644 / 1000000000000), orderedInterval (-39432568593 / 1000000000000) (-39432568592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1587941091010771 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (37494060449 / 1000000000000) (37494075630 / 1000000000000), orderedInterval (-14112422897 / 1000000000000) (-14112407715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1060671057152189 / 4000000000000) 2 (IntervalRat.scale (427 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43276090419 / 1000000000000) (43276117813 / 1000000000000), orderedInterval (-23059761555 / 1000000000000) (-23059734161 / 1000000000000)))) (orderedInterval (23131596925 / 1000000000000) (23131609290 / 1000000000000))) = true
  rfl'

theorem compactCertificate341_chunkChecks2 :
    compactCertificate341.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate341.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate341_chunkChecks2_0
    compactCertificate341_chunkChecks2_1 compactCertificate341_chunkChecks2_2

theorem compactCertificate341_chunkChecks3_0 :
    compactCertificate341.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (427 / 2) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33329212055 / 1000000000000) (33329212056 / 1000000000000), orderedInterval (43176903470 / 1000000000000) (43176903471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (629052534753727 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (52414800947 / 1000000000000) (52414800948 / 1000000000000), orderedInterval (35899955067 / 1000000000000) (35899955068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (203422665039391 / 800000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28013976500 / 1000000000000) (-28013976499 / 1000000000000), orderedInterval (-41403961252 / 1000000000000) (-41403961251 / 1000000000000)))) (orderedInterval (-13090037387 / 1000000000000) (-13090037364 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (183555960761789 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (51466219494 / 1000000000000) (51466223365 / 1000000000000), orderedInterval (-106507748188 / 1000000000000) (-106507744318 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (493057129887833 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71795041819 / 1000000000000) (-71795041799 / 1000000000000), orderedInterval (-2887325535 / 1000000000000) (-2887325515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1338746020916661 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27385983020 / 1000000000000) (27385992135 / 1000000000000), orderedInterval (-33984188812 / 1000000000000) (-33984179697 / 1000000000000)))) (orderedInterval (-9324515284 / 1000000000000) (-9324512718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (986114259776093 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38917930269 / 1000000000000) (38918012122 / 1000000000000), orderedInterval (-32755066857 / 1000000000000) (-32754985004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1689723591905489 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (30385230744 / 1000000000000) (30385278435 / 1000000000000), orderedInterval (-24197421466 / 1000000000000) (-24197373775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1244642750024051 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36205158894 / 1000000000000) (-36205158893 / 1000000000000), orderedInterval (-27055242448 / 1000000000000) (-27055242447 / 1000000000000)))) (orderedInterval (-3782804775 / 1000000000000) (-3782793286 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate341_chunkChecks3_1 :
    compactCertificate341.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1909602052784573 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22492099783 / 1000000000000) (22492099784 / 1000000000000), orderedInterval (28744804025 / 1000000000000) (28744804026 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1102509259220117 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2300880918 / 1000000000000) (-2300880914 / 1000000000000), orderedInterval (48008568811 / 1000000000000) (48008568815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1956422027675353 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7089880902 / 1000000000000) (-7089880895 / 1000000000000), orderedInterval (35381451777 / 1000000000000) (35381451783 / 1000000000000)))) (orderedInterval (-11140300691 / 1000000000000) (-11140299854 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1827943238644957 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29273865338 / 1000000000000) (-29273823571 / 1000000000000), orderedInterval (23186405693 / 1000000000000) (23186447460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1304506547830381 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (8171262965 / 1000000000000) (8171262966 / 1000000000000), orderedInterval (43407464153 / 1000000000000) (43407464154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1479171389663499 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-5379785278 / 1000000000000) (-5379785272 / 1000000000000), orderedInterval (41148704034 / 1000000000000) (41148704040 / 1000000000000)))) (orderedInterval (-9422913954 / 1000000000000) (-9422906427 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1233178893331931 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (42413242148 / 1000000000000) (42413242149 / 1000000000000), orderedInterval (16243363069 / 1000000000000) (16243363070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1089550950822551 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7027675877 / 1000000000000) (7027675894 / 1000000000000), orderedInterval (-47843828834 / 1000000000000) (-47843828817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (315794332836549 / 800000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12353174561 / 1000000000000) (-12353174482 / 1000000000000), orderedInterval (38227496026 / 1000000000000) (38227496105 / 1000000000000)))) (orderedInterval (-12440019439 / 1000000000000) (-12440019355 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate341_chunkChecks3_2 :
    compactCertificate341.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (873503743971103 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36832299175 / 1000000000000) (-36832267358 / 1000000000000), orderedInterval (39563807546 / 1000000000000) (39563839362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (740478797553383 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30674501585 / 1000000000000) (-30674501584 / 1000000000000), orderedInterval (-49897581325 / 1000000000000) (-49897581324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (463357249975949 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-27820850884 / 1000000000000) (-27820850883 / 1000000000000), orderedInterval (-68594919556 / 1000000000000) (-68594919555 / 1000000000000)))) (orderedInterval (5318501165 / 1000000000000) (5318506680 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (249195070093683 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25039222089 / 1000000000000) (25039222090 / 1000000000000), orderedInterval (97738543951 / 1000000000000) (97738543952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (676613090650049 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (17655877123 / 1000000000000) (17655877124 / 1000000000000), orderedInterval (58700269254 / 1000000000000) (58700269255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (923857329850273 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34959112184 / 1000000000000) (-34959087698 / 1000000000000), orderedInterval (39244754708 / 1000000000000) (39244779195 / 1000000000000)))) (orderedInterval (4528042506 / 1000000000000) (4528044916 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (390642750024051 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-70251155645 / 1000000000000) (-70251155644 / 1000000000000), orderedInterval (-39432568593 / 1000000000000) (-39432568592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1587941091010771 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (37494060449 / 1000000000000) (37494075630 / 1000000000000), orderedInterval (-14112422897 / 1000000000000) (-14112407715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1060671057152189 / 4000000000000) 3 (IntervalRat.scale (427 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43276090419 / 1000000000000) (43276117813 / 1000000000000), orderedInterval (-23059761555 / 1000000000000) (-23059734161 / 1000000000000)))) (orderedInterval (-15759972454 / 1000000000000) (-15759954415 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate341_chunkChecks3 :
    compactCertificate341.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate341.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate341_chunkChecks3_0
    compactCertificate341_chunkChecks3_1 compactCertificate341_chunkChecks3_2

theorem compactCertificate341_chunkChecks4_0 :
    compactCertificate341.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (427 / 2) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (33329212055 / 1000000000000) (33329212056 / 1000000000000), orderedInterval (43176903470 / 1000000000000) (43176903471 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (629052534753727 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (52414800947 / 1000000000000) (52414800948 / 1000000000000), orderedInterval (35899955067 / 1000000000000) (35899955068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (203422665039391 / 800000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28013976500 / 1000000000000) (-28013976499 / 1000000000000), orderedInterval (-41403961252 / 1000000000000) (-41403961251 / 1000000000000)))) (orderedInterval (10169040484 / 1000000000000) (10169040511 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (183555960761789 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (51466219494 / 1000000000000) (51466223365 / 1000000000000), orderedInterval (-106507748188 / 1000000000000) (-106507744318 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (493057129887833 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71795041819 / 1000000000000) (-71795041799 / 1000000000000), orderedInterval (-2887325535 / 1000000000000) (-2887325515 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1338746020916661 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27385983020 / 1000000000000) (27385992135 / 1000000000000), orderedInterval (-33984188812 / 1000000000000) (-33984179697 / 1000000000000)))) (orderedInterval (-11961969676 / 1000000000000) (-11961965646 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (986114259776093 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (38917930269 / 1000000000000) (38918012122 / 1000000000000), orderedInterval (-32755066857 / 1000000000000) (-32754985004 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1689723591905489 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (30385230744 / 1000000000000) (30385278435 / 1000000000000), orderedInterval (-24197421466 / 1000000000000) (-24197373775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1244642750024051 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-36205158894 / 1000000000000) (-36205158893 / 1000000000000), orderedInterval (-27055242448 / 1000000000000) (-27055242447 / 1000000000000)))) (orderedInterval (-18275938232 / 1000000000000) (-18275915456 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate341_chunkChecks4_1 :
    compactCertificate341.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1909602052784573 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22492099783 / 1000000000000) (22492099784 / 1000000000000), orderedInterval (28744804025 / 1000000000000) (28744804026 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1102509259220117 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2300880918 / 1000000000000) (-2300880914 / 1000000000000), orderedInterval (48008568811 / 1000000000000) (48008568815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1956422027675353 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7089880902 / 1000000000000) (-7089880895 / 1000000000000), orderedInterval (35381451777 / 1000000000000) (35381451783 / 1000000000000)))) (orderedInterval (-128043185931 / 1000000000000) (-128043184069 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1827943238644957 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29273865338 / 1000000000000) (-29273823571 / 1000000000000), orderedInterval (23186405693 / 1000000000000) (23186447460 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1304506547830381 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (8171262965 / 1000000000000) (8171262966 / 1000000000000), orderedInterval (43407464153 / 1000000000000) (43407464154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1479171389663499 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-5379785278 / 1000000000000) (-5379785272 / 1000000000000), orderedInterval (41148704034 / 1000000000000) (41148704040 / 1000000000000)))) (orderedInterval (15633141493 / 1000000000000) (15633157592 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1233178893331931 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (42413242148 / 1000000000000) (42413242149 / 1000000000000), orderedInterval (16243363069 / 1000000000000) (16243363070 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1089550950822551 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7027675877 / 1000000000000) (7027675894 / 1000000000000), orderedInterval (-47843828834 / 1000000000000) (-47843828817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (315794332836549 / 800000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-12353174561 / 1000000000000) (-12353174482 / 1000000000000), orderedInterval (38227496026 / 1000000000000) (38227496105 / 1000000000000)))) (orderedInterval (-2515698842 / 1000000000000) (-2515698707 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate341_chunkChecks4_2 :
    compactCertificate341.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (873503743971103 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36832299175 / 1000000000000) (-36832267358 / 1000000000000), orderedInterval (39563807546 / 1000000000000) (39563839362 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (740478797553383 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-30674501585 / 1000000000000) (-30674501584 / 1000000000000), orderedInterval (-49897581325 / 1000000000000) (-49897581324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (463357249975949 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-27820850884 / 1000000000000) (-27820850883 / 1000000000000), orderedInterval (-68594919556 / 1000000000000) (-68594919555 / 1000000000000)))) (orderedInterval (7298760076 / 1000000000000) (7298765741 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (249195070093683 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25039222089 / 1000000000000) (25039222090 / 1000000000000), orderedInterval (97738543951 / 1000000000000) (97738543952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (676613090650049 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (17655877123 / 1000000000000) (17655877124 / 1000000000000), orderedInterval (58700269254 / 1000000000000) (58700269255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (923857329850273 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34959112184 / 1000000000000) (-34959087698 / 1000000000000), orderedInterval (39244754708 / 1000000000000) (39244779195 / 1000000000000)))) (orderedInterval (3465757034 / 1000000000000) (3465759652 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (390642750024051 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-70251155645 / 1000000000000) (-70251155644 / 1000000000000), orderedInterval (-39432568593 / 1000000000000) (-39432568592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1587941091010771 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (37494060449 / 1000000000000) (37494075630 / 1000000000000), orderedInterval (-14112422897 / 1000000000000) (-14112407715 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1060671057152189 / 4000000000000) 4 (IntervalRat.scale (427 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (43276090419 / 1000000000000) (43276117813 / 1000000000000), orderedInterval (-23059761555 / 1000000000000) (-23059734161 / 1000000000000)))) (orderedInterval (-55675605817 / 1000000000000) (-55675578344 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate341_chunkChecks4 :
    compactCertificate341.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate341.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate341_chunkChecks4_0
    compactCertificate341_chunkChecks4_1 compactCertificate341_chunkChecks4_2

theorem compactCertificate341_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate341.chunkCheck r b = true :=
  compactCertificate341.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate341_chunkChecks0
    · exact compactCertificate341_chunkChecks1
    · exact compactCertificate341_chunkChecks2
    · exact compactCertificate341_chunkChecks3
    · exact compactCertificate341_chunkChecks4)

theorem compactCertificate341_coefficient0 :
    compactCertificate341.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate341_coefficient1 :
    compactCertificate341.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate341_coefficient2 :
    compactCertificate341.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate341_coefficient3 :
    compactCertificate341.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate341_coefficient4 :
    compactCertificate341.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate341_coefficients : ∀ r : Fin 5,
    compactCertificate341.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate341_coefficient0
  · exact compactCertificate341_coefficient1
  · exact compactCertificate341_coefficient2
  · exact compactCertificate341_coefficient3
  · exact compactCertificate341_coefficient4

theorem compactCertificate341_lower : (1 : ℚ) ≤ compactCertificate341.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate341, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate341_proves {t : ℝ} (ht : t ∈ compactCertificate341.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate341.proves compactCertificate341_states compactCertificate341_chunks
    compactCertificate341_coefficients compactCertificate341_lower ht

end Erdos232
