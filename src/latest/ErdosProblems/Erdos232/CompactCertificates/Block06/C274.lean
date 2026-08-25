/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate274 : CompactCertificate where
  left := 148
  right := 149
  center := 297 / 2
  grid := fun i =>
    match i.val with
    | 0 => 47
    | 1 => 35
    | 2 => 56
    | 3 => 10
    | 4 => 27
    | 5 => 74
    | 6 => 55
    | 7 => 94
    | 8 => 69
    | 9 => 106
    | 10 => 61
    | 11 => 108
    | 12 => 101
    | 13 => 72
    | 14 => 82
    | 15 => 68
    | 16 => 60
    | 17 => 87
    | 18 => 48
    | 19 => 41
    | 20 => 26
    | 21 => 14
    | 22 => 37
    | 23 => 51
    | 24 => 22
    | 25 => 88
    | _ => 59
  point := fun i =>
    match i.val with
    | 0 => 297 / 2
    | 1 => 437537711526597 / 4000000000000
    | 2 => 141490706128101 / 800000000000
    | 3 => 127672412988879 / 4000000000000
    | 4 => 342946059898563 / 4000000000000
    | 5 => 931165265134071 / 4000000000000
    | 6 => 685892119797423 / 4000000000000
    | 7 => 1175287837929579 / 4000000000000
    | 8 => 865711702007361 / 4000000000000
    | 9 => 1328224378634703 / 4000000000000
    | 10 => 766850702548887 / 4000000000000
    | 11 => 1360790028617283 / 4000000000000
    | 12 => 1271426561774127 / 4000000000000
    | 13 => 907349987600991 / 4000000000000
    | 14 => 1028838179695689 / 4000000000000
    | 15 => 857738012458041 / 4000000000000
    | 16 => 757837546590861 / 4000000000000
    | 17 => 219650859139239 / 800000000000
    | 18 => 607565835970533 / 4000000000000
    | 19 => 515040287759613 / 4000000000000
    | 20 => 322288297992639 / 4000000000000
    | 21 => 173327718542913 / 4000000000000
    | 22 => 470618472887739 / 4000000000000
    | 23 => 642589290317403 / 4000000000000
    | 24 => 271711702007361 / 4000000000000
    | 25 => 1104492983677281 / 4000000000000
    | _ => 737750126403279 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-65361453423 / 1000000000000) (-65361453313 / 1000000000000), orderedInterval (4074692550 / 1000000000000) (4074692660 / 1000000000000))
    | 1 => (orderedInterval (-16122455065 / 1000000000000) (-16122455064 / 1000000000000), orderedInterval (-74492676798 / 1000000000000) (-74492676797 / 1000000000000))
    | 2 => (orderedInterval (59339050858 / 1000000000000) (59339051293 / 1000000000000), orderedInterval (-9020063743 / 1000000000000) (-9020063308 / 1000000000000))
    | 3 => (orderedInterval (135437909767 / 1000000000000) (135437909768 / 1000000000000), orderedInterval (37878059001 / 1000000000000) (37878059002 / 1000000000000))
    | 4 => (orderedInterval (-85479231882 / 1000000000000) (-85479231701 / 1000000000000), orderedInterval (11383504815 / 1000000000000) (11383504996 / 1000000000000))
    | 5 => (orderedInterval (46565370637 / 1000000000000) (46565370638 / 1000000000000), orderedInterval (23698842021 / 1000000000000) (23698842022 / 1000000000000))
    | 6 => (orderedInterval (30797431192 / 1000000000000) (30797435781 / 1000000000000), orderedInterval (-52665257373 / 1000000000000) (-52665252784 / 1000000000000))
    | 7 => (orderedInterval (-30085574251 / 1000000000000) (-30085560097 / 1000000000000), orderedInterval (35569418994 / 1000000000000) (35569433149 / 1000000000000))
    | 8 => (orderedInterval (-23240898505 / 1000000000000) (-23240898504 / 1000000000000), orderedInterval (-48949898745 / 1000000000000) (-48949898744 / 1000000000000))
    | 9 => (orderedInterval (-7308734318 / 1000000000000) (-7308734303 / 1000000000000), orderedInterval (43182638972 / 1000000000000) (43182638987 / 1000000000000))
    | 10 => (orderedInterval (-43681123088 / 1000000000000) (-43681123087 / 1000000000000), orderedInterval (-37471382245 / 1000000000000) (-37471382244 / 1000000000000))
    | 11 => (orderedInterval (42949060531 / 1000000000000) (42949061380 / 1000000000000), orderedInterval (-5230351013 / 1000000000000) (-5230350164 / 1000000000000))
    | 12 => (orderedInterval (-43574600628 / 1000000000000) (-43574600623 / 1000000000000), orderedInterval (-10134585063 / 1000000000000) (-10134585058 / 1000000000000))
    | 13 => (orderedInterval (52434693309 / 1000000000000) (52434693319 / 1000000000000), orderedInterval (7440737075 / 1000000000000) (7440737084 / 1000000000000))
    | 14 => (orderedInterval (18631598826 / 1000000000000) (18631598827 / 1000000000000), orderedInterval (46093690946 / 1000000000000) (46093690947 / 1000000000000))
    | 15 => (orderedInterval (54475764981 / 1000000000000) (54475765083 / 1000000000000), orderedInterval (-1228760764 / 1000000000000) (-1228760663 / 1000000000000))
    | 16 => (orderedInterval (57053527536 / 1000000000000) (57053528217 / 1000000000000), orderedInterval (-10401189588 / 1000000000000) (-10401188907 / 1000000000000))
    | 17 => (orderedInterval (-43165068448 / 1000000000000) (-43165046580 / 1000000000000), orderedInterval (21419545349 / 1000000000000) (21419567216 / 1000000000000))
    | 18 => (orderedInterval (61677846387 / 1000000000000) (61677848901 / 1000000000000), orderedInterval (-19878028461 / 1000000000000) (-19878025947 / 1000000000000))
    | 19 => (orderedInterval (-47371009333 / 1000000000000) (-47371009332 / 1000000000000), orderedInterval (-51779729051 / 1000000000000) (-51779729050 / 1000000000000))
    | 20 => (orderedInterval (-28423821361 / 1000000000000) (-28423820605 / 1000000000000), orderedInterval (84399021514 / 1000000000000) (84399022270 / 1000000000000))
    | 21 => (orderedInterval (15970309030 / 1000000000000) (15970309032 / 1000000000000), orderedInterval (119972285175 / 1000000000000) (119972285177 / 1000000000000))
    | 22 => (orderedInterval (-59470791515 / 1000000000000) (-59470741443 / 1000000000000), orderedInterval (43543963247 / 1000000000000) (43544013319 / 1000000000000))
    | 23 => (orderedInterval (-58913838654 / 1000000000000) (-58913838653 / 1000000000000), orderedInterval (-21997396157 / 1000000000000) (-21997396156 / 1000000000000))
    | 24 => (orderedInterval (-38015422115 / 1000000000000) (-38015420091 / 1000000000000), orderedInterval (89313463803 / 1000000000000) (89313465827 / 1000000000000))
    | 25 => (orderedInterval (20800538093 / 1000000000000) (20800538094 / 1000000000000), orderedInterval (43239393633 / 1000000000000) (43239393634 / 1000000000000))
    | _ => (orderedInterval (7715992702 / 1000000000000) (7715992728 / 1000000000000), orderedInterval (-58263153464 / 1000000000000) (-58263153438 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-22575138887 / 1000000000000) (-22575138807 / 1000000000000)
      | 1 => orderedInterval (-7900716789 / 1000000000000) (-7900716764 / 1000000000000)
      | 2 => orderedInterval (366272379 / 1000000000000) (366272824 / 1000000000000)
      | 3 => orderedInterval (4167724052 / 1000000000000) (4167724235 / 1000000000000)
      | 4 => orderedInterval (5650744258 / 1000000000000) (5650744278 / 1000000000000)
      | 5 => orderedInterval (-3741111936 / 1000000000000) (-3741111321 / 1000000000000)
      | 6 => orderedInterval (-8105970060 / 1000000000000) (-8105969596 / 1000000000000)
      | 7 => orderedInterval (5569400892 / 1000000000000) (5569402046 / 1000000000000)
      | _ => orderedInterval (-3370095136 / 1000000000000) (-3370095077 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (473369539 / 1000000000000) (473369626 / 1000000000000)
      | 1 => orderedInterval (-2489395882 / 1000000000000) (-2489395857 / 1000000000000)
      | 2 => orderedInterval (-3894897238 / 1000000000000) (-3894896359 / 1000000000000)
      | 3 => orderedInterval (-22444975979 / 1000000000000) (-22444975574 / 1000000000000)
      | 4 => orderedInterval (1062391747 / 1000000000000) (1062391778 / 1000000000000)
      | 5 => orderedInterval (1752901623 / 1000000000000) (1752902731 / 1000000000000)
      | 6 => orderedInterval (7282876585 / 1000000000000) (7282877045 / 1000000000000)
      | 7 => orderedInterval (394657025 / 1000000000000) (394657942 / 1000000000000)
      | _ => orderedInterval (7278806719 / 1000000000000) (7278806789 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (21046052759 / 1000000000000) (21046052853 / 1000000000000)
      | 1 => orderedInterval (9259837877 / 1000000000000) (9259837908 / 1000000000000)
      | 2 => orderedInterval (-2413522703 / 1000000000000) (-2413520961 / 1000000000000)
      | 3 => orderedInterval (-32990815449 / 1000000000000) (-32990814538 / 1000000000000)
      | 4 => orderedInterval (-14897916643 / 1000000000000) (-14897916592 / 1000000000000)
      | 5 => orderedInterval (7769060607 / 1000000000000) (7769062626 / 1000000000000)
      | 6 => orderedInterval (8525023657 / 1000000000000) (8525024121 / 1000000000000)
      | 7 => orderedInterval (-6108442053 / 1000000000000) (-6108441317 / 1000000000000)
      | _ => orderedInterval (8086275156 / 1000000000000) (8086275253 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-585139477 / 1000000000000) (-585139374 / 1000000000000)
      | 1 => orderedInterval (6351768718 / 1000000000000) (6351768762 / 1000000000000)
      | 2 => orderedInterval (12176453802 / 1000000000000) (12176457243 / 1000000000000)
      | 3 => orderedInterval (100921383574 / 1000000000000) (100921385633 / 1000000000000)
      | 4 => orderedInterval (-2989627066 / 1000000000000) (-2989626981 / 1000000000000)
      | 5 => orderedInterval (-4711912616 / 1000000000000) (-4711908932 / 1000000000000)
      | 6 => orderedInterval (-5807533952 / 1000000000000) (-5807533482 / 1000000000000)
      | 7 => orderedInterval (-1546833881 / 1000000000000) (-1546833294 / 1000000000000)
      | _ => orderedInterval (1578318966 / 1000000000000) (1578319110 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-18936142317 / 1000000000000) (-18936142202 / 1000000000000)
      | 1 => orderedInterval (-20425861491 / 1000000000000) (-20425861424 / 1000000000000)
      | 2 => orderedInterval (11523673372 / 1000000000000) (11523680196 / 1000000000000)
      | 3 => orderedInterval (190281738193 / 1000000000000) (190281742877 / 1000000000000)
      | 4 => orderedInterval (42698777450 / 1000000000000) (42698777598 / 1000000000000)
      | 5 => orderedInterval (-18766898289 / 1000000000000) (-18766891514 / 1000000000000)
      | 6 => orderedInterval (-9280179385 / 1000000000000) (-9280178905 / 1000000000000)
      | 7 => orderedInterval (6733833399 / 1000000000000) (6733833872 / 1000000000000)
      | _ => orderedInterval (-23716019302 / 1000000000000) (-23716019076 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-29938891227 / 1000000000000) (-29938888182 / 1000000000000)
    | 1 => orderedInterval (-10584265861 / 1000000000000) (-10584261879 / 1000000000000)
    | 2 => orderedInterval (-1724446792 / 1000000000000) (-1724440647 / 1000000000000)
    | 3 => orderedInterval (105386878068 / 1000000000000) (105386888685 / 1000000000000)
    | _ => orderedInterval (160112921630 / 1000000000000) (160112941422 / 1000000000000)

theorem compactCertificate274_stateChecks0 :
    compactCertificate274.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (297 / 2)) (orderedInterval (-65361453423 / 1000000000000) (-65361453313 / 1000000000000), orderedInterval (4074692550 / 1000000000000) (4074692660 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (437537711526597 / 4000000000000)) (orderedInterval (-16122455065 / 1000000000000) (-16122455064 / 1000000000000), orderedInterval (-74492676798 / 1000000000000) (-74492676797 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (141490706128101 / 800000000000)) (orderedInterval (59339050858 / 1000000000000) (59339051293 / 1000000000000), orderedInterval (-9020063743 / 1000000000000) (-9020063308 / 1000000000000))) = true
  rfl'

theorem compactCertificate274_stateChecks1 :
    compactCertificate274.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 10 12 (127672412988879 / 4000000000000)) (orderedInterval (135437909767 / 1000000000000) (135437909768 / 1000000000000), orderedInterval (37878059001 / 1000000000000) (37878059002 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (342946059898563 / 4000000000000)) (orderedInterval (-85479231882 / 1000000000000) (-85479231701 / 1000000000000), orderedInterval (11383504815 / 1000000000000) (11383504996 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (931165265134071 / 4000000000000)) (orderedInterval (46565370637 / 1000000000000) (46565370638 / 1000000000000), orderedInterval (23698842021 / 1000000000000) (23698842022 / 1000000000000))) = true
  rfl'

theorem compactCertificate274_stateChecks2 :
    compactCertificate274.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (685892119797423 / 4000000000000)) (orderedInterval (30797431192 / 1000000000000) (30797435781 / 1000000000000), orderedInterval (-52665257373 / 1000000000000) (-52665252784 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1175287837929579 / 4000000000000)) (orderedInterval (-30085574251 / 1000000000000) (-30085560097 / 1000000000000), orderedInterval (35569418994 / 1000000000000) (35569433149 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (865711702007361 / 4000000000000)) (orderedInterval (-23240898505 / 1000000000000) (-23240898504 / 1000000000000), orderedInterval (-48949898745 / 1000000000000) (-48949898744 / 1000000000000))) = true
  rfl'

theorem compactCertificate274_stateChecks3 :
    compactCertificate274.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1328224378634703 / 4000000000000)) (orderedInterval (-7308734318 / 1000000000000) (-7308734303 / 1000000000000), orderedInterval (43182638972 / 1000000000000) (43182638987 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (766850702548887 / 4000000000000)) (orderedInterval (-43681123088 / 1000000000000) (-43681123087 / 1000000000000), orderedInterval (-37471382245 / 1000000000000) (-37471382244 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1360790028617283 / 4000000000000)) (orderedInterval (42949060531 / 1000000000000) (42949061380 / 1000000000000), orderedInterval (-5230351013 / 1000000000000) (-5230350164 / 1000000000000))) = true
  rfl'

theorem compactCertificate274_stateChecks4 :
    compactCertificate274.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1271426561774127 / 4000000000000)) (orderedInterval (-43574600628 / 1000000000000) (-43574600623 / 1000000000000), orderedInterval (-10134585063 / 1000000000000) (-10134585058 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (907349987600991 / 4000000000000)) (orderedInterval (52434693309 / 1000000000000) (52434693319 / 1000000000000), orderedInterval (7440737075 / 1000000000000) (7440737084 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1028838179695689 / 4000000000000)) (orderedInterval (18631598826 / 1000000000000) (18631598827 / 1000000000000), orderedInterval (46093690946 / 1000000000000) (46093690947 / 1000000000000))) = true
  rfl'

theorem compactCertificate274_stateChecks5 :
    compactCertificate274.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (857738012458041 / 4000000000000)) (orderedInterval (54475764981 / 1000000000000) (54475765083 / 1000000000000), orderedInterval (-1228760764 / 1000000000000) (-1228760663 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (757837546590861 / 4000000000000)) (orderedInterval (57053527536 / 1000000000000) (57053528217 / 1000000000000), orderedInterval (-10401189588 / 1000000000000) (-10401188907 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (219650859139239 / 800000000000)) (orderedInterval (-43165068448 / 1000000000000) (-43165046580 / 1000000000000), orderedInterval (21419545349 / 1000000000000) (21419567216 / 1000000000000))) = true
  rfl'

theorem compactCertificate274_stateChecks6 :
    compactCertificate274.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (607565835970533 / 4000000000000)) (orderedInterval (61677846387 / 1000000000000) (61677848901 / 1000000000000), orderedInterval (-19878028461 / 1000000000000) (-19878025947 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (515040287759613 / 4000000000000)) (orderedInterval (-47371009333 / 1000000000000) (-47371009332 / 1000000000000), orderedInterval (-51779729051 / 1000000000000) (-51779729050 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (322288297992639 / 4000000000000)) (orderedInterval (-28423821361 / 1000000000000) (-28423820605 / 1000000000000), orderedInterval (84399021514 / 1000000000000) (84399022270 / 1000000000000))) = true
  rfl'

theorem compactCertificate274_stateChecks7 :
    compactCertificate274.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (173327718542913 / 4000000000000)) (orderedInterval (15970309030 / 1000000000000) (15970309032 / 1000000000000), orderedInterval (119972285175 / 1000000000000) (119972285177 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (470618472887739 / 4000000000000)) (orderedInterval (-59470791515 / 1000000000000) (-59470741443 / 1000000000000), orderedInterval (43543963247 / 1000000000000) (43544013319 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (642589290317403 / 4000000000000)) (orderedInterval (-58913838654 / 1000000000000) (-58913838653 / 1000000000000), orderedInterval (-21997396157 / 1000000000000) (-21997396156 / 1000000000000))) = true
  rfl'

theorem compactCertificate274_stateChecks8 :
    compactCertificate274.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (271711702007361 / 4000000000000)) (orderedInterval (-38015422115 / 1000000000000) (-38015420091 / 1000000000000), orderedInterval (89313463803 / 1000000000000) (89313465827 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1104492983677281 / 4000000000000)) (orderedInterval (20800538093 / 1000000000000) (20800538094 / 1000000000000), orderedInterval (43239393633 / 1000000000000) (43239393634 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (737750126403279 / 4000000000000)) (orderedInterval (7715992702 / 1000000000000) (7715992728 / 1000000000000), orderedInterval (-58263153464 / 1000000000000) (-58263153438 / 1000000000000))) = true
  rfl'

theorem compactCertificate274_states : ∀ j,
    BesselStateValid (compactCertificate274.point j) (compactCertificate274.state j) :=
  compactCertificate274.statesValid_of_checks3 compactCertificate274_stateChecks0
    compactCertificate274_stateChecks1 compactCertificate274_stateChecks2
    compactCertificate274_stateChecks3 compactCertificate274_stateChecks4
    compactCertificate274_stateChecks5 compactCertificate274_stateChecks6
    compactCertificate274_stateChecks7 compactCertificate274_stateChecks8

theorem compactCertificate274_chunkChecks0_0 :
    compactCertificate274.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (297 / 2) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-65361453423 / 1000000000000) (-65361453313 / 1000000000000), orderedInterval (4074692550 / 1000000000000) (4074692660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (437537711526597 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16122455065 / 1000000000000) (-16122455064 / 1000000000000), orderedInterval (-74492676798 / 1000000000000) (-74492676797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (141490706128101 / 800000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (59339050858 / 1000000000000) (59339051293 / 1000000000000), orderedInterval (-9020063743 / 1000000000000) (-9020063308 / 1000000000000)))) (orderedInterval (-22575138887 / 1000000000000) (-22575138807 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (127672412988879 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (135437909767 / 1000000000000) (135437909768 / 1000000000000), orderedInterval (37878059001 / 1000000000000) (37878059002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (342946059898563 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-85479231882 / 1000000000000) (-85479231701 / 1000000000000), orderedInterval (11383504815 / 1000000000000) (11383504996 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (931165265134071 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (46565370637 / 1000000000000) (46565370638 / 1000000000000), orderedInterval (23698842021 / 1000000000000) (23698842022 / 1000000000000)))) (orderedInterval (-7900716789 / 1000000000000) (-7900716764 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (685892119797423 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30797431192 / 1000000000000) (30797435781 / 1000000000000), orderedInterval (-52665257373 / 1000000000000) (-52665252784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1175287837929579 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30085574251 / 1000000000000) (-30085560097 / 1000000000000), orderedInterval (35569418994 / 1000000000000) (35569433149 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (865711702007361 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23240898505 / 1000000000000) (-23240898504 / 1000000000000), orderedInterval (-48949898745 / 1000000000000) (-48949898744 / 1000000000000)))) (orderedInterval (366272379 / 1000000000000) (366272824 / 1000000000000))) = true
  rfl'

theorem compactCertificate274_chunkChecks0_1 :
    compactCertificate274.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1328224378634703 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7308734318 / 1000000000000) (-7308734303 / 1000000000000), orderedInterval (43182638972 / 1000000000000) (43182638987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (766850702548887 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-43681123088 / 1000000000000) (-43681123087 / 1000000000000), orderedInterval (-37471382245 / 1000000000000) (-37471382244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1360790028617283 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (42949060531 / 1000000000000) (42949061380 / 1000000000000), orderedInterval (-5230351013 / 1000000000000) (-5230350164 / 1000000000000)))) (orderedInterval (4167724052 / 1000000000000) (4167724235 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1271426561774127 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-43574600628 / 1000000000000) (-43574600623 / 1000000000000), orderedInterval (-10134585063 / 1000000000000) (-10134585058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (907349987600991 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (52434693309 / 1000000000000) (52434693319 / 1000000000000), orderedInterval (7440737075 / 1000000000000) (7440737084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1028838179695689 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18631598826 / 1000000000000) (18631598827 / 1000000000000), orderedInterval (46093690946 / 1000000000000) (46093690947 / 1000000000000)))) (orderedInterval (5650744258 / 1000000000000) (5650744278 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (857738012458041 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (54475764981 / 1000000000000) (54475765083 / 1000000000000), orderedInterval (-1228760764 / 1000000000000) (-1228760663 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (757837546590861 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (57053527536 / 1000000000000) (57053528217 / 1000000000000), orderedInterval (-10401189588 / 1000000000000) (-10401188907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (219650859139239 / 800000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-43165068448 / 1000000000000) (-43165046580 / 1000000000000), orderedInterval (21419545349 / 1000000000000) (21419567216 / 1000000000000)))) (orderedInterval (-3741111936 / 1000000000000) (-3741111321 / 1000000000000))) = true
  rfl'

theorem compactCertificate274_chunkChecks0_2 :
    compactCertificate274.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (607565835970533 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (61677846387 / 1000000000000) (61677848901 / 1000000000000), orderedInterval (-19878028461 / 1000000000000) (-19878025947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (515040287759613 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47371009333 / 1000000000000) (-47371009332 / 1000000000000), orderedInterval (-51779729051 / 1000000000000) (-51779729050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (322288297992639 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28423821361 / 1000000000000) (-28423820605 / 1000000000000), orderedInterval (84399021514 / 1000000000000) (84399022270 / 1000000000000)))) (orderedInterval (-8105970060 / 1000000000000) (-8105969596 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (173327718542913 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (15970309030 / 1000000000000) (15970309032 / 1000000000000), orderedInterval (119972285175 / 1000000000000) (119972285177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (470618472887739 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-59470791515 / 1000000000000) (-59470741443 / 1000000000000), orderedInterval (43543963247 / 1000000000000) (43544013319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (642589290317403 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-58913838654 / 1000000000000) (-58913838653 / 1000000000000), orderedInterval (-21997396157 / 1000000000000) (-21997396156 / 1000000000000)))) (orderedInterval (5569400892 / 1000000000000) (5569402046 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (271711702007361 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-38015422115 / 1000000000000) (-38015420091 / 1000000000000), orderedInterval (89313463803 / 1000000000000) (89313465827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1104492983677281 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20800538093 / 1000000000000) (20800538094 / 1000000000000), orderedInterval (43239393633 / 1000000000000) (43239393634 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (737750126403279 / 4000000000000) 0 (IntervalRat.scale (297 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7715992702 / 1000000000000) (7715992728 / 1000000000000), orderedInterval (-58263153464 / 1000000000000) (-58263153438 / 1000000000000)))) (orderedInterval (-3370095136 / 1000000000000) (-3370095077 / 1000000000000))) = true
  rfl'

theorem compactCertificate274_chunkChecks0 :
    compactCertificate274.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate274.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate274_chunkChecks0_0
    compactCertificate274_chunkChecks0_1 compactCertificate274_chunkChecks0_2

theorem compactCertificate274_chunkChecks1_0 :
    compactCertificate274.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (297 / 2) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-65361453423 / 1000000000000) (-65361453313 / 1000000000000), orderedInterval (4074692550 / 1000000000000) (4074692660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (437537711526597 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16122455065 / 1000000000000) (-16122455064 / 1000000000000), orderedInterval (-74492676798 / 1000000000000) (-74492676797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (141490706128101 / 800000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (59339050858 / 1000000000000) (59339051293 / 1000000000000), orderedInterval (-9020063743 / 1000000000000) (-9020063308 / 1000000000000)))) (orderedInterval (473369539 / 1000000000000) (473369626 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (127672412988879 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (135437909767 / 1000000000000) (135437909768 / 1000000000000), orderedInterval (37878059001 / 1000000000000) (37878059002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (342946059898563 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-85479231882 / 1000000000000) (-85479231701 / 1000000000000), orderedInterval (11383504815 / 1000000000000) (11383504996 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (931165265134071 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (46565370637 / 1000000000000) (46565370638 / 1000000000000), orderedInterval (23698842021 / 1000000000000) (23698842022 / 1000000000000)))) (orderedInterval (-2489395882 / 1000000000000) (-2489395857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (685892119797423 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30797431192 / 1000000000000) (30797435781 / 1000000000000), orderedInterval (-52665257373 / 1000000000000) (-52665252784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1175287837929579 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30085574251 / 1000000000000) (-30085560097 / 1000000000000), orderedInterval (35569418994 / 1000000000000) (35569433149 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (865711702007361 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23240898505 / 1000000000000) (-23240898504 / 1000000000000), orderedInterval (-48949898745 / 1000000000000) (-48949898744 / 1000000000000)))) (orderedInterval (-3894897238 / 1000000000000) (-3894896359 / 1000000000000))) = true
  rfl'

theorem compactCertificate274_chunkChecks1_1 :
    compactCertificate274.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1328224378634703 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7308734318 / 1000000000000) (-7308734303 / 1000000000000), orderedInterval (43182638972 / 1000000000000) (43182638987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (766850702548887 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-43681123088 / 1000000000000) (-43681123087 / 1000000000000), orderedInterval (-37471382245 / 1000000000000) (-37471382244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1360790028617283 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (42949060531 / 1000000000000) (42949061380 / 1000000000000), orderedInterval (-5230351013 / 1000000000000) (-5230350164 / 1000000000000)))) (orderedInterval (-22444975979 / 1000000000000) (-22444975574 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1271426561774127 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-43574600628 / 1000000000000) (-43574600623 / 1000000000000), orderedInterval (-10134585063 / 1000000000000) (-10134585058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (907349987600991 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (52434693309 / 1000000000000) (52434693319 / 1000000000000), orderedInterval (7440737075 / 1000000000000) (7440737084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1028838179695689 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18631598826 / 1000000000000) (18631598827 / 1000000000000), orderedInterval (46093690946 / 1000000000000) (46093690947 / 1000000000000)))) (orderedInterval (1062391747 / 1000000000000) (1062391778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (857738012458041 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (54475764981 / 1000000000000) (54475765083 / 1000000000000), orderedInterval (-1228760764 / 1000000000000) (-1228760663 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (757837546590861 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (57053527536 / 1000000000000) (57053528217 / 1000000000000), orderedInterval (-10401189588 / 1000000000000) (-10401188907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (219650859139239 / 800000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-43165068448 / 1000000000000) (-43165046580 / 1000000000000), orderedInterval (21419545349 / 1000000000000) (21419567216 / 1000000000000)))) (orderedInterval (1752901623 / 1000000000000) (1752902731 / 1000000000000))) = true
  rfl'

theorem compactCertificate274_chunkChecks1_2 :
    compactCertificate274.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (607565835970533 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (61677846387 / 1000000000000) (61677848901 / 1000000000000), orderedInterval (-19878028461 / 1000000000000) (-19878025947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (515040287759613 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47371009333 / 1000000000000) (-47371009332 / 1000000000000), orderedInterval (-51779729051 / 1000000000000) (-51779729050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (322288297992639 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28423821361 / 1000000000000) (-28423820605 / 1000000000000), orderedInterval (84399021514 / 1000000000000) (84399022270 / 1000000000000)))) (orderedInterval (7282876585 / 1000000000000) (7282877045 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (173327718542913 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (15970309030 / 1000000000000) (15970309032 / 1000000000000), orderedInterval (119972285175 / 1000000000000) (119972285177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (470618472887739 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-59470791515 / 1000000000000) (-59470741443 / 1000000000000), orderedInterval (43543963247 / 1000000000000) (43544013319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (642589290317403 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-58913838654 / 1000000000000) (-58913838653 / 1000000000000), orderedInterval (-21997396157 / 1000000000000) (-21997396156 / 1000000000000)))) (orderedInterval (394657025 / 1000000000000) (394657942 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (271711702007361 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-38015422115 / 1000000000000) (-38015420091 / 1000000000000), orderedInterval (89313463803 / 1000000000000) (89313465827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1104492983677281 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20800538093 / 1000000000000) (20800538094 / 1000000000000), orderedInterval (43239393633 / 1000000000000) (43239393634 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (737750126403279 / 4000000000000) 1 (IntervalRat.scale (297 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7715992702 / 1000000000000) (7715992728 / 1000000000000), orderedInterval (-58263153464 / 1000000000000) (-58263153438 / 1000000000000)))) (orderedInterval (7278806719 / 1000000000000) (7278806789 / 1000000000000))) = true
  rfl'

theorem compactCertificate274_chunkChecks1 :
    compactCertificate274.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate274.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate274_chunkChecks1_0
    compactCertificate274_chunkChecks1_1 compactCertificate274_chunkChecks1_2

theorem compactCertificate274_chunkChecks2_0 :
    compactCertificate274.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (297 / 2) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-65361453423 / 1000000000000) (-65361453313 / 1000000000000), orderedInterval (4074692550 / 1000000000000) (4074692660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (437537711526597 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16122455065 / 1000000000000) (-16122455064 / 1000000000000), orderedInterval (-74492676798 / 1000000000000) (-74492676797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (141490706128101 / 800000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (59339050858 / 1000000000000) (59339051293 / 1000000000000), orderedInterval (-9020063743 / 1000000000000) (-9020063308 / 1000000000000)))) (orderedInterval (21046052759 / 1000000000000) (21046052853 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (127672412988879 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (135437909767 / 1000000000000) (135437909768 / 1000000000000), orderedInterval (37878059001 / 1000000000000) (37878059002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (342946059898563 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-85479231882 / 1000000000000) (-85479231701 / 1000000000000), orderedInterval (11383504815 / 1000000000000) (11383504996 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (931165265134071 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (46565370637 / 1000000000000) (46565370638 / 1000000000000), orderedInterval (23698842021 / 1000000000000) (23698842022 / 1000000000000)))) (orderedInterval (9259837877 / 1000000000000) (9259837908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (685892119797423 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30797431192 / 1000000000000) (30797435781 / 1000000000000), orderedInterval (-52665257373 / 1000000000000) (-52665252784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1175287837929579 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30085574251 / 1000000000000) (-30085560097 / 1000000000000), orderedInterval (35569418994 / 1000000000000) (35569433149 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (865711702007361 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23240898505 / 1000000000000) (-23240898504 / 1000000000000), orderedInterval (-48949898745 / 1000000000000) (-48949898744 / 1000000000000)))) (orderedInterval (-2413522703 / 1000000000000) (-2413520961 / 1000000000000))) = true
  rfl'

theorem compactCertificate274_chunkChecks2_1 :
    compactCertificate274.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1328224378634703 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7308734318 / 1000000000000) (-7308734303 / 1000000000000), orderedInterval (43182638972 / 1000000000000) (43182638987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (766850702548887 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-43681123088 / 1000000000000) (-43681123087 / 1000000000000), orderedInterval (-37471382245 / 1000000000000) (-37471382244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1360790028617283 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (42949060531 / 1000000000000) (42949061380 / 1000000000000), orderedInterval (-5230351013 / 1000000000000) (-5230350164 / 1000000000000)))) (orderedInterval (-32990815449 / 1000000000000) (-32990814538 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1271426561774127 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-43574600628 / 1000000000000) (-43574600623 / 1000000000000), orderedInterval (-10134585063 / 1000000000000) (-10134585058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (907349987600991 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (52434693309 / 1000000000000) (52434693319 / 1000000000000), orderedInterval (7440737075 / 1000000000000) (7440737084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1028838179695689 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18631598826 / 1000000000000) (18631598827 / 1000000000000), orderedInterval (46093690946 / 1000000000000) (46093690947 / 1000000000000)))) (orderedInterval (-14897916643 / 1000000000000) (-14897916592 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (857738012458041 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (54475764981 / 1000000000000) (54475765083 / 1000000000000), orderedInterval (-1228760764 / 1000000000000) (-1228760663 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (757837546590861 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (57053527536 / 1000000000000) (57053528217 / 1000000000000), orderedInterval (-10401189588 / 1000000000000) (-10401188907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (219650859139239 / 800000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-43165068448 / 1000000000000) (-43165046580 / 1000000000000), orderedInterval (21419545349 / 1000000000000) (21419567216 / 1000000000000)))) (orderedInterval (7769060607 / 1000000000000) (7769062626 / 1000000000000))) = true
  rfl'

theorem compactCertificate274_chunkChecks2_2 :
    compactCertificate274.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (607565835970533 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (61677846387 / 1000000000000) (61677848901 / 1000000000000), orderedInterval (-19878028461 / 1000000000000) (-19878025947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (515040287759613 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47371009333 / 1000000000000) (-47371009332 / 1000000000000), orderedInterval (-51779729051 / 1000000000000) (-51779729050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (322288297992639 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28423821361 / 1000000000000) (-28423820605 / 1000000000000), orderedInterval (84399021514 / 1000000000000) (84399022270 / 1000000000000)))) (orderedInterval (8525023657 / 1000000000000) (8525024121 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (173327718542913 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (15970309030 / 1000000000000) (15970309032 / 1000000000000), orderedInterval (119972285175 / 1000000000000) (119972285177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (470618472887739 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-59470791515 / 1000000000000) (-59470741443 / 1000000000000), orderedInterval (43543963247 / 1000000000000) (43544013319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (642589290317403 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-58913838654 / 1000000000000) (-58913838653 / 1000000000000), orderedInterval (-21997396157 / 1000000000000) (-21997396156 / 1000000000000)))) (orderedInterval (-6108442053 / 1000000000000) (-6108441317 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (271711702007361 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-38015422115 / 1000000000000) (-38015420091 / 1000000000000), orderedInterval (89313463803 / 1000000000000) (89313465827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1104492983677281 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20800538093 / 1000000000000) (20800538094 / 1000000000000), orderedInterval (43239393633 / 1000000000000) (43239393634 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (737750126403279 / 4000000000000) 2 (IntervalRat.scale (297 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7715992702 / 1000000000000) (7715992728 / 1000000000000), orderedInterval (-58263153464 / 1000000000000) (-58263153438 / 1000000000000)))) (orderedInterval (8086275156 / 1000000000000) (8086275253 / 1000000000000))) = true
  rfl'

theorem compactCertificate274_chunkChecks2 :
    compactCertificate274.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate274.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate274_chunkChecks2_0
    compactCertificate274_chunkChecks2_1 compactCertificate274_chunkChecks2_2

theorem compactCertificate274_chunkChecks3_0 :
    compactCertificate274.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (297 / 2) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-65361453423 / 1000000000000) (-65361453313 / 1000000000000), orderedInterval (4074692550 / 1000000000000) (4074692660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (437537711526597 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16122455065 / 1000000000000) (-16122455064 / 1000000000000), orderedInterval (-74492676798 / 1000000000000) (-74492676797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (141490706128101 / 800000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (59339050858 / 1000000000000) (59339051293 / 1000000000000), orderedInterval (-9020063743 / 1000000000000) (-9020063308 / 1000000000000)))) (orderedInterval (-585139477 / 1000000000000) (-585139374 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (127672412988879 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (135437909767 / 1000000000000) (135437909768 / 1000000000000), orderedInterval (37878059001 / 1000000000000) (37878059002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (342946059898563 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-85479231882 / 1000000000000) (-85479231701 / 1000000000000), orderedInterval (11383504815 / 1000000000000) (11383504996 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (931165265134071 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (46565370637 / 1000000000000) (46565370638 / 1000000000000), orderedInterval (23698842021 / 1000000000000) (23698842022 / 1000000000000)))) (orderedInterval (6351768718 / 1000000000000) (6351768762 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (685892119797423 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30797431192 / 1000000000000) (30797435781 / 1000000000000), orderedInterval (-52665257373 / 1000000000000) (-52665252784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1175287837929579 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30085574251 / 1000000000000) (-30085560097 / 1000000000000), orderedInterval (35569418994 / 1000000000000) (35569433149 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (865711702007361 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23240898505 / 1000000000000) (-23240898504 / 1000000000000), orderedInterval (-48949898745 / 1000000000000) (-48949898744 / 1000000000000)))) (orderedInterval (12176453802 / 1000000000000) (12176457243 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate274_chunkChecks3_1 :
    compactCertificate274.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1328224378634703 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7308734318 / 1000000000000) (-7308734303 / 1000000000000), orderedInterval (43182638972 / 1000000000000) (43182638987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (766850702548887 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-43681123088 / 1000000000000) (-43681123087 / 1000000000000), orderedInterval (-37471382245 / 1000000000000) (-37471382244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1360790028617283 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (42949060531 / 1000000000000) (42949061380 / 1000000000000), orderedInterval (-5230351013 / 1000000000000) (-5230350164 / 1000000000000)))) (orderedInterval (100921383574 / 1000000000000) (100921385633 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1271426561774127 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-43574600628 / 1000000000000) (-43574600623 / 1000000000000), orderedInterval (-10134585063 / 1000000000000) (-10134585058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (907349987600991 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (52434693309 / 1000000000000) (52434693319 / 1000000000000), orderedInterval (7440737075 / 1000000000000) (7440737084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1028838179695689 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18631598826 / 1000000000000) (18631598827 / 1000000000000), orderedInterval (46093690946 / 1000000000000) (46093690947 / 1000000000000)))) (orderedInterval (-2989627066 / 1000000000000) (-2989626981 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (857738012458041 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (54475764981 / 1000000000000) (54475765083 / 1000000000000), orderedInterval (-1228760764 / 1000000000000) (-1228760663 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (757837546590861 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (57053527536 / 1000000000000) (57053528217 / 1000000000000), orderedInterval (-10401189588 / 1000000000000) (-10401188907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (219650859139239 / 800000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-43165068448 / 1000000000000) (-43165046580 / 1000000000000), orderedInterval (21419545349 / 1000000000000) (21419567216 / 1000000000000)))) (orderedInterval (-4711912616 / 1000000000000) (-4711908932 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate274_chunkChecks3_2 :
    compactCertificate274.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (607565835970533 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (61677846387 / 1000000000000) (61677848901 / 1000000000000), orderedInterval (-19878028461 / 1000000000000) (-19878025947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (515040287759613 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47371009333 / 1000000000000) (-47371009332 / 1000000000000), orderedInterval (-51779729051 / 1000000000000) (-51779729050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (322288297992639 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28423821361 / 1000000000000) (-28423820605 / 1000000000000), orderedInterval (84399021514 / 1000000000000) (84399022270 / 1000000000000)))) (orderedInterval (-5807533952 / 1000000000000) (-5807533482 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (173327718542913 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (15970309030 / 1000000000000) (15970309032 / 1000000000000), orderedInterval (119972285175 / 1000000000000) (119972285177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (470618472887739 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-59470791515 / 1000000000000) (-59470741443 / 1000000000000), orderedInterval (43543963247 / 1000000000000) (43544013319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (642589290317403 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-58913838654 / 1000000000000) (-58913838653 / 1000000000000), orderedInterval (-21997396157 / 1000000000000) (-21997396156 / 1000000000000)))) (orderedInterval (-1546833881 / 1000000000000) (-1546833294 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (271711702007361 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-38015422115 / 1000000000000) (-38015420091 / 1000000000000), orderedInterval (89313463803 / 1000000000000) (89313465827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1104492983677281 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20800538093 / 1000000000000) (20800538094 / 1000000000000), orderedInterval (43239393633 / 1000000000000) (43239393634 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (737750126403279 / 4000000000000) 3 (IntervalRat.scale (297 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7715992702 / 1000000000000) (7715992728 / 1000000000000), orderedInterval (-58263153464 / 1000000000000) (-58263153438 / 1000000000000)))) (orderedInterval (1578318966 / 1000000000000) (1578319110 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate274_chunkChecks3 :
    compactCertificate274.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate274.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate274_chunkChecks3_0
    compactCertificate274_chunkChecks3_1 compactCertificate274_chunkChecks3_2

theorem compactCertificate274_chunkChecks4_0 :
    compactCertificate274.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (297 / 2) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-65361453423 / 1000000000000) (-65361453313 / 1000000000000), orderedInterval (4074692550 / 1000000000000) (4074692660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (437537711526597 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16122455065 / 1000000000000) (-16122455064 / 1000000000000), orderedInterval (-74492676798 / 1000000000000) (-74492676797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (141490706128101 / 800000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (59339050858 / 1000000000000) (59339051293 / 1000000000000), orderedInterval (-9020063743 / 1000000000000) (-9020063308 / 1000000000000)))) (orderedInterval (-18936142317 / 1000000000000) (-18936142202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (127672412988879 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (135437909767 / 1000000000000) (135437909768 / 1000000000000), orderedInterval (37878059001 / 1000000000000) (37878059002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (342946059898563 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-85479231882 / 1000000000000) (-85479231701 / 1000000000000), orderedInterval (11383504815 / 1000000000000) (11383504996 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (931165265134071 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (46565370637 / 1000000000000) (46565370638 / 1000000000000), orderedInterval (23698842021 / 1000000000000) (23698842022 / 1000000000000)))) (orderedInterval (-20425861491 / 1000000000000) (-20425861424 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (685892119797423 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (30797431192 / 1000000000000) (30797435781 / 1000000000000), orderedInterval (-52665257373 / 1000000000000) (-52665252784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1175287837929579 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30085574251 / 1000000000000) (-30085560097 / 1000000000000), orderedInterval (35569418994 / 1000000000000) (35569433149 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (865711702007361 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-23240898505 / 1000000000000) (-23240898504 / 1000000000000), orderedInterval (-48949898745 / 1000000000000) (-48949898744 / 1000000000000)))) (orderedInterval (11523673372 / 1000000000000) (11523680196 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate274_chunkChecks4_1 :
    compactCertificate274.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1328224378634703 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7308734318 / 1000000000000) (-7308734303 / 1000000000000), orderedInterval (43182638972 / 1000000000000) (43182638987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (766850702548887 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-43681123088 / 1000000000000) (-43681123087 / 1000000000000), orderedInterval (-37471382245 / 1000000000000) (-37471382244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1360790028617283 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (42949060531 / 1000000000000) (42949061380 / 1000000000000), orderedInterval (-5230351013 / 1000000000000) (-5230350164 / 1000000000000)))) (orderedInterval (190281738193 / 1000000000000) (190281742877 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1271426561774127 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-43574600628 / 1000000000000) (-43574600623 / 1000000000000), orderedInterval (-10134585063 / 1000000000000) (-10134585058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (907349987600991 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (52434693309 / 1000000000000) (52434693319 / 1000000000000), orderedInterval (7440737075 / 1000000000000) (7440737084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1028838179695689 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18631598826 / 1000000000000) (18631598827 / 1000000000000), orderedInterval (46093690946 / 1000000000000) (46093690947 / 1000000000000)))) (orderedInterval (42698777450 / 1000000000000) (42698777598 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (857738012458041 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (54475764981 / 1000000000000) (54475765083 / 1000000000000), orderedInterval (-1228760764 / 1000000000000) (-1228760663 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (757837546590861 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (57053527536 / 1000000000000) (57053528217 / 1000000000000), orderedInterval (-10401189588 / 1000000000000) (-10401188907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (219650859139239 / 800000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-43165068448 / 1000000000000) (-43165046580 / 1000000000000), orderedInterval (21419545349 / 1000000000000) (21419567216 / 1000000000000)))) (orderedInterval (-18766898289 / 1000000000000) (-18766891514 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate274_chunkChecks4_2 :
    compactCertificate274.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (607565835970533 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (61677846387 / 1000000000000) (61677848901 / 1000000000000), orderedInterval (-19878028461 / 1000000000000) (-19878025947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (515040287759613 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47371009333 / 1000000000000) (-47371009332 / 1000000000000), orderedInterval (-51779729051 / 1000000000000) (-51779729050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (322288297992639 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28423821361 / 1000000000000) (-28423820605 / 1000000000000), orderedInterval (84399021514 / 1000000000000) (84399022270 / 1000000000000)))) (orderedInterval (-9280179385 / 1000000000000) (-9280178905 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (173327718542913 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (15970309030 / 1000000000000) (15970309032 / 1000000000000), orderedInterval (119972285175 / 1000000000000) (119972285177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (470618472887739 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-59470791515 / 1000000000000) (-59470741443 / 1000000000000), orderedInterval (43543963247 / 1000000000000) (43544013319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (642589290317403 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-58913838654 / 1000000000000) (-58913838653 / 1000000000000), orderedInterval (-21997396157 / 1000000000000) (-21997396156 / 1000000000000)))) (orderedInterval (6733833399 / 1000000000000) (6733833872 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (271711702007361 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-38015422115 / 1000000000000) (-38015420091 / 1000000000000), orderedInterval (89313463803 / 1000000000000) (89313465827 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1104492983677281 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20800538093 / 1000000000000) (20800538094 / 1000000000000), orderedInterval (43239393633 / 1000000000000) (43239393634 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (737750126403279 / 4000000000000) 4 (IntervalRat.scale (297 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (7715992702 / 1000000000000) (7715992728 / 1000000000000), orderedInterval (-58263153464 / 1000000000000) (-58263153438 / 1000000000000)))) (orderedInterval (-23716019302 / 1000000000000) (-23716019076 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate274_chunkChecks4 :
    compactCertificate274.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate274.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate274_chunkChecks4_0
    compactCertificate274_chunkChecks4_1 compactCertificate274_chunkChecks4_2

theorem compactCertificate274_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate274.chunkCheck r b = true :=
  compactCertificate274.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate274_chunkChecks0
    · exact compactCertificate274_chunkChecks1
    · exact compactCertificate274_chunkChecks2
    · exact compactCertificate274_chunkChecks3
    · exact compactCertificate274_chunkChecks4)

theorem compactCertificate274_coefficient0 :
    compactCertificate274.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate274_coefficient1 :
    compactCertificate274.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate274_coefficient2 :
    compactCertificate274.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate274_coefficient3 :
    compactCertificate274.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate274_coefficient4 :
    compactCertificate274.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate274_coefficients : ∀ r : Fin 5,
    compactCertificate274.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate274_coefficient0
  · exact compactCertificate274_coefficient1
  · exact compactCertificate274_coefficient2
  · exact compactCertificate274_coefficient3
  · exact compactCertificate274_coefficient4

theorem compactCertificate274_lower : (1 : ℚ) ≤ compactCertificate274.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate274, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate274_proves {t : ℝ} (ht : t ∈ compactCertificate274.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate274.proves compactCertificate274_states compactCertificate274_chunks
    compactCertificate274_coefficients compactCertificate274_lower ht

end Erdos232
