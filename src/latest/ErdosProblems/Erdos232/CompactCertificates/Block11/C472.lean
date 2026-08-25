/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate472 : CompactCertificate where
  left := 343
  right := 344
  center := 687 / 2
  grid := fun i =>
    match i.val with
    | 0 => 109
    | 1 => 81
    | 2 => 130
    | 3 => 24
    | 4 => 63
    | 5 => 171
    | 6 => 126
    | 7 => 216
    | 8 => 159
    | 9 => 245
    | 10 => 141
    | 11 => 251
    | 12 => 234
    | 13 => 167
    | 14 => 189
    | 15 => 158
    | 16 => 140
    | 17 => 202
    | 18 => 112
    | 19 => 95
    | 20 => 59
    | 21 => 32
    | 22 => 87
    | 23 => 118
    | 24 => 50
    | 25 => 203
    | _ => 136
  point := fun i =>
    match i.val with
    | 0 => 687 / 2
    | 1 => 1012082181207987 / 4000000000000
    | 2 => 327286582861971 / 800000000000
    | 3 => 295323056307609 / 4000000000000
    | 4 => 793279269866373 / 4000000000000
    | 5 => 2153907532481841 / 4000000000000
    | 6 => 1586558539733433 / 4000000000000
    | 7 => 2718595099857309 / 4000000000000
    | 8 => 2002504846057431 / 4000000000000
    | 9 => 3072357401084313 / 4000000000000
    | 10 => 1773826372562577 / 4000000000000
    | 11 => 3147686025791493 / 4000000000000
    | 12 => 2940976592386617 / 4000000000000
    | 13 => 2098819668289161 / 4000000000000
    | 14 => 2379837809599119 / 4000000000000
    | 15 => 1984060655079711 / 4000000000000
    | 16 => 1752977759285931 / 4000000000000
    | 17 => 508081280231169 / 800000000000
    | 18 => 1405379559972243 / 4000000000000
    | 19 => 1191355817140923 / 4000000000000
    | 20 => 745495153942569 / 4000000000000
    | 21 => 400929773195223 / 4000000000000
    | 22 => 1088602326174669 / 4000000000000
    | 23 => 1486393408916013 / 4000000000000
    | 24 => 628504846057431 / 4000000000000
    | 25 => 2554837305677751 / 4000000000000
    | _ => 1706512918650009 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-41366146885 / 1000000000000) (-41366141621 / 1000000000000), orderedInterval (11983846550 / 1000000000000) (11983851814 / 1000000000000))
    | 1 => (orderedInterval (30894930755 / 1000000000000) (30894942556 / 1000000000000), orderedInterval (-39577932882 / 1000000000000) (-39577921081 / 1000000000000))
    | 2 => (orderedInterval (39306802617 / 1000000000000) (39306802710 / 1000000000000), orderedInterval (3282111146 / 1000000000000) (3282111239 / 1000000000000))
    | 3 => (orderedInterval (-65552095024 / 1000000000000) (-65552014685 / 1000000000000), orderedInterval (66213303306 / 1000000000000) (66213383645 / 1000000000000))
    | 4 => (orderedInterval (-52476945088 / 1000000000000) (-52476945087 / 1000000000000), orderedInterval (-21227221376 / 1000000000000) (-21227221375 / 1000000000000))
    | 5 => (orderedInterval (-30515781397 / 1000000000000) (-30515695676 / 1000000000000), orderedInterval (15872833382 / 1000000000000) (15872919103 / 1000000000000))
    | 6 => (orderedInterval (40059333932 / 1000000000000) (40059334252 / 1000000000000), orderedInterval (-581206804 / 1000000000000) (-581206484 / 1000000000000))
    | 7 => (orderedInterval (29420377934 / 1000000000000) (29420405585 / 1000000000000), orderedInterval (-8455498010 / 1000000000000) (-8455470359 / 1000000000000))
    | 8 => (orderedInterval (-33766733231 / 1000000000000) (-33766714674 / 1000000000000), orderedInterval (11499086207 / 1000000000000) (11499104764 / 1000000000000))
    | 9 => (orderedInterval (20962983757 / 1000000000000) (20962987613 / 1000000000000), orderedInterval (-19746584664 / 1000000000000) (-19746580808 / 1000000000000))
    | 10 => (orderedInterval (-36267205219 / 1000000000000) (-36267205214 / 1000000000000), orderedInterval (-10926076231 / 1000000000000) (-10926076225 / 1000000000000))
    | 11 => (orderedInterval (21046615706 / 1000000000000) (21046619899 / 1000000000000), orderedInterval (-19145552147 / 1000000000000) (-19145547953 / 1000000000000))
    | 12 => (orderedInterval (22989233191 / 1000000000000) (22989233192 / 1000000000000), orderedInterval (18351642771 / 1000000000000) (18351642772 / 1000000000000))
    | 13 => (orderedInterval (-26032840146 / 1000000000000) (-26032840145 / 1000000000000), orderedInterval (-23117841955 / 1000000000000) (-23117841954 / 1000000000000))
    | 14 => (orderedInterval (-29963086115 / 1000000000000) (-29963023902 / 1000000000000), orderedInterval (13149064042 / 1000000000000) (13149126255 / 1000000000000))
    | 15 => (orderedInterval (14891310199 / 1000000000000) (14891310200 / 1000000000000), orderedInterval (32568998563 / 1000000000000) (32568998564 / 1000000000000))
    | 16 => (orderedInterval (-27165790635 / 1000000000000) (-27165773873 / 1000000000000), orderedInterval (26764472568 / 1000000000000) (26764489330 / 1000000000000))
    | 17 => (orderedInterval (30377077018 / 1000000000000) (30377077044 / 1000000000000), orderedInterval (8899277654 / 1000000000000) (8899277680 / 1000000000000))
    | 18 => (orderedInterval (11417743725 / 1000000000000) (11417743726 / 1000000000000), orderedInterval (40990919492 / 1000000000000) (40990919493 / 1000000000000))
    | 19 => (orderedInterval (-7941594762 / 1000000000000) (-7941594761 / 1000000000000), orderedInterval (-45532216634 / 1000000000000) (-45532216633 / 1000000000000))
    | 20 => (orderedInterval (-56855460498 / 1000000000000) (-56855459193 / 1000000000000), orderedInterval (13690186369 / 1000000000000) (13690187673 / 1000000000000))
    | 21 => (orderedInterval (37199033134 / 1000000000000) (37199033135 / 1000000000000), orderedInterval (70296429673 / 1000000000000) (70296429674 / 1000000000000))
    | 22 => (orderedInterval (18076207884 / 1000000000000) (18076208353 / 1000000000000), orderedInterval (-44893798570 / 1000000000000) (-44893798100 / 1000000000000))
    | 23 => (orderedInterval (41164128550 / 1000000000000) (41164129408 / 1000000000000), orderedInterval (-4380451628 / 1000000000000) (-4380450771 / 1000000000000))
    | 24 => (orderedInterval (47021807986 / 1000000000000) (47021807987 / 1000000000000), orderedInterval (42752510732 / 1000000000000) (42752510733 / 1000000000000))
    | 25 => (orderedInterval (-31058536903 / 1000000000000) (-31058528163 / 1000000000000), orderedInterval (5689619114 / 1000000000000) (5689627854 / 1000000000000))
    | _ => (orderedInterval (6029740302 / 1000000000000) (6029740303 / 1000000000000), orderedInterval (38148604235 / 1000000000000) (38148604236 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-13801643727 / 1000000000000) (-13801641501 / 1000000000000)
      | 1 => orderedInterval (964517823 / 1000000000000) (964524830 / 1000000000000)
      | 2 => orderedInterval (-1723518350 / 1000000000000) (-1723517028 / 1000000000000)
      | 3 => orderedInterval (-3420070895 / 1000000000000) (-3420069477 / 1000000000000)
      | 4 => orderedInterval (-2725136439 / 1000000000000) (-2725136083 / 1000000000000)
      | 5 => orderedInterval (2504340047 / 1000000000000) (2504341041 / 1000000000000)
      | 6 => orderedInterval (-3227061980 / 1000000000000) (-3227061851 / 1000000000000)
      | 7 => orderedInterval (-4251749327 / 1000000000000) (-4251749209 / 1000000000000)
      | _ => orderedInterval (1680342986 / 1000000000000) (1680343793 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (4707712618 / 1000000000000) (4707714820 / 1000000000000)
      | 1 => orderedInterval (-2370775649 / 1000000000000) (-2370765862 / 1000000000000)
      | 2 => orderedInterval (921053574 / 1000000000000) (921055949 / 1000000000000)
      | 3 => orderedInterval (565640628 / 1000000000000) (565643809 / 1000000000000)
      | 4 => orderedInterval (-4163699902 / 1000000000000) (-4163699289 / 1000000000000)
      | 5 => orderedInterval (-989730628 / 1000000000000) (-989729355 / 1000000000000)
      | 6 => orderedInterval (-4227456520 / 1000000000000) (-4227456416 / 1000000000000)
      | 7 => orderedInterval (791355522 / 1000000000000) (791355639 / 1000000000000)
      | _ => orderedInterval (-9633166542 / 1000000000000) (-9633165085 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (12954370361 / 1000000000000) (12954372553 / 1000000000000)
      | 1 => orderedInterval (-4718312963 / 1000000000000) (-4718297854 / 1000000000000)
      | 2 => orderedInterval (5283241930 / 1000000000000) (5283246288 / 1000000000000)
      | 3 => orderedInterval (7399143255 / 1000000000000) (7399150423 / 1000000000000)
      | 4 => orderedInterval (7202742909 / 1000000000000) (7202743966 / 1000000000000)
      | 5 => orderedInterval (-5544945931 / 1000000000000) (-5544944293 / 1000000000000)
      | 6 => orderedInterval (2129213016 / 1000000000000) (2129213105 / 1000000000000)
      | 7 => orderedInterval (4005607601 / 1000000000000) (4005607722 / 1000000000000)
      | _ => orderedInterval (-7027231058 / 1000000000000) (-7027228397 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-4965639706 / 1000000000000) (-4965637524 / 1000000000000)
      | 1 => orderedInterval (4516926967 / 1000000000000) (4516950593 / 1000000000000)
      | 2 => orderedInterval (-2895852726 / 1000000000000) (-2895844610 / 1000000000000)
      | 3 => orderedInterval (-4785974681 / 1000000000000) (-4785958507 / 1000000000000)
      | 4 => orderedInterval (11365407212 / 1000000000000) (11365409038 / 1000000000000)
      | 5 => orderedInterval (624289381 / 1000000000000) (624291491 / 1000000000000)
      | 6 => orderedInterval (5256141147 / 1000000000000) (5256141228 / 1000000000000)
      | 7 => orderedInterval (-910957896 / 1000000000000) (-910957769 / 1000000000000)
      | _ => orderedInterval (16686456133 / 1000000000000) (16686461018 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-11641316712 / 1000000000000) (-11641314527 / 1000000000000)
      | 1 => orderedInterval (12862877547 / 1000000000000) (12862914636 / 1000000000000)
      | 2 => orderedInterval (-17572589753 / 1000000000000) (-17572574412 / 1000000000000)
      | 3 => orderedInterval (-18150661116 / 1000000000000) (-18150624540 / 1000000000000)
      | 4 => orderedInterval (-20815795113 / 1000000000000) (-20815791946 / 1000000000000)
      | 5 => orderedInterval (13951909442 / 1000000000000) (13951912176 / 1000000000000)
      | 6 => orderedInterval (-1935115047 / 1000000000000) (-1935114970 / 1000000000000)
      | 7 => orderedInterval (-4481951489 / 1000000000000) (-4481951354 / 1000000000000)
      | _ => orderedInterval (27444972782 / 1000000000000) (27444981802 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-23999979862 / 1000000000000) (-23999965485 / 1000000000000)
    | 1 => orderedInterval (-14399066899 / 1000000000000) (-14399045790 / 1000000000000)
    | 2 => orderedInterval (21683829120 / 1000000000000) (21683863513 / 1000000000000)
    | 3 => orderedInterval (24890795831 / 1000000000000) (24890854958 / 1000000000000)
    | _ => orderedInterval (-20337669459 / 1000000000000) (-20337563135 / 1000000000000)

theorem compactCertificate472_stateChecks0 :
    compactCertificate472.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (687 / 2)) (orderedInterval (-41366146885 / 1000000000000) (-41366141621 / 1000000000000), orderedInterval (11983846550 / 1000000000000) (11983851814 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1012082181207987 / 4000000000000)) (orderedInterval (30894930755 / 1000000000000) (30894942556 / 1000000000000), orderedInterval (-39577932882 / 1000000000000) (-39577921081 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (327286582861971 / 800000000000)) (orderedInterval (39306802617 / 1000000000000) (39306802710 / 1000000000000), orderedInterval (3282111146 / 1000000000000) (3282111239 / 1000000000000))) = true
  rfl'

theorem compactCertificate472_stateChecks1 :
    compactCertificate472.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (295323056307609 / 4000000000000)) (orderedInterval (-65552095024 / 1000000000000) (-65552014685 / 1000000000000), orderedInterval (66213303306 / 1000000000000) (66213383645 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (793279269866373 / 4000000000000)) (orderedInterval (-52476945088 / 1000000000000) (-52476945087 / 1000000000000), orderedInterval (-21227221376 / 1000000000000) (-21227221375 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2153907532481841 / 4000000000000)) (orderedInterval (-30515781397 / 1000000000000) (-30515695676 / 1000000000000), orderedInterval (15872833382 / 1000000000000) (15872919103 / 1000000000000))) = true
  rfl'

theorem compactCertificate472_stateChecks2 :
    compactCertificate472.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1586558539733433 / 4000000000000)) (orderedInterval (40059333932 / 1000000000000) (40059334252 / 1000000000000), orderedInterval (-581206804 / 1000000000000) (-581206484 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (2718595099857309 / 4000000000000)) (orderedInterval (29420377934 / 1000000000000) (29420405585 / 1000000000000), orderedInterval (-8455498010 / 1000000000000) (-8455470359 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (2002504846057431 / 4000000000000)) (orderedInterval (-33766733231 / 1000000000000) (-33766714674 / 1000000000000), orderedInterval (11499086207 / 1000000000000) (11499104764 / 1000000000000))) = true
  rfl'

theorem compactCertificate472_stateChecks3 :
    compactCertificate472.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 245 12 (3072357401084313 / 4000000000000)) (orderedInterval (20962983757 / 1000000000000) (20962987613 / 1000000000000), orderedInterval (-19746584664 / 1000000000000) (-19746580808 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1773826372562577 / 4000000000000)) (orderedInterval (-36267205219 / 1000000000000) (-36267205214 / 1000000000000), orderedInterval (-10926076231 / 1000000000000) (-10926076225 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 251 12 (3147686025791493 / 4000000000000)) (orderedInterval (21046615706 / 1000000000000) (21046619899 / 1000000000000), orderedInterval (-19145552147 / 1000000000000) (-19145547953 / 1000000000000))) = true
  rfl'

theorem compactCertificate472_stateChecks4 :
    compactCertificate472.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 234 12 (2940976592386617 / 4000000000000)) (orderedInterval (22989233191 / 1000000000000) (22989233192 / 1000000000000), orderedInterval (18351642771 / 1000000000000) (18351642772 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2098819668289161 / 4000000000000)) (orderedInterval (-26032840146 / 1000000000000) (-26032840145 / 1000000000000), orderedInterval (-23117841955 / 1000000000000) (-23117841954 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2379837809599119 / 4000000000000)) (orderedInterval (-29963086115 / 1000000000000) (-29963023902 / 1000000000000), orderedInterval (13149064042 / 1000000000000) (13149126255 / 1000000000000))) = true
  rfl'

theorem compactCertificate472_stateChecks5 :
    compactCertificate472.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1984060655079711 / 4000000000000)) (orderedInterval (14891310199 / 1000000000000) (14891310200 / 1000000000000), orderedInterval (32568998563 / 1000000000000) (32568998564 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1752977759285931 / 4000000000000)) (orderedInterval (-27165790635 / 1000000000000) (-27165773873 / 1000000000000), orderedInterval (26764472568 / 1000000000000) (26764489330 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (508081280231169 / 800000000000)) (orderedInterval (30377077018 / 1000000000000) (30377077044 / 1000000000000), orderedInterval (8899277654 / 1000000000000) (8899277680 / 1000000000000))) = true
  rfl'

theorem compactCertificate472_stateChecks6 :
    compactCertificate472.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1405379559972243 / 4000000000000)) (orderedInterval (11417743725 / 1000000000000) (11417743726 / 1000000000000), orderedInterval (40990919492 / 1000000000000) (40990919493 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1191355817140923 / 4000000000000)) (orderedInterval (-7941594762 / 1000000000000) (-7941594761 / 1000000000000), orderedInterval (-45532216634 / 1000000000000) (-45532216633 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (745495153942569 / 4000000000000)) (orderedInterval (-56855460498 / 1000000000000) (-56855459193 / 1000000000000), orderedInterval (13690186369 / 1000000000000) (13690187673 / 1000000000000))) = true
  rfl'

theorem compactCertificate472_stateChecks7 :
    compactCertificate472.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (400929773195223 / 4000000000000)) (orderedInterval (37199033134 / 1000000000000) (37199033135 / 1000000000000), orderedInterval (70296429673 / 1000000000000) (70296429674 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1088602326174669 / 4000000000000)) (orderedInterval (18076207884 / 1000000000000) (18076208353 / 1000000000000), orderedInterval (-44893798570 / 1000000000000) (-44893798100 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1486393408916013 / 4000000000000)) (orderedInterval (41164128550 / 1000000000000) (41164129408 / 1000000000000), orderedInterval (-4380451628 / 1000000000000) (-4380450771 / 1000000000000))) = true
  rfl'

theorem compactCertificate472_stateChecks8 :
    compactCertificate472.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (628504846057431 / 4000000000000)) (orderedInterval (47021807986 / 1000000000000) (47021807987 / 1000000000000), orderedInterval (42752510732 / 1000000000000) (42752510733 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (2554837305677751 / 4000000000000)) (orderedInterval (-31058536903 / 1000000000000) (-31058528163 / 1000000000000), orderedInterval (5689619114 / 1000000000000) (5689627854 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1706512918650009 / 4000000000000)) (orderedInterval (6029740302 / 1000000000000) (6029740303 / 1000000000000), orderedInterval (38148604235 / 1000000000000) (38148604236 / 1000000000000))) = true
  rfl'

theorem compactCertificate472_states : ∀ j,
    BesselStateValid (compactCertificate472.point j) (compactCertificate472.state j) :=
  compactCertificate472.statesValid_of_checks3 compactCertificate472_stateChecks0
    compactCertificate472_stateChecks1 compactCertificate472_stateChecks2
    compactCertificate472_stateChecks3 compactCertificate472_stateChecks4
    compactCertificate472_stateChecks5 compactCertificate472_stateChecks6
    compactCertificate472_stateChecks7 compactCertificate472_stateChecks8

theorem compactCertificate472_chunkChecks0_0 :
    compactCertificate472.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (687 / 2) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-41366146885 / 1000000000000) (-41366141621 / 1000000000000), orderedInterval (11983846550 / 1000000000000) (11983851814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1012082181207987 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (30894930755 / 1000000000000) (30894942556 / 1000000000000), orderedInterval (-39577932882 / 1000000000000) (-39577921081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (327286582861971 / 800000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39306802617 / 1000000000000) (39306802710 / 1000000000000), orderedInterval (3282111146 / 1000000000000) (3282111239 / 1000000000000)))) (orderedInterval (-13801643727 / 1000000000000) (-13801641501 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (295323056307609 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-65552095024 / 1000000000000) (-65552014685 / 1000000000000), orderedInterval (66213303306 / 1000000000000) (66213383645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (793279269866373 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52476945088 / 1000000000000) (-52476945087 / 1000000000000), orderedInterval (-21227221376 / 1000000000000) (-21227221375 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2153907532481841 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30515781397 / 1000000000000) (-30515695676 / 1000000000000), orderedInterval (15872833382 / 1000000000000) (15872919103 / 1000000000000)))) (orderedInterval (964517823 / 1000000000000) (964524830 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1586558539733433 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40059333932 / 1000000000000) (40059334252 / 1000000000000), orderedInterval (-581206804 / 1000000000000) (-581206484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2718595099857309 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29420377934 / 1000000000000) (29420405585 / 1000000000000), orderedInterval (-8455498010 / 1000000000000) (-8455470359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2002504846057431 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33766733231 / 1000000000000) (-33766714674 / 1000000000000), orderedInterval (11499086207 / 1000000000000) (11499104764 / 1000000000000)))) (orderedInterval (-1723518350 / 1000000000000) (-1723517028 / 1000000000000))) = true
  rfl'

theorem compactCertificate472_chunkChecks0_1 :
    compactCertificate472.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3072357401084313 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20962983757 / 1000000000000) (20962987613 / 1000000000000), orderedInterval (-19746584664 / 1000000000000) (-19746580808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1773826372562577 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-36267205219 / 1000000000000) (-36267205214 / 1000000000000), orderedInterval (-10926076231 / 1000000000000) (-10926076225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3147686025791493 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21046615706 / 1000000000000) (21046619899 / 1000000000000), orderedInterval (-19145552147 / 1000000000000) (-19145547953 / 1000000000000)))) (orderedInterval (-3420070895 / 1000000000000) (-3420069477 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2940976592386617 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22989233191 / 1000000000000) (22989233192 / 1000000000000), orderedInterval (18351642771 / 1000000000000) (18351642772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2098819668289161 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26032840146 / 1000000000000) (-26032840145 / 1000000000000), orderedInterval (-23117841955 / 1000000000000) (-23117841954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2379837809599119 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29963086115 / 1000000000000) (-29963023902 / 1000000000000), orderedInterval (13149064042 / 1000000000000) (13149126255 / 1000000000000)))) (orderedInterval (-2725136439 / 1000000000000) (-2725136083 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1984060655079711 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14891310199 / 1000000000000) (14891310200 / 1000000000000), orderedInterval (32568998563 / 1000000000000) (32568998564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1752977759285931 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27165790635 / 1000000000000) (-27165773873 / 1000000000000), orderedInterval (26764472568 / 1000000000000) (26764489330 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (508081280231169 / 800000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30377077018 / 1000000000000) (30377077044 / 1000000000000), orderedInterval (8899277654 / 1000000000000) (8899277680 / 1000000000000)))) (orderedInterval (2504340047 / 1000000000000) (2504341041 / 1000000000000))) = true
  rfl'

theorem compactCertificate472_chunkChecks0_2 :
    compactCertificate472.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1405379559972243 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (11417743725 / 1000000000000) (11417743726 / 1000000000000), orderedInterval (40990919492 / 1000000000000) (40990919493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1191355817140923 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7941594762 / 1000000000000) (-7941594761 / 1000000000000), orderedInterval (-45532216634 / 1000000000000) (-45532216633 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (745495153942569 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-56855460498 / 1000000000000) (-56855459193 / 1000000000000), orderedInterval (13690186369 / 1000000000000) (13690187673 / 1000000000000)))) (orderedInterval (-3227061980 / 1000000000000) (-3227061851 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (400929773195223 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37199033134 / 1000000000000) (37199033135 / 1000000000000), orderedInterval (70296429673 / 1000000000000) (70296429674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1088602326174669 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18076207884 / 1000000000000) (18076208353 / 1000000000000), orderedInterval (-44893798570 / 1000000000000) (-44893798100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1486393408916013 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41164128550 / 1000000000000) (41164129408 / 1000000000000), orderedInterval (-4380451628 / 1000000000000) (-4380450771 / 1000000000000)))) (orderedInterval (-4251749327 / 1000000000000) (-4251749209 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (628504846057431 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47021807986 / 1000000000000) (47021807987 / 1000000000000), orderedInterval (42752510732 / 1000000000000) (42752510733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2554837305677751 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31058536903 / 1000000000000) (-31058528163 / 1000000000000), orderedInterval (5689619114 / 1000000000000) (5689627854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1706512918650009 / 4000000000000) 0 (IntervalRat.scale (687 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (6029740302 / 1000000000000) (6029740303 / 1000000000000), orderedInterval (38148604235 / 1000000000000) (38148604236 / 1000000000000)))) (orderedInterval (1680342986 / 1000000000000) (1680343793 / 1000000000000))) = true
  rfl'

theorem compactCertificate472_chunkChecks0 :
    compactCertificate472.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate472.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate472_chunkChecks0_0
    compactCertificate472_chunkChecks0_1 compactCertificate472_chunkChecks0_2

theorem compactCertificate472_chunkChecks1_0 :
    compactCertificate472.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (687 / 2) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-41366146885 / 1000000000000) (-41366141621 / 1000000000000), orderedInterval (11983846550 / 1000000000000) (11983851814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1012082181207987 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (30894930755 / 1000000000000) (30894942556 / 1000000000000), orderedInterval (-39577932882 / 1000000000000) (-39577921081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (327286582861971 / 800000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39306802617 / 1000000000000) (39306802710 / 1000000000000), orderedInterval (3282111146 / 1000000000000) (3282111239 / 1000000000000)))) (orderedInterval (4707712618 / 1000000000000) (4707714820 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (295323056307609 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-65552095024 / 1000000000000) (-65552014685 / 1000000000000), orderedInterval (66213303306 / 1000000000000) (66213383645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (793279269866373 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52476945088 / 1000000000000) (-52476945087 / 1000000000000), orderedInterval (-21227221376 / 1000000000000) (-21227221375 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2153907532481841 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30515781397 / 1000000000000) (-30515695676 / 1000000000000), orderedInterval (15872833382 / 1000000000000) (15872919103 / 1000000000000)))) (orderedInterval (-2370775649 / 1000000000000) (-2370765862 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1586558539733433 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40059333932 / 1000000000000) (40059334252 / 1000000000000), orderedInterval (-581206804 / 1000000000000) (-581206484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2718595099857309 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29420377934 / 1000000000000) (29420405585 / 1000000000000), orderedInterval (-8455498010 / 1000000000000) (-8455470359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2002504846057431 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33766733231 / 1000000000000) (-33766714674 / 1000000000000), orderedInterval (11499086207 / 1000000000000) (11499104764 / 1000000000000)))) (orderedInterval (921053574 / 1000000000000) (921055949 / 1000000000000))) = true
  rfl'

theorem compactCertificate472_chunkChecks1_1 :
    compactCertificate472.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3072357401084313 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20962983757 / 1000000000000) (20962987613 / 1000000000000), orderedInterval (-19746584664 / 1000000000000) (-19746580808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1773826372562577 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-36267205219 / 1000000000000) (-36267205214 / 1000000000000), orderedInterval (-10926076231 / 1000000000000) (-10926076225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3147686025791493 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21046615706 / 1000000000000) (21046619899 / 1000000000000), orderedInterval (-19145552147 / 1000000000000) (-19145547953 / 1000000000000)))) (orderedInterval (565640628 / 1000000000000) (565643809 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2940976592386617 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22989233191 / 1000000000000) (22989233192 / 1000000000000), orderedInterval (18351642771 / 1000000000000) (18351642772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2098819668289161 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26032840146 / 1000000000000) (-26032840145 / 1000000000000), orderedInterval (-23117841955 / 1000000000000) (-23117841954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2379837809599119 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29963086115 / 1000000000000) (-29963023902 / 1000000000000), orderedInterval (13149064042 / 1000000000000) (13149126255 / 1000000000000)))) (orderedInterval (-4163699902 / 1000000000000) (-4163699289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1984060655079711 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14891310199 / 1000000000000) (14891310200 / 1000000000000), orderedInterval (32568998563 / 1000000000000) (32568998564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1752977759285931 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27165790635 / 1000000000000) (-27165773873 / 1000000000000), orderedInterval (26764472568 / 1000000000000) (26764489330 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (508081280231169 / 800000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30377077018 / 1000000000000) (30377077044 / 1000000000000), orderedInterval (8899277654 / 1000000000000) (8899277680 / 1000000000000)))) (orderedInterval (-989730628 / 1000000000000) (-989729355 / 1000000000000))) = true
  rfl'

theorem compactCertificate472_chunkChecks1_2 :
    compactCertificate472.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1405379559972243 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (11417743725 / 1000000000000) (11417743726 / 1000000000000), orderedInterval (40990919492 / 1000000000000) (40990919493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1191355817140923 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7941594762 / 1000000000000) (-7941594761 / 1000000000000), orderedInterval (-45532216634 / 1000000000000) (-45532216633 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (745495153942569 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-56855460498 / 1000000000000) (-56855459193 / 1000000000000), orderedInterval (13690186369 / 1000000000000) (13690187673 / 1000000000000)))) (orderedInterval (-4227456520 / 1000000000000) (-4227456416 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (400929773195223 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37199033134 / 1000000000000) (37199033135 / 1000000000000), orderedInterval (70296429673 / 1000000000000) (70296429674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1088602326174669 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18076207884 / 1000000000000) (18076208353 / 1000000000000), orderedInterval (-44893798570 / 1000000000000) (-44893798100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1486393408916013 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41164128550 / 1000000000000) (41164129408 / 1000000000000), orderedInterval (-4380451628 / 1000000000000) (-4380450771 / 1000000000000)))) (orderedInterval (791355522 / 1000000000000) (791355639 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (628504846057431 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47021807986 / 1000000000000) (47021807987 / 1000000000000), orderedInterval (42752510732 / 1000000000000) (42752510733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2554837305677751 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31058536903 / 1000000000000) (-31058528163 / 1000000000000), orderedInterval (5689619114 / 1000000000000) (5689627854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1706512918650009 / 4000000000000) 1 (IntervalRat.scale (687 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (6029740302 / 1000000000000) (6029740303 / 1000000000000), orderedInterval (38148604235 / 1000000000000) (38148604236 / 1000000000000)))) (orderedInterval (-9633166542 / 1000000000000) (-9633165085 / 1000000000000))) = true
  rfl'

theorem compactCertificate472_chunkChecks1 :
    compactCertificate472.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate472.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate472_chunkChecks1_0
    compactCertificate472_chunkChecks1_1 compactCertificate472_chunkChecks1_2

theorem compactCertificate472_chunkChecks2_0 :
    compactCertificate472.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (687 / 2) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-41366146885 / 1000000000000) (-41366141621 / 1000000000000), orderedInterval (11983846550 / 1000000000000) (11983851814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1012082181207987 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (30894930755 / 1000000000000) (30894942556 / 1000000000000), orderedInterval (-39577932882 / 1000000000000) (-39577921081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (327286582861971 / 800000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39306802617 / 1000000000000) (39306802710 / 1000000000000), orderedInterval (3282111146 / 1000000000000) (3282111239 / 1000000000000)))) (orderedInterval (12954370361 / 1000000000000) (12954372553 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (295323056307609 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-65552095024 / 1000000000000) (-65552014685 / 1000000000000), orderedInterval (66213303306 / 1000000000000) (66213383645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (793279269866373 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52476945088 / 1000000000000) (-52476945087 / 1000000000000), orderedInterval (-21227221376 / 1000000000000) (-21227221375 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2153907532481841 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30515781397 / 1000000000000) (-30515695676 / 1000000000000), orderedInterval (15872833382 / 1000000000000) (15872919103 / 1000000000000)))) (orderedInterval (-4718312963 / 1000000000000) (-4718297854 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1586558539733433 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40059333932 / 1000000000000) (40059334252 / 1000000000000), orderedInterval (-581206804 / 1000000000000) (-581206484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2718595099857309 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29420377934 / 1000000000000) (29420405585 / 1000000000000), orderedInterval (-8455498010 / 1000000000000) (-8455470359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2002504846057431 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33766733231 / 1000000000000) (-33766714674 / 1000000000000), orderedInterval (11499086207 / 1000000000000) (11499104764 / 1000000000000)))) (orderedInterval (5283241930 / 1000000000000) (5283246288 / 1000000000000))) = true
  rfl'

theorem compactCertificate472_chunkChecks2_1 :
    compactCertificate472.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3072357401084313 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20962983757 / 1000000000000) (20962987613 / 1000000000000), orderedInterval (-19746584664 / 1000000000000) (-19746580808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1773826372562577 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-36267205219 / 1000000000000) (-36267205214 / 1000000000000), orderedInterval (-10926076231 / 1000000000000) (-10926076225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3147686025791493 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21046615706 / 1000000000000) (21046619899 / 1000000000000), orderedInterval (-19145552147 / 1000000000000) (-19145547953 / 1000000000000)))) (orderedInterval (7399143255 / 1000000000000) (7399150423 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2940976592386617 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22989233191 / 1000000000000) (22989233192 / 1000000000000), orderedInterval (18351642771 / 1000000000000) (18351642772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2098819668289161 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26032840146 / 1000000000000) (-26032840145 / 1000000000000), orderedInterval (-23117841955 / 1000000000000) (-23117841954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2379837809599119 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29963086115 / 1000000000000) (-29963023902 / 1000000000000), orderedInterval (13149064042 / 1000000000000) (13149126255 / 1000000000000)))) (orderedInterval (7202742909 / 1000000000000) (7202743966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1984060655079711 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14891310199 / 1000000000000) (14891310200 / 1000000000000), orderedInterval (32568998563 / 1000000000000) (32568998564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1752977759285931 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27165790635 / 1000000000000) (-27165773873 / 1000000000000), orderedInterval (26764472568 / 1000000000000) (26764489330 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (508081280231169 / 800000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30377077018 / 1000000000000) (30377077044 / 1000000000000), orderedInterval (8899277654 / 1000000000000) (8899277680 / 1000000000000)))) (orderedInterval (-5544945931 / 1000000000000) (-5544944293 / 1000000000000))) = true
  rfl'

theorem compactCertificate472_chunkChecks2_2 :
    compactCertificate472.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1405379559972243 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (11417743725 / 1000000000000) (11417743726 / 1000000000000), orderedInterval (40990919492 / 1000000000000) (40990919493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1191355817140923 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7941594762 / 1000000000000) (-7941594761 / 1000000000000), orderedInterval (-45532216634 / 1000000000000) (-45532216633 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (745495153942569 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-56855460498 / 1000000000000) (-56855459193 / 1000000000000), orderedInterval (13690186369 / 1000000000000) (13690187673 / 1000000000000)))) (orderedInterval (2129213016 / 1000000000000) (2129213105 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (400929773195223 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37199033134 / 1000000000000) (37199033135 / 1000000000000), orderedInterval (70296429673 / 1000000000000) (70296429674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1088602326174669 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18076207884 / 1000000000000) (18076208353 / 1000000000000), orderedInterval (-44893798570 / 1000000000000) (-44893798100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1486393408916013 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41164128550 / 1000000000000) (41164129408 / 1000000000000), orderedInterval (-4380451628 / 1000000000000) (-4380450771 / 1000000000000)))) (orderedInterval (4005607601 / 1000000000000) (4005607722 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (628504846057431 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47021807986 / 1000000000000) (47021807987 / 1000000000000), orderedInterval (42752510732 / 1000000000000) (42752510733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2554837305677751 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31058536903 / 1000000000000) (-31058528163 / 1000000000000), orderedInterval (5689619114 / 1000000000000) (5689627854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1706512918650009 / 4000000000000) 2 (IntervalRat.scale (687 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (6029740302 / 1000000000000) (6029740303 / 1000000000000), orderedInterval (38148604235 / 1000000000000) (38148604236 / 1000000000000)))) (orderedInterval (-7027231058 / 1000000000000) (-7027228397 / 1000000000000))) = true
  rfl'

theorem compactCertificate472_chunkChecks2 :
    compactCertificate472.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate472.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate472_chunkChecks2_0
    compactCertificate472_chunkChecks2_1 compactCertificate472_chunkChecks2_2

theorem compactCertificate472_chunkChecks3_0 :
    compactCertificate472.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (687 / 2) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-41366146885 / 1000000000000) (-41366141621 / 1000000000000), orderedInterval (11983846550 / 1000000000000) (11983851814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1012082181207987 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (30894930755 / 1000000000000) (30894942556 / 1000000000000), orderedInterval (-39577932882 / 1000000000000) (-39577921081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (327286582861971 / 800000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39306802617 / 1000000000000) (39306802710 / 1000000000000), orderedInterval (3282111146 / 1000000000000) (3282111239 / 1000000000000)))) (orderedInterval (-4965639706 / 1000000000000) (-4965637524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (295323056307609 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-65552095024 / 1000000000000) (-65552014685 / 1000000000000), orderedInterval (66213303306 / 1000000000000) (66213383645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (793279269866373 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52476945088 / 1000000000000) (-52476945087 / 1000000000000), orderedInterval (-21227221376 / 1000000000000) (-21227221375 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2153907532481841 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30515781397 / 1000000000000) (-30515695676 / 1000000000000), orderedInterval (15872833382 / 1000000000000) (15872919103 / 1000000000000)))) (orderedInterval (4516926967 / 1000000000000) (4516950593 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1586558539733433 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40059333932 / 1000000000000) (40059334252 / 1000000000000), orderedInterval (-581206804 / 1000000000000) (-581206484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2718595099857309 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29420377934 / 1000000000000) (29420405585 / 1000000000000), orderedInterval (-8455498010 / 1000000000000) (-8455470359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2002504846057431 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33766733231 / 1000000000000) (-33766714674 / 1000000000000), orderedInterval (11499086207 / 1000000000000) (11499104764 / 1000000000000)))) (orderedInterval (-2895852726 / 1000000000000) (-2895844610 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate472_chunkChecks3_1 :
    compactCertificate472.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3072357401084313 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20962983757 / 1000000000000) (20962987613 / 1000000000000), orderedInterval (-19746584664 / 1000000000000) (-19746580808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1773826372562577 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-36267205219 / 1000000000000) (-36267205214 / 1000000000000), orderedInterval (-10926076231 / 1000000000000) (-10926076225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3147686025791493 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21046615706 / 1000000000000) (21046619899 / 1000000000000), orderedInterval (-19145552147 / 1000000000000) (-19145547953 / 1000000000000)))) (orderedInterval (-4785974681 / 1000000000000) (-4785958507 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2940976592386617 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22989233191 / 1000000000000) (22989233192 / 1000000000000), orderedInterval (18351642771 / 1000000000000) (18351642772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2098819668289161 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26032840146 / 1000000000000) (-26032840145 / 1000000000000), orderedInterval (-23117841955 / 1000000000000) (-23117841954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2379837809599119 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29963086115 / 1000000000000) (-29963023902 / 1000000000000), orderedInterval (13149064042 / 1000000000000) (13149126255 / 1000000000000)))) (orderedInterval (11365407212 / 1000000000000) (11365409038 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1984060655079711 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14891310199 / 1000000000000) (14891310200 / 1000000000000), orderedInterval (32568998563 / 1000000000000) (32568998564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1752977759285931 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27165790635 / 1000000000000) (-27165773873 / 1000000000000), orderedInterval (26764472568 / 1000000000000) (26764489330 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (508081280231169 / 800000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30377077018 / 1000000000000) (30377077044 / 1000000000000), orderedInterval (8899277654 / 1000000000000) (8899277680 / 1000000000000)))) (orderedInterval (624289381 / 1000000000000) (624291491 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate472_chunkChecks3_2 :
    compactCertificate472.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1405379559972243 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (11417743725 / 1000000000000) (11417743726 / 1000000000000), orderedInterval (40990919492 / 1000000000000) (40990919493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1191355817140923 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7941594762 / 1000000000000) (-7941594761 / 1000000000000), orderedInterval (-45532216634 / 1000000000000) (-45532216633 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (745495153942569 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-56855460498 / 1000000000000) (-56855459193 / 1000000000000), orderedInterval (13690186369 / 1000000000000) (13690187673 / 1000000000000)))) (orderedInterval (5256141147 / 1000000000000) (5256141228 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (400929773195223 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37199033134 / 1000000000000) (37199033135 / 1000000000000), orderedInterval (70296429673 / 1000000000000) (70296429674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1088602326174669 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18076207884 / 1000000000000) (18076208353 / 1000000000000), orderedInterval (-44893798570 / 1000000000000) (-44893798100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1486393408916013 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41164128550 / 1000000000000) (41164129408 / 1000000000000), orderedInterval (-4380451628 / 1000000000000) (-4380450771 / 1000000000000)))) (orderedInterval (-910957896 / 1000000000000) (-910957769 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (628504846057431 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47021807986 / 1000000000000) (47021807987 / 1000000000000), orderedInterval (42752510732 / 1000000000000) (42752510733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2554837305677751 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31058536903 / 1000000000000) (-31058528163 / 1000000000000), orderedInterval (5689619114 / 1000000000000) (5689627854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1706512918650009 / 4000000000000) 3 (IntervalRat.scale (687 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (6029740302 / 1000000000000) (6029740303 / 1000000000000), orderedInterval (38148604235 / 1000000000000) (38148604236 / 1000000000000)))) (orderedInterval (16686456133 / 1000000000000) (16686461018 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate472_chunkChecks3 :
    compactCertificate472.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate472.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate472_chunkChecks3_0
    compactCertificate472_chunkChecks3_1 compactCertificate472_chunkChecks3_2

theorem compactCertificate472_chunkChecks4_0 :
    compactCertificate472.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (687 / 2) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-41366146885 / 1000000000000) (-41366141621 / 1000000000000), orderedInterval (11983846550 / 1000000000000) (11983851814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1012082181207987 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (30894930755 / 1000000000000) (30894942556 / 1000000000000), orderedInterval (-39577932882 / 1000000000000) (-39577921081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (327286582861971 / 800000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39306802617 / 1000000000000) (39306802710 / 1000000000000), orderedInterval (3282111146 / 1000000000000) (3282111239 / 1000000000000)))) (orderedInterval (-11641316712 / 1000000000000) (-11641314527 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (295323056307609 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-65552095024 / 1000000000000) (-65552014685 / 1000000000000), orderedInterval (66213303306 / 1000000000000) (66213383645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (793279269866373 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52476945088 / 1000000000000) (-52476945087 / 1000000000000), orderedInterval (-21227221376 / 1000000000000) (-21227221375 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2153907532481841 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30515781397 / 1000000000000) (-30515695676 / 1000000000000), orderedInterval (15872833382 / 1000000000000) (15872919103 / 1000000000000)))) (orderedInterval (12862877547 / 1000000000000) (12862914636 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1586558539733433 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40059333932 / 1000000000000) (40059334252 / 1000000000000), orderedInterval (-581206804 / 1000000000000) (-581206484 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2718595099857309 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29420377934 / 1000000000000) (29420405585 / 1000000000000), orderedInterval (-8455498010 / 1000000000000) (-8455470359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2002504846057431 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33766733231 / 1000000000000) (-33766714674 / 1000000000000), orderedInterval (11499086207 / 1000000000000) (11499104764 / 1000000000000)))) (orderedInterval (-17572589753 / 1000000000000) (-17572574412 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate472_chunkChecks4_1 :
    compactCertificate472.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3072357401084313 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20962983757 / 1000000000000) (20962987613 / 1000000000000), orderedInterval (-19746584664 / 1000000000000) (-19746580808 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1773826372562577 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-36267205219 / 1000000000000) (-36267205214 / 1000000000000), orderedInterval (-10926076231 / 1000000000000) (-10926076225 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3147686025791493 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21046615706 / 1000000000000) (21046619899 / 1000000000000), orderedInterval (-19145552147 / 1000000000000) (-19145547953 / 1000000000000)))) (orderedInterval (-18150661116 / 1000000000000) (-18150624540 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2940976592386617 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22989233191 / 1000000000000) (22989233192 / 1000000000000), orderedInterval (18351642771 / 1000000000000) (18351642772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2098819668289161 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26032840146 / 1000000000000) (-26032840145 / 1000000000000), orderedInterval (-23117841955 / 1000000000000) (-23117841954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2379837809599119 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29963086115 / 1000000000000) (-29963023902 / 1000000000000), orderedInterval (13149064042 / 1000000000000) (13149126255 / 1000000000000)))) (orderedInterval (-20815795113 / 1000000000000) (-20815791946 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1984060655079711 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14891310199 / 1000000000000) (14891310200 / 1000000000000), orderedInterval (32568998563 / 1000000000000) (32568998564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1752977759285931 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27165790635 / 1000000000000) (-27165773873 / 1000000000000), orderedInterval (26764472568 / 1000000000000) (26764489330 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (508081280231169 / 800000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30377077018 / 1000000000000) (30377077044 / 1000000000000), orderedInterval (8899277654 / 1000000000000) (8899277680 / 1000000000000)))) (orderedInterval (13951909442 / 1000000000000) (13951912176 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate472_chunkChecks4_2 :
    compactCertificate472.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1405379559972243 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (11417743725 / 1000000000000) (11417743726 / 1000000000000), orderedInterval (40990919492 / 1000000000000) (40990919493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1191355817140923 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-7941594762 / 1000000000000) (-7941594761 / 1000000000000), orderedInterval (-45532216634 / 1000000000000) (-45532216633 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (745495153942569 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-56855460498 / 1000000000000) (-56855459193 / 1000000000000), orderedInterval (13690186369 / 1000000000000) (13690187673 / 1000000000000)))) (orderedInterval (-1935115047 / 1000000000000) (-1935114970 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (400929773195223 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37199033134 / 1000000000000) (37199033135 / 1000000000000), orderedInterval (70296429673 / 1000000000000) (70296429674 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1088602326174669 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18076207884 / 1000000000000) (18076208353 / 1000000000000), orderedInterval (-44893798570 / 1000000000000) (-44893798100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1486393408916013 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41164128550 / 1000000000000) (41164129408 / 1000000000000), orderedInterval (-4380451628 / 1000000000000) (-4380450771 / 1000000000000)))) (orderedInterval (-4481951489 / 1000000000000) (-4481951354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (628504846057431 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (47021807986 / 1000000000000) (47021807987 / 1000000000000), orderedInterval (42752510732 / 1000000000000) (42752510733 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2554837305677751 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31058536903 / 1000000000000) (-31058528163 / 1000000000000), orderedInterval (5689619114 / 1000000000000) (5689627854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1706512918650009 / 4000000000000) 4 (IntervalRat.scale (687 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (6029740302 / 1000000000000) (6029740303 / 1000000000000), orderedInterval (38148604235 / 1000000000000) (38148604236 / 1000000000000)))) (orderedInterval (27444972782 / 1000000000000) (27444981802 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate472_chunkChecks4 :
    compactCertificate472.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate472.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate472_chunkChecks4_0
    compactCertificate472_chunkChecks4_1 compactCertificate472_chunkChecks4_2

theorem compactCertificate472_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate472.chunkCheck r b = true :=
  compactCertificate472.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate472_chunkChecks0
    · exact compactCertificate472_chunkChecks1
    · exact compactCertificate472_chunkChecks2
    · exact compactCertificate472_chunkChecks3
    · exact compactCertificate472_chunkChecks4)

theorem compactCertificate472_coefficient0 :
    compactCertificate472.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate472_coefficient1 :
    compactCertificate472.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate472_coefficient2 :
    compactCertificate472.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate472_coefficient3 :
    compactCertificate472.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate472_coefficient4 :
    compactCertificate472.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate472_coefficients : ∀ r : Fin 5,
    compactCertificate472.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate472_coefficient0
  · exact compactCertificate472_coefficient1
  · exact compactCertificate472_coefficient2
  · exact compactCertificate472_coefficient3
  · exact compactCertificate472_coefficient4

theorem compactCertificate472_lower : (1 : ℚ) ≤ compactCertificate472.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate472, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate472_proves {t : ℝ} (ht : t ∈ compactCertificate472.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate472.proves compactCertificate472_states compactCertificate472_chunks
    compactCertificate472_coefficients compactCertificate472_lower ht

end Erdos232
