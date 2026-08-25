/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate437 : CompactCertificate where
  left := 308
  right := 309
  center := 617 / 2
  grid := fun i =>
    match i.val with
    | 0 => 98
    | 1 => 72
    | 2 => 117
    | 3 => 21
    | 4 => 57
    | 5 => 154
    | 6 => 113
    | 7 => 194
    | 8 => 143
    | 9 => 220
    | 10 => 127
    | 11 => 225
    | 12 => 210
    | 13 => 150
    | 14 => 170
    | 15 => 142
    | 16 => 125
    | 17 => 182
    | 18 => 100
    | 19 => 85
    | 20 => 53
    | 21 => 29
    | 22 => 78
    | 23 => 106
    | 24 => 45
    | 25 => 183
    | _ => 122
  point := fun i =>
    match i.val with
    | 0 => 617 / 2
    | 1 => 908958814854917 / 4000000000000
    | 2 => 293938604986661 / 800000000000
    | 3 => 265231915199119 / 4000000000000
    | 4 => 712450232179843 / 4000000000000
    | 5 => 1934440971675831 / 4000000000000
    | 6 => 1424900464360303 / 4000000000000
    | 7 => 2441591232331819 / 4000000000000
    | 8 => 1798465050971521 / 4000000000000
    | 9 => 2759307884234383 / 4000000000000
    | 10 => 1593087149739607 / 4000000000000
    | 11 => 2826961103221763 / 4000000000000
    | 12 => 2641313766379247 / 4000000000000
    | 13 => 1884966135857951 / 4000000000000
    | 14 => 2137350696539529 / 4000000000000
    | 15 => 1781900180763001 / 4000000000000
    | 16 => 1574362849315021 / 4000000000000
    | 17 => 456311717471079 / 800000000000
    | 18 => 1262182224895013 / 4000000000000
    | 19 => 1069965850328893 / 4000000000000
    | 20 => 669534949028479 / 4000000000000
    | 21 => 360078122360193 / 4000000000000
    | 22 => 977682147379579 / 4000000000000
    | 23 => 1334941387629083 / 4000000000000
    | 24 => 564465050971521 / 4000000000000
    | 25 => 2294519094036641 / 4000000000000
    | _ => 1532632417477519 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (44832870935 / 1000000000000) (44832870949 / 1000000000000), orderedInterval (7249115356 / 1000000000000) (7249115370 / 1000000000000))
    | 1 => (orderedInterval (51162931491 / 1000000000000) (51162933696 / 1000000000000), orderedInterval (-13672903660 / 1000000000000) (-13672901454 / 1000000000000))
    | 2 => (orderedInterval (-24924240470 / 1000000000000) (-24924240469 / 1000000000000), orderedInterval (-33304396995 / 1000000000000) (-33304396994 / 1000000000000))
    | 3 => (orderedInterval (-88111025063 / 1000000000000) (-88111025062 / 1000000000000), orderedInterval (-42198570036 / 1000000000000) (-42198570035 / 1000000000000))
    | 4 => (orderedInterval (10322308827 / 1000000000000) (10322308878 / 1000000000000), orderedInterval (-58916314774 / 1000000000000) (-58916314723 / 1000000000000))
    | 5 => (orderedInterval (20189371723 / 1000000000000) (20189371724 / 1000000000000), orderedInterval (30125099826 / 1000000000000) (30125099827 / 1000000000000))
    | 6 => (orderedInterval (-38258705627 / 1000000000000) (-38258678895 / 1000000000000), orderedInterval (18036984424 / 1000000000000) (18037011155 / 1000000000000))
    | 7 => (orderedInterval (31964167236 / 1000000000000) (31964172380 / 1000000000000), orderedInterval (-4635992481 / 1000000000000) (-4635987337 / 1000000000000))
    | 8 => (orderedInterval (-34401719325 / 1000000000000) (-34401719324 / 1000000000000), orderedInterval (-15207698430 / 1000000000000) (-15207698428 / 1000000000000))
    | 9 => (orderedInterval (-15571772996 / 1000000000000) (-15571772769 / 1000000000000), orderedInterval (26095549678 / 1000000000000) (26095549904 / 1000000000000))
    | 10 => (orderedInterval (-2979981578 / 1000000000000) (-2979981577 / 1000000000000), orderedInterval (-39865753019 / 1000000000000) (-39865753018 / 1000000000000))
    | 11 => (orderedInterval (-18570561043 / 1000000000000) (-18570561042 / 1000000000000), orderedInterval (-23564765099 / 1000000000000) (-23564765098 / 1000000000000))
    | 12 => (orderedInterval (30481678648 / 1000000000000) (30481678772 / 1000000000000), orderedInterval (5889841368 / 1000000000000) (5889841491 / 1000000000000))
    | 13 => (orderedInterval (26051353549 / 1000000000000) (26051353550 / 1000000000000), orderedInterval (25900500564 / 1000000000000) (25900500565 / 1000000000000))
    | 14 => (orderedInterval (29976562879 / 1000000000000) (29976562880 / 1000000000000), orderedInterval (17084047274 / 1000000000000) (17084047275 / 1000000000000))
    | 15 => (orderedInterval (5798926570 / 1000000000000) (5798926571 / 1000000000000), orderedInterval (37349266901 / 1000000000000) (37349266902 / 1000000000000))
    | 16 => (orderedInterval (-39992352634 / 1000000000000) (-39992351640 / 1000000000000), orderedInterval (4302502821 / 1000000000000) (4302503815 / 1000000000000))
    | 17 => (orderedInterval (-18726662207 / 1000000000000) (-18726661218 / 1000000000000), orderedInterval (27682750809 / 1000000000000) (27682751798 / 1000000000000))
    | 18 => (orderedInterval (37058784157 / 1000000000000) (37058876384 / 1000000000000), orderedInterval (-25439133379 / 1000000000000) (-25439041153 / 1000000000000))
    | 19 => (orderedInterval (-46156008184 / 1000000000000) (-46156008183 / 1000000000000), orderedInterval (-15711907452 / 1000000000000) (-15711907451 / 1000000000000))
    | 20 => (orderedInterval (-61403662617 / 1000000000000) (-61403662417 / 1000000000000), orderedInterval (5921760024 / 1000000000000) (5921760223 / 1000000000000))
    | 21 => (orderedInterval (25064211548 / 1000000000000) (25064212087 / 1000000000000), orderedInterval (-80413075907 / 1000000000000) (-80413075369 / 1000000000000))
    | 22 => (orderedInterval (8191138086 / 1000000000000) (8191138087 / 1000000000000), orderedInterval (50357034442 / 1000000000000) (50357034443 / 1000000000000))
    | 23 => (orderedInterval (43598950367 / 1000000000000) (43598950444 / 1000000000000), orderedInterval (2520820681 / 1000000000000) (2520820758 / 1000000000000))
    | 24 => (orderedInterval (-33902867444 / 1000000000000) (-33902867443 / 1000000000000), orderedInterval (-57861973743 / 1000000000000) (-57861973742 / 1000000000000))
    | 25 => (orderedInterval (15869116772 / 1000000000000) (15869117056 / 1000000000000), orderedInterval (-29305142621 / 1000000000000) (-29305142337 / 1000000000000))
    | _ => (orderedInterval (25276324196 / 1000000000000) (25276324197 / 1000000000000), orderedInterval (31945360101 / 1000000000000) (31945360102 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (16784336984 / 1000000000000) (16784337032 / 1000000000000)
      | 1 => orderedInterval (-102427537 / 1000000000000) (-102427498 / 1000000000000)
      | 2 => orderedInterval (-1817324655 / 1000000000000) (-1817324479 / 1000000000000)
      | 3 => orderedInterval (-93790836 / 1000000000000) (-93790673 / 1000000000000)
      | 4 => orderedInterval (1761503593 / 1000000000000) (1761503633 / 1000000000000)
      | 5 => orderedInterval (1876116942 / 1000000000000) (1876117055 / 1000000000000)
      | 6 => orderedInterval (-5312019126 / 1000000000000) (-5312004296 / 1000000000000)
      | 7 => orderedInterval (-3990019142 / 1000000000000) (-3990019089 / 1000000000000)
      | _ => orderedInterval (-6238660900 / 1000000000000) (-6238660791 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (451832270 / 1000000000000) (451832316 / 1000000000000)
      | 1 => orderedInterval (-4500740486 / 1000000000000) (-4500740442 / 1000000000000)
      | 2 => orderedInterval (-252738248 / 1000000000000) (-252737903 / 1000000000000)
      | 3 => orderedInterval (-21855777015 / 1000000000000) (-21855776671 / 1000000000000)
      | 4 => orderedInterval (3363915637 / 1000000000000) (3363915702 / 1000000000000)
      | 5 => orderedInterval (1619151170 / 1000000000000) (1619151332 / 1000000000000)
      | 6 => orderedInterval (5036084838 / 1000000000000) (5036099996 / 1000000000000)
      | 7 => orderedInterval (-680867187 / 1000000000000) (-680867144 / 1000000000000)
      | _ => orderedInterval (-3168253920 / 1000000000000) (-3168253756 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-15955667795 / 1000000000000) (-15955667750 / 1000000000000)
      | 1 => orderedInterval (3371833160 / 1000000000000) (3371833220 / 1000000000000)
      | 2 => orderedInterval (5626502595 / 1000000000000) (5626503271 / 1000000000000)
      | 3 => orderedInterval (459018950 / 1000000000000) (459019696 / 1000000000000)
      | 4 => orderedInterval (-2782795349 / 1000000000000) (-2782795240 / 1000000000000)
      | 5 => orderedInterval (-2231042888 / 1000000000000) (-2231042644 / 1000000000000)
      | 6 => orderedInterval (4807260469 / 1000000000000) (4807276017 / 1000000000000)
      | 7 => orderedInterval (4068645522 / 1000000000000) (4068645563 / 1000000000000)
      | _ => orderedInterval (11834914863 / 1000000000000) (11834915121 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (531024197 / 1000000000000) (531024244 / 1000000000000)
      | 1 => orderedInterval (8648498334 / 1000000000000) (8648498422 / 1000000000000)
      | 2 => orderedInterval (11947288 / 1000000000000) (11948617 / 1000000000000)
      | 3 => orderedInterval (98470999372 / 1000000000000) (98471001014 / 1000000000000)
      | 4 => orderedInterval (-7228578219 / 1000000000000) (-7228578030 / 1000000000000)
      | 5 => orderedInterval (-5259925133 / 1000000000000) (-5259924756 / 1000000000000)
      | 6 => orderedInterval (-4978652393 / 1000000000000) (-4978636496 / 1000000000000)
      | 7 => orderedInterval (762674451 / 1000000000000) (762674494 / 1000000000000)
      | _ => orderedInterval (-3857438390 / 1000000000000) (-3857437968 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (14964077233 / 1000000000000) (14964077283 / 1000000000000)
      | 1 => orderedInterval (-8679547603 / 1000000000000) (-8679547468 / 1000000000000)
      | 2 => orderedInterval (-18861236642 / 1000000000000) (-18861234022 / 1000000000000)
      | 3 => orderedInterval (-4791209974 / 1000000000000) (-4791206315 / 1000000000000)
      | 4 => orderedInterval (543146757 / 1000000000000) (543147096 / 1000000000000)
      | 5 => orderedInterval (785713245 / 1000000000000) (785713849 / 1000000000000)
      | 6 => orderedInterval (-5149876004 / 1000000000000) (-5149859696 / 1000000000000)
      | 7 => orderedInterval (-4657767451 / 1000000000000) (-4657767407 / 1000000000000)
      | _ => orderedInterval (-26710378370 / 1000000000000) (-26710377653 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (2867715323 / 1000000000000) (2867730894 / 1000000000000)
    | 1 => orderedInterval (-19987392941 / 1000000000000) (-19987376570 / 1000000000000)
    | 2 => orderedInterval (9198669527 / 1000000000000) (9198687254 / 1000000000000)
    | 3 => orderedInterval (87100549507 / 1000000000000) (87100569541 / 1000000000000)
    | _ => orderedInterval (-52557078809 / 1000000000000) (-52557054333 / 1000000000000)

theorem compactCertificate437_stateChecks0 :
    compactCertificate437.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (617 / 2)) (orderedInterval (44832870935 / 1000000000000) (44832870949 / 1000000000000), orderedInterval (7249115356 / 1000000000000) (7249115370 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (908958814854917 / 4000000000000)) (orderedInterval (51162931491 / 1000000000000) (51162933696 / 1000000000000), orderedInterval (-13672903660 / 1000000000000) (-13672901454 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (293938604986661 / 800000000000)) (orderedInterval (-24924240470 / 1000000000000) (-24924240469 / 1000000000000), orderedInterval (-33304396995 / 1000000000000) (-33304396994 / 1000000000000))) = true
  rfl'

theorem compactCertificate437_stateChecks1 :
    compactCertificate437.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (265231915199119 / 4000000000000)) (orderedInterval (-88111025063 / 1000000000000) (-88111025062 / 1000000000000), orderedInterval (-42198570036 / 1000000000000) (-42198570035 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (712450232179843 / 4000000000000)) (orderedInterval (10322308827 / 1000000000000) (10322308878 / 1000000000000), orderedInterval (-58916314774 / 1000000000000) (-58916314723 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1934440971675831 / 4000000000000)) (orderedInterval (20189371723 / 1000000000000) (20189371724 / 1000000000000), orderedInterval (30125099826 / 1000000000000) (30125099827 / 1000000000000))) = true
  rfl'

theorem compactCertificate437_stateChecks2 :
    compactCertificate437.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1424900464360303 / 4000000000000)) (orderedInterval (-38258705627 / 1000000000000) (-38258678895 / 1000000000000), orderedInterval (18036984424 / 1000000000000) (18037011155 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (2441591232331819 / 4000000000000)) (orderedInterval (31964167236 / 1000000000000) (31964172380 / 1000000000000), orderedInterval (-4635992481 / 1000000000000) (-4635987337 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1798465050971521 / 4000000000000)) (orderedInterval (-34401719325 / 1000000000000) (-34401719324 / 1000000000000), orderedInterval (-15207698430 / 1000000000000) (-15207698428 / 1000000000000))) = true
  rfl'

theorem compactCertificate437_stateChecks3 :
    compactCertificate437.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 220 12 (2759307884234383 / 4000000000000)) (orderedInterval (-15571772996 / 1000000000000) (-15571772769 / 1000000000000), orderedInterval (26095549678 / 1000000000000) (26095549904 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1593087149739607 / 4000000000000)) (orderedInterval (-2979981578 / 1000000000000) (-2979981577 / 1000000000000), orderedInterval (-39865753019 / 1000000000000) (-39865753018 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (2826961103221763 / 4000000000000)) (orderedInterval (-18570561043 / 1000000000000) (-18570561042 / 1000000000000), orderedInterval (-23564765099 / 1000000000000) (-23564765098 / 1000000000000))) = true
  rfl'

theorem compactCertificate437_stateChecks4 :
    compactCertificate437.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (2641313766379247 / 4000000000000)) (orderedInterval (30481678648 / 1000000000000) (30481678772 / 1000000000000), orderedInterval (5889841368 / 1000000000000) (5889841491 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1884966135857951 / 4000000000000)) (orderedInterval (26051353549 / 1000000000000) (26051353550 / 1000000000000), orderedInterval (25900500564 / 1000000000000) (25900500565 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2137350696539529 / 4000000000000)) (orderedInterval (29976562879 / 1000000000000) (29976562880 / 1000000000000), orderedInterval (17084047274 / 1000000000000) (17084047275 / 1000000000000))) = true
  rfl'

theorem compactCertificate437_stateChecks5 :
    compactCertificate437.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1781900180763001 / 4000000000000)) (orderedInterval (5798926570 / 1000000000000) (5798926571 / 1000000000000), orderedInterval (37349266901 / 1000000000000) (37349266902 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1574362849315021 / 4000000000000)) (orderedInterval (-39992352634 / 1000000000000) (-39992351640 / 1000000000000), orderedInterval (4302502821 / 1000000000000) (4302503815 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (456311717471079 / 800000000000)) (orderedInterval (-18726662207 / 1000000000000) (-18726661218 / 1000000000000), orderedInterval (27682750809 / 1000000000000) (27682751798 / 1000000000000))) = true
  rfl'

theorem compactCertificate437_stateChecks6 :
    compactCertificate437.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1262182224895013 / 4000000000000)) (orderedInterval (37058784157 / 1000000000000) (37058876384 / 1000000000000), orderedInterval (-25439133379 / 1000000000000) (-25439041153 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1069965850328893 / 4000000000000)) (orderedInterval (-46156008184 / 1000000000000) (-46156008183 / 1000000000000), orderedInterval (-15711907452 / 1000000000000) (-15711907451 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (669534949028479 / 4000000000000)) (orderedInterval (-61403662617 / 1000000000000) (-61403662417 / 1000000000000), orderedInterval (5921760024 / 1000000000000) (5921760223 / 1000000000000))) = true
  rfl'

theorem compactCertificate437_stateChecks7 :
    compactCertificate437.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (360078122360193 / 4000000000000)) (orderedInterval (25064211548 / 1000000000000) (25064212087 / 1000000000000), orderedInterval (-80413075907 / 1000000000000) (-80413075369 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (977682147379579 / 4000000000000)) (orderedInterval (8191138086 / 1000000000000) (8191138087 / 1000000000000), orderedInterval (50357034442 / 1000000000000) (50357034443 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1334941387629083 / 4000000000000)) (orderedInterval (43598950367 / 1000000000000) (43598950444 / 1000000000000), orderedInterval (2520820681 / 1000000000000) (2520820758 / 1000000000000))) = true
  rfl'

theorem compactCertificate437_stateChecks8 :
    compactCertificate437.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (564465050971521 / 4000000000000)) (orderedInterval (-33902867444 / 1000000000000) (-33902867443 / 1000000000000), orderedInterval (-57861973743 / 1000000000000) (-57861973742 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2294519094036641 / 4000000000000)) (orderedInterval (15869116772 / 1000000000000) (15869117056 / 1000000000000), orderedInterval (-29305142621 / 1000000000000) (-29305142337 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1532632417477519 / 4000000000000)) (orderedInterval (25276324196 / 1000000000000) (25276324197 / 1000000000000), orderedInterval (31945360101 / 1000000000000) (31945360102 / 1000000000000))) = true
  rfl'

theorem compactCertificate437_states : ∀ j,
    BesselStateValid (compactCertificate437.point j) (compactCertificate437.state j) :=
  compactCertificate437.statesValid_of_checks3 compactCertificate437_stateChecks0
    compactCertificate437_stateChecks1 compactCertificate437_stateChecks2
    compactCertificate437_stateChecks3 compactCertificate437_stateChecks4
    compactCertificate437_stateChecks5 compactCertificate437_stateChecks6
    compactCertificate437_stateChecks7 compactCertificate437_stateChecks8

theorem compactCertificate437_chunkChecks0_0 :
    compactCertificate437.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (617 / 2) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44832870935 / 1000000000000) (44832870949 / 1000000000000), orderedInterval (7249115356 / 1000000000000) (7249115370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (908958814854917 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51162931491 / 1000000000000) (51162933696 / 1000000000000), orderedInterval (-13672903660 / 1000000000000) (-13672901454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (293938604986661 / 800000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24924240470 / 1000000000000) (-24924240469 / 1000000000000), orderedInterval (-33304396995 / 1000000000000) (-33304396994 / 1000000000000)))) (orderedInterval (16784336984 / 1000000000000) (16784337032 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (265231915199119 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-88111025063 / 1000000000000) (-88111025062 / 1000000000000), orderedInterval (-42198570036 / 1000000000000) (-42198570035 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (712450232179843 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (10322308827 / 1000000000000) (10322308878 / 1000000000000), orderedInterval (-58916314774 / 1000000000000) (-58916314723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1934440971675831 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20189371723 / 1000000000000) (20189371724 / 1000000000000), orderedInterval (30125099826 / 1000000000000) (30125099827 / 1000000000000)))) (orderedInterval (-102427537 / 1000000000000) (-102427498 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1424900464360303 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38258705627 / 1000000000000) (-38258678895 / 1000000000000), orderedInterval (18036984424 / 1000000000000) (18037011155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2441591232331819 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31964167236 / 1000000000000) (31964172380 / 1000000000000), orderedInterval (-4635992481 / 1000000000000) (-4635987337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1798465050971521 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34401719325 / 1000000000000) (-34401719324 / 1000000000000), orderedInterval (-15207698430 / 1000000000000) (-15207698428 / 1000000000000)))) (orderedInterval (-1817324655 / 1000000000000) (-1817324479 / 1000000000000))) = true
  rfl'

theorem compactCertificate437_chunkChecks0_1 :
    compactCertificate437.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2759307884234383 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15571772996 / 1000000000000) (-15571772769 / 1000000000000), orderedInterval (26095549678 / 1000000000000) (26095549904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1593087149739607 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2979981578 / 1000000000000) (-2979981577 / 1000000000000), orderedInterval (-39865753019 / 1000000000000) (-39865753018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2826961103221763 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18570561043 / 1000000000000) (-18570561042 / 1000000000000), orderedInterval (-23564765099 / 1000000000000) (-23564765098 / 1000000000000)))) (orderedInterval (-93790836 / 1000000000000) (-93790673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2641313766379247 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30481678648 / 1000000000000) (30481678772 / 1000000000000), orderedInterval (5889841368 / 1000000000000) (5889841491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1884966135857951 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26051353549 / 1000000000000) (26051353550 / 1000000000000), orderedInterval (25900500564 / 1000000000000) (25900500565 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2137350696539529 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29976562879 / 1000000000000) (29976562880 / 1000000000000), orderedInterval (17084047274 / 1000000000000) (17084047275 / 1000000000000)))) (orderedInterval (1761503593 / 1000000000000) (1761503633 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1781900180763001 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (5798926570 / 1000000000000) (5798926571 / 1000000000000), orderedInterval (37349266901 / 1000000000000) (37349266902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1574362849315021 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39992352634 / 1000000000000) (-39992351640 / 1000000000000), orderedInterval (4302502821 / 1000000000000) (4302503815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (456311717471079 / 800000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-18726662207 / 1000000000000) (-18726661218 / 1000000000000), orderedInterval (27682750809 / 1000000000000) (27682751798 / 1000000000000)))) (orderedInterval (1876116942 / 1000000000000) (1876117055 / 1000000000000))) = true
  rfl'

theorem compactCertificate437_chunkChecks0_2 :
    compactCertificate437.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1262182224895013 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37058784157 / 1000000000000) (37058876384 / 1000000000000), orderedInterval (-25439133379 / 1000000000000) (-25439041153 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1069965850328893 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-46156008184 / 1000000000000) (-46156008183 / 1000000000000), orderedInterval (-15711907452 / 1000000000000) (-15711907451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (669534949028479 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-61403662617 / 1000000000000) (-61403662417 / 1000000000000), orderedInterval (5921760024 / 1000000000000) (5921760223 / 1000000000000)))) (orderedInterval (-5312019126 / 1000000000000) (-5312004296 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (360078122360193 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25064211548 / 1000000000000) (25064212087 / 1000000000000), orderedInterval (-80413075907 / 1000000000000) (-80413075369 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (977682147379579 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8191138086 / 1000000000000) (8191138087 / 1000000000000), orderedInterval (50357034442 / 1000000000000) (50357034443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1334941387629083 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (43598950367 / 1000000000000) (43598950444 / 1000000000000), orderedInterval (2520820681 / 1000000000000) (2520820758 / 1000000000000)))) (orderedInterval (-3990019142 / 1000000000000) (-3990019089 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (564465050971521 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-33902867444 / 1000000000000) (-33902867443 / 1000000000000), orderedInterval (-57861973743 / 1000000000000) (-57861973742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2294519094036641 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (15869116772 / 1000000000000) (15869117056 / 1000000000000), orderedInterval (-29305142621 / 1000000000000) (-29305142337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1532632417477519 / 4000000000000) 0 (IntervalRat.scale (617 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25276324196 / 1000000000000) (25276324197 / 1000000000000), orderedInterval (31945360101 / 1000000000000) (31945360102 / 1000000000000)))) (orderedInterval (-6238660900 / 1000000000000) (-6238660791 / 1000000000000))) = true
  rfl'

theorem compactCertificate437_chunkChecks0 :
    compactCertificate437.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate437.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate437_chunkChecks0_0
    compactCertificate437_chunkChecks0_1 compactCertificate437_chunkChecks0_2

theorem compactCertificate437_chunkChecks1_0 :
    compactCertificate437.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (617 / 2) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44832870935 / 1000000000000) (44832870949 / 1000000000000), orderedInterval (7249115356 / 1000000000000) (7249115370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (908958814854917 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51162931491 / 1000000000000) (51162933696 / 1000000000000), orderedInterval (-13672903660 / 1000000000000) (-13672901454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (293938604986661 / 800000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24924240470 / 1000000000000) (-24924240469 / 1000000000000), orderedInterval (-33304396995 / 1000000000000) (-33304396994 / 1000000000000)))) (orderedInterval (451832270 / 1000000000000) (451832316 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (265231915199119 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-88111025063 / 1000000000000) (-88111025062 / 1000000000000), orderedInterval (-42198570036 / 1000000000000) (-42198570035 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (712450232179843 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (10322308827 / 1000000000000) (10322308878 / 1000000000000), orderedInterval (-58916314774 / 1000000000000) (-58916314723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1934440971675831 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20189371723 / 1000000000000) (20189371724 / 1000000000000), orderedInterval (30125099826 / 1000000000000) (30125099827 / 1000000000000)))) (orderedInterval (-4500740486 / 1000000000000) (-4500740442 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1424900464360303 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38258705627 / 1000000000000) (-38258678895 / 1000000000000), orderedInterval (18036984424 / 1000000000000) (18037011155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2441591232331819 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31964167236 / 1000000000000) (31964172380 / 1000000000000), orderedInterval (-4635992481 / 1000000000000) (-4635987337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1798465050971521 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34401719325 / 1000000000000) (-34401719324 / 1000000000000), orderedInterval (-15207698430 / 1000000000000) (-15207698428 / 1000000000000)))) (orderedInterval (-252738248 / 1000000000000) (-252737903 / 1000000000000))) = true
  rfl'

theorem compactCertificate437_chunkChecks1_1 :
    compactCertificate437.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2759307884234383 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15571772996 / 1000000000000) (-15571772769 / 1000000000000), orderedInterval (26095549678 / 1000000000000) (26095549904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1593087149739607 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2979981578 / 1000000000000) (-2979981577 / 1000000000000), orderedInterval (-39865753019 / 1000000000000) (-39865753018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2826961103221763 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18570561043 / 1000000000000) (-18570561042 / 1000000000000), orderedInterval (-23564765099 / 1000000000000) (-23564765098 / 1000000000000)))) (orderedInterval (-21855777015 / 1000000000000) (-21855776671 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2641313766379247 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30481678648 / 1000000000000) (30481678772 / 1000000000000), orderedInterval (5889841368 / 1000000000000) (5889841491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1884966135857951 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26051353549 / 1000000000000) (26051353550 / 1000000000000), orderedInterval (25900500564 / 1000000000000) (25900500565 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2137350696539529 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29976562879 / 1000000000000) (29976562880 / 1000000000000), orderedInterval (17084047274 / 1000000000000) (17084047275 / 1000000000000)))) (orderedInterval (3363915637 / 1000000000000) (3363915702 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1781900180763001 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (5798926570 / 1000000000000) (5798926571 / 1000000000000), orderedInterval (37349266901 / 1000000000000) (37349266902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1574362849315021 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39992352634 / 1000000000000) (-39992351640 / 1000000000000), orderedInterval (4302502821 / 1000000000000) (4302503815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (456311717471079 / 800000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-18726662207 / 1000000000000) (-18726661218 / 1000000000000), orderedInterval (27682750809 / 1000000000000) (27682751798 / 1000000000000)))) (orderedInterval (1619151170 / 1000000000000) (1619151332 / 1000000000000))) = true
  rfl'

theorem compactCertificate437_chunkChecks1_2 :
    compactCertificate437.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1262182224895013 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37058784157 / 1000000000000) (37058876384 / 1000000000000), orderedInterval (-25439133379 / 1000000000000) (-25439041153 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1069965850328893 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-46156008184 / 1000000000000) (-46156008183 / 1000000000000), orderedInterval (-15711907452 / 1000000000000) (-15711907451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (669534949028479 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-61403662617 / 1000000000000) (-61403662417 / 1000000000000), orderedInterval (5921760024 / 1000000000000) (5921760223 / 1000000000000)))) (orderedInterval (5036084838 / 1000000000000) (5036099996 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (360078122360193 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25064211548 / 1000000000000) (25064212087 / 1000000000000), orderedInterval (-80413075907 / 1000000000000) (-80413075369 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (977682147379579 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8191138086 / 1000000000000) (8191138087 / 1000000000000), orderedInterval (50357034442 / 1000000000000) (50357034443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1334941387629083 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (43598950367 / 1000000000000) (43598950444 / 1000000000000), orderedInterval (2520820681 / 1000000000000) (2520820758 / 1000000000000)))) (orderedInterval (-680867187 / 1000000000000) (-680867144 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (564465050971521 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-33902867444 / 1000000000000) (-33902867443 / 1000000000000), orderedInterval (-57861973743 / 1000000000000) (-57861973742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2294519094036641 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (15869116772 / 1000000000000) (15869117056 / 1000000000000), orderedInterval (-29305142621 / 1000000000000) (-29305142337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1532632417477519 / 4000000000000) 1 (IntervalRat.scale (617 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25276324196 / 1000000000000) (25276324197 / 1000000000000), orderedInterval (31945360101 / 1000000000000) (31945360102 / 1000000000000)))) (orderedInterval (-3168253920 / 1000000000000) (-3168253756 / 1000000000000))) = true
  rfl'

theorem compactCertificate437_chunkChecks1 :
    compactCertificate437.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate437.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate437_chunkChecks1_0
    compactCertificate437_chunkChecks1_1 compactCertificate437_chunkChecks1_2

theorem compactCertificate437_chunkChecks2_0 :
    compactCertificate437.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (617 / 2) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44832870935 / 1000000000000) (44832870949 / 1000000000000), orderedInterval (7249115356 / 1000000000000) (7249115370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (908958814854917 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51162931491 / 1000000000000) (51162933696 / 1000000000000), orderedInterval (-13672903660 / 1000000000000) (-13672901454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (293938604986661 / 800000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24924240470 / 1000000000000) (-24924240469 / 1000000000000), orderedInterval (-33304396995 / 1000000000000) (-33304396994 / 1000000000000)))) (orderedInterval (-15955667795 / 1000000000000) (-15955667750 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (265231915199119 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-88111025063 / 1000000000000) (-88111025062 / 1000000000000), orderedInterval (-42198570036 / 1000000000000) (-42198570035 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (712450232179843 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (10322308827 / 1000000000000) (10322308878 / 1000000000000), orderedInterval (-58916314774 / 1000000000000) (-58916314723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1934440971675831 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20189371723 / 1000000000000) (20189371724 / 1000000000000), orderedInterval (30125099826 / 1000000000000) (30125099827 / 1000000000000)))) (orderedInterval (3371833160 / 1000000000000) (3371833220 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1424900464360303 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38258705627 / 1000000000000) (-38258678895 / 1000000000000), orderedInterval (18036984424 / 1000000000000) (18037011155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2441591232331819 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31964167236 / 1000000000000) (31964172380 / 1000000000000), orderedInterval (-4635992481 / 1000000000000) (-4635987337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1798465050971521 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34401719325 / 1000000000000) (-34401719324 / 1000000000000), orderedInterval (-15207698430 / 1000000000000) (-15207698428 / 1000000000000)))) (orderedInterval (5626502595 / 1000000000000) (5626503271 / 1000000000000))) = true
  rfl'

theorem compactCertificate437_chunkChecks2_1 :
    compactCertificate437.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2759307884234383 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15571772996 / 1000000000000) (-15571772769 / 1000000000000), orderedInterval (26095549678 / 1000000000000) (26095549904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1593087149739607 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2979981578 / 1000000000000) (-2979981577 / 1000000000000), orderedInterval (-39865753019 / 1000000000000) (-39865753018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2826961103221763 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18570561043 / 1000000000000) (-18570561042 / 1000000000000), orderedInterval (-23564765099 / 1000000000000) (-23564765098 / 1000000000000)))) (orderedInterval (459018950 / 1000000000000) (459019696 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2641313766379247 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30481678648 / 1000000000000) (30481678772 / 1000000000000), orderedInterval (5889841368 / 1000000000000) (5889841491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1884966135857951 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26051353549 / 1000000000000) (26051353550 / 1000000000000), orderedInterval (25900500564 / 1000000000000) (25900500565 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2137350696539529 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29976562879 / 1000000000000) (29976562880 / 1000000000000), orderedInterval (17084047274 / 1000000000000) (17084047275 / 1000000000000)))) (orderedInterval (-2782795349 / 1000000000000) (-2782795240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1781900180763001 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (5798926570 / 1000000000000) (5798926571 / 1000000000000), orderedInterval (37349266901 / 1000000000000) (37349266902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1574362849315021 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39992352634 / 1000000000000) (-39992351640 / 1000000000000), orderedInterval (4302502821 / 1000000000000) (4302503815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (456311717471079 / 800000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-18726662207 / 1000000000000) (-18726661218 / 1000000000000), orderedInterval (27682750809 / 1000000000000) (27682751798 / 1000000000000)))) (orderedInterval (-2231042888 / 1000000000000) (-2231042644 / 1000000000000))) = true
  rfl'

theorem compactCertificate437_chunkChecks2_2 :
    compactCertificate437.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1262182224895013 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37058784157 / 1000000000000) (37058876384 / 1000000000000), orderedInterval (-25439133379 / 1000000000000) (-25439041153 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1069965850328893 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-46156008184 / 1000000000000) (-46156008183 / 1000000000000), orderedInterval (-15711907452 / 1000000000000) (-15711907451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (669534949028479 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-61403662617 / 1000000000000) (-61403662417 / 1000000000000), orderedInterval (5921760024 / 1000000000000) (5921760223 / 1000000000000)))) (orderedInterval (4807260469 / 1000000000000) (4807276017 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (360078122360193 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25064211548 / 1000000000000) (25064212087 / 1000000000000), orderedInterval (-80413075907 / 1000000000000) (-80413075369 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (977682147379579 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8191138086 / 1000000000000) (8191138087 / 1000000000000), orderedInterval (50357034442 / 1000000000000) (50357034443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1334941387629083 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (43598950367 / 1000000000000) (43598950444 / 1000000000000), orderedInterval (2520820681 / 1000000000000) (2520820758 / 1000000000000)))) (orderedInterval (4068645522 / 1000000000000) (4068645563 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (564465050971521 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-33902867444 / 1000000000000) (-33902867443 / 1000000000000), orderedInterval (-57861973743 / 1000000000000) (-57861973742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2294519094036641 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (15869116772 / 1000000000000) (15869117056 / 1000000000000), orderedInterval (-29305142621 / 1000000000000) (-29305142337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1532632417477519 / 4000000000000) 2 (IntervalRat.scale (617 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25276324196 / 1000000000000) (25276324197 / 1000000000000), orderedInterval (31945360101 / 1000000000000) (31945360102 / 1000000000000)))) (orderedInterval (11834914863 / 1000000000000) (11834915121 / 1000000000000))) = true
  rfl'

theorem compactCertificate437_chunkChecks2 :
    compactCertificate437.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate437.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate437_chunkChecks2_0
    compactCertificate437_chunkChecks2_1 compactCertificate437_chunkChecks2_2

theorem compactCertificate437_chunkChecks3_0 :
    compactCertificate437.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (617 / 2) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44832870935 / 1000000000000) (44832870949 / 1000000000000), orderedInterval (7249115356 / 1000000000000) (7249115370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (908958814854917 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51162931491 / 1000000000000) (51162933696 / 1000000000000), orderedInterval (-13672903660 / 1000000000000) (-13672901454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (293938604986661 / 800000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24924240470 / 1000000000000) (-24924240469 / 1000000000000), orderedInterval (-33304396995 / 1000000000000) (-33304396994 / 1000000000000)))) (orderedInterval (531024197 / 1000000000000) (531024244 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (265231915199119 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-88111025063 / 1000000000000) (-88111025062 / 1000000000000), orderedInterval (-42198570036 / 1000000000000) (-42198570035 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (712450232179843 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (10322308827 / 1000000000000) (10322308878 / 1000000000000), orderedInterval (-58916314774 / 1000000000000) (-58916314723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1934440971675831 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20189371723 / 1000000000000) (20189371724 / 1000000000000), orderedInterval (30125099826 / 1000000000000) (30125099827 / 1000000000000)))) (orderedInterval (8648498334 / 1000000000000) (8648498422 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1424900464360303 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38258705627 / 1000000000000) (-38258678895 / 1000000000000), orderedInterval (18036984424 / 1000000000000) (18037011155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2441591232331819 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31964167236 / 1000000000000) (31964172380 / 1000000000000), orderedInterval (-4635992481 / 1000000000000) (-4635987337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1798465050971521 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34401719325 / 1000000000000) (-34401719324 / 1000000000000), orderedInterval (-15207698430 / 1000000000000) (-15207698428 / 1000000000000)))) (orderedInterval (11947288 / 1000000000000) (11948617 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate437_chunkChecks3_1 :
    compactCertificate437.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2759307884234383 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15571772996 / 1000000000000) (-15571772769 / 1000000000000), orderedInterval (26095549678 / 1000000000000) (26095549904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1593087149739607 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2979981578 / 1000000000000) (-2979981577 / 1000000000000), orderedInterval (-39865753019 / 1000000000000) (-39865753018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2826961103221763 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18570561043 / 1000000000000) (-18570561042 / 1000000000000), orderedInterval (-23564765099 / 1000000000000) (-23564765098 / 1000000000000)))) (orderedInterval (98470999372 / 1000000000000) (98471001014 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2641313766379247 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30481678648 / 1000000000000) (30481678772 / 1000000000000), orderedInterval (5889841368 / 1000000000000) (5889841491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1884966135857951 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26051353549 / 1000000000000) (26051353550 / 1000000000000), orderedInterval (25900500564 / 1000000000000) (25900500565 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2137350696539529 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29976562879 / 1000000000000) (29976562880 / 1000000000000), orderedInterval (17084047274 / 1000000000000) (17084047275 / 1000000000000)))) (orderedInterval (-7228578219 / 1000000000000) (-7228578030 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1781900180763001 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (5798926570 / 1000000000000) (5798926571 / 1000000000000), orderedInterval (37349266901 / 1000000000000) (37349266902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1574362849315021 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39992352634 / 1000000000000) (-39992351640 / 1000000000000), orderedInterval (4302502821 / 1000000000000) (4302503815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (456311717471079 / 800000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-18726662207 / 1000000000000) (-18726661218 / 1000000000000), orderedInterval (27682750809 / 1000000000000) (27682751798 / 1000000000000)))) (orderedInterval (-5259925133 / 1000000000000) (-5259924756 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate437_chunkChecks3_2 :
    compactCertificate437.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1262182224895013 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37058784157 / 1000000000000) (37058876384 / 1000000000000), orderedInterval (-25439133379 / 1000000000000) (-25439041153 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1069965850328893 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-46156008184 / 1000000000000) (-46156008183 / 1000000000000), orderedInterval (-15711907452 / 1000000000000) (-15711907451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (669534949028479 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-61403662617 / 1000000000000) (-61403662417 / 1000000000000), orderedInterval (5921760024 / 1000000000000) (5921760223 / 1000000000000)))) (orderedInterval (-4978652393 / 1000000000000) (-4978636496 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (360078122360193 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25064211548 / 1000000000000) (25064212087 / 1000000000000), orderedInterval (-80413075907 / 1000000000000) (-80413075369 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (977682147379579 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8191138086 / 1000000000000) (8191138087 / 1000000000000), orderedInterval (50357034442 / 1000000000000) (50357034443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1334941387629083 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (43598950367 / 1000000000000) (43598950444 / 1000000000000), orderedInterval (2520820681 / 1000000000000) (2520820758 / 1000000000000)))) (orderedInterval (762674451 / 1000000000000) (762674494 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (564465050971521 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-33902867444 / 1000000000000) (-33902867443 / 1000000000000), orderedInterval (-57861973743 / 1000000000000) (-57861973742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2294519094036641 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (15869116772 / 1000000000000) (15869117056 / 1000000000000), orderedInterval (-29305142621 / 1000000000000) (-29305142337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1532632417477519 / 4000000000000) 3 (IntervalRat.scale (617 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25276324196 / 1000000000000) (25276324197 / 1000000000000), orderedInterval (31945360101 / 1000000000000) (31945360102 / 1000000000000)))) (orderedInterval (-3857438390 / 1000000000000) (-3857437968 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate437_chunkChecks3 :
    compactCertificate437.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate437.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate437_chunkChecks3_0
    compactCertificate437_chunkChecks3_1 compactCertificate437_chunkChecks3_2

theorem compactCertificate437_chunkChecks4_0 :
    compactCertificate437.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (617 / 2) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44832870935 / 1000000000000) (44832870949 / 1000000000000), orderedInterval (7249115356 / 1000000000000) (7249115370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (908958814854917 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51162931491 / 1000000000000) (51162933696 / 1000000000000), orderedInterval (-13672903660 / 1000000000000) (-13672901454 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (293938604986661 / 800000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24924240470 / 1000000000000) (-24924240469 / 1000000000000), orderedInterval (-33304396995 / 1000000000000) (-33304396994 / 1000000000000)))) (orderedInterval (14964077233 / 1000000000000) (14964077283 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (265231915199119 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-88111025063 / 1000000000000) (-88111025062 / 1000000000000), orderedInterval (-42198570036 / 1000000000000) (-42198570035 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (712450232179843 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (10322308827 / 1000000000000) (10322308878 / 1000000000000), orderedInterval (-58916314774 / 1000000000000) (-58916314723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1934440971675831 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20189371723 / 1000000000000) (20189371724 / 1000000000000), orderedInterval (30125099826 / 1000000000000) (30125099827 / 1000000000000)))) (orderedInterval (-8679547603 / 1000000000000) (-8679547468 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1424900464360303 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38258705627 / 1000000000000) (-38258678895 / 1000000000000), orderedInterval (18036984424 / 1000000000000) (18037011155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2441591232331819 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (31964167236 / 1000000000000) (31964172380 / 1000000000000), orderedInterval (-4635992481 / 1000000000000) (-4635987337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1798465050971521 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-34401719325 / 1000000000000) (-34401719324 / 1000000000000), orderedInterval (-15207698430 / 1000000000000) (-15207698428 / 1000000000000)))) (orderedInterval (-18861236642 / 1000000000000) (-18861234022 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate437_chunkChecks4_1 :
    compactCertificate437.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2759307884234383 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15571772996 / 1000000000000) (-15571772769 / 1000000000000), orderedInterval (26095549678 / 1000000000000) (26095549904 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1593087149739607 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2979981578 / 1000000000000) (-2979981577 / 1000000000000), orderedInterval (-39865753019 / 1000000000000) (-39865753018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2826961103221763 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18570561043 / 1000000000000) (-18570561042 / 1000000000000), orderedInterval (-23564765099 / 1000000000000) (-23564765098 / 1000000000000)))) (orderedInterval (-4791209974 / 1000000000000) (-4791206315 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2641313766379247 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (30481678648 / 1000000000000) (30481678772 / 1000000000000), orderedInterval (5889841368 / 1000000000000) (5889841491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1884966135857951 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26051353549 / 1000000000000) (26051353550 / 1000000000000), orderedInterval (25900500564 / 1000000000000) (25900500565 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2137350696539529 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29976562879 / 1000000000000) (29976562880 / 1000000000000), orderedInterval (17084047274 / 1000000000000) (17084047275 / 1000000000000)))) (orderedInterval (543146757 / 1000000000000) (543147096 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1781900180763001 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (5798926570 / 1000000000000) (5798926571 / 1000000000000), orderedInterval (37349266901 / 1000000000000) (37349266902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1574362849315021 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39992352634 / 1000000000000) (-39992351640 / 1000000000000), orderedInterval (4302502821 / 1000000000000) (4302503815 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (456311717471079 / 800000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-18726662207 / 1000000000000) (-18726661218 / 1000000000000), orderedInterval (27682750809 / 1000000000000) (27682751798 / 1000000000000)))) (orderedInterval (785713245 / 1000000000000) (785713849 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate437_chunkChecks4_2 :
    compactCertificate437.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1262182224895013 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37058784157 / 1000000000000) (37058876384 / 1000000000000), orderedInterval (-25439133379 / 1000000000000) (-25439041153 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1069965850328893 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-46156008184 / 1000000000000) (-46156008183 / 1000000000000), orderedInterval (-15711907452 / 1000000000000) (-15711907451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (669534949028479 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-61403662617 / 1000000000000) (-61403662417 / 1000000000000), orderedInterval (5921760024 / 1000000000000) (5921760223 / 1000000000000)))) (orderedInterval (-5149876004 / 1000000000000) (-5149859696 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (360078122360193 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (25064211548 / 1000000000000) (25064212087 / 1000000000000), orderedInterval (-80413075907 / 1000000000000) (-80413075369 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (977682147379579 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8191138086 / 1000000000000) (8191138087 / 1000000000000), orderedInterval (50357034442 / 1000000000000) (50357034443 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1334941387629083 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (43598950367 / 1000000000000) (43598950444 / 1000000000000), orderedInterval (2520820681 / 1000000000000) (2520820758 / 1000000000000)))) (orderedInterval (-4657767451 / 1000000000000) (-4657767407 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (564465050971521 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-33902867444 / 1000000000000) (-33902867443 / 1000000000000), orderedInterval (-57861973743 / 1000000000000) (-57861973742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2294519094036641 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (15869116772 / 1000000000000) (15869117056 / 1000000000000), orderedInterval (-29305142621 / 1000000000000) (-29305142337 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1532632417477519 / 4000000000000) 4 (IntervalRat.scale (617 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25276324196 / 1000000000000) (25276324197 / 1000000000000), orderedInterval (31945360101 / 1000000000000) (31945360102 / 1000000000000)))) (orderedInterval (-26710378370 / 1000000000000) (-26710377653 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate437_chunkChecks4 :
    compactCertificate437.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate437.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate437_chunkChecks4_0
    compactCertificate437_chunkChecks4_1 compactCertificate437_chunkChecks4_2

theorem compactCertificate437_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate437.chunkCheck r b = true :=
  compactCertificate437.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate437_chunkChecks0
    · exact compactCertificate437_chunkChecks1
    · exact compactCertificate437_chunkChecks2
    · exact compactCertificate437_chunkChecks3
    · exact compactCertificate437_chunkChecks4)

theorem compactCertificate437_coefficient0 :
    compactCertificate437.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate437_coefficient1 :
    compactCertificate437.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate437_coefficient2 :
    compactCertificate437.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate437_coefficient3 :
    compactCertificate437.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate437_coefficient4 :
    compactCertificate437.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate437_coefficients : ∀ r : Fin 5,
    compactCertificate437.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate437_coefficient0
  · exact compactCertificate437_coefficient1
  · exact compactCertificate437_coefficient2
  · exact compactCertificate437_coefficient3
  · exact compactCertificate437_coefficient4

theorem compactCertificate437_lower : (1 : ℚ) ≤ compactCertificate437.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate437, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate437_proves {t : ℝ} (ht : t ∈ compactCertificate437.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate437.proves compactCertificate437_states compactCertificate437_chunks
    compactCertificate437_coefficients compactCertificate437_lower ht

end Erdos232
